/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8 -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.StatementComposed -- proof-setup: allow-public-import
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.ReductionDsl.SM.DeliverForgeMultiPotOK
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap
import Computational.Proofs.SessionCostedFig8.RedFSUniEval
import Computational.Proofs.SessionCostedFig8.Stage2Swap

/-!
# Stage-2 `SessionCostedDF` Helpers (`SessionCostedDFStage2`)

Houses relocated `DeliverForge` query/invariant lemmas (`simDeliverForgeClamp_sendShort`,
`hooksCKAShifted_commit_vR`, `hooksCKAShifted_vrInv_fromAEADPRG`), Stage-2 Critic `S3` + `[B4]` +
`[B7]` + `[B8]` reduction bounds, and Stage-2 mixture `fig8MixShortPrivV1` / `fig8MixShortAuthV1`
bridges so `Computational/Proofs/SessionCostedDF.lean` stays comfortably below 1,200 lines.-/

namespace Computational.Proofs.SessionCostedDFStage2

public section

set_option autoImplicit false
set_option exponentiation.threshold 1024

open scoped ENNReal BigOperators
open OracleSpec OracleComp _root_.ReductionDsl
open _root_.CryptoGames _root_.CryptoGames.LibsignalSM _root_.CryptoGames.LibsignalSM.Inst
open _root_.CryptoGames.Ratchet _root_.CryptoGames.CKA _root_.CryptoGames.SM
open _root_.CryptoGames.SM.Construction
open _root_.CryptoGames.LibsignalSession _root_.CryptoGames.Ratchet.LibsignalInst
open _root_.CryptoGames.Ratchet.LibsignalSim _root_.CryptoGames.LibsignalSM.Proofs
open _root_.CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open _root_.CryptoVerification.E2E
open _root_.CryptoGames.CBC _root_.CryptoGames.FSAEAD

local notation "Bytes" => List (BitVec 8)

section RelocatedDFHelpers

open _root_.CryptoVerification.LibsignalSession.HeadlineV1
open _root_.CryptoVerification.E2E.Signed

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_runDFM {PQ : Type} [Inhabited PQ] {ℓ : ℕ}
    {Q : (HeadlineV1.DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {n : ℕ} (hx : HeadlineV1.df_QBC Q x n)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    IsQueryBoundP (LibsignalSim.runDFM x sC ex) Q n := by
  unfold LibsignalSim.runDFM
  rw [← Nat.add_zero n]
  exact isQueryBoundP_bind (hx sC ex) fun p _ => isQueryBoundP_pure Q (p.1.1, p.1.2, p.2) 0

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_deliverQueryDF_QShortDF {ℓ : ℕ} (Q : Party) (c : Fig8C Pt) :
    IsQueryBoundP
      (DeliverForge.deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c)
      (HeadlineV1.QShortDF Pt ℓ) 0 :=
  (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ)
    (.inr (.inl (.inl (.inl (.inr (Q, c)))))) 0).2 fun h => nomatch h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_injectQueryDF_QShortDF {ℓ : ℕ} (Q : Party) (c : Fig8C Pt) :
    IsQueryBoundP
      (DeliverForge.injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c)
      (HeadlineV1.QShortDF Pt ℓ) 0 :=
  (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ)
    (.inr (.inl (.inl (.inr (Q, c))))) 0).2 fun h => nomatch h

omit [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_deliverForgeSemHook_onProbe {PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (Q : Party) (c' : Fig8C Pt) (ex : List (Fig8C Pt)) :
    IsQueryBoundP
      ((LibsignalSim.deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => Proofs.Refinement.sameWireFig8 c c') with _ | c
  · simp
  · have hq : IsQueryBoundP
        (DeliverForge.deliverForgeQuery
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q c c') (HeadlineV1.QShortDF Pt ℓ) 0 :=
      (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inr (.inr (Q, c, c'))) 0).2
        fun h => nomatch h
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind hq fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdAnswerHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdAnswerHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel ci? Tpk pq' c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdAnswerHook LibsignalSim.deliverForgeSemHook
  dsimp only
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun ⟨res, ex'⟩ _ => by rcases res with _ | (_ | _) <;> simp
  split_ifs
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_deliverQueryDF_QShortDF Q c') fun _ _ => by simp
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_injectQueryDF_QShortDF Q c') fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semResyncHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × CBC.Plain ℓ))) :
    IsQueryBoundP
      (LibsignalSim.semResyncHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w ci? Tpk pq' c r)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semResyncHook LibsignalSim.deliverForgeSemHook
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp
  · dsimp only
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind ?_ fun ⟨res, ex'⟩ _ => by rcases res with _ | (_ | _) <;> simp
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_deliverQueryDF_QShortDF Q c) fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdEvictHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdEvictHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel Tpk pq' c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdEvictHook
  split_ifs
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_deliverForgeSemHook_onProbe (PQC := PQC) Q c' ex)
      fun _ _ => by simp
  · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel none
      Tpk pq' c'

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel ci? Tpk pq' honestC c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdHook
  rcases honestC with _ | c
  · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel ci?
      Tpk pq' c'
  · dsimp only
    split_ifs
    · rcases LibsignalSim.evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · rw [← Nat.zero_add 0]
        exact isQueryBoundP_bind
          (isQueryBoundP_deliverForgeSemHook_onProbe (PQC := PQC) Q c' ex)
          fun _ _ => by simp
      · exact isQueryBoundP_semResyncHook_QShortDF P Dh encPt encT lam qep sC ex Q w ci?
          Tpk pq' c r
    · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel ci?
        Tpk pq' c'

omit [SampleableType Pt] in
private lemma isQueryBoundP_semRecvHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semRecvHook
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · simp
    · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · simp
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact isQueryBoundP_semFwdHook_QShortDF P Dh encPt encT lam qep B _ ex
                    Q w isDel none pk pq' _ _
                · simp only [↓reduceIte]
                  exact isQueryBoundP_semFwdEvictHook_QShortDF P Dh encPt encT lam qep _ ex
                    Q w isDel pk pq' _
            · simp
          · simp
        · simp
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects
            i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact isQueryBoundP_semFwdHook_QShortDF P Dh encPt encT lam qep B sC ex
            Q w isDel (some ci) pk pq' _ _
        · simp
  · simp

omit [SampleableType Pt] in
/-- Under `LengthsOk P ℓ`, `LibsignalSim.simDeliverForgeClamp ... A` sends only short public parts
(`HeadlineV1.SendMsgsOkDF (·.1.shortB)`). -/
theorem simDeliverForgeClamp_sendShort {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) {ℓ : ℕ} (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) PQC Bytes) :
    HeadlineV1.SendMsgsOkDF (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1.shortB)
      (LibsignalSim.simDeliverForgeClamp P Dh encPt encT decT lam qep B A) := by
  unfold HeadlineV1.SendMsgsOkDF LibsignalSim.simDeliverForgeClamp
  have hpqr : IsQueryBoundP
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256))
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
    induction ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx ih =>
      change IsQueryBoundP (query (spec := HeadlineV1.DFSpec Pt ℓ) (.inl t) >>=
        fun u => liftM (mx u)) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        ((isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inl t) 0).2 fun h => nomatch h)
        fun u _ => ih u
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind hpqr fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  have hstep :
      ∀ (t : (unifSpec + SM.spec (GhostState PQ) (CBC.Plain ℓ) PQC Bytes).Domain)
        (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)),
        IsQueryBoundP
          ((LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B t).run (sC, ex))
          (HeadlineV1.QShortDF Pt ℓ) 0 := by
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) sC ex
    · show IsQueryBoundP (query (spec := HeadlineV1.DFSpec Pt ℓ) (.inl n) >>=
        fun a => pure (a, (sC, ex))) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        ((isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inl n) 0).2 fun h => nomatch h)
        fun _ _ => by simp
    · change IsQueryBoundP
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m none r) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simSendC_short P hL qep _ HeadlineV1.hQ_QShortDF Q m none r))
        sC ex
    · change IsQueryBoundP
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m₀ (some m₁) r) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simSendC_short P hL qep _ HeadlineV1.hQ_QShortDF Q m₀ (some m₁) r))
        sC ex
    · change IsQueryBoundP
        (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
          qep B sC ex Q w true >>= fun ⟨rr, sC₁, ex₁⟩ =>
            (LibsignalSim.deliverForgeSemHook (PQC := PQC)).onDeliverPost Q none rr ex₁ >>=
              fun ex₂ => pure (rr, (sC₁, ex₂)))
        (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        (isQueryBoundP_semRecvHook_QShortDF P Dh encPt encT decT lam qep B sC ex Q w true)
        fun ⟨rr, sC₁, ex₁⟩ _ => by simp [LibsignalSim.deliverForgeSemHook]
    · exact isQueryBoundP_semRecvHook_QShortDF P Dh encPt encT decT lam qep B sC ex Q w false
    · change IsQueryBoundP
        (LibsignalSim.semCorrHook P Dh encT LibsignalSim.deliverForgeSemHook sC ex Q)
        (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semCorrHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simCorrC P Dh encT HeadlineV1.hQ_QShortDF 0
            (fun _ h => nomatch h) Q))
        sC ex
  exact Computational.Proofs.GameHop.StateSim.isQueryBoundP_simulateQ_stateT_inv
    (LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B)
    (p := fun _ => False) (fun _ _ => True) 0
    (fun _ _ _ h => False.elim h)
    (fun t _ ⟨sC, ex⟩ _ _ => ⟨hstep t sC ex, fun _ _ => trivial⟩)
    A 0 (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false A 0) (_, []) trivial

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_commit_vR {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    (ctx : SM.Engine.Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : SM.Engine.VP (Option Γ) T RSt SS RS) (h : DeliverForge.CKAStateShifted Γ T I) :
    ∀ res ∈ support (((DeliverForge.hooksCKAShifted cka prng fs l tStar).commit
        ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  dsimp only at hEq
  subst hEq
  dsimp only [DeliverForge.hooksCKAShifted] at hmem
  by_cases h1 : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [h1, ↓reduceIte, DeliverForge.liftCShifted, StateT.run_bind, StateT.run_lift,
      mem_support_bind_iff] at hmem
    obtain ⟨rcvRes, _, hmem⟩ := hmem
    rcases rcvRes with _ | ⟨⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
    · dsimp only at hmem
      by_cases h2 : l + 2 ≤ new.tcur
      · simp only [h2, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          mem_support_bind_iff] at hmem
        obtain ⟨γ?, _, hmem⟩ := hmem
        rcases γ? with _ | γ'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
      · simp only [h2, ↓reduceIte] at hmem
        by_cases h3 : new.tcur + 1 ≤ l
        · simp only [h3, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            mem_support_bind_iff] at hmem
          obtain ⟨γ?, _, hmem⟩ := hmem
          rcases γ? with _ | γ'
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨h, _⟩; cases h
          · simp only [DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq, Option.some.injEq] at hmem
            rcases hmem with ⟨rfl, rfl⟩; rfl
        · simp only [h3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_vrInv_fromAEADPRG {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip l tStar : ℕ) :
    SM.Engine.HooksVRInv (SM.Engine.RSReach maxSkip)
      (DeliverForge.hooksCKAShifted cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    SM.Construction.hooksCKAShifted_startRecv_rs cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar
      (SM.Engine.RSReach.init ae G maxSkip) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [DeliverForge.hooksCKAShifted] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (SM.Engine.RSReach.receive ae G maxSkip _ hVR hrec.symm).2
  commit_vR := hooksCKAShifted_commit_vR cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar

end RelocatedDFHelpers

section V1SessionRedsBoundedHelpers

local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-- `[B4]`-clamped leak guess for Stage-2 `(tL, par)` bucket reductions. -/
@[expose] def clampDFBucketLeakGuess (qep : ℕ) (tL : Option ℕ) : Option ℕ :=
  if tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1) then tL else none

/-- `[B4]`-clamped hybrid index for Stage-2 `(tL, par)` bucket PRNG reductions. -/
@[expose] def clampDFBucketEpoch (qep t : ℕ) : ℕ :=
  if t < (qep + 1) + 2 then t else 0

@[simp] theorem clampDFBucketLeakGuess_of_mem {qep : ℕ} {tL : Option ℕ}
    (htL : tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1)) :
    clampDFBucketLeakGuess qep tL = tL := by
  simp [clampDFBucketLeakGuess, htL]

@[simp] theorem clampDFBucketEpoch_of_lt {qep t : ℕ} (ht : t < (qep + 1) + 2) :
    clampDFBucketEpoch qep t = t := by
  simp [clampDFBucketEpoch, ht]

private theorem clampDFBucketLeakGuess_getD_le (qep : ℕ) (tL : Option ℕ) :
    (clampDFBucketLeakGuess qep tL).getD 0 ≤ (qep + 1) + 2 := by
  unfold clampDFBucketLeakGuess
  split_ifs with htL
  · unfold admissibleLastLeakGuesses at htL
    rcases tL with _ | k
    · simp
    · simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
        Option.some.injEq, false_or, exists_eq_right] at htL
      simp
      omega
  · simp

private theorem clampDFBucketEpoch_lt (qep t : ℕ) :
    clampDFBucketEpoch qep t < (qep + 1) + 2 := by
  unfold clampDFBucketEpoch
  split_ifs with ht
  · exact ht
  · omega

private theorem mem_admissibleLastLeakGuesses_sub_two {t : ℕ} (ht : 2 ≤ t) :
    some (t - 2) ∈ admissibleLastLeakGuesses 2 t := by
  unfold admissibleLastLeakGuesses
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
    Option.some.injEq, false_or, exists_eq_right]
  omega

private theorem mem_admissibleLastLeakGuesses_sub_three {t : ℕ} (ht : 3 ≤ t) :
    some (t - 3) ∈ admissibleLastLeakGuesses 3 t := by
  unfold admissibleLastLeakGuesses
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
    Option.some.injEq, false_or, exists_eq_right]
  omega

private theorem redPRNGAuthDFAtomicProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    PRFPRNG.MakesAtMostQueries
      ((redPRNGAuthDFAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) :=
  Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
    (Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK.redPRNGAuthDFProg_makesAtMostQueries
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q A
      (hA.of_imp fun x hx => by cases x <;> [cases hx; rfl]))

private theorem redPRNGAuthDFBucketHybridAtomicProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    PRFPRNG.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFBucketHybridAtomicProg
        Dh encPt C ℓ encT idOf lam qep q tL par t).eval (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) :=
  Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
    (_root_.CryptoGames.SM.Construction.redPRNGAuthDFBucketHybridProg_makesAtMostQueries
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL par t q A
      (hA.of_imp fun x hx => by cases x <;> [cases hx; rfl]))

theorem v1SessionReds_nonFs_df_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ q + 10) :
    let B := ratchetCostBudget q (qep + 1)
    let B_cka_u := fun tL par =>
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFBucketAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (clampDFBucketLeakGuess qep tL) par
    let B_prng_u := fun tL par t =>
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFBucketHybridAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
        (clampDFBucketLeakGuess qep tL) par (clampDFBucketEpoch qep t)
    (∀ t ∈ Finset.Ico 2 ((qep + 1) + 2),
      GRedBounded
        (redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (some (t - 2)) t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B ∧
      GRedBounded
        (redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (some (t - 2)) t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
    (∀ t ∈ Finset.Ico 3 ((qep + 1) + 2),
      GRedBounded
        (redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (some (t - 3)) t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B ∧
      GRedBounded
        (redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (some (t - 3)) t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
    (∀ tL : Option ℕ, ∀ par : Bool,
      GRedBounded (B_cka_u tL par) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B ∧
      (∀ t : ℕ, GRedBounded (B_prng_u tL par t) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B)) ∧
    (∀ t : ℕ,
      ∀ A : OracleComp
          (unifSpec +
            _root_.CryptoGames.SM.specDF (LibsignalSim.Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
          Bool,
        A.IsQueryBoundP (· matches .inr _) q →
          PRFPRNG.MakesAtMostQueries
            ((redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
              (some (t - 2)) t).eval (fun _ => A) ())
            (min (2 + 2 * q) (q + 3)) ∧
          PRFPRNG.MakesAtMostQueries
            ((redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
              (some (t - 3)) t).eval (fun _ => A) ())
            (min (2 + 2 * q) (q + 3))) ∧
    (∀ tL : Option ℕ, ∀ par : Bool, ∀ t : ℕ,
      ∀ A : OracleComp
          (unifSpec +
            _root_.CryptoGames.SM.specDF (LibsignalSim.Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
          Bool,
        A.IsQueryBoundP (· matches .inr _) q →
          PRFPRNG.MakesAtMostQueries
            ((B_prng_u tL par t).eval (fun _ => A) ())
            (min (2 + 2 * q) (q + 3))) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun tL par => ?_, fun t A hA => ?_, fun tL par t A hA => ?_⟩
  · simp only [Finset.mem_Ico] at ht
    exact ⟨Computational.Proofs.SessionCostedFig8.DFProgBoundsBase.redCKAAuthDFAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t ht.2 (some (t - 2))
        (mem_admissibleLastLeakGuesses_sub_two ht.1) (by omega),
      Computational.Proofs.SessionCostedFig8.DFProgBoundsBase.redPRNGAuthDFAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t ht.2 (some (t - 2))
        (mem_admissibleLastLeakGuesses_sub_two ht.1) (by omega)⟩
  · simp only [Finset.mem_Ico] at ht
    exact ⟨Computational.Proofs.SessionCostedFig8.DFProgBoundsBase.redCKAAuthDFAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t ht.2 (some (t - 3))
        (mem_admissibleLastLeakGuesses_sub_three ht.1) (by omega),
      Computational.Proofs.SessionCostedFig8.DFProgBoundsBase.redPRNGAuthDFAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t ht.2 (some (t - 3))
        (mem_admissibleLastLeakGuesses_sub_three ht.1) (by omega)⟩
  · exact ⟨Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFBucketAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
        (clampDFBucketLeakGuess qep tL) par (clampDFBucketLeakGuess_getD_le qep tL) (by omega),
      fun t =>
        Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFBucketHybridAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
          (clampDFBucketLeakGuess qep tL) par (clampDFBucketEpoch qep t)
          (clampDFBucketEpoch_lt qep t) (clampDFBucketLeakGuess_getD_le qep tL) (by omega)⟩
  · exact ⟨redPRNGAuthDFAtomicProg_makesAtMostQueries Dh encPt C ℓ encT (idsOf idA idB) lam
        (qep + 1) q (some (t - 2)) t A hA,
      redPRNGAuthDFAtomicProg_makesAtMostQueries Dh encPt C ℓ encT (idsOf idA idB) lam
        (qep + 1) q (some (t - 3)) t A hA⟩
  · exact redPRNGAuthDFBucketHybridAtomicProg_makesAtMostQueries Dh encPt C ℓ encT (idsOf idA idB) lam
      (qep + 1) q (clampDFBucketLeakGuess qep tL) par (clampDFBucketEpoch qep t) A hA

private theorem dummyFsDFShallowProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qR : ℕ)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg
        Dh encPt C ℓ encT idOf lam).eval (fun _ => A) ()) qR := by
  unfold FSAEAD.MakesAtMostQueries
  let R := Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg
    Dh encPt C ℓ encT idOf lam
  let P : (unifSpec + FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Domain → Prop :=
    fun q => (match q with | .inl _ => false | .inr _ => true) = true
  refine (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (p := P) (by rintro (_ | _) <;> rfl) ?_).mono (Nat.zero_le qR)
  unfold CostedReduction.eval
  dsimp only [R, Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg,
    Comp.eval, Expr.eval]
  rw [pure_bind]
  change IsQueryBoundP _ P (0 + 0)
  refine isQueryBoundP_bind
    (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_simulateQ_run_zero A ?_ ())
    (fun _ _ => by simp)
  rintro (n | t) s
  · have hPn : ¬ P (Sum.inl n) := by simp [P]
    dsimp only [R, Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg,
      CostedReduction.impl, handlerImpl, _root_.CryptoGames.PRFPRNG.fsaeadHeaderAdIface]
    simp [StateT.run_lift, map_eq_bind_pure_comp, isQueryBoundP_query_bind_iff, hPn]
  · dsimp only [R, Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg,
      CostedReduction.impl, handlerImpl, _root_.CryptoGames.PRFPRNG.fsaeadHeaderAdIface]
    rcases t with ((((_ | _) | _) | _) | _) | _ <;>
      simp [Comp.eval, Expr.eval, Expr.v0, Expr.v1]

private theorem dummyFsStage2AtomicProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qR : ℕ)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsStage2AtomicProg
        Dh encPt C ℓ encT idOf lam).eval (fun _ => A) ()) qR :=
  Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam 0 qR _ A
    (dummyFsDFShallowProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam qR A)

private theorem compileFsMultiDFAtomic_multi_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qepC qR B0 q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.BundlesMultiFs.compileFsMultiDFAtomic
          ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
          (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg
            (q + 1) B0 1 qepC maxForwardJumps la tL t)).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine Computational.Proofs.SessionCostedFig8.BundlesMultiFs.compileFsMultiDFAtomic_makesAtMostQueries
    ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
    (min (2 * q) (q + 2))
    (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg
      (q + 1) B0 1 qepC maxForwardJumps la tL t) A ?_
  exact (Computational.Proofs.ReductionDsl.SM.DeliverForgeMultiPotOK.redFSAuthDFMultiProg_sess_isQueryBoundP
    (ckaInitA := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).initA)
    (ckaInitB := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).initB)
    (ckaSend := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).send)
    (ckaReceive := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).receive)
    (prngInit := (rootPRNG C.F encPt).init)
    (prngUp := (rootPRNG C.F encPt).up)
    (fsInitSender := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).initSender)
    (fsInitReceiver := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).initReceiver)
    (fsSend := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).send)
    (fsReceive := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).receive)
    (eqT := @BEq.beq Pt instBEqOfDecidableEq)
    (eqI := @BEq.beq Pt instBEqOfDecidableEq)
    (eqM := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
    (eqE := @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq)
    (lam := lam) (defaultE := default)
    (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
    (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
    (q + 1) B0 1 qepC maxForwardJumps la tL t j q A
    (hA.of_imp fun x hx => by cases x <;> [cases hx; rfl])).of_imp
      (fun x hx => by rcases x with _ | ⟨s, _⟩ <;> exact hx)

private theorem compileFsMultiDFAtomic_multiBucket_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qepC qR B0 q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.BundlesMultiFs.compileFsMultiDFAtomic
          ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
          (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg
            (q + 1) B0 1 4 qepC maxForwardJumps la tL par)).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  refine Computational.Proofs.SessionCostedFig8.BundlesMultiFs.compileFsMultiDFAtomic_makesAtMostQueries
    ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
    (min (2 * q) (q + 2))
    (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg
      (q + 1) B0 1 4 qepC maxForwardJumps la tL par) A ?_
  exact (Computational.Proofs.ReductionDsl.SM.DeliverForgeMultiPotOK.redFSAuthDFMultiBucketProg_sess_isQueryBoundP
    (ckaInitA := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).initA)
    (ckaInitB := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).initB)
    (ckaSend := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).send)
    (ckaReceive := (Computational.Proofs.ReductionDsl.Fig8Atomic.dhSchemeFb Dh).receive)
    (prngInit := (rootPRNG C.F encPt).init)
    (prngUp := (rootPRNG C.F encPt).up)
    (fsInitSender := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).initSender)
    (fsInitReceiver := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).initReceiver)
    (fsSend := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).send)
    (fsReceive := (Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B0).receive)
    (eqT := @BEq.beq Pt instBEqOfDecidableEq)
    (eqI := @BEq.beq Pt instBEqOfDecidableEq)
    (eqM := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
    (eqE := @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq)
    (lam := lam) (defaultE := default)
    (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
    (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
    (q + 1) B0 1 4 qepC maxForwardJumps la tL par j q A
    (hA.of_imp fun x hx => by cases x <;> [cases hx; rfl])).of_imp
      (fun x hx => by rcases x with _ | ⟨s, _⟩ <;> exact hx)

theorem redFSAuthDFMultiAtomicProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiAtomicProg
          ℓ Pt C Dh encPt encT idOf lam stage la j (min (2 * q) (q + 2)) q qep tL t).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  unfold Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiAtomicProg
  dsimp only
  split_ifs
  · exact compileFsMultiDFAtomic_multi_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam stage la j qep (min (2 * q) (q + 2))
      ((q + 1) * (maxForwardJumps + 1)) q tL t A hA
  · exact dummyFsStage2AtomicProg_makesAtMostQueries
      Dh encPt C ℓ encT idOf lam (min (2 * q) (q + 2)) A

theorem redFSAuthDFMultiBucketAtomicProg_makesAtMostQueries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : OracleComp
      (unifSpec + _root_.CryptoGames.SM.specDF (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiBucketAtomicProg
          ℓ Pt C Dh encPt encT idOf lam stage la j (min (2 * q) (q + 2)) q qep tL par).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  unfold Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiBucketAtomicProg
  dsimp only
  split_ifs
  · exact compileFsMultiDFAtomic_multiBucket_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam stage la j qep (min (2 * q) (q + 2))
      ((q + 1) * (maxForwardJumps + 1)) q tL par A hA
  · exact dummyFsStage2AtomicProg_makesAtMostQueries
      Dh encPt C ℓ encT idOf lam (min (2 * q) (q + 2)) A

end V1SessionRedsBoundedHelpers

end

end Computational.Proofs.SessionCostedDFStage2
