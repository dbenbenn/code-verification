/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
import Computational.Proofs.SessionCostedFig8.RedFSUniEval
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import
import Computational.Proofs.SignalWireRoundTrip

/-!
# Unconditional `FsOk` and `EncMsgsOk` for Stage-2 `redFSPrivUni` / `redFSPrivUniCoin`

Closes the privacy half (`redFSPriv` and `redFSPrivCoin`) of
`SessionCostedFig8.fig8RedsInst_fsOk_and_encAtomicShort` (`SessionCostedFig8.lean:1166`) and
discharges `hPrivFsOk2q` in `SessionCostedDFStage2Priv` unconditionally (`no proof gaps`), at both
`min (2 * q) (q + 2)` (`fig8RedsInst_priv_fsOk_min_and_encAtomicShort`) and `2 * q`
(`fig8RedsInst_priv_fsOk_2q_and_encAtomicShort`).-/

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM (GuardedSMShort)
open _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed
  (FsSendShort FGSafeS fgSafeS_abortE fgSafeS_liftH_and fgSafeS_liftH_true
   fgSafeS_vSend fgSafeS_reveal fgSafeS_initFS fgSafeS_deliverE fgSafeS_injectE fgSafeS_coinsE
   guardedSafePost_sampleT badSendMsg validQ_encBadMsg)

public section

open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB dhSchemeFb fsAtomicB fsAtomicB_send_eq)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.GuardedSafe (GuardedSafePost guardedSafeS_bind_and guardedSafeS_bind_true guardedSafeS_get_bind guardedSafeS_modify_true guardedSafeS_pure)
open CryptoGames.LibsignalSM (Fig8Adv lBlank)
open CryptoGames.LibsignalSM.Proofs.RestrictedReds (InvE InvVP QSM SafePost SafeS ValidQGen epMgmt_st invFS_empty invVP_record privRedB_equalPub_local safePost_sampleT safeS_abortE safeS_bind_and safeS_bind_true safeS_coinsE safeS_deliverE safeS_get_bind safeS_initFS safeS_injectE safeS_liftH_and safeS_liftH_true safeS_modify_true safeS_pure_true safeS_reveal safeS_vSendGen validQ_offClass validQ_unequalPubChall)
open CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed (FGSafeS FsSendShort badSendMsg fgSafeS_abortE fgSafeS_coinsE fgSafeS_deliverE fgSafeS_initFS fgSafeS_injectE fgSafeS_liftH_and fgSafeS_liftH_true fgSafeS_reveal fgSafeS_vSend guardedSafePost_sampleT validQ_encBadMsg)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM (GuardedSMShort)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (GuardedFSInjectShort LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart fsInjectLong fsRespShort)
open CryptoGames.SM.Construction (Header Mode PartyState SchemeAdversary hooksFS)
open CryptoGames.SM.Construction.ReductionsQueries (RSpec)
open CryptoGames.SM.Engine (challE corrE engRun implE transmitE)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (signalEncodeFits32_proto)

namespace Computational.Proofs.SessionCostedFig8.RedFSUniSafePost

section RunFSUniSafePost

private theorem safeS_transmitEPol
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    {transOk : M → Prop} {challOk : M → M → Prop}
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q mo transOk challOk)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ)
    (pol : CryptoGames.SM.Engine.Policy) (q : CryptoGames.Party × M × Option CCoins) (hm : transOk q.2.1) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep pol q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', InvVP mo.tStar (s₁.st P') := by
        rw [epMgmt_st (2 + Δcka) qep hep]
        exact hes.vp
      by_cases h2 : pol.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine safeS_bind_and
          (safeS_liftH_and (mo := mo)
            (safeS_vSendGen hQ cka prng fs Δcka j s₁ P (s₁.st P) (hst₁ P) m
              none r (fun _ => hm) (by rintro _ _ ⟨⟩)))
          fun res hres => ?_
        cases res with
        | none =>
          exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
        | some sc =>
          rcases sc with ⟨st', c⟩
          have hst' : InvVP mo.tStar st' := hres st' c rfl
          exact safeS_bind_true
            (safeS_modify_true _ fun _ h =>
              ⟨invVP_record (2 + Δcka) hst₁ P hst' _ false, h.fs⟩)
            fun _ => safeS_pure_true (some c)

private theorem safeS_challEPol
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    {transOk : M → Prop} {challOk : M → M → Prop}
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q mo transOk challOk)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ)
    (pol : CryptoGames.SM.Engine.Policy) (q : CryptoGames.Party × M × M × Option CCoins)
    (heq : challOk q.2.1 q.2.2.1) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg pol q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', InvVP mo.tStar (s₁.st P') := by
        rw [epMgmt_st (2 + Δcka) qep hep]
        exact hes.vp
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : pol.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hpair : ∀ x₀ x₁, some (m₀, m₁) = some (x₀, x₁) → challOk x₀ x₁ := by
            intro x₀ x₁ h
            cases h
            exact heq
          refine safeS_bind_and
            (safeS_liftH_and (mo := mo)
              (safeS_vSendGen hQ cka prng fs Δcka j s₁ P (s₁.st P) (hst₁ P) _
                (some (m₀, m₁)) r (by rintro ⟨⟩) hpair))
            fun res hres => ?_
          cases res with
          | none =>
            exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
          | some sc =>
            rcases sc with ⟨st', c⟩
            have hst' : InvVP mo.tStar st' := hres st' c rfl
            exact safeS_bind_true
              (safeS_modify_true _ fun _ h =>
                ⟨invVP_record (2 + Δcka) hst₁ P hst' _ true, h.fs⟩)
              fun _ => safeS_pure_true (some c)

private theorem safeS_corrEPol
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    {transOk : M → Prop} {challOk : M → M → Prop}
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q mo transOk challOk)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka j : ℕ)
    (pol : CryptoGames.SM.Engine.Policy) (P : CryptoGames.Party) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (corrE (hooksFS cka prng fs Δcka mo j) pol P) := by
  unfold corrE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowed P) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (pol.leakDoom es.g (es.g.afterCorr P) || pol.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine safeS_bind_true
        (safeS_liftH_true (mo := mo)
          (safeS_reveal hQ cka prng fs Δcka j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none => exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
      | some st =>
        refine safeS_bind_true
          (safeS_modify_true _ fun _ h => ⟨hes.vp, h.fs⟩)
          fun _ => safeS_pure_true (some st)

theorem safePost_runFSUniGen
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨false, none, t⟩ transOk challOk)
    (b : Bool) (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (CryptoGames.SM.Construction.runFSUni cka prng fs lam Δcka qep t b B) := by
  let mo : Mode := ⟨false, none, t⟩
  unfold CryptoGames.SM.Construction.runFSUni engRun
  refine (safeS_initFS hQ cka prng fs lam 0 {} (invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨vs, h⟩
  cases vs with
  | none => exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    have hes₀ : InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
        (M := M) (E := E) mo.tStar
        { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h } :=
      ⟨fun P => by cases P <;> assumption, hp.2⟩
    have hsim : SafePost Q (fun r => InvE mo.tStar r.2)
        ((simulateQ (implE (hooksFS cka prng fs Δcka mo 0) (2 + Δcka) qep fs.maxSkip mo.cfg
          (CryptoGames.SM.Construction.polUni12 Δcka t)) B).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h }) := by
      refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.simulateQ_run (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.of_isQueryBoundP hB) ?_ hes₀
      rintro (u | qv) hpt
      · exact safeS_coinsE hQ u
      · rcases qv with ((((q | q) | q) | q) | P)
        · exact safeS_transmitEPol hQ cka prng fs Δcka qep 0 (CryptoGames.SM.Construction.polUni12 Δcka t) q (htrans q hpt)
        · exact safeS_challEPol hQ cka prng fs Δcka qep 0 (CryptoGames.SM.Construction.polUni12 Δcka t) q (hchall q hpt)
        · exact safeS_deliverE hQ cka prng fs Δcka 0 q
        · exact safeS_injectE hQ cka prng fs Δcka qep 0 q
        · exact safeS_corrEPol hQ cka prng fs Δcka 0 (CryptoGames.SM.Construction.polUni12 Δcka t) P
    exact hsim.bind fun _ _ => CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial

theorem safePost_redFSPrivUniGen
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨false, none, t⟩ transOk challOk)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (CryptoGames.SM.Construction.redFSPrivUni cka prng fs lam Δcka qep t B) := by
  unfold CryptoGames.SM.Construction.redFSPrivUni
  refine (safePost_runFSUniGen cka prng fs lam Δcka qep t hQ false B hB htrans hchall).bind fun res _ => ?_
  cases res with
  | none => exact safePost_sampleT hQ Bool
  | some p =>
    rcases p with ⟨b', es⟩
    dsimp only
    split_ifs
    · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
    · exact safePost_sampleT hQ Bool

theorem safePost_redFSPrivUniCoinGen
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨false, none, t⟩ transOk challOk)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (CryptoGames.SM.Construction.redFSPrivUniCoin cka prng fs lam Δcka qep t B) := by
  unfold CryptoGames.SM.Construction.redFSPrivUniCoin
  exact (safePost_runFSUniGen cka prng fs lam Δcka qep t hQ false B hB htrans hchall).bind fun _ _ =>
    safePost_sampleT hQ Bool

private theorem fgSafeS_transmitEPol
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (hfs : FsSendShort ok fs) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (pol : CryptoGames.SM.Engine.Policy) (q : CryptoGames.Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × (ℕ × LibsignalCiphertextWithSalt32),
        res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep pol q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : pol.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_and
          (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) m none r hok))
          fun res hres => ?_
        rcases res with _ | ⟨st', c⟩
        · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
          rintro _ ⟨⟩
          exact hres st' c rfl

private theorem fgSafeS_challEPol
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (hfs : FsSendShort ok fs) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (pol : CryptoGames.SM.Engine.Policy) (q : CryptoGames.Party × M × M × Option CCoins)
    (hok₀ : ok q.2.1 = true) (hok₁ : ok q.2.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × (ℕ × LibsignalCiphertextWithSalt32),
        res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg pol q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : pol.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hm : ok (((mo.cfg (M := M)).challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)) = true := by
            have hcfg : (mo.cfg (M := M)).challMsg (s₁.epoch P) = none := by
              unfold CryptoGames.SM.Construction.Mode.cfg CryptoGames.SM.Config.auth CryptoGames.SM.Config.priv
              split <;> rfl
            rw [hcfg]
            dsimp only [Option.getD]
            cases es.g.b <;> assumption
          refine guardedSafeS_bind_and
            (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r hm))
            fun res hres => ?_
          rcases res with _ | ⟨st', c⟩
          · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
              guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
            rintro _ ⟨⟩
            exact hres st' c rfl

private theorem fgSafeS_corrEPol
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (j : ℕ) (pol : CryptoGames.SM.Engine.Policy) (P : CryptoGames.Party) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (corrE (hooksFS cka prng fs Δcka mo j) pol P) := by
  unfold corrE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowed P) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (pol.leakDoom es.g (es.g.afterCorr P) || pol.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
        guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_reveal cka prng fs Δcka mo j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none => exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure (some st) fun _ _ => ⟨trivial, trivial⟩

theorem guardedSafePost_runFSUni
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (hfs : FsSendShort ok fs) (lam : I) (Δcka qep t : ℕ) (b : Bool)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (hok : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok B)
    (hg : GuardedSMShort B) :
    GuardedSafePost
      (fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True)
      (CryptoGames.SM.Construction.runFSUni cka prng fs lam Δcka qep t b B) := by
  let mo : Mode := ⟨false, none, t⟩
  unfold CryptoGames.SM.Construction.runFSUni engRun
  refine (fgSafeS_initFS cka prng fs lam mo 0 {} trivial).bind fun p _ => ?_
  rcases p with ⟨vs, h⟩
  rcases vs with _ | ⟨vA, vB⟩
  · exact CryptoGames.GuardedSafe.GuardedSafePost.pure trivial
  · have hB := hg.and_isQueryBoundP hok
    have hsim : GuardedSafePost fsRespShort fsInjectLong (fun _ => True)
        ((simulateQ (implE (hooksFS cka prng fs Δcka mo 0) (2 + Δcka) qep fs.maxSkip mo.cfg
          (CryptoGames.SM.Construction.polUni12 Δcka t)) B).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h }) := by
      refine CryptoGames.GuardedSafe.GuardedSafePost.simulateQ_run (I := fun _ => True) hB ?_ trivial
      rintro (u | qv) hpt
      · exact fgSafeS_coinsE u
      · rcases qv with ((((q | q) | q) | q) | P)
        · have hok_q : ok q.2.1 = true := by
            have hnb : ¬ badSendMsg (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × (ℕ × LibsignalCiphertextWithSalt32)) ok
                (.inr (.inl (.inl (.inl (.inl q))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsg] using hnb
          exact fgSafeS_transmitEPol cka prng fs hfs Δcka qep mo 0 (CryptoGames.SM.Construction.polUni12 Δcka t) q hok_q
        · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
            have hnb : ¬ badSendMsg (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × (ℕ × LibsignalCiphertextWithSalt32)) ok
                (.inr (.inl (.inl (.inl (.inr q))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsg, Bool.or_eq_true] using hnb
          exact fgSafeS_challEPol cka prng fs hfs Δcka qep mo 0 (CryptoGames.SM.Construction.polUni12 Δcka t) q hok_q.1 hok_q.2
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_deliverE cka prng fs Δcka mo 0 q hc
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_injectE cka prng fs Δcka qep mo 0 q hc
        · exact fgSafeS_corrEPol cka prng fs Δcka mo 0 (CryptoGames.SM.Construction.polUni12 Δcka t) P
    exact hsim.bind fun _ _ => CryptoGames.GuardedSafe.GuardedSafePost.pure (P := fun _ => True) trivial

theorem guardedFSInjectShort_redFSPrivUni
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (hfs : FsSendShort ok fs) (lam : I) (Δcka qep t : ℕ)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (hok : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok B)
    (hg : GuardedSMShort B) :
    GuardedFSInjectShort (CryptoGames.SM.Construction.redFSPrivUni cka prng fs lam Δcka qep t B) := by
  unfold GuardedFSInjectShort CryptoGames.SM.Construction.redFSPrivUni
  refine (guardedSafePost_runFSUni cka prng fs hfs lam Δcka qep t false B hok hg).bind
    fun res _ => ?_
  rcases res with _ | ⟨b', es⟩
  · exact guardedSafePost_sampleT Bool
  · dsimp only
    split
    · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (P := fun _ => True) trivial
    · exact guardedSafePost_sampleT Bool

theorem guardedFSInjectShort_redFSPrivUniCoin
    {KC Γ CCoins T I KR Sig K SS RS M : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32))
    (hfs : FsSendShort ok fs) (lam : I) (Δcka qep t : ℕ)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (hok : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok B)
    (hg : GuardedSMShort B) :
    GuardedFSInjectShort (CryptoGames.SM.Construction.redFSPrivUniCoin cka prng fs lam Δcka qep t B) := by
  unfold GuardedFSInjectShort CryptoGames.SM.Construction.redFSPrivUniCoin
  exact (guardedSafePost_runFSUni cka prng fs hfs lam Δcka qep t false B hok hg).bind
    fun _ _ => guardedSafePost_sampleT Bool

end RunFSUniSafePost

section PrivFsOk

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
local instance : Inhabited Pt := ⟨0⟩

/-- Exact copy of `CryptoVerification.LibsignalSession.FsOk` (`SessionCostedFig8.lean:88–99`,
definitionally equal by `rfl`). -/
@[expose] def FsOk2 (ℓ qR qd : ℕ)
    (R : CryptoGames.FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) : Prop :=
  CryptoGames.FSAEAD.MakesAtMostQueries R qR ∧ CryptoGames.FSAEAD.MakesAtMostDecQueries R qd ∧
    CryptoGames.FSAEAD.EqualPubChallenges R ∧
    CryptoGames.FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R

private theorem isQueryBoundP_zero_mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ x, q x → p x) (h : IsQueryBoundP oa p 0) : IsQueryBoundP oa q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    have hnp : ¬ p t := h.1.resolve_right (Nat.not_lt_zero 0)
    have hnq : ¬ q t := mt (hqp t) hnp
    exact ⟨Or.inl hnq, fun u => by
      have hu := h.2 u
      simp only [hnp, ite_false] at hu
      simpa [hnq] using ih u hu⟩

private theorem encMsgsOk_shortB_of_atomicShortPubB {SS RS AD C : Type} {ℓ : ℕ}
    {R : CryptoGames.FSAEAD.Adversary SS RS AD (LibsignalMsgPublicPart × Plain ℓ) C}
    (h : CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R) :
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R := by
  refine isQueryBoundP_zero_mono (fun t ht => ?_) h
  rcases t with _ | (((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _)
  · cases ht
  · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.not_eq_true'] at ht ⊢
    cases hat : atomicShortPubB m.1
    · rfl
    · rw [atomicShortPubB_imp_shortB hat] at ht; cases ht
  · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.or_eq_true, Bool.not_eq_true'] at ht ⊢
    rcases ht with ht₀ | ht₁
    · left
      cases hat : atomicShortPubB m₀.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₀; cases ht₀
    · right
      cases hat : atomicShortPubB m₁.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₁; cases ht₁
  all_goals cases ht

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fsClamp_fsAtomicB_fsSendShort (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey) (B B0 : ℕ) :
    FsSendShort (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) := by
  intro ss hdr m hm
  change ((fsAtomicB C ℓ encT idOf B0).send ss hdr m).2.2.1.1.length + 8 < 2 ^ 32
  rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  exact _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.lFS_fsSendShort C protoSignalCodec
    signalEncodeFits32_proto ℓ (by omega) encT idOf maxForwardJumps ss hdr m
    (atomicShortPubB_imp_shortB hm)

/-- Unconditional `FsOk2 ℓ (min (2 * q) (q + 2)) q` and `EncMsgsOk atomicShortPubB` on
`fig8RedsInst.redFSPriv` and `fig8RedsInst.redFSPrivCoin`. -/
theorem fig8RedsInst_priv_fsOk_min_and_encAtomicShort
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (_hc : codec = protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey)
    (lam : Pt) (qep q i : ℕ) (B_adv : Fig8Adv Pt ℓ)
    (hqB : CryptoGames.SM.MakesAtMostQueries B_adv q)
    (hshB : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv)
    (hgB : CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.GuardedSMShort B_adv) :
    let R := Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
    let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
    (FsOk2 ℓ (min (2 * q) (q + 2)) q ((R.redFSPriv i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPriv i).eval (fun _ => privAdv) ())) ∧
    (FsOk2 ℓ (min (2 * q) (q + 2)) q ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPrivCoin i).eval (fun _ => privAdv) ())) := by
  intro R privAdv
  have hPrivEq : privAdv = CryptoGames.SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv :=
    BundlesEval.fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i B_adv hqB
  have hqPriv : CryptoGames.SM.MakesAtMostQueries privAdv q := by
    rw [hPrivEq]
    exact CryptoGames.LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
  have heqPriv : CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) privAdv := by
    rw [hPrivEq]
    exact privRedB_equalPub_local (2 + 1) qep i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ) (fun _ => rfl) B_adv
  have hshPriv : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) privAdv := by
    rw [hPrivEq]
    exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
      (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
      (CryptoGames.LibsignalSM.Proofs.SessionShort.privRedB_sendOk (2 + 1) qep i
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        (lBlank ℓ) (fun _ => rfl) B_adv hshB)
  have hgPriv : CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.GuardedSMShort privAdv := by
    rw [hPrivEq]
    exact CryptoGames.LibsignalSM.Proofs.SessionShort.privRedB_guardedSMShort (2 + 1) qep i (lBlank ℓ) B_adv hgB
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let cka := dhSchemeFb Dh
  let prng := rootPRNG C.F encPt
  let fs' := CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  have hfsShort : FsSendShort
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) fs' :=
    fsClamp_fsAtomicB_fsSendShort C ℓ hℓ encT idOf B0 B0
  have hSubPriv := BundlesEval.fig8RedsInst_redFSPriv_querySubsumes
    Dh encPt C codec ℓ hℓ encT idOf lam qep q i privAdv
  have hSubCoin := BundlesEval.fig8RedsInst_redFSPrivCoin_querySubsumes
    Dh encPt C codec ℓ hℓ encT idOf lam qep q i privAdv
  have hClampPriv :
      ((CryptoGames.SM.Construction.redFSPrivUniProg (q + 1) B0 1 qep maxForwardJumps i :
        ReductionDsl.CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => privAdv) ()) =
      CryptoGames.SM.Construction.redFSPrivUni cka prng fs' lam 1 qep i privAdv :=
    RedFSUniEval.redFSPrivUniProg_eval_clamp_eq cka prng
      (fsAtomicB C ℓ encT idOf B0) (q + 1) B0 q 1 qep i
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
      privAdv q hqPriv (Nat.le_refl q)
  have hClampCoin :
      ((CryptoGames.SM.Construction.redFSPrivUniCoinProg (q + 1) B0 1 qep maxForwardJumps i :
        ReductionDsl.CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => privAdv) ()) =
      CryptoGames.SM.Construction.redFSPrivUniCoin cka prng fs' lam 1 qep i privAdv :=
    RedFSUniEval.redFSPrivUniCoinProg_eval_clamp_eq cka prng
      (fsAtomicB C ℓ encT idOf B0) (q + 1) B0 q 1 qep i
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
      privAdv q hqPriv (Nat.le_refl q)
  refine ⟨?_, ?_⟩
  · have hEncAt : CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPriv i).eval (fun _ => privAdv) ()) := by
      refine hSubPriv.fsaeadEncMsgsOk_of_querySubsumes ?_
      rw [hClampPriv]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniGen cka prng fs' lam 1 qep i
          (validQ_encBadMsg ⟨false, none, i⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1))
          privAdv hshPriv
          (fun q hpt => by simpa [badSendMsg] using hpt)
          (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt))
    refine ⟨⟨?_, ?_, ?_, ?_, encMsgsOk_shortB_of_atomicShortPubB hEncAt, ?_⟩, hEncAt⟩
    · exact hSubPriv.fsaeadMakesAtMostQueries_of_querySubsumes
        (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniProg_makesAtMostQueries
          (q + 1) B0 1 qep maxForwardJumps i q privAdv hqPriv)
    · exact hSubPriv.fsaeadMakesAtMostDecQueries_of_querySubsumes
        (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniProg_makesAtMostDecQueries
          (q + 1) B0 1 qep maxForwardJumps i q privAdv hqPriv)
    · refine hSubPriv.fsaeadEqualPubChallenges_of_querySubsumes ?_
      rw [hClampPriv]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniGen cka prng fs' lam 1 qep i
          (validQ_unequalPubChall ⟨false, none, i⟩) privAdv heqPriv
          (fun _ _ => trivial) (fun q hpt => by simpa [QSM, CryptoGames.SM.unequalPubChall] using hpt))
    · refine hSubPriv.fsaeadAllQueriesInOneADClass_of_querySubsumes ⟨i, ?_⟩
      rw [hClampPriv]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniGen cka prng fs' lam 1 qep i
          (validQ_offClass ⟨false, none, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1))
          privAdv heqPriv
          (fun _ _ => trivial) (fun q hpt => by simpa [QSM, CryptoGames.SM.unequalPubChall] using hpt))
    · refine hSubPriv.guardedFSInjectShort_of_querySubsumes ?_
      rw [hClampPriv]
      exact guardedFSInjectShort_redFSPrivUni cka prng fs' hfsShort lam 1 qep i privAdv hshPriv hgPriv
  · have hEncAt : CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()) := by
      refine hSubCoin.fsaeadEncMsgsOk_of_querySubsumes ?_
      rw [hClampCoin]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniCoinGen cka prng fs' lam 1 qep i
          (validQ_encBadMsg ⟨false, none, i⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1))
          privAdv hshPriv
          (fun q hpt => by simpa [badSendMsg] using hpt)
          (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt))
    refine ⟨⟨?_, ?_, ?_, ?_, encMsgsOk_shortB_of_atomicShortPubB hEncAt, ?_⟩, hEncAt⟩
    · exact hSubCoin.fsaeadMakesAtMostQueries_of_querySubsumes
        (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniCoinProg_makesAtMostQueries
          (q + 1) B0 1 qep maxForwardJumps i q privAdv hqPriv)
    · exact hSubCoin.fsaeadMakesAtMostDecQueries_of_querySubsumes
        (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniCoinProg_makesAtMostDecQueries
          (q + 1) B0 1 qep maxForwardJumps i q privAdv hqPriv)
    · refine hSubCoin.fsaeadEqualPubChallenges_of_querySubsumes ?_
      rw [hClampCoin]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniCoinGen cka prng fs' lam 1 qep i
          (validQ_unequalPubChall ⟨false, none, i⟩) privAdv heqPriv
          (fun _ _ => trivial) (fun q hpt => by simpa [QSM, CryptoGames.SM.unequalPubChall] using hpt))
    · refine hSubCoin.fsaeadAllQueriesInOneADClass_of_querySubsumes ⟨i, ?_⟩
      rw [hClampCoin]
      exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSPrivUniCoinGen cka prng fs' lam 1 qep i
          (validQ_offClass ⟨false, none, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1))
          privAdv heqPriv
          (fun _ _ => trivial) (fun q hpt => by simpa [QSM, CryptoGames.SM.unequalPubChall] using hpt))
    · refine hSubCoin.guardedFSInjectShort_of_querySubsumes ?_
      rw [hClampCoin]
      exact guardedFSInjectShort_redFSPrivUniCoin cka prng fs' hfsShort lam 1 qep i privAdv hshPriv hgPriv

/-- Direct `2 * q` specialization closing `SessionCostedFig8.lean:1166` and `hPrivFsOk2q` in
`SessionCostedDFStage2Priv`. -/
theorem fig8RedsInst_priv_fsOk_2q_and_encAtomicShort
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey)
    (lam : Pt) (qep q i : ℕ) (B_adv : Fig8Adv Pt ℓ)
    (hqB : CryptoGames.SM.MakesAtMostQueries B_adv q)
    (hshB : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv)
    (hgB : CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.GuardedSMShort B_adv) :
    let R := Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
    let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
    (FsOk2 ℓ (2 * q) q ((R.redFSPriv i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPriv i).eval (fun _ => privAdv) ())) ∧
    (FsOk2 ℓ (2 * q) q ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPrivCoin i).eval (fun _ => privAdv) ())) := by
  obtain ⟨⟨hOkP, hEncP⟩, ⟨hOkC, hEncC⟩⟩ :=
    fig8RedsInst_priv_fsOk_min_and_encAtomicShort Dh encPt C codec hc ℓ hℓ encT idOf lam qep q i
      B_adv hqB hshB hgB
  exact ⟨⟨⟨hOkP.1.mono (Nat.min_le_left _ _), hOkP.2⟩, hEncP⟩,
    ⟨⟨hOkC.1.mono (Nat.min_le_left _ _), hOkC.2⟩, hEncC⟩⟩

end PrivFsOk

end Computational.Proofs.SessionCostedFig8.RedFSUniSafePost
