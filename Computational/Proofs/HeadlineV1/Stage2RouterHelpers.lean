/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SessionCostedHalt -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.GameHop.Rnd

set_option autoImplicit false

open Computational.Proofs.E2E.SessionAuthBridge (MultiSessFsAdv MultiSessPubFsAdv RouterAdvCompat authHopCutoff multiSessPubToAD)
open CryptoGames (Party)
open CryptoGames.AEADScheme (OTCCAAdversary)
open CryptoGames.CBC (Plain)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.FSAEAD.Thm5 (DG IndexedOtccaSpec Params SpecialOps hInit hp isLookaheadHop multiImplWith otOpsWith)
open CryptoGames.HKDF (DerivedMessageKeys)
open CryptoGames.LibsignalSM.Proofs.WireHop (lWireRed_eq wRedImpl)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.MACScheme (PRFState prfEval prfSpec)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart LibsignalWireOracleSpec Salt32 SaltSlotSt lAeadR lChainPRG lIdeal lPubOf lSaltPRF32 lSaltRed lWireRed slotSaltImpl slotSaltImplNF slotSaltRed slotWireRed)
open CryptoGames.SM.Construction (Header)
open CryptoVerification.E2E.Signed.SessionFS (fsImpl fsInit fsSessAdv fsSlotImpl fsSlotInit fsSpec)
open CryptoVerification.E2E.Signed.SessionFSMix (lSessAdv)
open CryptoVerification.E2E.Signed.SessionQueries (FsIdx)
open CryptoVerification.E2E.Signed.SessionRouter (fwd fwd_inl fwd_inr lazyInit multiSessSpec onAnySess onInr onSess sessAdv sessAdv_isQueryBoundP sessRedImpl)
open CryptoVerification.E2E.Signed.SessionWire (fsWireSessAdv lWireSessAdv)
open CryptoVerification.E2E.Signed.SessionWireQueries (onSess_imp_onAnySess)
open CryptoVerification.LibsignalSession (FsAdv LCt chainPRGTermAuth fsAeadAuthSlotSumBound_inst_eq fsAuthCompBound fsCostedRedsInst fsSlotCount pubToAD saltPRFTermAuth wireOtccaTermAuth)

namespace Computational.Proofs.HeadlineV1.Stage2RouterHelpers

public section

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out (advBit hRunOut multiRunOut
  cumulativeChainPrgReductionOut multiSlotOtccaReductionOut)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB CoinSimEquiv ValidCoinSim
  compCoinImpl simulateQ_compCoinImpl_run
  prgAdvantage_congr prfAdvantage_congr wireOtccaAdvantage_congr)
open Computational.Proofs.GameHop.Rnd (evalDistEq_bind_right_of_mem_support
  evalDistEq_uniformBool_beq)
open _root_.CryptoVerification.LibsignalSession (fsCostedRedsInst fsAuthCompBound
  chainPRGTermAuth saltPRFTermAuth wireOtccaTermAuth fsSlotCount pubToAD FsAdv LCt
  fsAeadAuthSlotSumBound_inst_eq)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSpqrV1 (Bytes)
open Computational.Proofs.SessionCostedHalt (dummyFig8SmDFRed)

theorem onSess_of_onAnySess {ι : Type} {spec : OracleSpec ι} {α : Type}
    (M : OracleComp (unifSpec + multiSessSpec spec) α)
    (Q : ι → Bool) (k n : ℕ)
    (h : M.IsQueryBoundP (fun t => onAnySess Q t = true) n) :
    M.IsQueryBoundP (fun t => onSess Q k t = true) n :=
  h.of_imp fun t ht => onSess_imp_onAnySess Q k t ht

@[expose] def fsAnyQ {ι : Type} : ι → Bool := fun _ => true

theorem sessAdv_makesAtMostQueries {SS RS AD Msg Ct σL σR : Type}
    (implL : QueryImpl (CryptoGames.FSAEAD.spec SS RS AD Msg Ct) (StateT σL ProbComp))
    (implR : QueryImpl (CryptoGames.FSAEAD.spec SS RS AD Msg Ct) (StateT σR ProbComp))
    (M : OracleComp (unifSpec + multiSessSpec (CryptoGames.FSAEAD.spec SS RS AD Msg Ct)) Bool)
    (sL : ℕ → σL) (sR : ℕ → σR) (j qR : ℕ)
    (hM : M.IsQueryBoundP (fun t => onAnySess fsAnyQ t = true) qR) :
    CryptoGames.FSAEAD.MakesAtMostQueries (sessAdv implL implR M sL sR j) qR := by
  unfold CryptoGames.FSAEAD.MakesAtMostQueries
  have h1 := sessAdv_isQueryBoundP implL implR M sL sR j fsAnyQ
    (onSess_of_onAnySess M fsAnyQ j qR hM)
  exact h1.of_imp fun t ht => by
    cases t with
    | inl n => cases ht
    | inr i => simp [onInr, fsAnyQ] at ht ⊢

@[expose] def fsEncBadMsg {AD Msg Ct : Type} (ok : Msg → Bool) :
    FsIdx AD Msg Ct → Bool
  | .inl (.inl (.inl (.inl (.inl ⟨_, m⟩)))) => !ok m
  | .inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁⟩)))) => !ok m₀ || !ok m₁
  | _ => false
private theorem encBadMsg_inr_eq_fsEncBadMsg {SS RS AD Msg Ct : Type} (ok : Msg → Bool)
    (i : (CryptoGames.FSAEAD.spec SS RS AD Msg Ct).Domain) :
    CryptoGames.FSAEAD.encBadMsg (SS := SS) (RS := RS) (AD := AD) (C := Ct) ok (.inr i) =
      fsEncBadMsg ok i := by
  rcases i with (((((⟨_, _⟩ | ⟨_, _, _⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;> rfl

@[expose] def wrapTrImpl {ι₁ ι₂ σ : Type} {G₁ : OracleSpec ι₁} {G₂ : OracleSpec ι₂}
    (tr : QueryImpl (unifSpec + G₁) (StateT Bool (OracleComp (unifSpec + G₂))))
    (impl : QueryImpl G₂ (StateT σ ProbComp)) :
    QueryImpl G₁ (StateT (σ × Bool) ProbComp) :=
  fun q => StateT.mk fun ⟨s, b⟩ => do
    let ⟨⟨r, b'⟩, s'⟩ ← (simulateQ (fwd impl) ((tr (.inr q)).run b)).run s
    return (r, (s', b'))

abbrev wrapPubImpl {SS RS AD Pub M C σ : Type}
    (pubOf : C → Option Pub)
    (impl : QueryImpl (CryptoGames.FSAEAD.spec SS RS (AD × Pub) M C) (StateT σ ProbComp)) :
    QueryImpl (CryptoGames.FSAEAD.spec SS RS AD (Pub × M) C) (StateT (σ × Bool) ProbComp) :=
  wrapTrImpl (CryptoGames.FSAEAD.pubRedImpl (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf) impl

@[expose] def sessTag {ι : Type} {spec : OracleSpec ι} (s : ℕ) :
    QueryImpl (unifSpec + spec) (OracleComp (unifSpec + multiSessSpec spec))
  | .inl n => query (spec := unifSpec + multiSessSpec spec) (.inl n)
  | .inr q => query (spec := unifSpec + multiSessSpec spec) (.inr ⟨s, q⟩)

@[expose] def multiTrImpl {ι₁ ι₂ : Type} {G₁ : OracleSpec ι₁} {G₂ : OracleSpec ι₂}
    (tr : QueryImpl (unifSpec + G₁) (StateT Bool (OracleComp (unifSpec + G₂)))) :
    QueryImpl (unifSpec + multiSessSpec G₁)
      (StateT (ℕ → Bool) (OracleComp (unifSpec + multiSessSpec G₂)))
  | .inl n => StateT.lift (query (spec := unifSpec + multiSessSpec G₂) (.inl n))
  | .inr ⟨s, q⟩ => StateT.mk fun st => do
      let r ← simulateQ (sessTag s) ((tr (.inr q)).run (st s))
      return (r.1, Function.update st s r.2)
private theorem simulateQ_tr_liftM_run {ι₁ ι₂ α : Type} {G₁ : OracleSpec ι₁} {G₂ : OracleSpec ι₂}
    (tr : QueryImpl (unifSpec + G₁) (StateT Bool (OracleComp (unifSpec + G₂))))
    (htr_inl : ∀ n b, (tr (.inl n)).run b =
      (query (spec := unifSpec + G₂) (.inl n) >>= fun u => pure (u, b)))
    (p : ProbComp α) (b : Bool) :
    (simulateQ tr (liftM p : OracleComp (unifSpec + G₁) α)).run b =
      (liftM ((·, b) <$> p) : OracleComp (unifSpec + G₂) (α × Bool)) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    change (simulateQ tr
        ((query (spec := unifSpec + G₁) (.inl n)) >>= fun u =>
          (liftM (k u) : OracleComp (unifSpec + G₁) α))).run b =
      ((query (spec := unifSpec + G₂) (.inl n)) >>= fun u =>
        (liftM ((·, b) <$> k u) : OracleComp (unifSpec + G₂) (α × Bool)))
    rw [simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query, htr_inl]
    simp only [bind_assoc, pure_bind, ih]
private theorem sessRedImpl_sessTag_inl {ι σL σR : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    (s k n : ℕ) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (sessRedImpl implL implR k) (sessTag (spec := spec) s (.inl n))).run (sL, sR) =
      (query (spec := unifSpec + spec) (.inl n) >>= fun a => pure (a, (sL, sR))) := by
  change (simulateQ (sessRedImpl implL implR k)
      (query (spec := unifSpec + multiSessSpec spec) (.inl n))).run (sL, sR) = _
  rw [simulateQ_HasQuery_query]
  rfl
private theorem sessRedImpl_sessTag_inr_same {ι σL σR : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    (k : ℕ) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (sessRedImpl implL implR k) (sessTag (spec := spec) k (.inr q'))).run (sL, sR) =
      (query (spec := unifSpec + spec) (.inr q') >>= fun a => pure (a, (sL, sR))) := by
  change (simulateQ (sessRedImpl implL implR k)
      (query (spec := unifSpec + multiSessSpec spec) (.inr ⟨k, q'⟩))).run (sL, sR) = _
  rw [simulateQ_HasQuery_query]
  simp only [sessRedImpl, ↓reduceIte, StateT.run_lift]
  rfl
private theorem sessRedImpl_sessTag_inr_lt {ι σL σR : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hsk : s < k) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (sessRedImpl implL implR k) (sessTag (spec := spec) s (.inr q'))).run (sL, sR) =
      (liftM ((fun r => (r.1, (sL, Function.update sR s r.2))) <$>
        (fwd implR (.inr q')).run (sR s)) :
        OracleComp (unifSpec + spec) (spec.Range q' × (ℕ → σL) × (ℕ → σR))) := by
  have hne : s ≠ k := Nat.ne_of_lt hsk
  change (simulateQ (sessRedImpl implL implR k)
      (query (spec := unifSpec + multiSessSpec spec) (.inr ⟨s, q'⟩))).run (sL, sR) = _
  rw [simulateQ_HasQuery_query]
  simp only [sessRedImpl, hne, hsk, ↓reduceIte, StateT.run_mk, fwd_inr, liftM_map]
  rfl
private theorem sessRedImpl_sessTag_inr_gt {ι σL σR : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hks : k < s) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (sessRedImpl implL implR k) (sessTag (spec := spec) s (.inr q'))).run (sL, sR) =
      (liftM ((fun r => (r.1, (Function.update sL s r.2, sR))) <$>
        (fwd implL (.inr q')).run (sL s)) :
        OracleComp (unifSpec + spec) (spec.Range q' × (ℕ → σL) × (ℕ → σR))) := by
  have hne : s ≠ k := (Nat.ne_of_lt hks).symm
  have hnotlt : ¬ s < k := Nat.not_lt.mpr (Nat.le_of_lt hks)
  change (simulateQ (sessRedImpl implL implR k)
      (query (spec := unifSpec + multiSessSpec spec) (.inr ⟨s, q'⟩))).run (sL, sR) = _
  rw [simulateQ_HasQuery_query]
  simp only [sessRedImpl, hne, hnotlt, ↓reduceIte, StateT.run_mk, fwd_inr, liftM_map]
  rfl
private theorem simulateQ_sessRedImpl_tag_same {ι σL σR α : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    (k : ℕ) (X : OracleComp (unifSpec + spec) α) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (sessRedImpl implL implR k) (simulateQ (sessTag k) X)).run (sL, sR) =
      (·, (sL, sR)) <$> X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t kz ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | q'
    · rw [sessRedImpl_sessTag_inl]
      simp only [bind_assoc, pure_bind, ih]
      rfl
    · rw [sessRedImpl_sessTag_inr_same]
      simp only [bind_assoc, pure_bind, ih]
      rfl
private theorem simulateQ_sessRedImpl_tag_lt {ι σL σR α : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hsk : s < k)
    (X : OracleComp (unifSpec + spec) α) :
    ∀ (sL : ℕ → σL) (sR : ℕ → σR),
      (simulateQ (sessRedImpl implL implR k) (simulateQ (sessTag s) X)).run (sL, sR) =
        (liftM ((fun r => (r.1, (sL, Function.update sR s r.2))) <$>
          (simulateQ (fwd implR) X).run (sR s)) :
          OracleComp (unifSpec + spec) (α × (ℕ → σL) × (ℕ → σR))) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro sL sR
    simp [Function.update_eq_self]
  | query_bind t kz ih =>
    intro sL sR
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | q'
    · rw [sessRedImpl_sessTag_inl]
      simp only [bind_assoc, pure_bind, ih, fwd_inl,
        QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B,
        QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, liftM_bind, liftM_map]
      rfl
    · rw [sessRedImpl_sessTag_inr_lt implL implR hsk, liftM_map, bind_map_left]
      have hstep : ∀ r : spec.Range q' × σR,
          (simulateQ (sessRedImpl implL implR k) (simulateQ (sessTag s) (kz r.1))).run
            (sL, Function.update sR s r.2) =
          liftM ((fun r' => (r'.1, (sL, Function.update sR s r'.2))) <$>
            (simulateQ (fwd implR) (kz r.1)).run r.2) := fun r => by
        rw [ih r.1 sL (Function.update sR s r.2)]
        simp [Function.update_self, Function.update_idem]
      simp only [hstep]
      rw [← liftM_bind]
private theorem simulateQ_sessRedImpl_tag_gt {ι σL σR α : Type} {spec : OracleSpec ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hks : k < s)
    (X : OracleComp (unifSpec + spec) α) :
    ∀ (sL : ℕ → σL) (sR : ℕ → σR),
      (simulateQ (sessRedImpl implL implR k) (simulateQ (sessTag s) X)).run (sL, sR) =
        (liftM ((fun r => (r.1, (Function.update sL s r.2, sR))) <$>
          (simulateQ (fwd implL) X).run (sL s)) :
          OracleComp (unifSpec + spec) (α × (ℕ → σL) × (ℕ → σR))) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro sL sR
    simp [Function.update_eq_self]
  | query_bind t kz ih =>
    intro sL sR
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | q'
    · rw [sessRedImpl_sessTag_inl]
      simp only [bind_assoc, pure_bind, ih, fwd_inl,
        QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B,
        QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, liftM_bind, liftM_map]
      rfl
    · rw [sessRedImpl_sessTag_inr_gt implL implR hks, liftM_map, bind_map_left]
      have hstep : ∀ r : spec.Range q' × σL,
          (simulateQ (sessRedImpl implL implR k) (simulateQ (sessTag s) (kz r.1))).run
            (Function.update sL s r.2, sR) =
          liftM ((fun r' => (r'.1, (Function.update sL s r'.2, sR))) <$>
            (simulateQ (fwd implL) (kz r.1)).run r.2) := fun r => by
        rw [ih r.1 (Function.update sL s r.2) sR]
        simp [Function.update_self, Function.update_idem]
      simp only [hstep]
      rw [← liftM_bind]
private def mkLSt {σL : Type} (k : ℕ) (sL : ℕ → σL) (st : ℕ → Bool) : ℕ → σL × Bool :=
  fun s => (sL s, if k < s then st s else false)
private def mkRSt {σR : Type} (k : ℕ) (sR : ℕ → σR) (st : ℕ → Bool) : ℕ → σR × Bool :=
  fun s => (sR s, if s < k then st s else false)
private theorem mkLSt_update_same {σL : Type} (k : ℕ) (sL : ℕ → σL) (st : ℕ → Bool) (b : Bool) :
    mkLSt k sL (Function.update st k b) = mkLSt k sL st := by
  funext s
  by_cases h : k < s
  · have hne : s ≠ k := (Nat.ne_of_lt h).symm
    simp [mkLSt, h, hne]
  · simp [mkLSt, h]
private theorem mkRSt_update_same {σR : Type} (k : ℕ) (sR : ℕ → σR) (st : ℕ → Bool) (b : Bool) :
    mkRSt k sR (Function.update st k b) = mkRSt k sR st := by
  funext s
  by_cases h : s < k
  · have hne : s ≠ k := Nat.ne_of_lt h
    simp [mkRSt, h, hne]
  · simp [mkRSt, h]
private theorem mkLSt_update_lt {σL : Type} {s k : ℕ} (hsk : s < k)
    (sL : ℕ → σL) (st : ℕ → Bool) (b : Bool) :
    mkLSt k sL (Function.update st s b) = mkLSt k sL st := by
  funext i
  by_cases h : k < i
  · have hne : i ≠ s := by omega
    simp [mkLSt, h, hne]
  · simp [mkLSt, h]
private theorem mkRSt_update_lt {σR : Type} {s k : ℕ} (hsk : s < k)
    (sR : ℕ → σR) (st : ℕ → Bool) (s' : σR) (b : Bool) :
    Function.update (mkRSt k sR st) s (s', b) =
      mkRSt k (Function.update sR s s') (Function.update st s b) := by
  funext i
  by_cases hi : i = s
  · subst hi; simp [mkRSt, hsk]
  · simp [mkRSt, hi]
private theorem mkRSt_update_gt {σR : Type} {s k : ℕ} (hks : k < s)
    (sR : ℕ → σR) (st : ℕ → Bool) (b : Bool) :
    mkRSt k sR (Function.update st s b) = mkRSt k sR st := by
  funext i
  by_cases h : i < k
  · have hne : i ≠ s := by omega
    simp [mkRSt, h, hne]
  · simp [mkRSt, h]
private theorem mkLSt_update_gt {σL : Type} {s k : ℕ} (hks : k < s)
    (sL : ℕ → σL) (st : ℕ → Bool) (s' : σL) (b : Bool) :
    Function.update (mkLSt k sL st) s (s', b) =
      mkLSt k (Function.update sL s s') (Function.update st s b) := by
  funext i
  by_cases hi : i = s
  · subst hi; simp [mkLSt, hks]
  · simp [mkLSt, hi]
private theorem tr_sessAdv_wrapTrImpl_run_eq {ι₁ ι₂ σL σR α : Type}
    {G₁ : OracleSpec ι₁} {G₂ : OracleSpec ι₂}
    (tr : QueryImpl (unifSpec + G₁) (StateT Bool (OracleComp (unifSpec + G₂))))
    (implL : QueryImpl G₂ (StateT σL ProbComp))
    (implR : QueryImpl G₂ (StateT σR ProbComp))
    (htr_inl : ∀ n b, (tr (.inl n)).run b =
      (query (spec := unifSpec + G₂) (.inl n) >>= fun u => pure (u, b)))
    (k : ℕ) (M : OracleComp (unifSpec + multiSessSpec G₁) α) :
    ∀ (sL : ℕ → σL) (sR : ℕ → σR) (st : ℕ → Bool),
      (fun z => z.1.1) <$>
        (simulateQ tr
          ((simulateQ (sessRedImpl (wrapTrImpl tr implL) (wrapTrImpl tr implR) k) M).run
            (mkLSt k sL st, mkRSt k sR st))).run (st k) =
      (fun z => z.1.1) <$>
        (simulateQ (sessRedImpl implL implR k)
          ((simulateQ (multiTrImpl tr) M).run st)).run (sL, sR) := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro sL sR st
    simp
  | query_bind t cont ih =>
    intro sL sR st
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨s, q⟩
    · simp only [add_apply_inl, sessRedImpl, multiTrImpl, StateT.run_lift, bind_pure_comp,
        simulateQ_map, StateT.run_map, bind_map_left, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, htr_inl]
      exact bind_congr fun u => ih u sL sR st
    · by_cases heq : s = k
      · subst heq
        simp only [add_apply_inr, sigma_apply, sessRedImpl, multiTrImpl, ↓reduceIte,
          StateT.run_lift, StateT.run_mk, bind_pure_comp, simulateQ_map,
          StateT.run_map, bind_map_left]
        rw [simulateQ_sessRedImpl_tag_same]
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          bind_map_left]
        refine bind_congr fun ⟨u, b'⟩ => ?_
        have hst := ih u sL sR (Function.update st s b')
        simpa only [mkLSt_update_same, mkRSt_update_same, Function.update_self] using hst
      · by_cases hlt : s < k
        · simp only [add_apply_inr, sigma_apply, sessRedImpl, multiTrImpl, heq, hlt, ↓reduceIte,
            StateT.run_mk, simulateQ_bind, StateT.run_bind, bind_assoc]
          rw [simulateQ_sessRedImpl_tag_lt implL implR hlt]
          have hmkR : (mkRSt k sR st) s = (sR s, st s) := by simp [mkRSt, hlt]
          rw [hmkR]
          dsimp only [wrapTrImpl]
          rw [StateT.run_mk, liftM_map, simulateQ_map, StateT.run_map,
            simulateQ_tr_liftM_run tr htr_inl]
          simp only [bind_map_left, simulateQ_pure, StateT.run_pure, pure_bind,
            liftM_bind, bind_assoc, liftM_map, Functor.map_map]
          refine bind_congr fun ⟨⟨u, b'⟩, s'⟩ => ?_
          have hst := ih u sL (Function.update sR s s') (Function.update st s b')
          have hbk : Function.update st s b' k = st k := Function.update_of_ne (Ne.symm heq) b' st
          rw [mkLSt_update_lt hlt, ← mkRSt_update_lt hlt, hbk] at hst
          exact hst
        · have hgt : k < s := by omega
          simp only [add_apply_inr, sigma_apply, sessRedImpl, multiTrImpl, heq, hlt, ↓reduceIte,
            StateT.run_mk, simulateQ_bind, StateT.run_bind, bind_assoc]
          rw [simulateQ_sessRedImpl_tag_gt implL implR hgt]
          have hmkL : (mkLSt k sL st) s = (sL s, st s) := by simp [mkLSt, hgt]
          rw [hmkL]
          dsimp only [wrapTrImpl]
          rw [StateT.run_mk, liftM_map, simulateQ_map, StateT.run_map,
            simulateQ_tr_liftM_run tr htr_inl]
          simp only [bind_map_left, simulateQ_pure, StateT.run_pure, pure_bind,
            liftM_bind, bind_assoc, liftM_map, Functor.map_map]
          refine bind_congr fun ⟨⟨u, b'⟩, s'⟩ => ?_
          have hst := ih u (Function.update sL s s') sR (Function.update st s b')
          have hbk : Function.update st s b' k = st k := Function.update_of_ne (Ne.symm heq) b' st
          rw [mkRSt_update_gt hgt, ← mkLSt_update_gt hgt, hbk] at hst
          exact hst

theorem pubRed_sessAdv_wrapPubImpl_eq {SS RS AD Pub M C σL σR α : Type}
    (pubOf : C → Option Pub)
    (implL : QueryImpl (CryptoGames.FSAEAD.spec SS RS (AD × Pub) M C) (StateT σL ProbComp))
    (implR : QueryImpl (CryptoGames.FSAEAD.spec SS RS (AD × Pub) M C) (StateT σR ProbComp))
    (M_adv : OracleComp (unifSpec + multiSessSpec (CryptoGames.FSAEAD.spec SS RS AD (Pub × M) C)) α)
    (sL : ℕ → σL) (sR : ℕ → σR) (k : ℕ) :
    (simulateQ (CryptoGames.FSAEAD.pubRedImpl (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf)
      (sessAdv (wrapPubImpl pubOf implL) (wrapPubImpl pubOf implR) M_adv
        (fun s => (sL s, false)) (fun s => (sR s, false)) k)).run' false =
      sessAdv implL implR
        ((simulateQ (multiTrImpl
            (CryptoGames.FSAEAD.pubRedImpl (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf)) M_adv).run'
          (fun _ => false))
        sL sR k := by
  have h := tr_sessAdv_wrapTrImpl_run_eq
    (CryptoGames.FSAEAD.pubRedImpl (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf)
    implL implR (fun _ _ => rfl) k M_adv sL sR (fun _ => false)
  have hL : mkLSt k sL (fun _ => false) = fun s => (sL s, false) := by funext s; simp [mkLSt]
  have hR : mkRSt k sR (fun _ => false) = fun s => (sR s, false) := by funext s; simp [mkRSt]
  rw [hL, hR] at h
  simpa only [sessAdv, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
    Function.comp_def] using h
private theorem multiSessPubToAD_eq_multiTrImpl {Pt : Type} (codec : SignalMessageProtoCodec)
    {ℓ : ℕ} (AdvPub : MultiSessPubFsAdv Pt ℓ) :
    multiSessPubToAD codec AdvPub =
      (simulateQ (multiTrImpl
        (CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LCt => lPubOf codec c.2))) AdvPub).run' (fun _ => false) := by
  dsimp only [multiSessPubToAD]
  congr 2
  funext t
  rcases t with n | ⟨s, q⟩
  · rfl
  · dsimp only [multiTrImpl]
    refine congrArg StateT.mk (funext fun st =>
      congrArg (· >>= _) (congrArg (simulateQ · _) ?_))
    funext x
    cases x <;> rfl

@[expose] def lPubSessAdv {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
    (AdvPub : α → MultiSessPubFsAdv Pt ℓ) (o : α) (j : ℕ) : FsAdv Pt ℓ :=
  sessAdv
    (wrapPubImpl (fun c : ℕ × LCt => lPubOf codec c.2)
      (lazyInit fsInit
        (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp 0 0 la))))
    (wrapPubImpl (fun c : ℕ × LCt => lPubOf codec c.2)
      (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
        (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip N la (slotSaltImpl C codec ℓ encT (idOf o) false))))
    (AdvPub o) (fun _ => (none, false)) (fun _ => (none, false)) j

@[expose] def lPubWireSessAdv {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
    (AdvPub : α → MultiSessPubFsAdv Pt ℓ) (P : Params) (o : α) (j : ℕ) : FsAdv Pt ℓ :=
  sessAdv
    (wrapPubImpl (fun c : ℕ × LCt => lPubOf codec c.2)
      (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
        (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip N la (slotSaltImplNF C codec ℓ encT (idOf o) false))))
    (wrapPubImpl (fun c : ℕ × LCt => lPubOf codec c.2)
      (lazyInit fsInit
        (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip P)))
    (AdvPub o) (fun _ => (none, false)) (fun _ => (none, false)) j

@[expose] def lPubRouterAdv {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (maxSkip qR : ℕ)
    (AdvPub : Bool → α → MultiSessPubFsAdv Pt ℓ) :
    Bool → Bool → ℕ → α → FsAdv Pt ℓ :=
  fun stage la j o =>
    let N := authHopCutoff maxSkip qR la
    if stage then
      lPubWireSessAdv C codec ℓ encT idOf maxSkip N la (AdvPub la) (hp N N la) o j
    else
      lPubSessAdv C codec ℓ encT idOf maxSkip N la (AdvPub la) o j

theorem pubToAD_lPubSessAdv_eq {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
    (AdvPub : α → MultiSessPubFsAdv Pt ℓ) (o : α) (j : ℕ) :
    pubToAD codec (lPubSessAdv C codec ℓ encT idOf maxSkip N la AdvPub o j) =
      lSessAdv C codec ℓ encT idOf maxSkip N la
        (fun o' => multiSessPubToAD codec (AdvPub o')) o j := by
  unfold pubToAD CryptoGames.FSAEAD.pubRed lPubSessAdv lSessAdv fsSessAdv
  rw [pubRed_sessAdv_wrapPubImpl_eq (fun c : ℕ × LCt => lPubOf codec c.2) _ _
    (AdvPub o) (fun _ => none) (fun _ => none) j, ← multiSessPubToAD_eq_multiTrImpl]

theorem pubToAD_lPubWireSessAdv_eq {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
    (AdvPub : α → MultiSessPubFsAdv Pt ℓ) (P : Params) (o : α) (j : ℕ) :
    pubToAD codec (lPubWireSessAdv C codec ℓ encT idOf maxSkip N la AdvPub P o j) =
      lWireSessAdv C codec ℓ encT idOf maxSkip N la
        (fun o' => multiSessPubToAD codec (AdvPub o')) P o j := by
  unfold pubToAD CryptoGames.FSAEAD.pubRed lPubWireSessAdv lWireSessAdv fsWireSessAdv
  rw [pubRed_sessAdv_wrapPubImpl_eq (fun c : ℕ × LCt => lPubOf codec c.2) _ _
    (AdvPub o) (fun _ => none) (fun _ => none) j, ← multiSessPubToAD_eq_multiTrImpl]

end

end Computational.Proofs.HeadlineV1.Stage2RouterHelpers
