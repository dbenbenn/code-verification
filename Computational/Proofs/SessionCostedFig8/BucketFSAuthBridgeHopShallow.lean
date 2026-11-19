/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.ReductionDsl.SM.Theorem1

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames (Party AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult
  withPub fromAEADPRG transmitQuery corruptSenderQuery deliverQuery injectQuery pubRedImpl)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt HState DG SpecialOps hp hInit
  transmitHWith corruptSenderH deliverH injectH)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (SyncRML)
open _root_.CryptoGames.SM (GameState healedBy ltOpt lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (Header healEpoch FSMultiSpec)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lChainPRG lAead lAeadR lIdeal lPubOf lFS)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift sessLift_inl sessLift_inr
  sessLiftCore lazyInit sessOffRange multiSessSpec fwd sessAdv hybSess hybSess_inl hybSess_inr
  hybSessCore sessLift_lazy_boolDist_le sessRed_step_left lazyInit_run_some lazyInit_run_none
  lazyInit_run_some')
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsInit fsImpl)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (validGuessBucketParAuth)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak)

/-! ### 1. Pure Session-Slot & Bucket Arithmetic Helpers -/

@[expose] def sIdxMain (q : ℕ) (tL : Option ℕ) (t0 : ℕ) : ℕ :=
  (q + 1) * (t0 - healEpoch tL)

@[expose] def mSessMain (q qep : ℕ) (tL : Option ℕ) : ℕ :=
  (q + 1) * ((qep + 2) - healEpoch tL)

theorem healedBy_imp_healEpoch_le (tL : Option ℕ) (t0 : ℕ)
    (h : healedBy tL 3 t0 = true) : healEpoch tL ≤ t0 := by
  cases tL with
  | none => simp [healEpoch]
  | some l =>
    simp [healedBy] at h
    simp [healEpoch]; omega

theorem sIdxMain_lt_mSessMain (q qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ht0 : !(decide (qep + 1 < t0)) = true)
    (hv : validGuessBucketParAuth 1 tL par t0 = true) :
    sIdxMain q tL t0 < mSessMain q qep tL := by
  have hle : t0 ≤ qep + 1 := by simp at ht0; exact ht0
  have hh : healEpoch tL ≤ t0 := by
    apply healedBy_imp_healEpoch_le
    simp [validGuessBucketParAuth, lastLeakGuessAdmissible] at hv
    exact hv.1
  unfold sIdxMain mSessMain
  have hsub : t0 - healEpoch tL < (qep + 2) - healEpoch tL := by omega
  exact Nat.mul_lt_mul_of_pos_left hsub (Nat.succ_pos q)

theorem sIdxMain_inj (q : ℕ) (tL : Option ℕ) {t1 t2 : ℕ}
    (h1 : healEpoch tL ≤ t1) (h2 : healEpoch tL ≤ t2)
    (heq : sIdxMain q tL t1 = sIdxMain q tL t2) : t1 = t2 := by
  unfold sIdxMain at heq
  have hsub := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) heq
  omega

theorem healedBy_of_not_postLeak {St Msg C : Type}
    (tL : Option ℕ) (ctx : GameState St Msg C) (t0 : ℕ)
    (hpl : postLeak tL ctx = false) (hh : healedBy tL 3 t0 = true) :
    healedBy ctx.tL 3 t0 = true := by
  unfold postLeak at hpl
  cases hctx : ctx.tL with
  | none => rfl
  | some cur =>
    rw [hctx] at hpl
    cases tL with
    | none => simp [ltOpt] at hpl
    | some l =>
      simp [ltOpt] at hpl
      simp [healedBy] at hh ⊢
      omega

theorem receiverOf_eq_of_sender_par (par : Bool) {t0 tWin : ℕ}
    (h0 : (decide (Party.senderOf t0 == Party.A) == par) = true)
    (hw : (decide (Party.senderOf tWin == Party.A) == par) = true) :
    Party.receiverOf t0 = Party.receiverOf tWin := by
  have hs : Party.senderOf t0 = Party.senderOf tWin := by
    cases hs0 : Party.senderOf t0 <;> cases hsw : Party.senderOf tWin <;>
      cases par <;> simp_all
  simp only [Party.receiverOf, hs]

theorem ltOpt_of_healedBy_le (tL : Option ℕ) {t0 ep : ℕ}
    (hh : healedBy tL 3 t0 = true) (hle : t0 ≤ ep) :
    ltOpt tL ep = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp [healedBy] at hh
    simp [ltOpt]; omega

/-! ### 2. `LeAdd`, `LeOne`, and Eager Session/Slot Pre-Sampling -/

@[expose] def LeAdd (cLoc cM cL : ProbComp Bool) : Prop :=
  𝒟[cLoc] {true} ≤ 𝒟[cM] {true} + 𝒟[cL] {true}

@[expose] def LeOne (cLoc cM : ProbComp Bool) : Prop :=
  𝒟[cLoc] {true} ≤ 𝒟[cM] {true}

theorem leAdd_of_lhs_zero {cLoc cM cL : ProbComp Bool}
    (h0 : 𝒟[cLoc] {true} = 0) : LeAdd cLoc cM cL := by
  unfold LeAdd; rw [h0]; simp

theorem leAdd_of_le_main {cLoc cM cL : ProbComp Bool}
    (hle : LeOne cLoc cM) : LeAdd cLoc cM cL :=
  hle.trans le_self_add

theorem leAdd_of_la_one {cLoc cM cL : ProbComp Bool}
    (h1 : 𝒟[cL] {true} = 1) : LeAdd cLoc cM cL := by
  unfold LeAdd
  rw [h1]
  have hle1 : 𝒟[cLoc] {true} ≤ 1 := by
    calc
      𝒟[cLoc] {true} ≤ 𝒟[cLoc] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  exact hle1.trans le_add_self

theorem leOne_of_lhs_zero {cLoc cM : ProbComp Bool}
    (h0 : 𝒟[cLoc] {true} = 0) : LeOne cLoc cM := by
  unfold LeOne; rw [h0]; simp

private theorem evalDist_bind_const_true {α : Type} (oa : ProbComp α) (c : ProbComp Bool) :
    𝒟[oa >>= fun _ => c] {true} = 𝒟[c] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp only [pure_bind]
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
    have hcongr : (fun u => 𝒟[k u >>= fun _ => c] {true}) = fun _ => 𝒟[c] {true} := by
      funext u; exact ih u
    rw [hcongr, MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ,
      mul_one]

theorem leAdd_bind {α : Type} (oa : ProbComp α)
    {fLoc fM fL : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeAdd (fLoc a) (fM a) (fL a)) :
    LeAdd (oa >>= fLoc) (oa >>= fM) (oa >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    unfold LeAdd
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] {true} =
          ∫⁻ u, 𝒟[g u] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fLoc), h1 (fun u => k u >>= fM), h1 (fun u => k u >>= fL),
      ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩

theorem leAdd_bind_dummy_loc {α : Type} (oa : ProbComp α)
    {cLoc : ProbComp Bool} {fM fL : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeAdd cLoc (fM a) (fL a)) :
    LeAdd cLoc (oa >>= fM) (oa >>= fL) := by
  have hL := leAdd_bind oa (fLoc := fun _ => cLoc) h
  unfold LeAdd at hL ⊢
  rwa [evalDist_bind_const_true oa cLoc] at hL

theorem leOne_bind {α : Type} (oa : ProbComp α)
    {fLoc fM : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeOne (fLoc a) (fM a)) :
    LeOne (oa >>= fLoc) (oa >>= fM) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    unfold LeOne
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] {true} =
          ∫⁻ u, 𝒟[g u] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fLoc), h1 (fun u => k u >>= fM)]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩

theorem leOne_bind_dummy_loc {α : Type} (oa : ProbComp α)
    {cLoc : ProbComp Bool} {fM : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeOne cLoc (fM a)) :
    LeOne cLoc (oa >>= fM) := by
  have hL := leOne_bind oa (fLoc := fun _ => cLoc) h
  unfold LeOne at hL ⊢
  rwa [evalDist_bind_const_true oa cLoc] at hL

private def fsSeedInit {CK MK AD M C : Type} [SampleableType CK] :
    ProbComp (_root_.CryptoGames.FSAEAD.Thm5.HSt CK MK AD M C) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ CK : ProbComp CK)
  return _root_.CryptoGames.FSAEAD.Thm5.hInit b (.seed k)

private theorem fsSeedInit_bind_run_evalDist_eq {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : _root_.CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (la : Bool)
    (B : _root_.CryptoGames.FSAEAD.RatchetAdversary CK MK AD M C) :
    𝒟[fsSeedInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd
          (fsImpl ideal ae G maxSkip (hp 0 0 la))) B).run s] =
      𝒟[fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd
          (fsImpl ideal ae G maxSkip (hp 0 0 la))) B).run s] := by
  unfold fsSeedInit fsInit
  simp only [bind_assoc, pure_bind, _root_.CryptoVerification.E2E.Signed.SessionFS.fwd_fsImpl]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  let P := hp 0 0 la
  let D := DG G
  let fill := _root_.CryptoGames.FSAEAD.Thm5.seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hI := _root_.CryptoGames.FSAEAD.Thm5.seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hK : ∀ h h' : HState CK MK AD M C,
      h.keys.length = h'.keys.length → fill h = fill h' := by
    intro h h' hl; funext sl; cases sl <;> simp [fill, _root_.CryptoGames.FSAEAD.Thm5.seedFill, hl]
  have hGen := _root_.CryptoGames.FSAEAD.Thm5.comm_genStep_seed (AD := AD) (M := M) (C := C) G P 0 le_rfl
  have hRev := _root_.CryptoGames.FSAEAD.Thm5.comm_reveal_seed (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hc := _root_.CryptoGames.Lazy.Comm.simulateQ hI
    (_root_.CryptoGames.FSAEAD.Thm5.comm_impl ideal ae G maxSkip P D hI hK hGen hRev) B
    (hInit b .unknown)
  have hdeq : _root_.CryptoGames.Lazy.DEq
      ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
        (_root_.CryptoGames.Lazy.fillSt fill (hInit b .unknown) >>=
          (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxSkip P D
            (none : Option (SpecialOps AD M C ProbComp))) B).run))
      ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
        (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxSkip P D none) B).run
          (hInit b .unknown)) :=
    (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _).symm.trans
      ((_root_.CryptoGames.Lazy.DEq.map hc _).trans
        (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
          Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _))
  have h0 : _root_.CryptoGames.Lazy.fillSt fill
      (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown) =
      (($ᵗ CK) >>= fun k => pure (hInit b (.seed k))) := by
    simp [fill, _root_.CryptoGames.Lazy.fillSt, _root_.CryptoGames.FSAEAD.Thm5.seedFill,
      hInit, map_eq_bind_pure_comp]
  have heq := _root_.CryptoGames.Lazy.DEq.evalDist_eq hdeq
  rw [h0] at heq
  simpa only [Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, P, D] using heq

private theorem multiFsSeeded_le_real {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : _root_.CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip M_sess : ℕ) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)
    (hoff : Adv.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0) :
    𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} ≤
      𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} := by
  have hbd := sessLift_lazy_boolDist_le
    fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la))
    fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la))
    M_sess Adv hoff
  have hsum0 : (∑ k ∈ Finset.range M_sess,
      𝒟[fsSeedInit >>= fun s => Prod.fst <$> (simulateQ (fwd
          (fsImpl ideal ae G maxSkip (hp 0 0 la)))
          (sessAdv
            (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))
            Adv (fun _ => none) (fun _ => none) k)).run s].boolDist
        𝒟[fsInit >>= fun s => Prod.fst <$> (simulateQ (fwd
          (fsImpl ideal ae G maxSkip (hp 0 0 la)))
          (sessAdv
            (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))
            Adv (fun _ => none) (fun _ => none) k)).run s]) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [fsSeedInit_bind_run_evalDist_eq]
    exact MeasureTheory.Measure.boolDist_self _
  rw [hsum0] at hbd
  calc
    _ ≤ 𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
          (fun _ => none)] {true} +
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
          (fun _ => none)].boolDist
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
          (fun _ => none)] := MeasureTheory.Measure.apply_true_le_add_boolDist _ _
    _ ≤ _ + 0 := add_le_add le_rfl hbd
    _ = _ := add_zero _

private theorem hybSess_same_eq_sessLift {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (k : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α) (s1 s2 : ℕ → σ) :
    Prod.fst <$> (simulateQ (hybSess impl impl k) oa).run (s1, s2) =
      Prod.fst <$> (simulateQ (sessLift impl) oa).run (fun i => if i < k then s2 i else s1 i) := by
  induction oa using OracleComp.inductionOn generalizing s1 s2 with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨i, q⟩
    · simp only [hybSess_inl, sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u s1 s2
    · by_cases hi : i < k
      · simp only [hybSess_inr, hybSessCore, sessLift_inr, sessLiftCore, hi, ↓reduceIte,
          StateT.run_mk, bind_map_left]
        refine bind_congr fun z => ?_
        have hupd : (fun j => if j < k then Function.update s2 i z.2 j else s1 j) =
            Function.update (fun j => if j < k then s2 j else s1 j) i z.2 := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [hi]
          · simp [Function.update_of_ne hj]
        rw [← hupd]
        exact ih z.1 s1 (Function.update s2 i z.2)
      · simp only [hybSess_inr, hybSessCore, sessLift_inr, sessLiftCore, hi, ↓reduceIte,
          StateT.run_mk, bind_map_left]
        refine bind_congr fun z => ?_
        have hupd : (fun j => if j < k then s2 j else Function.update s1 i z.2 j) =
            Function.update (fun j => if j < k then s2 j else s1 j) i z.2 := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [hi]
          · simp [Function.update_of_ne hj]
        rw [← hupd]
        exact ih z.1 (Function.update s1 i z.2) s2

private theorem sessLift_lazyInit_step_evalDist {ι σ : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (M : OracleComp (unifSpec + multiSessSpec spec) Bool)
    (tbl : ℕ → Option σ) (k : ℕ) (hk : tbl k = none) :
    𝒟[init >>= fun v =>
        Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run
          (Function.update tbl k (some v))] =
      𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run tbl] := by
  let L := lazyInit init impl
  let Ak := sessAdv L L M tbl tbl k
  have hstep : ∀ sx : Option σ,
      Prod.fst <$> (simulateQ (fwd L) Ak).run sx =
        Prod.fst <$> (simulateQ (sessLift L) M).run (Function.update tbl k sx) := by
    intro sx
    have h1 := congrArg (fun x => Prod.fst <$> x) (sessRed_step_left L L k M tbl tbl sx)
    simp only [Ak, sessAdv, simulateQ_map, StateT.run_map, Functor.map_map] at h1 ⊢
    rw [h1, hybSess_same_eq_sessLift L k M (Function.update tbl k sx) tbl]
    have hmerge : (fun i => if i < k then tbl i else Function.update tbl k sx i) =
        Function.update tbl k sx := by
      funext i
      by_cases hi : i < k
      · have hne : i ≠ k := Nat.ne_of_lt hi
        simp [hi, Function.update_of_ne hne]
      · simp [hi]
    rw [hmerge]
  have hnone : Prod.fst <$> (simulateQ (sessLift L) M).run tbl =
      Prod.fst <$> (simulateQ (fwd L) Ak).run none := by
    have h0 := hstep none
    have hupd0 : Function.update tbl k none = tbl := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [hk]
      · simp [Function.update_of_ne hi]
    rw [hupd0] at h0
    exact h0.symm
  have hsome : ∀ v : σ,
      Prod.fst <$> (simulateQ (sessLift L) M).run (Function.update tbl k (some v)) =
        Prod.fst <$> (simulateQ (fwd impl) Ak).run v := by
    intro v
    rw [← hstep (some v), lazyInit_run_some init impl Ak v, Functor.map_map]
  rw [hnone, (lazyInit_run_none init impl Ak).evalDist_eq]
  exact evalDist_bind_congr init _ _ fun v => congrArg evalDist (hsome v)

@[expose] def sampleVec {α : Type} (samp : ProbComp α) (dflt : α) : ℕ → ProbComp (ℕ → α)
  | 0 => pure (fun _ => dflt)
  | m + 1 => do
    let tbl ← sampleVec samp dflt m
    let v ← samp
    return Function.update tbl m v

private def toOptTbl {σ : Type} (m : ℕ) (tbl : ℕ → σ) : ℕ → Option σ :=
  fun i => if i < m then some (tbl i) else none

private theorem sessLift_lazyInit_sampleVec_evalDist {ι σ : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (dflt : σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (M : OracleComp (unifSpec + multiSessSpec spec) Bool) :
    ∀ m : ℕ,
      𝒟[sampleVec init dflt m >>= fun tbl =>
          Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run (toOptTbl m tbl)] =
        𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run (fun _ => none)]
  | 0 => by
    have h0 : toOptTbl 0 (fun _ : ℕ => dflt) = (fun _ => none) := by
      funext i; simp [toOptTbl]
    simp [sampleVec, h0]
  | m + 1 => by
    simp only [sampleVec, bind_assoc, pure_bind]
    have hstep : ∀ tbl : ℕ → σ,
        𝒟[init >>= fun v =>
            Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run
              (toOptTbl (m + 1) (Function.update tbl m v))] =
          𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run (toOptTbl m tbl)] := by
      intro tbl
      have hto : ∀ v : σ, toOptTbl (m + 1) (Function.update tbl m v) =
          Function.update (toOptTbl m tbl) m (some v) := by
        intro v; funext i
        by_cases hi : i = m
        · subst hi; simp [toOptTbl]
        · have hiff : (i < m + 1) ↔ (i < m) := by omega
          simp [toOptTbl, Function.update_of_ne hi, hiff]
      have hm_none : toOptTbl m tbl m = none := by simp [toOptTbl]
      simp_rw [hto]
      exact sessLift_lazyInit_step_evalDist init impl M (toOptTbl m tbl) m hm_none
    calc
      _ = 𝒟[sampleVec init dflt m >>= fun tbl =>
            Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) M).run (toOptTbl m tbl)] := by
            rw [← evalDist_bind_congr (sampleVec init dflt m) _ _ hstep]
      _ = _ := sessLift_lazyInit_sampleVec_evalDist init dflt impl M m

private theorem sessLift_lazyInit_eq_of_offRange {ι σ : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp)) (q : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α)
    (hoff : oa.IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    (s : ℕ → σ) (tbl : ℕ → Option σ) (htbl : ∀ i < q, tbl i = some (s i)) :
    Prod.fst <$> (simulateQ (sessLift (lazyInit init impl)) oa).run tbl =
      Prod.fst <$> (simulateQ (sessLift impl) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s tbl with
  | pure a => simp
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hoff
    have hnp : ¬ (sessOffRange q t = true) := hoff.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (r u).IsQueryBoundP (fun t => sessOffRange q t = true) 0 :=
      fun u => by simpa [hnp] using hoff.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨i, o⟩
    · simp only [sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hcont u) s tbl htbl
    · have hi : i < q := by simpa [sessOffRange] using hnp
      simp only [sessLift_inr, sessLiftCore, StateT.run_mk, htbl i hi, lazyInit_run_some',
        Functor.map_map, bind_map_left]
      refine bind_congr fun z => ih z.1 (hcont z.1) (Function.update s i z.2)
        (Function.update tbl i (some z.2)) fun j hj => ?_
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update_of_ne hji, htbl j hj]

private theorem sampleSeedInit_split_deq {CK MK AD M C : Type} [SampleableType CK]
    (k0 : CK) :
    ∀ m : ℕ,
      _root_.CryptoGames.Lazy.DEq
        (sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
          (hInit false (.seed k0)) m)
        (sampleVec ($ᵗ CK : ProbComp CK) k0 m >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false m >>= fun bs =>
            pure (fun i => hInit (bs i) (.seed (ks i))))
  | 0 => by
    dsimp only [sampleVec]
    simp only [pure_bind]
    exact _root_.CryptoGames.Lazy.DEq.refl _
  | m + 1 => by
    have ih := sampleSeedInit_split_deq (MK := MK) (AD := AD) (M := M) (C := C) k0 m
    dsimp only [sampleVec, fsSeedInit]
    refine (_root_.CryptoGames.Lazy.DEq.bind_left ih _).trans ?_
    simp only [bind_assoc, pure_bind]
    refine _root_.CryptoGames.Lazy.DEq.bind_right (sampleVec ($ᵗ CK : ProbComp CK) k0 m) fun ks => ?_
    refine (_root_.CryptoGames.Lazy.DEq.bind_right (sampleVec ($ᵗ Bool : ProbComp Bool) false m)
      fun bs => _root_.CryptoGames.Lazy.DEq.swap ($ᵗ Bool : ProbComp Bool) ($ᵗ CK : ProbComp CK) _).trans ?_
    refine (_root_.CryptoGames.Lazy.DEq.swap
      (sampleVec ($ᵗ Bool : ProbComp Bool) false m) ($ᵗ CK : ProbComp CK) _).trans ?_
    refine _root_.CryptoGames.Lazy.DEq.bind_right ($ᵗ CK : ProbComp CK) fun k => ?_
    refine _root_.CryptoGames.Lazy.DEq.bind_right (sampleVec ($ᵗ Bool : ProbComp Bool) false m) fun bs => ?_
    refine _root_.CryptoGames.Lazy.DEq.bind_right ($ᵗ Bool : ProbComp Bool) fun b => ?_
    refine _root_.CryptoGames.Lazy.DEq.of_eq ?_
    congr 1; funext i
    by_cases hi : i = m
    · subst hi; simp
    · simp [Function.update_of_ne hi]

theorem multiFsEager_le_real {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : _root_.CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip M_sess : ℕ) (k0 : CK) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)
    (hoff : Adv.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0) :
    𝒟[sampleVec ($ᵗ CK : ProbComp CK) k0 M_sess >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift
            (fsImpl ideal ae G maxSkip (hp 0 0 la))) Adv).run
            (fun i => hInit (bs i) (.seed (ks i)))] {true} ≤
      𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} := by
  have heq1 :
      𝒟[sampleVec ($ᵗ CK : ProbComp CK) k0 M_sess >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
            Prod.fst <$> (simulateQ (sessLift
              (fsImpl ideal ae G maxSkip (hp 0 0 la))) Adv).run
              (fun i => hInit (bs i) (.seed (ks i)))] =
        𝒟[sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
            (hInit false (.seed k0)) M_sess >>= fun tbl =>
          Prod.fst <$> (simulateQ (sessLift
            (fsImpl ideal ae G maxSkip (hp 0 0 la))) Adv).run tbl] := by
    have hdeq1 := _root_.CryptoGames.Lazy.DEq.bind_left
      (sampleSeedInit_split_deq (MK := MK) (AD := AD) (M := M) (C := C) k0 M_sess).symm
      (fun tbl => Prod.fst <$> (simulateQ (sessLift
        (fsImpl ideal ae G maxSkip (hp 0 0 la))) Adv).run tbl)
    simp only [bind_assoc, pure_bind] at hdeq1
    exact hdeq1.evalDist_eq
  have heq2 :
      𝒟[sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
          (hInit false (.seed k0)) M_sess >>= fun tbl =>
        Prod.fst <$> (simulateQ (sessLift
          (fsImpl ideal ae G maxSkip (hp 0 0 la))) Adv).run tbl] =
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (hp 0 0 la)))) Adv).run
          (fun _ => none)] := by
    rw [← sessLift_lazyInit_sampleVec_evalDist fsSeedInit
      (hInit false (.seed k0))
      (fsImpl ideal ae G maxSkip (hp 0 0 la)) Adv M_sess]
    refine evalDist_bind_congr _ _ _ fun tbl => congrArg evalDist ?_
    exact (sessLift_lazyInit_eq_of_offRange fsSeedInit
      (fsImpl ideal ae G maxSkip (hp 0 0 la)) M_sess Adv hoff
      tbl (toOptTbl M_sess tbl) fun i hi => by simp [toOptTbl, hi]).symm
  rw [heq1, heq2]
  exact multiFsSeeded_le_real ideal ae G maxSkip M_sess la Adv hoff

@[expose] def keySlotSpec (K : Type) : OracleSpec Unit := fun _ => K

@[expose] def keySlotImpl (K : Type) : QueryImpl (keySlotSpec K) (StateT K ProbComp) :=
  fun _ => get

theorem keySlot_lazy_eq_eager {K : Type} [SampleableType K]
    (k0 : K) (M_sess : ℕ)
    (M : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) Bool)
    (hoff : M.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0) :
    𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit ($ᵗ K : ProbComp K) (keySlotImpl K))) M).run
        (fun _ => none)] =
      𝒟[sampleVec ($ᵗ K : ProbComp K) k0 M_sess >>= fun ks =>
          Prod.fst <$> (simulateQ (sessLift (keySlotImpl K)) M).run ks] := by
  rw [← sessLift_lazyInit_sampleVec_evalDist ($ᵗ K : ProbComp K) k0 (keySlotImpl K) M M_sess]
  refine evalDist_bind_congr _ _ _ fun ks => congrArg evalDist ?_
  exact sessLift_lazyInit_eq_of_offRange ($ᵗ K : ProbComp K) (keySlotImpl K) M_sess M hoff
    ks (toOptTbl M_sess ks) fun i hi => by simp [toOptTbl, hi]

theorem isQueryBoundP_sessOffRange_of_ge_zero {κ β : Type} {spec : OracleSpec.{0, 0} κ}
    (M : ℕ)
    (c : OracleComp (unifSpec + multiSessSpec spec) β)
    (h : ∀ idx ≥ M, c.IsQueryBoundP
      (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0) :
    c.IsQueryBoundP (fun t => sessOffRange M t = true) 0 := by
  induction c using OracleComp.inductionOn with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff]
    rcases t with n | ⟨s, q_fs⟩
    · have hfalse : ¬ sessOffRange M (.inl n : ℕ ⊕ (_ : ℕ) × κ) = true := by
        simp [sessOffRange]
      refine ⟨Or.inl hfalse, fun u => ?_⟩
      simp only [hfalse]
      exact ih u fun idx hidx => by
        have hstep := h idx hidx
        rw [isQueryBoundP_query_bind_iff] at hstep
        simpa using hstep.2 u
    · by_cases hs : M ≤ s
      · exfalso
        have hstep := h s hs
        rw [isQueryBoundP_query_bind_iff] at hstep
        exact Nat.not_lt_zero _ (hstep.1.resolve_left (by simp))
      · have hfalse : ¬ sessOffRange M (.inr ⟨s, q_fs⟩) = true := by
          simp [sessOffRange]; omega
        refine ⟨Or.inl hfalse, fun u => ?_⟩
        simp only [hfalse]
        exact ih u fun idx hidx => by
          have hne : s ≠ idx := by omega
          have hstep := h idx hidx
          rw [isQueryBoundP_query_bind_iff] at hstep
          simpa [hne] using hstep.2 u

/-! ### 3. `lFS` Unfoldings & Single-Pass `pubFsMultiImpl` Step Lemmas -/

theorem lFS_initSender_eq {Pt : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (k : BitVec 256) :
    (lFS C codec ℓ encT idOf maxSkip).initSender k =
      (fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).initSender k := rfl

theorem lFS_initReceiver_eq {Pt : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (k : BitVec 256) :
    (lFS C codec ℓ encT idOf maxSkip).initReceiver k =
      (fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).initReceiver k := rfl

theorem lFS_send_eq {Pt : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ)
    (ss : RatchetSenderState (BitVec 256)) (h : Header Pt)
    (pm : LibsignalMsgPublicPart × Plain ℓ) :
    (lFS C codec ℓ encT idOf maxSkip).send ss h pm =
      (fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).send ss (h, pm.1) pm.2 :=
  rfl

theorem lFS_receive_eq {Pt : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ)
    (rs : RatchetReceiverState (BitVec 256) (BitVec 256)) (h : Header Pt)
    (ic : ℕ × LibsignalCiphertextWithSalt32) :
    (lFS C codec ℓ encT idOf maxSkip).receive rs h ic =
      match lPubOf codec ic.2 with
      | none => none
      | some p =>
        ((fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).receive
          rs (h, p) ic).map (fun o => (o.1, o.2.1, (p, o.2.2))) := by
  rcases ic with ⟨i, ct⟩
  unfold lFS fromAEADPRG AEADScheme.movePubPartToAD lAeadR
  dsimp only
  cases hlk : rs.skippedKeys.lookup i with
  | some key =>
    cases hp : lPubOf codec ct with
    | none => simp
    | some p => simp only [Option.map_map, Function.comp_def]
  | none =>
    by_cases hw : i ≤ rs.lastIndex ∨ maxSkip < i - rs.lastIndex - 1
    · simp only [hw, ↓reduceIte]
      cases lPubOf codec ct <;> rfl
    · simp only [hw, ↓reduceIte]
      cases hp : lPubOf codec ct with
      | none => simp
      | some p => simp only [Option.map_map, Function.comp_def]

theorem update_const_false (sIdx : ℕ) :
    Function.update (fun _ : ℕ => false) sIdx false = (fun _ => false) := by
  funext j
  by_cases hj : j = sIdx
  · subst hj; simp
  · simp [Function.update_of_ne hj]

private def sessTag {Pt : Type} {ℓ : ℕ} (s : ℕ) :
    QueryImpl
      (unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))
  | .inl n => liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n))
  | .inr q => liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩))

private theorem simulateQ_sessLift_sessTag {Pt : Type} {ℓ : ℕ} {σ α : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (s : ℕ)
    (inner : OracleComp (unifSpec + fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) α)
    (tbl : ℕ → σ) :
    (simulateQ (sessLift impl) (simulateQ (sessTag s) inner)).run tbl =
      (fun z => (z.1, Function.update tbl s z.2)) <$>
        (simulateQ (fwd impl) inner).run (tbl s) := by
  induction inner using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp [Function.update_eq_self]
  | query_bind x k ih =>
    rcases x with n | q
    · rw [simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, sessTag, monadLift_self]
      rw [simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, sessLift_inl, fwd,
        QueryImpl.add_apply, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_bind, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind, map_bind]
      exact bind_congr fun u => ih u tbl
    · rw [simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, sessTag, monadLift_self, id_eq]
      change (simulateQ (sessLift impl)
          (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩)) >>=
            fun u => simulateQ (sessTag s) (k u))).run tbl =
        (fun z => (z.1, Function.update tbl s z.2)) <$>
          (fwd impl (.inr q) >>= fun u => simulateQ (fwd impl) (k u)).run (tbl s)
      rw [simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self, id_eq,
        sessLift_inr, sessLiftCore, fwd,
        QueryImpl.add_apply, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      refine bind_congr fun z => ?_
      have hget : Function.update tbl s z.2 s = z.2 := Function.update_self s z.2 tbl
      have hidem : ∀ w, Function.update (Function.update tbl s z.2) s w = Function.update tbl s w :=
        fun w => by simp
      let u : (unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Range (.inr q) := z.1
      erw [ih u (Function.update tbl s z.2), hget]
      simp [hidem, u, fwd]

@[expose] def pubFsMultiImpl {Pt : Type} {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp)) :
    QueryImpl
      (unifSpec + FSMultiSpec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (StateT ((ℕ → Bool) × (ℕ → σ)) ProbComp)
  | .inl n => StateT.lift (liftM (OracleSpec.query (spec := unifSpec) n))
  | .inr ⟨s, q⟩ => StateT.mk fun (pubSt, tbl) => do
      let ((ans, ended'), h') ←
        (simulateQ (fwd impl)
          ((pubRedImpl
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (M := Plain ℓ)
            (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
            (.inr q)).run (pubSt s))).run (tbl s)
      return (ans, (Function.update pubSt s ended', Function.update tbl s h'))

theorem simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl
    {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (oa : OracleComp (unifSpec + FSMultiSpec
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) Bool)
    (tbl : ℕ → σ) :
    Prod.fst <$> (simulateQ (sessLift impl) (multiSessPubToAD protoSignalCodec oa)).run tbl =
      Prod.fst <$> (simulateQ (pubFsMultiImpl impl) oa).run (fun _ => false, tbl) := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  let redStep : QueryImpl
      (unifSpec + FSMultiSpec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (StateT (ℕ → Bool) (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))) :=
    fun x => match x with
      | .inl n => StateT.lift (liftM (OracleSpec.query
          (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n)))
      | .inr ⟨s, q⟩ => StateT.mk fun st => do
          let r ← simulateQ (sessTag s)
            ((pubRedImpl
              (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
              (.inr q)).run (st s))
          return (r.1, Function.update st s r.2)
  change (fun a => a.1.1) <$>
      (simulateQ (sessLift impl) ((simulateQ redStep oa).run (fun _ => false))).run tbl =
    Prod.fst <$> (simulateQ (pubFsMultiImpl impl) oa).run (fun _ => false, tbl)
  suffices hgen : ∀ (pubSt : ℕ → Bool) (tbl : ℕ → σ),
      (fun a => a.1.1) <$>
        (simulateQ (sessLift impl) ((simulateQ redStep oa).run pubSt)).run tbl =
      Prod.fst <$> (simulateQ (pubFsMultiImpl impl) oa).run (pubSt, tbl) from
    hgen (fun _ => false) tbl
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro pubSt tbl; simp
  | query_bind x k ih =>
    intro pubSt tbl
    rcases x with n | ⟨s, q⟩
    · rw [simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, redStep, pubFsMultiImpl,
        monadLift_self, StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, id_eq]
      rw [simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self,
        sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_bind, StateT.run_monadLift,
        bind_assoc, pure_bind, map_bind, id_eq]
      exact bind_congr fun u => ih u pubSt tbl
    · rw [simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, redStep, pubFsMultiImpl,
        monadLift_self, StateT.run_bind, StateT.run_mk,
        simulateQ_bind,
        bind_assoc, pure_bind, map_bind, simulateQ_sessLift_sessTag, bind_map_left, id_eq]
      exact bind_congr fun z => ih z.1.1 (Function.update pubSt s z.1.2) (Function.update tbl s z.2)

theorem pubFsMultiImpl_inl_run {Pt : Type} {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (n : ℕ) (s : (ℕ → Bool) × (ℕ → σ)) :
    (pubFsMultiImpl impl (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)) := by
  simp [pubFsMultiImpl]

theorem pubFsMultiImpl_transmit_run {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (tbl : ℕ → HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (ℕ × LibsignalCiphertextWithSalt32)}
    {s' : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) (hp 0 0 la) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run (tbl sIdx) =
      pure (u, s')) :
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
      (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (h, pm)))))⟩)).run (fun _ => false, tbl) =
    pure (u, (fun _ => false, Function.update tbl sIdx s')) := by
  simp only [pubFsMultiImpl, pubRedImpl, transmitQuery, stateT_lift_run, query_eq_liftM,
    simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind, StateT.run_pure, StateT.run_mk,
    fwd, QueryImpl.add_apply, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith, bind_assoc, pure_bind, update_const_false]
  change (do
    let x ← (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 la) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run (tbl sIdx)
    pure (x.1, fun _ => false, Function.update tbl sIdx x.2)) = _
  rw [hstep, pure_bind]

theorem pubFsMultiImpl_corruptSender_run {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sIdx : ℕ)
    (tbl : ℕ → HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (RatchetSenderState (BitVec 256))}
    {s' : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : ((corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
          (Plain ℓ) LibsignalCiphertextWithSalt32) ProbComp _)).run (tbl sIdx) = pure (u, s')) :
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false))
      (.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩)).run (fun _ => false, tbl) =
    pure (u, (fun _ => false, Function.update tbl sIdx s')) := by
  simp only [pubFsMultiImpl, pubRedImpl, corruptSenderQuery, stateT_lift_run, query_eq_liftM,
    simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind, StateT.run_pure, StateT.run_mk,
    fwd, QueryImpl.add_apply, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith, bind_assoc, pure_bind, update_const_false]
  change (do
    let x ← ((corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
          (Plain ℓ) LibsignalCiphertextWithSalt32) ProbComp _)).run (tbl sIdx)
    pure (x.1, fun _ => false, Function.update tbl sIdx x.2)) = _
  rw [hstep, pure_bind]

theorem pubFsMultiImpl_deliver_some_run {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec ct = some p)
    (tbl : ℕ → HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (ReceiveResult (Plain ℓ))}
    {s' : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run (tbl sIdx) = pure (u, s')) :
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
      (.inr ⟨sIdx, .inl (.inr (h, (i, ct)))⟩)).run (fun _ => false, tbl) =
    pure (u.map (withPub p),
      (fun _ => false, Function.update tbl sIdx s')) := by
  simp only [pubFsMultiImpl, pubRedImpl, hp_pub, deliverQuery, stateT_lift_run, query_eq_liftM,
    simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind, StateT.run_pure, StateT.run_mk,
    fwd, QueryImpl.add_apply, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith, bind_assoc, pure_bind, update_const_false]
  change (do
    let x ← (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run (tbl sIdx)
    pure (Option.map (withPub p) x.1, fun _ => false, Function.update tbl sIdx x.2)) = _
  rw [hstep, pure_bind]

theorem pubFsMultiImpl_inject_none_run {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (hp_none : lPubOf protoSignalCodec ct = none)
    (tbl : ℕ → HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32) :
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
      (.inr ⟨sIdx, .inr (h, (i, ct))⟩)).run (fun _ => false, tbl) =
    pure (some .rejected, (fun _ => false, tbl)) := by
  simp [pubFsMultiImpl, pubRedImpl, hp_none, Function.update_eq_self]

theorem pubFsMultiImpl_inject_some_run {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec ct = some p)
    (tbl : ℕ → HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (ReceiveResult (Plain ℓ))}
    {s' : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run (tbl sIdx) = pure (u, s')) :
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
      (.inr ⟨sIdx, .inr (h, (i, ct))⟩)).run (fun _ => false, tbl) =
    pure (u.map (withPub p),
      (fun _ => false, Function.update tbl sIdx s')) := by
  simp only [pubFsMultiImpl, pubRedImpl, hp_pub, injectQuery, stateT_lift_run, query_eq_liftM,
    simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind, StateT.run_pure, StateT.run_mk,
    fwd, QueryImpl.add_apply, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith, bind_assoc, pure_bind, update_const_false]
  change (do
    let x ← (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run (tbl sIdx)
    pure (Option.map (withPub p) x.1, fun _ => false, Function.update tbl sIdx x.2)) = _
  rw [hstep, pure_bind]

theorem injectL_lookahead_some_accepted {MK CK AD M C : Type}
    [SampleableType MK] [SampleableType CK] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    {k : CK}
    {stR : _root_.CryptoGames.FSAEAD.State (RatchetSenderState CK)
      (RatchetReceiverState CK MK) AD M (ℕ × C)}
    {sM sL : HSt CK MK AD M C}
    (hsync : SyncRML ae G k stR sM sL)
    (a : AD) (i : ℕ) (e : C) (msg : M)
    (hend : sM.1.ended = false)
    (hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false)
    (hcont : i ∉ sM.1.skipped)
    (hout : ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1))
    (_hlt : sM.1.lastSentIdx < i)
    (hdec : ae.dec (_root_.CryptoGames.FSAEAD.Thm5.Ends.keyAt G k (i - 1)) (i, a) e = some msg) :
    ∃ sL',
      (injectH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp))
        (a, i, e)).run sL = pure (some (.accepted i (some msg)), sL') := by
  have hsL1 : sL.1 = { sM.1 with keys := sL.1.keys } := hsync.sL_eq
  have hendL : sL.1.ended = false := by rw [hsL1]; exact hend
  have hanyL : (sL.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
    rw [hsL1]; exact hany
  have hcontL : i ∉ sL.1.skipped := by rw [hsL1]; exact hcont
  have houtL : ¬ (i ≤ sL.1.receiverIdx ∨ maxSkip < i - sL.1.receiverIdx - 1) := by
    rw [hsL1]; exact hout
  have hlarejL : ¬ ((true = false ∧ sL.1.lastSentIdx < i) ∧ sL.1.isCompromised i = false) := by simp
  let sL₁ : HSt CK MK AD M C :=
    ({ sL.1 with keys := _root_.CryptoGames.FSAEAD.Thm5.Ends.keysUpTo G k (max sL.1.keys.length i) },
      .seed (_root_.CryptoGames.FSAEAD.Thm5.chainFrom G 0 k (max sL.1.keys.length i)))
  let forged := !sL.1.isCompromised i
  let lfNow := forged && decide (sL.1.lastSentIdx < i)
  let sL' : HSt CK MK AD M C := (HState.removeFromTransit
    { sL₁.1 with
      skipped := _root_.CryptoGames.FSAEAD.Thm5.newSkipped sL.1.receiverIdx i ++ sL.1.skipped
      receiverIdx := max sL.1.receiverIdx i
      win := sL.1.win || forged
      lf := sL.1.lf || lfNow
      ended := sL.1.ended || lfNow } i, sL₁.2)
  refine ⟨sL', ?_⟩
  unfold injectH
  simp only [StateT.run_bind, _root_.CryptoGames.FSAEAD.Thm5.getH_run, pure_bind,
    hendL, hanyL, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    _root_.CryptoGames.FSAEAD.Thm5.Ends.receiveH_none_run_of_in_window ae G maxSkip true
      hsync.wf_seedL a e hcontL houtL hlarejL,
    hdec, _root_.CryptoGames.FSAEAD.Thm5.modifyH_run, StateT.run_pure, sL', sL₁, forged, lfNow]
  simp [hp]



end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
