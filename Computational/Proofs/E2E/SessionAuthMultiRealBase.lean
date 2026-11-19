/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

/-!
# Real Multi-Session Hop-3 Coupling (`localAuthDF* ≤ multiSessRealWinProb`)

Couples the post-PRNG local games of the Stage-2 `DeliverForgePaper` families
(`localAuthDFShiftedDir2Paper`, `localAuthDFShiftedPaper`, `AuthL11.localAuthDFPaper`, and
`localAuthDFPaperBucketRaw`) to the two-mode (`la = false` + `la = true`) real multi-session
`FSMultiSpec` experiments (`multiSessRealWinProb`).-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiReal

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket
  localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)

/-- Single-session real (`b_fs = false`) initial state sampler for `fs : FSAEADScheme`. -/
@[expose] def fsMultiRealInit {K SS RS AD M E : Type} [SampleableType K]
    (fs : FSAEADScheme K SS RS AD M E) :
    ProbComp (_root_.CryptoGames.FSAEAD.State SS RS AD M E) := do
  let k ← ($ᵗ K : ProbComp K)
  return _root_.CryptoGames.FSAEAD.initState fs k false

theorem fsMultiRealInit_b_false {K SS RS AD M E : Type} [SampleableType K]
    (fs : FSAEADScheme K SS RS AD M E)
    {st : _root_.CryptoGames.FSAEAD.State SS RS AD M E} (hst : st ∈ support (fsMultiRealInit fs)) :
    st.b = false := by
  unfold fsMultiRealInit at hst
  rw [mem_support_bind_iff] at hst
  obtain ⟨k, _, hk⟩ := hst
  simp only [support_pure, Set.mem_singleton_iff] at hk
  subst hk
  rfl

/-- Multi-session real (`Thm5.hp 0 0 la`) execution of a multi-session ratchet adversary `Adv`. -/
@[expose] def multiFsRealRun {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (CryptoVerification.E2E.Signed.SessionFS.fsSpec CK MK AD M C)) Bool) :
    ProbComp Bool :=
  Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run (fun _ => none)

/-- Post-PRNG `(tL, par)`-bucket local game under `corrAllowedPaper` (`engRunDFPaperBucket`)
evaluated with `authOutBucket` (without `&& (s.tL == tL)`). -/
@[expose] def localAuthDFPaperBucketRaw
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) =>
      match st.2 with
      | none => false
      | some tWin => !st.1.abort && st.1.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin st.1.g

def bucketRawOut {VP M C HS : Type} (Δ : ℕ) (tL : Option ℕ) :
    Option (Bool × (_root_.CryptoGames.SM.Engine.EState VP M C HS × Option ℕ)) → Bool
  | none => false
  | some (_, st) =>
    match st.2 with
    | none => false
    | some tWin => !st.1.abort && st.1.g.win && authLosingConditionsAvoided Δ tL tWin st.1.g

theorem localAuthDFPaperBucketRaw_eq_map
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    localAuthDFPaperBucketRaw cka prng fs lam Δcka qep tL par A =
      bucketRawOut (2 + Δcka) tL <$>
        simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
            (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A) := by
  unfold localAuthDFPaperBucketRaw bucketRawOut
  rw [map_eq_bind_pure_comp]
  congr 1; funext r; rcases r with _ | ⟨_, _⟩ <;> rfl

/-- One-sided 3-way authenticity coupling inequality `𝒟[cLoc] {true} ≤ 𝒟[cM] {true} + 𝒟[cL] {true}`. -/
def LeAdd (cLoc cM cL : ProbComp Bool) : Prop :=
  𝒟[cLoc] {true} ≤ 𝒟[cM] {true} + 𝒟[cL] {true}

theorem leAdd_of_lhs_zero {cLoc cM cL : ProbComp Bool}
    (h0 : 𝒟[cLoc] {true} = 0) : LeAdd cLoc cM cL := by
  unfold LeAdd
  rw [h0]
  simp

theorem leAdd_of_le_main {cLoc cM cL : ProbComp Bool}
    (hle : 𝒟[cLoc] {true} ≤ 𝒟[cM] {true}) : LeAdd cLoc cM cL := by
  unfold LeAdd
  exact hle.trans le_self_add

theorem leAdd_of_la_one {cLoc cM cL : ProbComp Bool}
    (h1 : 𝒟[cL] {true} = 1) : LeAdd cLoc cM cL := by
  unfold LeAdd
  rw [h1]
  have hle1 : 𝒟[cLoc] {true} ≤ 1 := by
    calc
      𝒟[cLoc] {true} ≤ 𝒟[cLoc] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  exact hle1.trans le_add_self

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

theorem leAdd_bind_dummy_loc {α : Type} (oa : ProbComp α)
    {cLoc : ProbComp Bool} {fM fL : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeAdd cLoc (fM a) (fL a)) :
    LeAdd cLoc (oa >>= fM) (oa >>= fL) := by
  have hL := leAdd_bind oa (fLoc := fun _ => cLoc) h
  unfold LeAdd at hL ⊢
  rwa [evalDist_bind_const_true oa cLoc] at hL

def fsSeedInit {CK MK AD M C : Type} [SampleableType CK] :
    ProbComp (_root_.CryptoGames.FSAEAD.Thm5.HSt CK MK AD M C) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ CK : ProbComp CK)
  return _root_.CryptoGames.FSAEAD.Thm5.hInit b (.seed k)

theorem fsSeedInit_bind_run_evalDist_eq {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (la : Bool)
    (B : _root_.CryptoGames.FSAEAD.RatchetAdversary CK MK AD M C) :
    𝒟[fsSeedInit >>= fun s =>
        Prod.fst <$> (simulateQ (_root_.CryptoVerification.E2E.Signed.SessionRouter.fwd
          (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) B).run s] =
      𝒟[fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (_root_.CryptoVerification.E2E.Signed.SessionRouter.fwd
          (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) B).run s] := by
  unfold fsSeedInit fsInit
  simp only [bind_assoc, pure_bind, _root_.CryptoVerification.E2E.Signed.SessionFS.fwd_fsImpl]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  let P := _root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la
  let D := _root_.CryptoGames.FSAEAD.Thm5.DG G
  let fill := _root_.CryptoGames.FSAEAD.Thm5.seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hI := _root_.CryptoGames.FSAEAD.Thm5.seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hK : ∀ h h' : _root_.CryptoGames.FSAEAD.Thm5.HState CK MK AD M C,
      h.keys.length = h'.keys.length → fill h = fill h' := by
    intro h h' hl; funext sl; cases sl <;> simp [fill, _root_.CryptoGames.FSAEAD.Thm5.seedFill, hl]
  have hGen := _root_.CryptoGames.FSAEAD.Thm5.comm_genStep_seed (AD := AD) (M := M) (C := C) G P 0 le_rfl
  have hRev := _root_.CryptoGames.FSAEAD.Thm5.comm_reveal_seed (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hc := _root_.CryptoGames.Lazy.Comm.simulateQ hI
    (_root_.CryptoGames.FSAEAD.Thm5.comm_impl ideal ae G maxSkip P D hI hK hGen hRev) B
    (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown)
  have hdeq : _root_.CryptoGames.Lazy.DEq
      ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
        (_root_.CryptoGames.Lazy.fillSt fill (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown) >>=
          (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxSkip P D
            (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp))) B).run))
      ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
        (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxSkip P D none) B).run
          (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown)) :=
    (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _).symm.trans
      ((_root_.CryptoGames.Lazy.DEq.map hc _).trans
        (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
          Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _))
  have h0 : _root_.CryptoGames.Lazy.fillSt fill
      (_root_.CryptoGames.FSAEAD.Thm5.hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown) =
      (($ᵗ CK) >>= fun k => pure (_root_.CryptoGames.FSAEAD.Thm5.hInit b (.seed k))) := by
    simp [fill, _root_.CryptoGames.Lazy.fillSt, _root_.CryptoGames.FSAEAD.Thm5.seedFill,
      _root_.CryptoGames.FSAEAD.Thm5.hInit, map_eq_bind_pure_comp]
  have heq := _root_.CryptoGames.Lazy.DEq.evalDist_eq hdeq
  rw [h0] at heq
  simpa only [Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, P, D] using heq

theorem multiFsSeeded_le_real {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip M_sess : ℕ) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (CryptoVerification.E2E.Signed.SessionFS.fsSpec CK MK AD M C)) Bool)
    (hoff : Adv.IsQueryBoundP (fun t =>
      _root_.CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess t = true) 0) :
    𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} ≤
      𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} := by
  have hbd := _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_lazy_boolDist_le
    fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    M_sess Adv hoff
  have hsum0 : (∑ k ∈ Finset.range M_sess,
      𝒟[fsSeedInit >>= fun s => Prod.fst <$> (simulateQ (_root_.CryptoVerification.E2E.Signed.SessionRouter.fwd
          (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
          (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
            (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
            Adv (fun _ => none) (fun _ => none) k)).run s].boolDist
        𝒟[fsInit >>= fun s => Prod.fst <$> (simulateQ (_root_.CryptoVerification.E2E.Signed.SessionRouter.fwd
          (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
          (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
            (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
            Adv (fun _ => none) (fun _ => none) k)).run s]) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [fsSeedInit_bind_run_evalDist_eq]
    exact MeasureTheory.Measure.boolDist_self _
  rw [hsum0] at hbd
  calc
    _ ≤ 𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
          (fun _ => none)] {true} +
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
          (fun _ => none)].boolDist
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
          (fun _ => none)] := MeasureTheory.Measure.apply_true_le_add_boolDist _ _
    _ ≤ _ + 0 := add_le_add le_rfl hbd
    _ = _ := add_zero _

section EagerSessionInit

open _root_.CryptoVerification.E2E.Signed.SessionRouter

theorem hybSess_same_eq_sessLift {ι σ : Type} {spec : OracleSpec ι}
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

theorem sessLift_lazyInit_step_evalDist {ι σ : Type} {spec : OracleSpec ι}
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

def toOptTbl {σ : Type} (m : ℕ) (tbl : ℕ → σ) : ℕ → Option σ :=
  fun i => if i < m then some (tbl i) else none

theorem sessLift_lazyInit_sampleVec_evalDist {ι σ : Type} {spec : OracleSpec ι}
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
            -- rewrite inner bind via evalDist_bind_congr
            rw [← evalDist_bind_congr (sampleVec init dflt m) _ _ hstep]
      _ = _ := sessLift_lazyInit_sampleVec_evalDist init dflt impl M m

theorem sessLift_lazyInit_eq_of_offRange {ι σ : Type} {spec : OracleSpec ι}
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

theorem sampleSeedInit_split_deq {CK MK AD M C : Type} [SampleableType CK]
    (k0 : CK) :
    ∀ m : ℕ,
      _root_.CryptoGames.Lazy.DEq
        (sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
          (_root_.CryptoGames.FSAEAD.Thm5.hInit false (.seed k0)) m)
        (sampleVec ($ᵗ CK : ProbComp CK) k0 m >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false m >>= fun bs =>
            pure (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))
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
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip M_sess : ℕ) (k0 : CK) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (CryptoVerification.E2E.Signed.SessionFS.fsSpec CK MK AD M C)) Bool)
    (hoff : Adv.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0) :
    𝒟[sampleVec ($ᵗ CK : ProbComp CK) k0 M_sess >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift
            (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) Adv).run
            (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i)))] {true} ≤
      𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
        (fun _ => none)] {true} := by
  have heq1 :
      𝒟[sampleVec ($ᵗ CK : ProbComp CK) k0 M_sess >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
            Prod.fst <$> (simulateQ (sessLift
              (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) Adv).run
              (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i)))] =
        𝒟[sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
            (_root_.CryptoGames.FSAEAD.Thm5.hInit false (.seed k0)) M_sess >>= fun tbl =>
          Prod.fst <$> (simulateQ (sessLift
            (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) Adv).run tbl] := by
    have hdeq1 := _root_.CryptoGames.Lazy.DEq.bind_left
      (sampleSeedInit_split_deq (MK := MK) (AD := AD) (M := M) (C := C) k0 M_sess).symm
      (fun tbl => Prod.fst <$> (simulateQ (sessLift
        (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) Adv).run tbl)
    simp only [bind_assoc, pure_bind] at hdeq1
    exact hdeq1.evalDist_eq
  have heq2 :
      𝒟[sampleVec (fsSeedInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C))
          (_root_.CryptoGames.FSAEAD.Thm5.hInit false (.seed k0)) M_sess >>= fun tbl =>
        Prod.fst <$> (simulateQ (sessLift
          (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) Adv).run tbl] =
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsSeedInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run
          (fun _ => none)] := by
    rw [← sessLift_lazyInit_sampleVec_evalDist fsSeedInit
      (_root_.CryptoGames.FSAEAD.Thm5.hInit false (.seed k0))
      (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)) Adv M_sess]
    refine evalDist_bind_congr _ _ _ fun tbl => congrArg evalDist ?_
    exact (sessLift_lazyInit_eq_of_offRange fsSeedInit
      (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)) M_sess Adv hoff
      tbl (toOptTbl M_sess tbl) fun i hi => by simp [toOptTbl, hi]).symm
  rw [heq1, heq2]
  exact multiFsSeeded_le_real ideal ae G maxSkip M_sess la Adv hoff

/-- Generic outer assembly (`G1`) bounding `𝒟[LOCAL] {true}` by the `la = false` + `la = true`
`multiSessRealWinProb` sum from eager key reduction (`hH1`), off-range `0`-query bound (`hH3`),
and per-`(ks, bs)` `LeAdd` coupling (`hK`). -/
theorem le_multiSessRealWinProb_of_perKey {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Adv : Bool → Computational.Proofs.E2E.SessionAuthBridge.MultiSessFsAdv Pt ℓ)
    (LOCAL : ProbComp Bool) (LOCALks : (ℕ → BitVec 256) → ProbComp Bool)
    (M : ℕ) (k0 : BitVec 256)
    (hH1 : 𝒟[LOCAL] {true} ≤
      𝒟[sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= LOCALks] {true})
    (hH3 : ∀ la, (Adv la).IsQueryBoundP (fun t => sessOffRange M t = true) 0)
    (hK : ∀ (ks : ℕ → BitVec 256) (bs : ℕ → Bool), LeAdd (LOCALks ks)
      (Prod.fst <$> (simulateQ (sessLift (fsImpl
          (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
          maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
          (Adv false)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))
      (Prod.fst <$> (simulateQ (sessLift (fsImpl
          (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
          maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
          (Adv true)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))) :
    𝒟[LOCAL] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  refine hH1.trans ?_
  have hStep : LeAdd
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= LOCALks)
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift (fsImpl
            (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
            maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
            (Adv false)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift (fsImpl
            (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
            maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
            (Adv true)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i)))) :=
    leAdd_bind _ fun ks _ =>
      leAdd_bind_dummy_loc _ fun bs _ => hK ks bs
  exact hStep.trans (add_le_add
    (multiFsEager_le_real
      (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
      maxForwardJumps M k0 false (Adv false) (hH3 false))
    (multiFsEager_le_real
      (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
      maxForwardJumps M k0 true (Adv true) (hH3 true)))

end EagerSessionInit

end

end Computational.Proofs.E2E.SessionAuthMultiReal

