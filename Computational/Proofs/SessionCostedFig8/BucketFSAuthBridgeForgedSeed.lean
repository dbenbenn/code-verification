/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.ReductionDsl.SM.Engine

/-!
# Slot-Parameterized Local Forged-Header `(tL, par)`-Bucket Game (`localAuthBucketForgedSlot`)

Mirrors `BucketFSAuthBridgeHopSlot` for the forged-header (`gMain = false`) branch:
1. Halted (`abort || win`) and lookahead-win (`lfWin`) exit bounds `forged_halted_leOne` and
   `forged_lfWin_aborted_eq_one`.
2. Slot-parameterized local game `localAuthBucketForgedSlot` routing active `(tL, par)`-bucket
   `fTable` key draws (`1 ≤ t0 ≤ qep + 1`, `!postLeak`, `validGuessBucketParAuth`) through
   `multiSessSpec (keySlotSpec K)`.
3. Off-range `0`-query bound `localAuthBucketForgedSlot_offRange` and lazy-to-eager equivalence
   `localAuthBucketForgedHdrPar_eq_eager_ks`.
4. Halted / post-leak equivalence `forgedSlot_fixed_eq_localGen_of_halted_or_postLeak` back to
   `implLocalBucketAuthGen` under `lImpl`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (PRFPRNG CKAScheme FSAEADScheme Party)
open _root_.CryptoGames.SM (GameState Record RecvResult ltOpt maxOpt canon
  lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header PartyState mkParties realParty
  SchemeAdversary healEpoch sampleT FSMultiSpec)
open _root_.CryptoGames.SM.Engine (Hooks HM EState VP Ctx
  liftH run_liftH_bind abortE commitE
  vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind deliverE injectE)
open _root_.CryptoGames.SM.Construction.AuthL11 (lImpl nilSpec)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift sessLiftCore
  sessLift_inl sessLift_inr lazyInit lazyInit_run_none' sessOffRange multiSessSpec)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg
  LocalBucketAuthState LocalBucketAuthEState lookupLocalBucketAuthF rootLocalBucketAuth
  hooksLocalBucketAuth hooksLocalBucketAuthForgedHdr initLocalBucketAuth isHonestHdrLocalBucket
  implLocalBucketAuthGen localAuthBucketForgedHdrPar)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  validGuessBucketParAuth implFSMultiBucketAuth isHonestHdrMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (LeOne leOne_bind
  sampleVec keySlotSpec keySlotImpl keySlot_lazy_eq_eager)

/-! ### 1. Halted (`abort || win`) and Lookahead-Win (`lfWin`) Exit Lemmas -/

private theorem authLosingConditionsAvoided_congr' {St₁ St₂ Msg C : Type} (Δ : ℕ) (tLStar : Option ℕ) (tStar : ℕ) (g₁ : GameState St₁ Msg C) (g₂ : GameState St₂ Msg C) (hleaks : g₁.leaks = g₂.leaks) (hcorrs : g₁.corrs = g₂.corrs) : authLosingConditionsAvoided Δ tLStar tStar g₁ = authLosingConditionsAvoided Δ tLStar tStar g₂ := by
  simp only [authLosingConditionsAvoided, canon, hleaks, hcorrs]

@[expose] def forgedOut {St Msg C HS : Type} (Δ : ℕ) (tL : Option ℕ) (par : Bool)
    (es : EState St Msg C HS) (winEp : Option ℕ) : Bool :=
  match winEp with
  | none => false
  | some tWin =>
    !es.abort && es.g.win &&
      authLosingConditionsAvoided Δ tL tWin es.g &&
      (decide (Party.senderOf tWin == Party.A) == par)

theorem forged_halted_leOne
    {Γ T Sig SS RS M E CCoins K I σM : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hkLoc : Hooks nilSpec (LocalBucketAuthState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (hkM : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T Sig K I E)
      Γ T Sig SS RS M E CCoins Γ Sig (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool)
    (implM : QueryImpl (unifSpec + FSMultiSpec SS RS T M E) (StateT σM ProbComp))
    (hImplM_inl : ∀ (n : ℕ) (s : σM), (implM (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esLoc : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
    (esM : EState (VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T Sig K I E))
    (winEp : Option ℕ) (sM : σM) (hhalt : (esLoc.abort || esLoc.g.win) = true)
    (habort : esM.abort = esLoc.abort) (hwin : esM.g.win = esLoc.g.win)
    (hleaks : esM.g.leaks = esLoc.g.leaks) (hcorrs : esM.g.corrs = esLoc.g.corrs) :
    LeOne
      (simulateQ lImpl do
        let (_, es, we) ← (simulateQ (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true) oa).run
          (esLoc, winEp)
        return forgedOut (2 + Δcka) tL par es we)
      (Prod.fst <$> (simulateQ implM do
        let (_, es, we) ← (simulateQ (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL) oa).run
          (esM, winEp)
        return forgedOut (2 + Δcka) tL par es we).run sM) := by
  have hhaltM : (esM.abort || esM.g.win) = true := by rw [habort, hwin]; exact hhalt
  induction oa using OracleComp.inductionOn generalizing sM with
  | pure _ =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_pure, LeOne]; have hout : forgedOut (2 + Δcka) tL par esLoc winEp =
        forgedOut (2 + Δcka) tL par esM winEp := by
      cases winEp with
      | none => rfl
      | some tWin =>
        dsimp only [forgedOut]; rw [habort, hwin, authLosingConditionsAvoided_congr' (2 + Δcka) tL tWin esLoc.g esM.g hleaks.symm hcorrs.symm]
    rw [hout]
  | query_bind q k ih =>
    have hhalt' := (Bool.or_eq_true _ _).mp hhalt; have hhaltM' := (Bool.or_eq_true _ _).mp hhaltM
    rw [simulateQ_query_bind, simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, simulateQ_bind, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inl n)).run (esLoc, winEp) =
          (liftM (OracleSpec.query (spec := unifSpec + nilSpec) (.inl n)) >>=
            fun u => pure (u, (esLoc, winEp))) := by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inl]
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inl n)).run (esM, winEp) =
          (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)) >>=
            fun u => pure (u, (esM, winEp))) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
      rw [hL, hM, simulateQ_query_bind, simulateQ_query_bind]; simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, simulateQ_pure, StateT.run_bind, StateT.run_pure, hImplM_inl, bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ => ih u sM
    · rw [show (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hhalt'], show (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esM, winEp) = pure (none, (esM, winEp)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hhaltM']]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · rw [show (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl], show (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esM, winEp) = pure (none, (esM, winEp)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · rw [show (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inr (.inl (.inl (.inr (P, c)))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hhalt'], show (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inr (.inl (.inl (.inr (P, c)))))).run (esM, winEp) = pure (none, (esM, winEp)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hhaltM']]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · rw [show (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inr (.inl (.inr (P, c))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hhalt'], show (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inr (.inl (.inr (P, c))))).run (esM, winEp) = pure (none, (esM, winEp)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hhaltM']]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · rw [show (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL true (.inr (.inr P))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, hhalt'], show (implFSMultiBucketAuth hkM Δcka qep maxSkip false tL (.inr (.inr P))).run (esM, winEp) = pure (none, (esM, winEp)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, hhaltM']]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM

theorem forged_lfWin_aborted_eq_one
    {Γ T Sig SS RS M E CCoins K I σL : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hkL : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T Sig K I E)
      Γ T Sig SS RS M E CCoins Γ Sig (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ)
    (implL : QueryImpl (unifSpec + FSMultiSpec SS RS T M E) (StateT σL ProbComp))
    (hImplL_inl : ∀ (n : ℕ) (s : σL), (implL (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esL : EState (VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T Sig K I E))
    (winEpL : Option ℕ) (sL : σL) (habort : esL.abort = true) (hlf : esL.h.lfWin = true) :
    𝒟[Prod.fst <$> (simulateQ implL do
        let (_, es, _) ← (simulateQ (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL) oa).run
          (esL, winEpL)
        return es.h.lfWin).run sL] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing winEpL sL with
  | pure _ => simp [simulateQ_pure, StateT.run_pure, hlf]
  | query_bind q k ih =>
    rw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL (.inl n)).run (esL, winEpL) =
          (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)) >>=
            fun u => pure (u, (esL, winEpL))) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
      rw [hStep, simulateQ_query_bind]; simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, simulateQ_pure, StateT.run_bind, StateT.run_pure, hImplL_inl, bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]; trans ∫⁻ (_ : Fin (n + 1)), (1 : ℝ≥0∞)
          ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => ih u winEpL sL
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    · rw [show (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esL, winEpL) = pure (none, (esL, winEpL)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, habort]]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · rw [show (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esL, winEpL) = pure (none, (esL, winEpL)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · rw [show (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL (.inr (.inl (.inl (.inr (P, c)))))).run (esL, winEpL) = pure (none, (esL, winEpL)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, habort]]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · rcases (⟨if !esL.g.win && esL.g.win &&
            (decide (c.1.1 = (esL.g.st P).tcur + 1) && !isHonestHdrMultiBucket esL.h c.1)
          then some c.1.1 else winEpL, by
          simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, habort]⟩ :
          ∃ we', (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL
            (.inr (.inl (.inr (P, c))))).run (esL, winEpL) = pure (none, (esL, we'))) with ⟨we', hStep⟩
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none we' sL
    · rw [show (implFSMultiBucketAuth hkL Δcka qep maxSkip false tL (.inr (.inr P))).run (esL, winEpL) = pure (none, (esL, winEpL)) by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, habort]]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL

/-! ### 2. Definitions (`localAuthBucketForgedSlot` & `keySlotFixedImpl`) -/

structure LocalForgedSlotState (T Sig K I : Type) where
  loc : LocalBucketAuthState T Sig K I := {}
  sessions : ℕ → List I := fun _ => []
  usedSlot : ℕ → Bool := fun _ => false

abbrev ForgedSlotHM (T Sig K I : Type) (α : Type) :=
  StateT (LocalForgedSlotState T Sig K I) (OracleComp (unifSpec + multiSessSpec (keySlotSpec K))) α

@[expose] def sampleOrSlotF {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) : ForgedSlotHM T Sig K I K := do
  let st ← get
  if useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx then
    modify fun s => { s with usedSlot := Function.update s.usedSlot sIdx true }
    StateT.lift (query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩))
  else
    StateT.lift (sampleT K)

private theorem sampleOrSlotF_pos_run {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) (st : LocalForgedSlotState T Sig K I)
    (hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true) :
    (sampleOrSlotF M_sess useSlot sIdx).run st =
      ((query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) >>=
        fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
          Pure.pure ((k : K), { st with usedSlot := Function.update st.usedSlot sIdx true })) := by
  simp only [sampleOrSlotF, hc, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]; rfl

@[expose] def lookupLocalForgedSlotF {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (sIdxFn : ℕ → ℕ → ℕ) (M_sess : ℕ) (reg : Bool) (t0 : ℕ) (ik : I) :
    ForgedSlotHM T Sig K I K := do
  let st ← get
  let tb0 := st.loc.fTable t0
  match tb0.lookup ik with
  | some k =>
    if reg && !(st.sessions t0).contains ik then
      modify fun s => { s with sessions := Function.update s.sessions t0 (s.sessions t0 ++ [ik]) }
    return k
  | none =>
    let idx := (st.sessions t0).length
    let k ← sampleOrSlotF M_sess reg (sIdxFn t0 idx)
    modify fun s =>
      { s with
        loc := { s.loc with fTable := Function.update s.loc.fTable t0 ((ik, k) :: tb0) }
        sessions := if reg then Function.update s.sessions t0 (s.sessions t0 ++ [ik]) else s.sessions }
    return k

@[expose] def rootLocalForgedSlot {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig) :
    ForgedSlotHM T Sig K I (Sig × K) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  let reg := decide (1 ≤ t0) && !pl && !(decide (qep + 1 < t0)) &&
    validGuessBucketParAuth Δcka tL par t0
  if pl || qep + 1 < t0 then
    return (pIk.1, pIk.2)
  else if tL.isSome && t0 = tH then
    let ir ← StateT.lift (sampleT I)
    let kSample ← sampleOrSlotF M_sess reg (sIdxFn t0 0)
    return ((prng.up σ0 ir).1, kSample)
  else if !(t0 < tH) then
    let kLookup ← lookupLocalForgedSlotF sIdxFn M_sess reg t0 ik0
    return (pIk.1, kLookup)
  else
    return (pIk.1, pIk.2)

@[expose] def hooksLocalForgedSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) :
    Hooks (multiSessSpec (keySlotSpec K)) (LocalForgedSlotState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let pl := postLeak tL ctx
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    let (σ', kVal) ← rootLocalForgedSlot prng sIdxFn Δcka qep M_sess tL par t0 pl c.2.2 σ0
    modify fun s =>
      { s with loc := { s.loc with cache := Function.update s.loc.cache t0 (some (c.2.1, σ', kVal)) } }
    return some (c.1, c.2.1, σ', fs.initSender kVal)
  startRecv ctx _ t0 γ0 σ0 tn0 := do
    let tH := healEpoch tL
    let pl := postLeak tL ctx
    let reg := decide (1 ≤ t0) && !pl && !(decide (qep + 1 < t0)) &&
      validGuessBucketParAuth Δcka tL par t0
    let honest := match (← get).loc.cache t0 with
      | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
      | none => none
    match honest with
    | some (σc, kVal) =>
      return some (some ((cka.receive γ0 tn0).1, σc, fs.initReceiver kVal))
    | none =>
      if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 then
        if tL.isSome && t0 = tH then
          return none
        else if pl then
          let kk := cka.receive γ0 tn0
          let p := prng.up σ0 kk.2
          return some (some (kk.1, p.1, fs.initReceiver p.2))
        else if !(t0 < tH) then
          let kk := cka.receive γ0 tn0
          let kOut ← lookupLocalForgedSlotF sIdxFn M_sess reg t0 kk.2
          return some (some (kk.1, (prng.up σ0 kk.2).1, fs.initReceiver kOut))
        else
          return some none
      else
        return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal ctx _ vp :=
    if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
      pure none
    else
      pure (some (realParty vp vp.γ vp.root vp.vS vp.vR))

@[expose] def initLocalForgedSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) :
    ForgedSlotHM T Sig K I (Option (VP Γ T Sig SS RS × VP Γ T Sig SS RS)) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ0, k0) ← rootLocalForgedSlot prng sIdxFn Δcka qep M_sess tL par 0 false lam (prng.init kr)
  return some (mkParties (cka.initA kc) (cka.initB kc) σ0
    (fs.initSender k0) (fs.initReceiver k0))

abbrev LocalForgedSlotEState (Γ T Sig SS RS M E K I : Type) :=
  EState (VP Γ T Sig SS RS) M (Header T × E) (LocalForgedSlotState T Sig K I) × Option ℕ

@[expose] def implLocalForgedSlot {Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (multiSessSpec (keySlotSpec K)) (LocalForgedSlotState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) :
    QueryImpl (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun n => StateT.lift (query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun ⟨P, m, r⟩ => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win then return none
      match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => return none
      | some s₁ =>
        let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) m none r).run es0.h)
        match res with
        | none =>
          set ({ es0 with h := h', abort := true }, winEp0)
          return none
        | some (st', ct) =>
          let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
          return some ct
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let isNewForged :=
        decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) && !isHonestHdrLocalBucket es0.h.loc x.2.1
      let winEp' := if !wasWin && es'.g.win && isNewForged then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (LocalForgedSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun P => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
      let s₁ := es0.g.afterCorr P
      let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
      match res with
      | none =>
        set ({ es0 with h := h', abort := true }, winEp0)
        return none
      | some stOut =>
        set ({ es0 with g := s₁, h := h' }, winEp0)
        return some stOut
  HAdd.hAdd i₀ (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def localAuthBucketForgedSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) Bool := do
  let (vs, h) ← (initLocalForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par).run {}
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let (_, es, winEp) ←
      (simulateQ (implLocalForgedSlot (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par)
        Δcka qep fs.maxSkip tL) A).run ({ g, h }, none)
    return forgedOut (2 + Δcka) tL par es winEp

@[expose] def keySlotFixedImplF {K : Type} (ks : ℕ → K) :
    QueryImpl (unifSpec + multiSessSpec (keySlotSpec K)) ProbComp :=
  let i₀ : QueryImpl unifSpec ProbComp := QueryImpl.ofLift unifSpec ProbComp
  let i₁ : QueryImpl (multiSessSpec (keySlotSpec K)) ProbComp := fun ⟨sIdx, _⟩ => pure (ks sIdx)
  i₀ + i₁

private theorem simulateQ_sessLift_keySlotImpl_run {K α : Type} (ks : ℕ → K) (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) : (simulateQ (sessLift (keySlotImpl K)) m).run ks = (fun a => (a, ks)) <$> simulateQ (keySlotFixedImplF ks) m := by
  induction m using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    rw [StateT.run_bind, map_bind]; rcases t with n | ⟨sIdx, u⟩
    · simp only [sessLift_inl, keySlotFixedImplF, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun x => ih x
    · cases u
      have hstep : (sessLift (keySlotImpl K) (.inr ⟨sIdx, ()⟩)).run ks = Pure.pure (ks sIdx, ks) := by
        simp only [sessLift_inr, sessLiftCore, keySlotImpl]
        change (fun r : K × K => (r.1, Function.update ks sIdx r.2)) <$> (Pure.pure (ks sIdx, ks sIdx) : ProbComp (K × K)) = _
        simp
      simp only [monadLift_self, hstep, keySlotFixedImplF, QueryImpl.add_apply_inr]; exact ih (ks sIdx)

theorem simulateQ_sessLift_keySlotImpl_fst {K α : Type} (ks : ℕ → K)
    (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) :
    Prod.fst <$> (simulateQ (sessLift (keySlotImpl K)) m).run ks =
      simulateQ (keySlotFixedImplF ks) m := by
  rw [simulateQ_sessLift_keySlotImpl_run, Functor.map_map]; simp

/-! ### 3. Off-Range `0`-Query Bound (`localAuthBucketForgedSlot_offRange`) -/
private inductive ZeroOff {K α : Type} (M_sess : ℕ) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α → Prop where
  | pure (a : α) : ZeroOff M_sess (Pure.pure a)
  | query_bind {t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain}
      {k : (unifSpec + multiSessSpec (keySlotSpec K)).Range t → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
      (ht : sessOffRange M_sess t = false) (hk : ∀ y, ZeroOff M_sess (k y)) :
      ZeroOff M_sess (liftM (OracleSpec.query t) >>= k)
private theorem ZeroOff.bind {K α β : Type} {M_sess : ℕ} {mx : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α} {f : α → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) β} (h : ZeroOff M_sess mx) (hf : ∀ a, ZeroOff M_sess (f a)) : ZeroOff M_sess (mx >>= f) := by
  induction h with
  | pure a => rw [pure_bind]; exact hf a
  | query_bind ht _ ih => rw [bind_assoc]; exact ZeroOff.query_bind ht ih
private theorem ZeroOff.query_false {K : Type} {M_sess : ℕ} (t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain) (ht : sessOffRange M_sess t = false) : ZeroOff M_sess (liftM (OracleSpec.query t) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) := by
  rw [← bind_pure (liftM (OracleSpec.query t) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _)]
  exact ZeroOff.query_bind ht fun y => ZeroOff.pure y
private theorem ZeroOff.to_isQueryBoundP {K α : Type} {M_sess : ℕ} {oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α} (h : ZeroOff M_sess oa) : oa.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0 := by
  induction h with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | query_bind ht _ ih => rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl (by simp [ht]), fun y => by simpa [ht] using ih y⟩
private theorem ZeroOff.sampleT_run {K HS α : Type} (M_sess : ℕ) [SampleableType α] (h : HS) : ZeroOff M_sess ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run h) := by
  rw [StateT.run_lift]; suffices hs : ∀ oa : ProbComp α, ZeroOff M_sess (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) from
    (hs ($ᵗ α : ProbComp α)).bind fun a => ZeroOff.pure (a, h)
  intro oa; induction oa using OracleComp.inductionOn with
  | pure a => exact ZeroOff.pure a
  | query_bind t _ ih => exact (ZeroOff.query_false (.inl t) rfl).bind ih
private theorem ZeroOff.sampleOrSlot_run {T Sig K I : Type} [SampleableType K] (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) (st : LocalForgedSlotState T Sig K I) : ZeroOff M_sess ((sampleOrSlotF M_sess useSlot sIdx).run st) := by
  by_cases hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · rw [sampleOrSlotF_pos_run M_sess useSlot sIdx st hc]
    have hoff : sessOffRange M_sess (.inr ⟨sIdx, ()⟩ : (unifSpec + multiSessSpec (keySlotSpec K)).Domain) = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; simp [sessOffRange, Nat.not_le.mpr hc.1.2]
    exact (ZeroOff.query_false _ hoff).bind fun _ => ZeroOff.pure _
  · dsimp only [sampleOrSlotF]; rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact ZeroOff.sampleT_run M_sess st
private theorem ZeroOff.lookup_run {T Sig K I : Type} [DecidableEq I] [SampleableType K] (sIdxFn : ℕ → ℕ → ℕ) (M_sess : ℕ) (reg : Bool) (t0 : ℕ) (ik : I) (st : LocalForgedSlotState T Sig K I) : ZeroOff M_sess ((lookupLocalForgedSlotF sIdxFn M_sess reg t0 ik).run st) := by
  dsimp only [lookupLocalForgedSlotF]; rw [StateT.run_bind, StateT.run_get, pure_bind]
  cases (st.loc.fTable t0).lookup ik with
  | some _ =>
    by_cases hr : (reg && !(st.sessions t0).contains ik) = true
    · simp only [hr, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]; exact ZeroOff.pure _
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact ZeroOff.pure _
  | none =>
    rw [StateT.run_bind]; refine (ZeroOff.sampleOrSlot_run M_sess _ _ st).bind fun _ => ?_
    rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact ZeroOff.pure _
private theorem ZeroOff.root_run {KR T Sig K I : Type} [DecidableEq I] [SampleableType I] [SampleableType K] (prng : PRFPRNG KR Sig I K) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig) (st : LocalForgedSlotState T Sig K I) : ZeroOff M_sess ((rootLocalForgedSlot prng sIdxFn Δcka qep M_sess tL par t0 pl ik0 σ0).run st) := by
  dsimp only [rootLocalForgedSlot]; split
  · exact ZeroOff.pure _
  · split
    · rw [StateT.run_bind]; refine (ZeroOff.sampleT_run M_sess st).bind fun p1 => ?_
      rw [StateT.run_bind]; exact (ZeroOff.sampleOrSlot_run M_sess _ _ p1.2).bind fun _ => ZeroOff.pure _
    · split
      · rw [StateT.run_bind]; exact (ZeroOff.lookup_run sIdxFn M_sess _ _ _ st).bind fun _ => ZeroOff.pure _
      · exact ZeroOff.pure _
private theorem ZeroOff.vSend_run {KC KR Γ T Sig SS RS M E CCoins K I : Type} [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS) (m : M) (pair : Option (M × M)) (r0 : Option CCoins) (st : LocalForgedSlotState T Sig K I) : ZeroOff M_sess ((vSend (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par) ctx P vp m pair r0).run st) := by
  rw [vSend_eq_bind, StateT.run_bind]
  refine (?_ : ZeroOff M_sess ((vSendStep1 _ ctx P vp r0).run st)).bind fun p => ?_
  · unfold vSendStep1; split
    · rw [StateT.run_bind]; dsimp only [hooksLocalForgedSlot]
      refine (?_ : ZeroOff M_sess _).bind fun p0 => by rcases p0.1 with _ | ⟨_, _, _, _⟩ <;> exact ZeroOff.pure _
      cases r0 with
      | none =>
        rw [StateT.run_bind]; refine (ZeroOff.sampleT_run M_sess st).bind fun p1 => ?_
        rw [StateT.run_bind]; refine (ZeroOff.root_run prng sIdxFn Δcka qep M_sess tL par _ _ _ _ p1.2).bind fun p2 => ?_
        rcases p2 with ⟨⟨_, _⟩, _⟩; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact ZeroOff.pure _
      | some _ =>
        rw [StateT.run_bind]; simp only [StateT.run_pure, pure_bind]; rw [StateT.run_bind]
        refine (ZeroOff.root_run prng sIdxFn Δcka qep M_sess tL par _ _ _ _ st).bind fun p2 => ?_
        rcases p2 with ⟨⟨_, _⟩, _⟩; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact ZeroOff.pure _
    · exact ZeroOff.pure _
  · rcases p.1 with _ | s1; · exact ZeroOff.pure _
    dsimp only; rcases s1.vS with _ | v; · simp only [StateT.run_pure]; exact ZeroOff.pure _
    dsimp only [hooksLocalForgedSlot]; simp only [StateT.run_pure, pure_bind]; exact ZeroOff.pure _
private theorem ZeroOff.vRecv_run {KC KR Γ T Sig SS RS M E CCoins K I : Type} [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS) (c : Header T × E) (rec : Option (Record M (Header T × E))) (st : LocalForgedSlotState T Sig K I) : ZeroOff M_sess ((vRecv (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par) ctx P vp c rec).run st) := by
  rw [vRecv_eq_bind]; split
  · exact ZeroOff.pure _
  · rw [StateT.run_bind]; refine (?_ : ZeroOff M_sess ((vRecvStep1 _ ctx P vp c).run st)).bind fun p => ?_
    · unfold vRecvStep1; by_cases hnew : c.1.1 = vp.tcur + 1
      · simp only [hnew, ↓reduceIte]; cases c.1.2 with
        | none => exact ZeroOff.pure _
        | some Tn =>
          rw [StateT.run_bind]; dsimp only [hooksLocalForgedSlot]
          refine (?_ : ZeroOff M_sess _).bind fun p0 => by rcases p0.1 with _ | (_ | ⟨_, _, _⟩) <;> exact ZeroOff.pure _
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases st.loc.cache (vp.tcur + 1) with
          | some entry =>
            rcases entry with ⟨tC, σc, kV⟩; by_cases htc : tC = Tn
            · simp only [htc, ↓reduceIte]; exact ZeroOff.pure _
            · simp only [htc, ↓reduceIte]; split_ifs
              · exact ZeroOff.pure _
              · exact ZeroOff.pure _
              · rw [StateT.run_bind]; exact (ZeroOff.lookup_run sIdxFn M_sess _ _ _ st).bind fun _ => ZeroOff.pure _
              · exact ZeroOff.pure _
              · exact ZeroOff.pure _
          | none =>
            dsimp only; split_ifs
            · exact ZeroOff.pure _
            · exact ZeroOff.pure _
            · rw [StateT.run_bind]; exact (ZeroOff.lookup_run sIdxFn M_sess _ _ _ st).bind fun _ => ZeroOff.pure _
            · exact ZeroOff.pure _
            · exact ZeroOff.pure _
      · simp only [hnew, ↓reduceIte]; exact ZeroOff.pure _
    · rcases p.1 with _ | (_ | s1)
      · exact ZeroOff.pure _
      · exact ZeroOff.pure _
      · dsimp only; cases s1.vR c.1.1 with
        | none => exact ZeroOff.pure _
        | some rs =>
          dsimp only [hooksLocalForgedSlot]; simp only [pure_bind]
          rcases fs.receive rs c.1 c.2 with _ | ⟨_, _, _⟩ <;> exact ZeroOff.pure _

theorem localAuthBucketForgedSlot_offRange {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    (localAuthBucketForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par A).IsQueryBoundP
      (fun t => sessOffRange M_sess t = true) 0 := by
  apply ZeroOff.to_isQueryBoundP; dsimp only [localAuthBucketForgedSlot]
  have hinit : ZeroOff M_sess ((initLocalForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par).run {}) := by
    dsimp only [initLocalForgedSlot]
    rw [StateT.run_bind]; refine (ZeroOff.sampleT_run (K := K) (α := KR) M_sess _).bind fun p1 => ?_
    rw [StateT.run_bind]; refine (ZeroOff.sampleT_run (K := K) (α := KC) M_sess p1.2).bind fun p2 => ?_
    rw [StateT.run_bind]; refine (ZeroOff.root_run prng sIdxFn Δcka qep M_sess tL par 0 false lam _ p2.2).bind fun p3 => ?_
    rcases p3 with ⟨⟨_, _⟩, _⟩; exact ZeroOff.pure _
  let hk := hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par
  have hsim : ∀ (oa : SchemeAdversary Γ T Sig SS RS M CCoins E) (s : LocalForgedSlotEState Γ T Sig SS RS M E K I),
      ZeroOff M_sess ((simulateQ (implLocalForgedSlot hk Δcka qep fs.maxSkip tL) oa).run s) := by
    intro oa; induction oa using OracleComp.inductionOn with
    | pure a => intro s; exact ZeroOff.pure (a, s)
    | query_bind t _ ih =>
      intro ⟨es0, we0⟩; rw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind]; refine ZeroOff.bind ?_ (fun p => ih p.1 p.2)
      rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P)
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inl]; rw [StateT.run_lift]
        exact (ZeroOff.query_false (.inl n) rfl).bind fun _ => ZeroOff.pure _
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rw [StateT.run_bind, StateT.run_get, pure_bind]; split
        · exact ZeroOff.pure _
        · split
          · exact ZeroOff.pure _
          · rw [StateT.run_bind, StateT.run_lift, bind_assoc]
            refine (ZeroOff.vSend_run cka prng fs sIdxFn Δcka qep M_sess tL par _ P _ m none r es0.h).bind fun p => ?_
            rw [pure_bind]; rcases p with ⟨res, _⟩
            cases res <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;> exact ZeroOff.pure _
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]; exact ZeroOff.pure _
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, bind_assoc]
        refine (?_ : ZeroOff M_sess ((deliverE hk fs.maxSkip (bucketAuthCfg Δcka tL) x).run es0)).bind fun _ => by
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]; exact ZeroOff.pure _
        dsimp only [deliverE]; rw [StateT.run_bind, StateT.run_get, pure_bind]; split
        · exact ZeroOff.pure _
        · cases es0.g.inTransit x.1.other x.2 with
          | none => exact ZeroOff.pure _
          | some r =>
            rw [run_liftH_bind]
            refine (ZeroOff.vRecv_run cka prng fs sIdxFn Δcka qep M_sess tL par _ _ _ _ _ es0.h).bind fun p => ?_
            rcases p.1 with _ | (_ | ⟨_, _, _, _⟩)
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroOff.pure _
            · dsimp only; split <;>
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact ZeroOff.pure _
            · dsimp only [commitE, hk, hooksLocalForgedSlot]; split <;> exact ZeroOff.pure _
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, bind_assoc]
        refine (?_ : ZeroOff M_sess ((injectE hk (2 + Δcka) qep (bucketAuthCfg Δcka tL) x).run es0)).bind fun _ => by
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]; exact ZeroOff.pure _
        dsimp only [injectE]; rw [StateT.run_bind, StateT.run_get, pure_bind]; split
        · exact ZeroOff.pure _
        · rw [run_liftH_bind]
          refine (ZeroOff.vRecv_run cka prng fs sIdxFn Δcka qep M_sess tL par _ _ _ _ _ es0.h).bind fun p => ?_
          rcases p.1 with _ | (_ | ⟨_, _, _, _⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroOff.pure _
          · exact ZeroOff.pure _
          · dsimp only; split_ifs <;>
              simp only [commitE, hk, hooksLocalForgedSlot, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact ZeroOff.pure _
      · dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr]; rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOff.pure _
        · dsimp only [hk, hooksLocalForgedSlot]
          split <;> simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind] <;>
            exact ZeroOff.pure _
  refine hinit.bind fun ⟨vs, _⟩ => ?_
  cases vs with
  | none => exact ZeroOff.pure _
  | some pair => rcases pair with ⟨_, _⟩; exact (hsim A _).bind fun _ => ZeroOff.pure _

/-! ### 4. Lazy-to-Eager Key-Slot & Post-Leak/Halted Equivalence -/

private def EqDistRel {α β : Type} (R : α → β → Prop)
    (mL : ProbComp α) (mR : ProbComp β) : Prop :=
  ∀ (fL : α → ProbComp Bool) (fR : β → ProbComp Bool),
    (∀ a b, R a b → 𝒟[fL a] = 𝒟[fR b]) →
    𝒟[mL >>= fL] = 𝒟[mR >>= fR]

private theorem EqDistRel.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) : EqDistRel R (Pure.pure a) (Pure.pure b) := by
  intro fL fR hf; simp only [pure_bind]; exact hf a b h

private theorem EqDistRel.bind {α₁ β₁ α₂ β₂ : Type} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop} {mL : ProbComp α₁} {mR : ProbComp β₁} {kL : α₁ → ProbComp α₂} {kR : β₁ → ProbComp β₂} (hm : EqDistRel R₁ mL mR) (hk : ∀ a b, R₁ a b → EqDistRel R₂ (kL a) (kR b)) : EqDistRel R₂ (mL >>= kL) (mR >>= kR) := by
  intro fL fR hf; simp only [bind_assoc]
  exact hm (fun a => kL a >>= fL) (fun b => kR b >>= fR) fun a b hab => hk a b hab fL fR hf

private theorem EqDistRel.same {ξ α β : Type} {R : α → β → Prop} (c : ProbComp ξ) (gL : ξ → α) (gR : ξ → β) (hg : ∀ x, R (gL x) (gR x)) : EqDistRel R (c >>= fun x => Pure.pure (gL x)) (c >>= fun x => Pure.pure (gR x)) := by
  intro fL fR hf; simp only [bind_assoc, pure_bind]
  exact evalDist_bind_congr _ _ _ fun x => hf _ _ (hg x)

private def LazySlotSync {T Sig K I : Type}
    (tbl : ℕ → Option K) (st : LocalForgedSlotState T Sig K I)
    (hLoc : LocalBucketAuthState T Sig K I) : Prop :=
  st.loc = hLoc ∧ ∀ i, st.usedSlot i = false → tbl i = none

private abbrev lazySlotImpl (K : Type) [SampleableType K] :=
  sessLift (lazyInit ($ᵗ K : ProbComp K) (keySlotImpl K))

theorem sim_sampleT_lImplF {α : Type} [SampleableType α] :
    simulateQ lImpl (sampleT (tspec := nilSpec) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α, simulateQ lImpl (liftM oa : OracleComp (unifSpec + nilSpec) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ lImpl
      ((liftM (OracleSpec.query (spec := unifSpec + nilSpec) (.inl t)) :
        OracleComp (unifSpec + nilSpec) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + nilSpec) α)) = _
    rw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

theorem sim_sampleT_fixedF {K α : Type} [SampleableType α] (ks : ℕ → K) :
    simulateQ (keySlotFixedImplF ks)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α,
      simulateQ (keySlotFixedImplF ks)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (keySlotFixedImplF ks)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)) = _
    rw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, keySlotFixedImplF, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

private theorem sim_sampleT_lazy_run {K α : Type} [SampleableType K] [SampleableType α]
    (tbl : ℕ → Option K) :
    (simulateQ (lazySlotImpl K)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run tbl =
      (($ᵗ α : ProbComp α) >>= fun a => Pure.pure (a, tbl)) := by
  suffices h : ∀ oa : ProbComp α,
      (simulateQ (lazySlotImpl K)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)).run tbl =
        (oa >>= fun a => Pure.pure (a, tbl)) from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (lazySlotImpl K)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α))).run tbl = _
    rw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, lazySlotImpl]
    simp only [sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private def HMRel {T Sig K I α : Type} :
    (α × LocalBucketAuthState T Sig K I) →
    ((α × LocalForgedSlotState T Sig K I) × (ℕ → Option K)) → Prop :=
  fun ⟨aL, hLoc⟩ ⟨⟨aR, st⟩, tbl⟩ => aL = aR ∧ LazySlotSync tbl st hLoc

private theorem eqDist_sampleT_hm {T Sig K I α : Type} [SampleableType K] [SampleableType α]
    {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) α)).run hLoc))
      ((simulateQ (lazySlotImpl K)
        ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run st)).run tbl) := by
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, sim_sampleT_lImplF, StateT.run_bind, sim_sampleT_lazy_run, bind_assoc, pure_bind]
  exact EqDistRel.same (R := HMRel) ($ᵗ α : ProbComp α) (fun a => (a, hLoc)) (fun a => ((a, st), tbl))
    fun _ => ⟨rfl, hsync⟩

private theorem eqDist_sampleOrSlot {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ)
    {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) K)).run hLoc))
      ((simulateQ (lazySlotImpl K) ((sampleOrSlotF M_sess useSlot sIdx).run st)).run tbl) := by
  by_cases hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · have hus : st.usedSlot sIdx = false := by simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc; exact hc.2
    have htbl : tbl sIdx = none := hsync.2 sIdx hus
    rw [sampleOrSlotF_pos_run M_sess useSlot sIdx st hc]; intro fL fR hf; have hL : (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) K)).run hLoc) >>= fL) =
        (($ᵗ K : ProbComp K) >>= fun k => fL (k, hLoc)) := by
      simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, sim_sampleT_lImplF, bind_assoc, pure_bind]
    have hq : (lazySlotImpl K (.inr ⟨sIdx, ()⟩)).run tbl =
        (($ᵗ K : ProbComp K) >>= fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
          Pure.pure (k, Function.update tbl sIdx (some (k : K)))) := by
      simp [-bind_pure_comp, lazySlotImpl, sessLift_inr, sessLiftCore, lazyInit, keySlotImpl, htbl, map_eq_bind_pure_comp]
      refine bind_congr fun k => ?_; change (Pure.pure (k, k) : ProbComp ((keySlotSpec K).Range () × K)) >>= _ = _; rw [pure_bind]
    have hR : (((simulateQ (lazySlotImpl K)
          ((query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) >>=
            fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
              Pure.pure ((k : K), { st with usedSlot := Function.update st.usedSlot sIdx true }))).run tbl) >>= fR) =
        (($ᵗ K : ProbComp K) >>= fun k =>
          fR ((k, { st with usedSlot := Function.update st.usedSlot sIdx true }), Function.update tbl sIdx (some k))) := by
      erw [simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]; erw [StateT.run_bind, hq]; simp only [simulateQ_pure, StateT.run_pure]
      erw [bind_assoc, bind_assoc]; refine bind_congr fun k => by erw [pure_bind, pure_bind]; rfl
    erw [hL, hR]; refine evalDist_bind_congr _ _ _ fun k =>
      hf (k, hLoc) ((k, { st with usedSlot := Function.update st.usedSlot sIdx true }), Function.update tbl sIdx (some k))
        ⟨rfl, hsync.1, fun i hi => ?_⟩
    by_cases his : i = sIdx; · subst his; simp at hi
    · simp only [Function.update_of_ne his] at hi ⊢; exact hsync.2 i hi
  · dsimp only [sampleOrSlotF]; rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact eqDist_sampleT_hm hsync

private theorem eqDist_hm_bind {T Sig K I α β : Type} [SampleableType K] {mL : HM nilSpec (LocalBucketAuthState T Sig K I) α} {mR : ForgedSlotHM T Sig K I α} {kL : α → HM nilSpec (LocalBucketAuthState T Sig K I) β} {kR : α → ForgedSlotHM T Sig K I β} {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I} (hm : EqDistRel HMRel (simulateQ lImpl (mL.run hLoc)) ((simulateQ (lazySlotImpl K) (mR.run st)).run tbl)) (hk : ∀ x tbl' st' hLoc', LazySlotSync tbl' st' hLoc' → EqDistRel HMRel (simulateQ lImpl ((kL x).run hLoc')) ((simulateQ (lazySlotImpl K) ((kR x).run st')).run tbl')) : EqDistRel HMRel (simulateQ lImpl ((mL >>= kL).run hLoc)) ((simulateQ (lazySlotImpl K) ((mR >>= kR).run st)).run tbl) := by
  simp only [StateT.run_bind, simulateQ_bind]
  exact hm.bind fun ⟨xL, hLoc'⟩ ⟨⟨xR, st'⟩, tbl'⟩ ⟨hx, hsync'⟩ => by
    subst hx; exact hk xL tbl' st' hLoc' hsync'

private theorem eqDist_lookup {T Sig K I : Type} [DecidableEq I] [SampleableType K] (sIdxFn : ℕ → ℕ → ℕ) (M_sess : ℕ) (reg : Bool) (t0 : ℕ) (ik : I) {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I} (hsync : LazySlotSync tbl st hLoc) : EqDistRel HMRel (simulateQ lImpl ((lookupLocalBucketAuthF t0 ik).run hLoc)) ((simulateQ (lazySlotImpl K) ((lookupLocalForgedSlotF sIdxFn M_sess reg t0 ik).run st)).run tbl) := by
  dsimp only [lookupLocalBucketAuthF, lookupLocalForgedSlotF]; simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.1]
  cases (hLoc.fTable t0).lookup ik with
  | some k =>
    by_cases hc : (reg && !(st.sessions t0).contains ik) = true
    · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure (R := HMRel) ⟨rfl, hsync.1, hsync.2⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure (R := HMRel) ⟨rfl, hsync⟩
  | none =>
    refine eqDist_hm_bind (eqDist_sampleOrSlot M_sess _ _ hsync)
      fun k tbl1 st1 hLoc1 hsync1 => ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
    exact EqDistRel.pure (R := HMRel) ⟨rfl, by rw [hsync1.1], hsync1.2⟩

private theorem eqDist_root {KR T Sig K I : Type} [DecidableEq I] [SampleableType I] [SampleableType K] (prng : PRFPRNG KR Sig I K) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig) {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I} (hsync : LazySlotSync tbl st hLoc) : EqDistRel HMRel (simulateQ lImpl ((rootLocalBucketAuth prng qep tL t0 pl ik0 σ0).run hLoc)) ((simulateQ (lazySlotImpl K) ((rootLocalForgedSlot prng sIdxFn Δcka qep M_sess tL par t0 pl ik0 σ0).run st)).run tbl) := by
  dsimp only [rootLocalBucketAuth, rootLocalForgedSlot]; split
  · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
  · split
    · refine eqDist_hm_bind (eqDist_sampleT_hm hsync) fun ir tbl1 st1 hLoc1 hsync1 => ?_
      refine eqDist_hm_bind (eqDist_sampleOrSlot M_sess _ _ hsync1) fun k tbl2 st2 hLoc2 hsync2 => ?_
      simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync2⟩
    · split
      · refine eqDist_hm_bind (eqDist_lookup sIdxFn M_sess _ t0 ik0 hsync) fun k tbl1 st1 hLoc1 hsync1 => ?_
        simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩

private theorem eqDist_vSend {KC KR Γ T Sig SS RS M E CCoins K I : Type} [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS) (m : M) (pair : Option (M × M)) (r0 : Option CCoins) {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I} (hsync : LazySlotSync tbl st hLoc) : EqDistRel HMRel (simulateQ lImpl ((vSend (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL) ctx P vp m pair r0).run hLoc)) ((simulateQ (lazySlotImpl K) ((vSend (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par) ctx P vp m pair r0).run st)).run tbl) := by
  rw [vSend_eq_bind, vSend_eq_bind]
  refine eqDist_hm_bind (K := K) ?_ fun s1? tbl1 st1 hLoc1 hsync1 => ?_
  · unfold vSendStep1; split
    · refine eqDist_hm_bind (K := K) ?_ fun res tbl1 st1 hLoc1 hsync1 => ?_
      · dsimp only [hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot]
        cases r0 with
        | none =>
          refine eqDist_hm_bind (eqDist_sampleT_hm hsync) fun coins tbl1 st1 hLoc1 hsync1 => ?_
          refine eqDist_hm_bind (eqDist_root prng sIdxFn Δcka qep M_sess tL par _ _ _ _ hsync1)
            fun ⟨σ', kVal⟩ tbl2 st2 hLoc2 hsync2 => ?_
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          exact EqDistRel.pure ⟨rfl, by rw [hsync2.1], hsync2.2⟩
        | some c =>
          simp only [pure_bind]; refine eqDist_hm_bind (eqDist_root prng sIdxFn Δcka qep M_sess tL par _ _ _ _ hsync)
            fun ⟨σ', kVal⟩ tbl2 st2 hLoc2 hsync2 => ?_
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          exact EqDistRel.pure ⟨rfl, by rw [hsync2.1], hsync2.2⟩
      · rcases res with _ | ⟨_, _, _, _⟩ <;>
          simp only [StateT.run_pure, simulateQ_pure] <;> exact EqDistRel.pure ⟨rfl, hsync1⟩
    · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
  · cases s1? with
    | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
    | some s1 =>
      dsimp only
      cases s1.vS with
      | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      | some v =>
        dsimp only [hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot]; simp only [StateT.run_pure, pure_bind, simulateQ_pure]
        exact EqDistRel.pure ⟨rfl, hsync1⟩

private theorem eqDist_vRecv {KC KR Γ T Sig SS RS M E CCoins K I : Type} [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS) (c : Header T × E) (rec : Option (Record M (Header T × E))) {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I} (hsync : LazySlotSync tbl st hLoc) : EqDistRel HMRel (simulateQ lImpl ((vRecv (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL) ctx P vp c rec).run hLoc)) ((simulateQ (lazySlotImpl K) ((vRecv (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par) ctx P vp c rec).run st)).run tbl) := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases hbad : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hbad, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    refine eqDist_hm_bind (K := K) ?_ fun s1? tbl1 st1 hLoc1 hsync1 => ?_
    · unfold vRecvStep1
      by_cases hnew : c.1.1 = vp.tcur + 1
      · simp only [hnew, ↓reduceIte]
        cases c.1.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
        | some Tn =>
          refine eqDist_hm_bind (K := K) ?_ fun sr tbl1 st1 hLoc1 hsync1 => ?_
          · dsimp only [hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.1]
            cases hLoc.cache (vp.tcur + 1) with
            | some entry =>
              rcases entry with ⟨tCached, σc, kVal⟩
              by_cases htc : tCached = Tn
              · simp only [htc, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
              · simp only [htc, ↓reduceIte]
                split_ifs
                · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
                · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
                · refine eqDist_hm_bind (eqDist_lookup sIdxFn M_sess _ _ _ hsync)
                    fun kOut tbl1 st1 hLoc1 hsync1 => ?_
                  simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
                · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
                · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
            | none =>
              dsimp only; split_ifs
              · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
              · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
              · refine eqDist_hm_bind (eqDist_lookup sIdxFn M_sess _ _ _ hsync)
                  fun kOut tbl1 st1 hLoc1 hsync1 => ?_
                simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
              · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
              · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
          · rcases sr with _ | (_ | ⟨γ', σ', rs⟩) <;>
              simp only [StateT.run_pure, simulateQ_pure] <;> exact EqDistRel.pure ⟨rfl, hsync1⟩
      · simp only [hnew, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
    · rcases s1? with _ | (_ | s1)
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      · dsimp only
        cases s1.vR c.1.1 with
        | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure (R := HMRel) ⟨rfl, hsync1⟩
        | some rs =>
          dsimp only [hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot]; simp only [pure_bind]
          rcases fs.receive rs c.1 c.2 with _ | ⟨_, _, _⟩ <;>
            simp only [StateT.run_pure, simulateQ_pure] <;>
            exact EqDistRel.pure (R := HMRel) ⟨rfl, hsync1⟩

private def EStateRel {Γ T Sig SS RS M E K I α : Type} :
    (α × EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)) →
    ((α × EState (VP Γ T Sig SS RS) M (Header T × E) (LocalForgedSlotState T Sig K I)) ×
      (ℕ → Option K)) → Prop :=
  fun ⟨aL, esL⟩ ⟨⟨aR, esR⟩, tbl⟩ =>
    aL = aR ∧ esL.g = esR.g ∧ esL.abort = esR.abort ∧ LazySlotSync tbl esR.h esL.h

private theorem eqDist_deliverE {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × (Header T × E)) (g : Ctx Γ T Sig SS RS M E) (abort : Bool)
    {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel EStateRel
      (simulateQ lImpl ((deliverE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
        fs.maxSkip (bucketAuthCfg Δcka tL) x).run { g := g, h := hLoc, abort := abort }))
      ((simulateQ (lazySlotImpl K)
        ((deliverE (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par)
          fs.maxSkip (bucketAuthCfg Δcka tL) x).run { g := g, h := st, abort := abort })).run tbl) := by
  dsimp only [deliverE]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync⟩
  · cases g.inTransit x.1.other x.2 with
    | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync⟩
    | some r =>
      rw [run_liftH_bind, run_liftH_bind]; simp only [simulateQ_bind, StateT.run_bind]
      refine (eqDist_vRecv cka prng fs sIdxFn Δcka qep M_sess tL par g x.1 (g.st x.1) x.2
        (some r) hsync).bind fun ⟨vL, hLoc1⟩ ⟨⟨vR, st1⟩, tbl1⟩ ⟨hv, hsync1⟩ => ?_
      subst hv
      rcases vL with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
      · dsimp only; split <;>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure] <;>
          exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
      · dsimp only [commitE, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot, liftH]
        split <;> simp <;> exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩

private theorem eqDist_injectE {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × (Header T × E)) (g : Ctx Γ T Sig SS RS M E) (abort : Bool)
    {tbl : ℕ → Option K} {st : LocalForgedSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel EStateRel
      (simulateQ lImpl ((injectE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
        (2 + Δcka) qep (bucketAuthCfg Δcka tL) x).run { g := g, h := hLoc, abort := abort }))
      ((simulateQ (lazySlotImpl K)
        ((injectE (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) x).run { g := g, h := st, abort := abort })).run tbl) := by
  dsimp only [injectE]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync⟩
  · rw [run_liftH_bind, run_liftH_bind]
    simp only [simulateQ_bind, StateT.run_bind]
    refine (eqDist_vRecv cka prng fs sIdxFn Δcka qep M_sess tL par g x.1 (g.st x.1) x.2
      none hsync).bind fun ⟨vL, hLoc1⟩ ⟨⟨vR, st1⟩, tbl1⟩ ⟨hv, hsync1⟩ => ?_
    subst hv
    rcases vL with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
    · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
    · dsimp only; split_ifs
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
      · dsimp only [commitE, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot, liftH]
        simp; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, hsync1⟩

theorem localAuthBucketForgedSlot_lazy_eq {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketForgedHdrPar cka prng fs lam Δcka qep tL par A] =
      𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit ($ᵗ K : ProbComp K) (keySlotImpl K)))
        (localAuthBucketForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par A)).run
        (fun _ => none)] := by
  have hinit : EqDistRel HMRel (simulateQ lImpl ((initLocalBucketAuth cka prng fs lam qep tL).run {}))
      ((simulateQ (lazySlotImpl K) ((initLocalForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par).run {})).run (fun _ => none)) := by
    dsimp only [initLocalBucketAuth, initLocalForgedSlot]
    have hsync0 : LazySlotSync (K := K) (fun _ => none) ({} : LocalForgedSlotState T Sig K I) {} := ⟨rfl, fun _ _ => rfl⟩
    refine eqDist_hm_bind (eqDist_sampleT_hm hsync0) fun kr _ _ _ hsync1 => ?_
    refine eqDist_hm_bind (eqDist_sampleT_hm hsync1) fun kc _ _ _ hsync2 => ?_
    refine eqDist_hm_bind (eqDist_root prng sIdxFn Δcka qep M_sess tL par 0 false lam (prng.init kr) hsync2) fun ⟨σ0, k0⟩ _ _ _ hsync3 => ?_
    simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync3⟩
  let hkL := hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL
  let hkR := hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par
  have hsim : ∀ (oa : SchemeAdversary Γ T Sig SS RS M CCoins E) (g : Ctx Γ T Sig SS RS M E) (abort : Bool) (winEp : Option ℕ)
      (tbl : ℕ → Option K) (st : LocalForgedSlotState T Sig K I) (hLoc : LocalBucketAuthState T Sig K I), LazySlotSync tbl st hLoc →
      EqDistRel (fun (pL : Bool × LocalBucketAuthEState Γ T Sig SS RS M E K I)
                     (pR : (Bool × LocalForgedSlotEState Γ T Sig SS RS M E K I) × (ℕ → Option K)) =>
          pL.1 = pR.1.1 ∧ pL.2.2 = pR.1.2.2 ∧ pL.2.1.g = pR.1.2.1.g ∧ pL.2.1.abort = pR.1.2.1.abort ∧ LazySlotSync pR.2 pR.1.2.1.h pL.2.1.h)
        (simulateQ lImpl ((simulateQ (implLocalBucketAuthGen hkL Δcka qep fs.maxSkip tL true) oa).run ({ g := g, h := hLoc, abort := abort }, winEp)))
        ((simulateQ (lazySlotImpl K) ((simulateQ (implLocalForgedSlot hkR Δcka qep fs.maxSkip tL) oa).run ({ g := g, h := st, abort := abort }, winEp))).run tbl) := by
    intro oa; induction oa using OracleComp.inductionOn with
    | pure a => intro g abort winEp tbl st hLoc hsync; simp only [simulateQ_pure, StateT.run_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
    | query_bind t _ ih =>
      intro g abort winEp tbl st hLoc hsync; rw [simulateQ_query_bind, simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind]
      refine EqDistRel.bind (R₁ := fun (pL : _ × LocalBucketAuthEState Γ T Sig SS RS M E K I)
          (pR : (_ × LocalForgedSlotEState Γ T Sig SS RS M E K I) × (ℕ → Option K)) =>
          pL.1 = pR.1.1 ∧ pL.2.2 = pR.1.2.2 ∧ pL.2.1.g = pR.1.2.1.g ∧ pL.2.1.abort = pR.1.2.1.abort ∧ LazySlotSync pR.2 pR.1.2.1.h pL.2.1.h) ?_ ?_
      · rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P)
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inl]
          intro fL fR hf; simp [-bind_pure_comp, lImpl, lazySlotImpl, sessLift_inl, map_eq_bind_pure_comp]
          exact evalDist_bind_congr _ _ _ fun u => hf (u, ({ g := g, h := hLoc, abort := abort }, winEp)) ((u, ({ g := g, h := st, abort := abort }, winEp)), tbl) ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hhalt : (abort || g.win) = true
          · simp only [hhalt, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
          · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]; cases g.epMgmt (2 + Δcka) qep P r.isSome with
            | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
            | some s1 =>
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind]
              refine (eqDist_vSend cka prng fs sIdxFn Δcka qep M_sess tL par s1 P (s1.st P) m none r hsync).bind fun ⟨resL, _⟩ ⟨⟨resR, _⟩, _⟩ ⟨hres, hsync'⟩ => ?_
              subst hres; rcases resL with _ | ⟨_, _⟩ <;> simp <;> exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync'⟩
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind]
          refine (eqDist_deliverE cka prng fs sIdxFn Δcka qep M_sess tL par x g abort hsync).bind fun ⟨outL, esL'⟩ ⟨⟨outR, esR'⟩, _⟩ ⟨hout, hg', hab', hsync'⟩ => ?_
          subst hout; simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, hg', hab', hsync'⟩
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind]
          refine (eqDist_injectE cka prng fs sIdxFn Δcka qep M_sess tL par x g abort hsync).bind fun ⟨outL, esL'⟩ ⟨⟨outR, esR'⟩, _⟩ ⟨hout, hg', hab', hsync'⟩ => ?_
          subst hout; simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, hsync.1, hg']; exact EqDistRel.pure ⟨rfl, rfl, hg', hab', hsync'⟩
        · dsimp only [implLocalBucketAuthGen, implLocalForgedSlot, QueryImpl.add_apply_inr]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hskip : (abort || g.win || !(g.corrAllowed P)) = true
          · simp only [hskip, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
          · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
            dsimp only [hkL, hkR, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, hooksLocalForgedSlot]; split <;> simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure] <;>
              exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
      · intro ⟨uL, ⟨esL, weL⟩⟩ ⟨⟨uR, ⟨esR, weR⟩⟩, tbl'⟩ ⟨hu, hwe, hg, habort, hsync'⟩
        subst hu; subst hwe; cases esL; cases esR; dsimp only at hg habort hsync'; subst hg; subst habort; exact ih uL _ _ weL tbl' _ _ hsync'
  dsimp only [localAuthBucketForgedHdrPar, localAuthBucketForgedSlot]; rw [map_eq_bind_pure_comp]; simp only [Function.comp_def, simulateQ_bind, StateT.run_bind, bind_assoc]
  refine hinit ?_ ?_ ?_; intro ⟨vsL, hLoc0⟩ ⟨⟨vsR, st0⟩, tbl0⟩ ⟨hvs, hsync0⟩; subst hvs
  cases vsL with
  | none => simp
  | some pair =>
    rcases pair with ⟨vA, vB⟩; simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    convert hsim A _ false none tbl0 st0 hLoc0 hsync0 _ _ ?_
    intro ⟨_, ⟨esL, weL⟩⟩ ⟨⟨_, ⟨esR, weR⟩⟩, _⟩ ⟨_, hwe, hg, habort, _⟩; subst hwe; dsimp only at hg habort; cases weL <;> simp [forgedOut, hg, habort]

theorem localAuthBucketForgedHdrPar_eq_eager_ks {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (k0 : K)
    (sIdxFn : ℕ → ℕ → ℕ) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketForgedHdrPar cka prng fs lam Δcka qep tL par A] =
      𝒟[sampleVec ($ᵗ K : ProbComp K) k0 M_sess >>= fun ks =>
          simulateQ (keySlotFixedImplF ks)
            (localAuthBucketForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par A)] := by
  rw [localAuthBucketForgedSlot_lazy_eq cka prng fs lam sIdxFn Δcka qep M_sess tL par A, keySlot_lazy_eq_eager k0 M_sess (localAuthBucketForgedSlot cka prng fs lam sIdxFn Δcka qep M_sess tL par A) (localAuthBucketForgedSlot_offRange cka prng fs lam sIdxFn Δcka qep M_sess tL par A)]
  refine evalDist_bind_congr _ _ _ fun ks => ?_
  rw [simulateQ_sessLift_keySlotImpl_fst]

/-! ### 5. Halted / Post-Leak Equivalence (`keySlotFixedImplF ks` ↔ `lImpl`) -/

theorem forgedSlot_fixed_eq_localGen_of_halted_or_postLeak
    {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sIdxFn : ℕ → ℕ → ℕ) (ks : ℕ → K) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esSlot : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalForgedSlotState T Sig K I))
    (we : Option ℕ)
    (hexit : (esSlot.abort || esSlot.g.win) = true ∨ postLeak tL esSlot.g = true) :
    𝒟[simulateQ (keySlotFixedImplF ks) do
        let (_, es', we') ←
          (simulateQ (implLocalForgedSlot
            (hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par)
            Δcka qep fs.maxSkip tL) oa).run (esSlot, we)
        return forgedOut (2 + Δcka) tL par es' we'] =
      𝒟[simulateQ lImpl do
        let (_, es', we') ←
          (simulateQ (implLocalBucketAuthGen
            (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
            Δcka qep fs.maxSkip tL true) oa).run
            ({ g := esSlot.g, h := esSlot.h.loc, abort := esSlot.abort }, we)
        return forgedOut (2 + Δcka) tL par es' we'] := by
  have hpl_ep : ∀ {g s₁ : Ctx Γ T Sig SS RS M E} {P : Party} {bad : Bool},
      postLeak tL g = true → g.epMgmt (2 + Δcka) qep P bad = some s₁ → postLeak tL s₁ = true := by
    intro g s₁ P bad hpl hep
    have hmono : ∀ cur, g.tL = some cur → ltOpt tL cur = true → ∀ l, ltOpt tL (maxOpt g.tL l) = true := by
      intro cur hcur hlt l; rw [hcur]; dsimp only [maxOpt]; cases tL with | none => rfl | some _ => simp only [ltOpt, decide_eq_true_eq] at hlt ⊢; omega
    unfold postLeak at hpl ⊢; cases hcur : g.tL with
    | none => rw [hcur] at hpl; cases hpl
    | some cur =>
      rw [hcur] at hpl; unfold GameState.epMgmt at hep; split_ifs at hep <;> injection hep with hs₁ <;> subst hs₁
      · exact hmono cur hcur hpl _
      · rw [hcur]; exact hpl
      · rw [hcur]; exact hpl
  have hpl_corr : ∀ {g : Ctx Γ T Sig SS RS M E} {P : Party}, postLeak tL g = true → postLeak tL (g.afterCorr P) = true := by
    intro g P hpl; unfold postLeak at hpl ⊢; dsimp only [GameState.afterCorr, GameState.leak]
    cases hcur : g.tL with
    | none => rw [hcur] at hpl; cases hpl
    | some cur => rw [hcur] at hpl; dsimp only [maxOpt]; cases tL with | none => rfl | some _ => simp only [ltOpt, decide_eq_true_eq] at hpl ⊢; omega
  let hkR := hooksLocalForgedSlot cka prng fs sIdxFn Δcka qep M_sess tL par
  let hkL := hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL
  have hvRecv_pl : ∀ (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E))) (st : LocalForgedSlotState T Sig K I)
      (hLoc : LocalBucketAuthState T Sig K I), postLeak tL ctx = true → st.loc = hLoc → ∃ res, (vRecv hkR ctx P (ctx.st P) c rec).run st = pure (res, st) ∧ (vRecv hkL ctx P (ctx.st P) c rec).run hLoc = pure (res, hLoc) := by
    intro ctx P c rec st hLoc hpl hloc; rw [vRecv_eq_bind, vRecv_eq_bind]
    by_cases hbad : ((ctx.st P).id.sendsIn c.1.1 || decide ((ctx.st P).tcur + 1 < c.1.1)) = true
    · simp only [hbad, ↓reduceIte]; exact ⟨some none, rfl, rfl⟩
    · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      have hs1 : ∃ s1?, (vRecvStep1 hkR ctx P (ctx.st P) c).run st = pure (s1?, st) ∧ (vRecvStep1 hkL ctx P (ctx.st P) c).run hLoc = pure (s1?, hLoc) := by
        unfold vRecvStep1; by_cases hnew : c.1.1 = (ctx.st P).tcur + 1
        · simp only [hnew, ↓reduceIte]; cases c.1.2 with
          | none => exact ⟨some none, rfl, rfl⟩
          | some Tn =>
            dsimp only [hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]; simp only [StateT.run_bind, StateT.run_get, pure_bind, hloc, hpl, ↓reduceIte]
            cases hLoc.cache ((ctx.st P).tcur + 1) with
            | none => dsimp only; split_ifs <;> exact ⟨_, rfl, rfl⟩
            | some entry =>
              rcases entry with ⟨tC, _, _⟩; by_cases ht : tC = Tn
              · simp only [ht, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
              · simp only [ht, ↓reduceIte]; split_ifs <;> exact ⟨_, rfl, rfl⟩
        · simp only [hnew, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
      rcases hs1 with ⟨s1?, hs1R, hs1L⟩; rw [hs1R, hs1L, pure_bind, pure_bind]
      rcases s1? with _ | (_ | s1)
      · exact ⟨none, rfl, rfl⟩
      · exact ⟨some none, rfl, rfl⟩
      · dsimp only; cases s1.vR c.1.1 with
        | none => exact ⟨some none, rfl, rfl⟩
        | some rs =>
          dsimp only [hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]
          cases fs.receive rs c.1 c.2 with | none => exact ⟨some none, rfl, rfl⟩ | some res => rcases res with ⟨_, _, _⟩; exact ⟨_, rfl, rfl⟩
  suffices hsim : ∀ (oa' : SchemeAdversary Γ T Sig SS RS M CCoins E) (g : Ctx Γ T Sig SS RS M E) (abort : Bool) (we0 : Option ℕ) (st : LocalForgedSlotState T Sig K I) (hLoc : LocalBucketAuthState T Sig K I),
      st.loc = hLoc → ((abort || g.win) = true ∨ postLeak tL g = true) →
      EqDistRel (fun (pR : Bool × LocalForgedSlotEState Γ T Sig SS RS M E K I) (pL : Bool × LocalBucketAuthEState Γ T Sig SS RS M E K I) =>
          pR.1 = pL.1 ∧ pR.2.2 = pL.2.2 ∧ pR.2.1.g = pL.2.1.g ∧ pR.2.1.abort = pL.2.1.abort ∧ pR.2.1.h.loc = pL.2.1.h ∧ ((pR.2.1.abort || pR.2.1.g.win) = true ∨ postLeak tL pR.2.1.g = true))
        (simulateQ (keySlotFixedImplF ks) ((simulateQ (implLocalForgedSlot hkR Δcka qep fs.maxSkip tL) oa').run ({ g := g, h := st, abort := abort }, we0)))
        (simulateQ lImpl ((simulateQ (implLocalBucketAuthGen hkL Δcka qep fs.maxSkip tL true) oa').run ({ g := g, h := hLoc, abort := abort }, we0))) by
    have hes : esSlot = { g := esSlot.g, h := esSlot.h, abort := esSlot.abort } := by cases esSlot; rfl
    rw [hes]; simp only [simulateQ_bind]; refine hsim oa esSlot.g esSlot.abort we esSlot.h esSlot.h.loc rfl hexit _ _ ?_
    intro ⟨_, esR, weR⟩ ⟨_, esL, weL⟩ ⟨_, hwe, hg, hab, _, _⟩; dsimp only at hwe hg hab; subst hwe; simp only [simulateQ_pure]; cases weR <;> simp [forgedOut, hg, hab]
  intro oa'; induction oa' using OracleComp.inductionOn with
  | pure a => intro g abort we0 st hLoc hloc hex; simp only [simulateQ_pure, StateT.run_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, hex⟩
  | query_bind t _ ih =>
    intro g abort we0 st hLoc hloc hex; rw [simulateQ_query_bind, simulateQ_query_bind]; dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind]
    refine EqDistRel.bind (R₁ := fun (pR : _ × LocalForgedSlotEState Γ T Sig SS RS M E K I) (pL : _ × LocalBucketAuthEState Γ T Sig SS RS M E K I) =>
        pR.1 = pL.1 ∧ pR.2.2 = pL.2.2 ∧ pR.2.1.g = pL.2.1.g ∧ pR.2.1.abort = pL.2.1.abort ∧ pR.2.1.h.loc = pL.2.1.h ∧ ((pR.2.1.abort || pR.2.1.g.win) = true ∨ postLeak tL pR.2.1.g = true)) ?_ ?_
    · rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P)
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inl]
        intro fR fL hf; simp [-bind_pure_comp, keySlotFixedImplF, lImpl, map_eq_bind_pure_comp]; exact evalDist_bind_congr _ _ _ fun u => hf (u, ({ g := g, h := st, abort := abort }, we0)) (u, ({ g := g, h := hLoc, abort := abort }, we0)) ⟨rfl, rfl, rfl, rfl, hloc, hex⟩
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
        by_cases hhalt : (abort || g.win) = true
        · simp only [hhalt, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl hhalt⟩
        · have hpl_g : postLeak tL g = true := hex.resolve_left hhalt
          simp only [hhalt, Bool.false_eq_true, ↓reduceIte]; cases hep : g.epMgmt (2 + Δcka) qep P r.isSome with
          | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
          | some s1 =>
            have hpl_s1 : postLeak tL s1 = true := hpl_ep hpl_g hep
            simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind]; rw [vSend_eq_bind, vSend_eq_bind]; simp only [StateT.run_bind, bind_assoc, simulateQ_bind]
            unfold vSendStep1; by_cases hs : (s1.st P).id.sendsIn ((s1.st P).tcur + 1) = true
            · simp only [hs, ↓reduceIte]; dsimp only [hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]
              cases r with
              | none =>
                intro fR fL hf; simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind, sim_sampleT_fixedF, sim_sampleT_lImplF, rootLocalForgedSlot, rootLocalBucketAuth, hpl_s1, Bool.true_or, ↓reduceIte, StateT.run_modify, StateT.run_set, StateT.run_pure, simulateQ_pure]
                refine evalDist_bind_congr _ _ _ fun c => hf _ _ ⟨rfl, rfl, rfl, rfl, by simp [hloc], Or.inr hpl_s1⟩
              | some c =>
                simp only [StateT.run_bind, StateT.run_pure, pure_bind, rootLocalForgedSlot, rootLocalBucketAuth, hpl_s1, Bool.true_or, ↓reduceIte, StateT.run_modify, StateT.run_set, bind_assoc, simulateQ_pure]
                exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, by simp [hloc], Or.inr hpl_s1⟩
            · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
              cases (s1.st P).vS with
              | none => simp only [StateT.run_pure, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_s1⟩
              | some v =>
                dsimp only [hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]; simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
                exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_s1⟩
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]; simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, hex⟩
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE]; simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, bind_assoc, pure_bind]
        by_cases hhalt : (abort || g.win) = true
        · simp only [hhalt, ↓reduceIte, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl hhalt⟩
        · have hpl_g : postLeak tL g = true := hex.resolve_left hhalt
          simp only [hhalt, Bool.false_eq_true, ↓reduceIte]; cases g.inTransit x.1.other x.2 with
          | none => simp only [StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
          | some rec =>
            rcases hvRecv_pl g x.1 x.2 (some rec) st hLoc hpl_g hloc with ⟨res, hR, hL⟩; rw [run_liftH_bind, run_liftH_bind, hR, hL]; simp only [pure_bind]
            rcases res with _ | (_ | ⟨st', t', i', m'⟩)
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl rfl⟩
            · dsimp only; split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]
              · exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl (by simp)⟩
              · exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
            · dsimp only [commitE, hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]
              split <;> simp only [StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind] <;> exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE]; simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, bind_assoc, pure_bind]
        by_cases hskip : (abort || g.win || (g.inTransit x.1.other x.2).isSome || !g.safeInj (2 + Δcka)) = true
        · simp only [hskip, ↓reduceIte, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc]
          have hnw : (!g.win && g.win) = false := by cases g.win <;> rfl
          simp only [hnw, Bool.false_and]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, hex⟩
        · have hhalt : (abort || g.win) = false := by revert hskip; cases abort || g.win <;> simp
          have hpl_g : postLeak tL g = true := hex.resolve_left (by simp [hhalt]); simp only [hskip, Bool.false_eq_true, ↓reduceIte]
          rcases hvRecv_pl g x.1 x.2 none st hLoc hpl_g hloc with ⟨res, hR, hL⟩; rw [run_liftH_bind, run_liftH_bind, hR, hL]; simp only [pure_bind]
          rcases res with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc, Bool.not_true, Bool.false_or]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl rfl⟩
          · simp only [StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
          · dsimp only; split_ifs
            · simp only [StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
            · dsimp only [commitE, hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]; simp only [StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, hloc]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl (by simp)⟩
            · simp only [StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure, hloc]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr hpl_g⟩
      · dsimp only [implLocalForgedSlot, implLocalBucketAuthGen, QueryImpl.add_apply_inr]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
        by_cases hskip : (abort || g.win || !(g.corrAllowed P)) = true
        · simp only [hskip, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, hex⟩
        · have hhalt : (abort || g.win) = false := by revert hskip; cases abort || g.win <;> simp
          have hpl_g : postLeak tL g = true := hex.resolve_left (by simp [hhalt]); simp only [hskip, Bool.false_eq_true, ↓reduceIte]; dsimp only [hkR, hkL, hooksLocalForgedSlot, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]
          split <;> simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
          · exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inl rfl⟩
          · exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hloc, Or.inr (hpl_corr hpl_g)⟩
    · intro ⟨uR, esR, weR⟩ ⟨uL, esL, weL⟩ ⟨hu, hwe, hg, hab, hloc', hex'⟩; subst hu; subst hwe; cases esR; cases esL; dsimp only at hg hab hloc' hex'; subst hg; subst hab; exact ih uR _ _ weR _ _ hloc' hex'

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed
