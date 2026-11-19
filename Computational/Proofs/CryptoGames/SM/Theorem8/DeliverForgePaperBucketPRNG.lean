/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGPotOK
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2Base
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2Step
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2StepHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2StepHooks2
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2Top
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGForgedTop
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGInactive
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGMainTopZero
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGEval
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEval
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval

/-!
# Stage-2 `(tL, par)` Bucket Ascending `t`-Hybrid PRF-PRNG Reduction (`[B7]` × `[B8]`, Piece `(B)`)

Re-exports the definitions of `DeliverForgeBucketPRNGDefs` and assembles:
1. Parity-slot bijection (`sum_ico_forged_add_main_eq_slotDispatchGen`,
   `sum_ico_forged_add_main_eq_bucketSlotPacked`) packing active `ForgedHdr` (`t0 ↦ t0`) and
   active `Main` (`t0 ↦ t0 + 1`) epochs into `1 *` `Finset.Ico (healEpoch tL) (qep + 2)`.
2. Shallow Hop-2a (`Main + ForgedHdr` split at `t = healEpoch tL`), `Main` & `ForgedHdr`
   telescopes, and parity-slot packed `(tL, par)` bucket bounds
   (`cka_branch_true_redCKAAuthDFPaperBucket_le_sum_slotDispatch_add_local_split`,
   `cka_branch_true_redCKAAuthDFPaperBucket_le_sum_prng_add_local`,
   `forgeBucketAdvantagePaper_le_cka_add_sum_prng_add_local`).
3. Combined syntactic + potential PRF-PRNG query bounds `min (2 + 2 * q) (q + 3)` and costed
   `PRFPRNG.advantage` bridges for `redPRNGAuthDF{,Paper}Bucket{Hybrid,Split,Packed}Prog`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

open scoped ENNReal
open OracleSpec OracleComp MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

/-! ## 1. `Finset` Parity-Slot Bijection (`ForgedHdr` `t0 ↦ t0`, `Main` `t0 ↦ t0 + 1`) -/

section ParitySlotBijection

/-- Exact 3-way slot dispatcher on `t ∈ Finset.Ico (healEpoch tL) (N + 2)`:
- if `isActiveBucketEpoch Δbucket tL par t`, dispatches `ForgedHdr` at `t`;
- else if `healEpoch tL < t` and `isActiveBucketEpoch Δbucket tL par (t - 1)`, dispatches `Main` at `t - 1`;
- else `0`. -/
@[expose] def slotDispatchGen (Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (f_forged f_main : ℕ → ℝ≥0∞) (t : ℕ) : ℝ≥0∞ :=
  if isActiveBucketEpoch Δbucket tL par t then
    f_forged t
  else if healEpoch tL < t && isActiveBucketEpoch Δbucket tL par (t - 1) then
    f_main (t - 1)
  else
    0

/-- Exact 3-way slot dispatcher at `Δbucket = 3 + Δcka` (`inStage2Bucket Δcka`). -/
abbrev slotDispatch (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (f_forged f_main : ℕ → ℝ≥0∞) (t : ℕ) : ℝ≥0∞ :=
  slotDispatchGen (3 + Δcka) tL par f_forged f_main t

/-- `Party.senderOf` strictly alternates parity on all `t0 : ℕ` (including `0 ↦ 1`). -/
theorem partyPar_senderOf_succ (t0 : ℕ) :
    partyPar (Party.senderOf (t0 + 1)) = !partyPar (Party.senderOf t0) := by
  unfold Party.senderOf partyPar
  by_cases h0 : t0 % 2 = 1
  · have h1 : (t0 + 1) % 2 ≠ 1 := by omega
    simp [h0, h1]
  · have h1 : (t0 + 1) % 2 = 1 := by omega
    simp [h0, h1]

/-- Key parity-slot disjointness: whenever `4 ≤ Δbucket`, if `t0` is active then `t0 + 1` is NOT
active (`tL = none` alternates parity; `tL = some l` maps `tH = l + 2` to unused gap slot
`l + 3 < l + Δbucket`, and `[l + Δbucket, ∞)` alternates parity). -/
theorem isActiveBucketEpoch_succ_eq_false
    {Δbucket : ℕ} (hΔ : 4 ≤ Δbucket) {tL : Option ℕ} {par : Bool} {t0 : ℕ}
    (hAct : isActiveBucketEpoch Δbucket tL par t0 = true) :
    isActiveBucketEpoch Δbucket tL par (t0 + 1) = false := by
  unfold isActiveBucketEpoch inStage2BucketGen at hAct ⊢
  cases tL with
  | none =>
    simp only [Option.isSome_none, Bool.false_and, Bool.false_or,
      lastLeakGuessAdmissible, healedBy, Bool.true_and, beq_iff_eq] at hAct ⊢
    rw [partyPar_senderOf_succ, hAct]
    cases par <;> simp
  | some l =>
    simp only [Option.isSome_some, Bool.true_and, healEpoch, lastLeakGuessAdmissible, healedBy,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hAct
    rcases hAct with hEq | ⟨hle, hpar⟩
    · have h0 : t0 = l + 2 := of_decide_eq_true hEq
      subst h0
      simp [healEpoch, lastLeakGuessAdmissible, healedBy]
      omega
    · rw [partyPar_senderOf_succ, hpar]
      cases par <;> simp [healEpoch] <;> omega

/-- Exact `Finset.Ico` parity-slot packing equality (`4 ≤ Δbucket`):
mapping active `ForgedHdr` epochs `t0 ∈ Ico tH (N + 2)` to `t := t0` and active `Main` epochs
`t0 ∈ Ico tH (N + 1)` to `t := t0 + 1` packs disjointly into `Finset.Ico tH (N + 2)`. -/
theorem sum_ico_forged_add_main_eq_slotDispatchGen
    {Δbucket : ℕ} (hΔ : 4 ≤ Δbucket) (tL : Option ℕ) (par : Bool) (N : ℕ)
    (f_forged f_main : ℕ → ℝ≥0∞)
    (hf : ∀ t0 ∈ Finset.Ico (healEpoch tL) (N + 2),
      isActiveBucketEpoch Δbucket tL par t0 = false → f_forged t0 = 0)
    (hm : ∀ t0 ∈ Finset.Ico (healEpoch tL) (N + 1),
      isActiveBucketEpoch Δbucket tL par t0 = false → f_main t0 = 0) :
    (∑ t0 ∈ Finset.Ico (healEpoch tL) (N + 2), f_forged t0) +
      (∑ t0 ∈ Finset.Ico (healEpoch tL) (N + 1), f_main t0) =
      ∑ t ∈ Finset.Ico (healEpoch tL) (N + 2),
        slotDispatchGen Δbucket tL par f_forged f_main t := by
  let tH := healEpoch tL
  let p := isActiveBucketEpoch Δbucket tL par
  have hSplit :
      ∀ t ∈ Finset.Ico tH (N + 2),
        slotDispatchGen Δbucket tL par f_forged f_main t =
          (if p t then f_forged t else 0) +
            (if tH < t && p (t - 1) then f_main (t - 1) else 0) := by
    intro t _
    unfold slotDispatchGen
    by_cases hpt : p t = true
    · have hnot : ¬ (tH < t && p (t - 1)) = true := by
        intro h2
        rw [Bool.and_eq_true, decide_eq_true_eq] at h2
        have hsucc : t - 1 + 1 = t := by omega
        have hfalse := isActiveBucketEpoch_succ_eq_false hΔ h2.2
        rw [hsucc] at hfalse
        change p t = false at hfalse
        rw [hpt] at hfalse
        cases hfalse
      simp [p, tH, hpt, hnot]
    · simp only [Bool.not_eq_true] at hpt
      simp [p, tH, hpt]
  rw [Finset.sum_congr rfl hSplit, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun t0 ht0 => ?_
    by_cases hp0 : p t0 = true
    · simp [hp0]
    · simp only [Bool.not_eq_true] at hp0
      simp [hp0, hf t0 ht0 hp0]
  · by_cases hLe : tH ≤ N + 1
    · have hIco : Finset.Ico tH (N + 2) = insert tH (Finset.Ico (tH + 1) (N + 2)) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hNotMem : tH ∉ Finset.Ico (tH + 1) (N + 2) := by simp
      rw [hIco, Finset.sum_insert hNotMem]
      have hZeroTH : (if (tH < tH && p (tH - 1)) = true then f_main (tH - 1) else 0) = 0 := by
        simp
      rw [hZeroTH, zero_add]
      have hBij :
          (∑ t0 ∈ Finset.Ico tH (N + 1), f_main t0) =
            ∑ t ∈ Finset.Ico (tH + 1) (N + 2),
              if (tH < t && p (t - 1)) = true then f_main (t - 1) else 0 := by
        refine Finset.sum_bij (fun t0 _ => t0 + 1) ?_ ?_ ?_ ?_
        · intro t0 ht0
          simp only [Finset.mem_Ico] at ht0 ⊢
          omega
        · intro a _ b _ hab
          omega
        · intro t ht
          simp only [Finset.mem_Ico] at ht
          exact ⟨t - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro t0 ht0
          have hlt : tH < t0 + 1 := by
            simp only [Finset.mem_Ico] at ht0
            omega
          simp only [Nat.add_sub_cancel, decide_eq_true hlt, Bool.true_and]
          by_cases hp0 : p t0 = true
          · simp [hp0]
          · simp only [Bool.not_eq_true] at hp0
            simp [hp0, hm t0 ht0 hp0]
      exact hBij
    · have hEmpty1 : Finset.Ico (healEpoch tL) (N + 1) = ∅ :=
        Finset.Ico_eq_empty (by dsimp [tH] at hLe; omega)
      have hEmpty2 : Finset.Ico tH (N + 2) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hEmpty1, hEmpty2]
      simp

/-- Exact equality between `slotDispatchGen` and `bucketSlotIsMain` / `bucketSlotEpoch` packing on
`Finset.Ico (healEpoch tL) (N + 2)`. -/
theorem sum_ico_forged_add_main_eq_bucketSlotPacked
    {Δbucket : ℕ} (hΔ : 4 ≤ Δbucket) (tL : Option ℕ) (par : Bool) (N : ℕ)
    (f_forged f_main : ℕ → ℝ≥0∞)
    (hf : ∀ t0 ∈ Finset.Ico (healEpoch tL) (N + 2),
      isActiveBucketEpoch Δbucket tL par t0 = false → f_forged t0 = 0)
    (hm : ∀ t0 ∈ Finset.Ico (healEpoch tL) (N + 1),
      isActiveBucketEpoch Δbucket tL par t0 = false → f_main t0 = 0) :
    (∑ t0 ∈ Finset.Ico (healEpoch tL) (N + 2), f_forged t0) +
      (∑ t0 ∈ Finset.Ico (healEpoch tL) (N + 1), f_main t0) =
      ∑ t ∈ Finset.Ico (healEpoch tL) (N + 2),
        if bucketSlotIsMain Δbucket tL par t then
          f_main (bucketSlotEpoch Δbucket tL par t)
        else
          f_forged (bucketSlotEpoch Δbucket tL par t) := by
  rw [sum_ico_forged_add_main_eq_slotDispatchGen hΔ tL par N f_forged f_main hf hm]
  refine Finset.sum_congr rfl fun t ht => ?_
  unfold slotDispatchGen bucketSlotEpoch bucketSlotIsMain
  by_cases hAct : isActiveBucketEpoch Δbucket tL par t = true
  · simp [hAct]
  · simp only [Bool.not_eq_true] at hAct
    by_cases hPrev : (decide (healEpoch tL < t) && isActiveBucketEpoch Δbucket tL par (t - 1)) = true
    · simp [hAct, hPrev]
    · simp only [Bool.not_eq_true] at hPrev
      simp [hAct, hPrev, hf t ht hAct]

end ParitySlotBijection

/-! ## 2. Shallow Split `Main` / `ForgedHdr` & Parity-Packed `(tL, par)` Bucket Theorems -/

section ShallowBucketPRNG

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}

private theorem evalDist_bind_le_add_of_support_2a {α : Type} (p : ProbComp α)
    (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
        ≤ ∫⁻ u, (𝒟[r u >>= G₁] {true} + 𝒟[r u >>= G₂] {true}) ∂𝒟[query t] :=
          MeasureTheory.lintegral_mono fun u =>
            ih u fun a ha => h a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)
      _ = (∫⁻ u, 𝒟[r u >>= G₁] {true} ∂𝒟[query t]) +
          (∫⁻ u, 𝒟[r u >>= G₂] {true} ∂𝒟[query t]) :=
          MeasureTheory.lintegral_add_left Measurable.of_discrete _

private def postPBucketDF [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δcka : ℕ) (tL : Option ℕ) (useAt : Bool)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ) :
    Bool :=
  if useAt then
    authOutBucketPaperAt (2 + Δcka) tL (healEpoch tL) st
  else
    authOutBucketPaper (2 + Δcka) tL st

private def frozenInrOutDF
    (q : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain) :
    (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q :=
  match q with
  | .inl (.inl (.inl (.inl (.inl _)))) => none
  | .inl (.inl (.inl (.inl (.inr _)))) => none
  | .inl (.inl (.inl (.inr _))) => none
  | .inl (.inl (.inr _)) => none
  | .inl (.inr _) => none
  | .inr _ => none

private theorem implEDFPaperBucketMode_frozen_inl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (n : unifSpec.Domain)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (AuthL11.pImpl prng)
      (((implEDFPaperBucketMode hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
        gMain isHonestHdrPRNGBucket) (.inl n)).run st)).run sp =
    (query (spec := unifSpec) n >>= fun u => pure ((u, st), sp)) := by
  rcases st with ⟨es, winEp⟩
  have hw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  cases gMain <;>
    simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      coinsE, AuthL11.pImpl, StateT.run_lift, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]

private theorem implEDFPaperBucketMode_frozen_inr
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (q : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ)
    (hfr : es.abort = true ∨ es.g.win = true) :
    ((implEDFPaperBucketMode hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
      gMain isHonestHdrPRNGBucket) (.inr q)).run (es, winEp) =
      pure (frozenInrOutDF q, (es, winEp)) := by
  have hw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  have hraw : ((implEDFPaperBucketRaw hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par))
      (.inr q)).run es = pure (frozenInrOutDF q, es) := by
    rcases q with ((((⟨P, m, r0⟩ | x) | x) | x) | P) | ⟨P, c, c'⟩
    · rcases hfr with h | h <;>
        simp [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket, frozenInrOutDF, h,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
    · simp [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, frozenInrOutDF, StateT.run_pure]
    · rcases hfr with h | h <;>
        simp [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE, frozenInrOutDF, h,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
    · rcases hfr with h | h <;>
        simp [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE, frozenInrOutDF, h,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
    · rcases hfr with h | h <;>
        simp [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket, frozenInrOutDF, h,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
    · rcases hfr with h | h <;>
        simp [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE, frozenInrOutDF, h,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
  cases gMain <;>
    simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, hraw]

private theorem implEDFPaperBucketMode_frozen_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk₁ hk₂ : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain₁ gMain₂ : Bool)
    {α : Type} (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (hfr : es.abort = true ∨ es.g.win = true) :
    (simulateQ (AuthL11.pImpl prng)
      ((simulateQ (implEDFPaperBucketMode hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
        gMain₁ isHonestHdrPRNGBucket) oa).run (es, winEp))).run sp =
    (simulateQ (AuthL11.pImpl prng)
      ((simulateQ (implEDFPaperBucketMode hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
        gMain₂ isHonestHdrPRNGBucket) oa).run (es, winEp))).run sp := by
  induction oa using OracleComp.inductionOn generalizing sp with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    cases q with
    | inl n =>
      rw [implEDFPaperBucketMode_frozen_inl prng hk₁ Δcka qep maxSkip tL par gMain₁ n (es, winEp) sp,
        implEDFPaperBucketMode_frozen_inl prng hk₂ Δcka qep maxSkip tL par gMain₂ n (es, winEp) sp]
      simp only [bind_assoc, pure_bind]
      congr 1; funext u
      exact ih u sp
    | inr q' =>
      rw [implEDFPaperBucketMode_frozen_inr hk₁ Δcka qep maxSkip tL par gMain₁ q' es winEp hfr,
        implEDFPaperBucketMode_frozen_inr hk₂ Δcka qep maxSkip tL par gMain₂ q' es winEp hfr]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih (frozenInrOutDF q') sp

private def runPostPBucketDF [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain useAt : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool :=
  (simulateQ (AuthL11.pImpl prng)
    ((simulateQ (implEDFPaperBucketMode hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
      gMain isHonestHdrPRNGBucket) oa).run st)).run sp >>=
    fun r => pure (postPBucketDF Δcka tL useAt r.1.2)

private theorem runPostPBucketDF_frozen_le_forged
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk₁ hk₂ : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain₁ gMain₂ : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (hfr : es.abort = true ∨ es.g.win = true) :
    𝒟[runPostPBucketDF prng hk₁ Δcka qep maxSkip tL par gMain₁ true oa (es, winEp) sp] {true} ≤
      𝒟[runPostPBucketDF prng hk₂ Δcka qep maxSkip tL par gMain₂ false oa (es, winEp) sp] {true} := by
  dsimp only [runPostPBucketDF]
  rw [implEDFPaperBucketMode_frozen_eq prng hk₁ hk₂ Δcka qep maxSkip tL par gMain₁ gMain₂
    oa es winEp sp hfr]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun r _ => ?_
  dsimp only [postPBucketDF, authOutBucketPaperAt]
  cases authOutBucketPaper (2 + Δcka) tL r.1.2 <;> simp [Pi.single_apply]
  split_ifs <;> simp

private theorem runPostPBucketDF_dead_zero
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain useAt : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K)
    (hfr : st.1.abort = true ∨ st.1.g.win = true)
    (hpost : postPBucketDF Δcka tL useAt st = false) :
    𝒟[runPostPBucketDF prng hk Δcka qep maxSkip tL par gMain useAt oa st sp] {true} = 0 := by
  rcases st with ⟨es, winEp⟩
  dsimp only at hfr
  induction oa using OracleComp.inductionOn generalizing sp with
  | pure a =>
    simp [runPostPBucketDF, hpost]
  | query_bind q cont ih =>
    dsimp only [runPostPBucketDF]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    cases q with
    | inl n =>
      rw [implEDFPaperBucketMode_frozen_inl prng hk Δcka qep maxSkip tL par gMain n (es, winEp) sp]
      simp only [bind_assoc, pure_bind]
      exact AuthL11.evalDist_bind_eq_zero _ _ fun u _ => ih u sp
    | inr q' =>
      rw [implEDFPaperBucketMode_frozen_inr hk Δcka qep maxSkip tL par gMain q' es winEp hfr]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih (frozenInrOutDF q') sp

private theorem runPostPBucketDF_frozen_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk₁ hk₂ : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain₁ gMain₂ useAt : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (hfr : es.abort = true ∨ es.g.win = true) :
    runPostPBucketDF prng hk₁ Δcka qep maxSkip tL par gMain₁ useAt oa (es, winEp) sp =
      runPostPBucketDF prng hk₂ Δcka qep maxSkip tL par gMain₂ useAt oa (es, winEp) sp := by
  dsimp only [runPostPBucketDF]
  rw [implEDFPaperBucketMode_frozen_eq prng hk₁ hk₂ Δcka qep maxSkip tL par gMain₁ gMain₂
    oa es winEp sp hfr]

private structure UnsplitInvDF [DecidableEq T] (Δcka qep : ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    Prop where
  abort_false : es.abort = false
  win_false : es.g.win = false
  id_eq : ∀ P, (es.g.st P).id = P
  tcur_eq : ∀ P, (es.g.st P).tcur = es.g.epoch P
  root_some : ∀ P, ((es.g.st P).root).isSome = true
  cache_some : ∀ m Tc σc kc, es.h.cache m = some (Tc, σc, kc) → σc.isSome = true
  epoch_le_qep : ∀ P, es.g.epoch P ≤ qep
  cache_gt : ∀ m, max (es.g.epoch .A) (es.g.epoch .B) < m → es.h.cache m = none
  epoch_le : ∀ P, es.g.epoch P ≤ es.g.epoch P.other + 1
  epoch_sends : ∀ P, es.g.epoch P.other < es.g.epoch P → P.sendsIn (es.g.epoch P) = true
  sender_cur : ∀ P, 1 ≤ es.g.epoch P → P.sendsIn (es.g.epoch P) = true →
    isHonestHdrPRNGBucket es.h (es.g.epoch P, (es.g.st P).curCkaMsg) = true
  trans_inv : ∀ r ∈ es.g.trans,
    r.ct.1.1 = r.pos.epoch ∧ r.pos.epoch ≤ es.g.epoch r.pos.sender ∧
    (1 ≤ r.pos.epoch → isHonestHdrPRNGBucket es.h r.ct.1 = true)
  comp_inv : ∀ pos ∈ es.g.comp, healedBy es.g.tL (2 + Δcka) pos.epoch = false

private theorem sendsIn_succ_not_2a_df (P : Party) (e : ℕ) :
    P.sendsIn (e + 1) = !P.sendsIn e := by
  unfold Party.sendsIn
  by_cases h0 : e % 2 = 1
  · have h1 : (e + 1) % 2 = 0 := by omega
    cases P <;> simp [h0, h1]
  · have h0' : e % 2 = 0 := by omega
    have h1 : (e + 1) % 2 = 1 := by omega
    cases P <;> simp [h0', h1]

private theorem UnsplitInvDF.synced_of_sendsIn_succ [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) {P : Party}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true) :
    es.g.epoch P.other = es.g.epoch P ∧
      max (es.g.epoch .A) (es.g.epoch .B) = es.g.epoch P := by
  have heq : es.g.epoch P.other = es.g.epoch P := by
    by_cases hlt1 : es.g.epoch P.other < es.g.epoch P
    · have hs := hI.epoch_sends P hlt1
      have hsucc := sendsIn_succ_not_2a_df P (es.g.epoch P)
      rw [hs] at hsucc
      simp [hsend] at hsucc
    · by_cases hlt2 : es.g.epoch P < es.g.epoch P.other
      · have hle := hI.epoch_le P.other
        rw [Party.other_other] at hle
        have hop : es.g.epoch P.other = es.g.epoch P + 1 := by omega
        have hs := hI.epoch_sends P.other (by rw [Party.other_other]; exact hlt2)
        have hso : P.other.sendsIn (es.g.epoch P + 1) = false := by
          unfold Party.sendsIn at hsend
          unfold Party.sendsIn Party.other
          by_cases h0 : (es.g.epoch P + 1) % 2 = 1 <;>
            (have h0' : (es.g.epoch P + 1) % 2 = 0 ∨ (es.g.epoch P + 1) % 2 = 1 := by omega;
             cases P <;> rcases h0' with h00 | h01 <;> simp_all)
        rw [hop, hso] at hs
        simp at hs
      · omega
  refine ⟨heq, ?_⟩
  cases P with
  | A => change es.g.epoch .B = es.g.epoch .A at heq; omega
  | B => change es.g.epoch .A = es.g.epoch .B at heq; omega

private theorem rootPRNGBucketHybrid_at_tH_mem_support
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σv0 : Option Sig)
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {out : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hmem : out ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((rootPRNGBucketHybrid prng Δbucket tL par (healEpoch tL) t0 pl ik0 σv0).run h0)).run sp0)) :
    out.1.2.cache = h0.cache ∧
      ∀ σ' kVal, out.1.1 = some (σ', kVal) → σ'.isSome = true := by
  unfold rootPRNGBucketHybrid at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases h1 : healEpoch tL < t0
  · simp only [h1, ↓reduceIte] at hmem
    rcases hσv : resolveCorrRoot h0 (t0 - 1) σv0 with _ | σ <;>
      · simp only [hσv, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl
        simp
  · simp only [h1, ↓reduceIte] at hmem
    by_cases h2 : (pl || h0.corrRoot.isSome) = true
    · simp only [h2, ↓reduceIte] at hmem
      rcases hσv : resolveCorrRoot h0 (t0 - 1) σv0 with _ | σ
      · simp only [hσv, liftPBucket, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem
        rcases hmem with ⟨⟨qOut, sp1⟩, _, hmem2⟩
        cases qOut <;>
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl
            simp
      · simp only [hσv, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl
        simp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h3 : t0 = healEpoch tL
      · simp only [h3, ↓reduceIte, decide_true, Bool.and_true] at hmem
        cases htL : tL.isSome
        · simp only [htL, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hinB : inStage2BucketGen Δbucket tL par (healEpoch tL)
          · simp only [hinB, Bool.false_eq_true, ↓reduceIte, liftPBucket, StateT.run_bind,
              StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
              mem_support_bind_iff] at hmem
            rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
            cases qOut1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
              rcases hmem2 with rfl; simp
            | some kOut =>
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc,
                pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem2
              rcases hmem2 with ⟨⟨qOut2, sp2⟩, _, hmem3⟩
              cases qOut2 <;>
                · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hmem3
                  rcases hmem3 with rfl; simp
          · simp only [hinB, ↓reduceIte, liftPBucket, StateT.run_bind,
              StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
              mem_support_bind_iff] at hmem
            rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
            cases qOut1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
              rcases hmem2 with rfl; simp
            | some pOut =>
              rcases pOut with ⟨σOut, kOut⟩
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
              rcases hmem2 with rfl; simp
        · simp only [htL, ↓reduceIte, liftPBucket, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, simulateQ_bind,
            mem_support_bind_iff] at hmem
          rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
          cases qOut1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl; simp
          | some kOut =>
            simp only [StateT.run_bind, StateT.run_lift, bind_assoc,
              pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem2
            rcases hmem2 with ⟨⟨qOut2, sp2⟩, _, hmem3⟩
            cases qOut2 <;>
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hmem3
                rcases hmem3 with rfl; simp
      · have hlt : t0 < healEpoch tL := by omega
        simp only [h3, hlt, decide_true, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, liftPBucket, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, simulateQ_bind,
          mem_support_bind_iff] at hmem
        rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
        cases qOut1 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
          rcases hmem2 with rfl; simp
        | some kOut =>
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc,
            pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem2
          rcases hmem2 with ⟨⟨qOut2, sp2⟩, _, hmem3⟩
          cases qOut2 <;>
            · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hmem3
              rcases hmem3 with rfl; simp

private theorem UnsplitInvDF.record_same [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) {P : Party}
    (hsend0 : P.sendsIn (es.g.epoch P + 1) = false)
    (st' : VP Γ T (Option Sig) SS RS) (m_msg : M) (e_ct : E)
    (hid' : st'.id = P) (htcur' : st'.tcur = es.g.epoch P)
    (hroot' : st'.root = (es.g.st P).root) (hcur' : st'.curCkaMsg = (es.g.st P).curCkaMsg) :
    let hdr : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let recE : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m_msg, (hdr, e_ct)⟩
    UnsplitInvDF Δcka qep { es with g := es.g.record (2 + Δcka) P st' recE false } where
  abort_false := hI.abort_false
  win_false := hI.win_false
  id_eq Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, hid']
    · simp [GameState.record, hQ, hI.id_eq Q]
  tcur_eq Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, htcur']
    · simp [GameState.record, hQ, hI.tcur_eq Q]
  root_some Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, hroot', hI.root_some P]
    · simp [GameState.record, hQ, hI.root_some Q]
  cache_some := hI.cache_some
  epoch_le_qep := hI.epoch_le_qep
  cache_gt := hI.cache_gt
  epoch_le := hI.epoch_le
  epoch_sends := hI.epoch_sends
  sender_cur Q h1 hs := by
    by_cases hQ : Q = P
    · subst Q
      simp only [GameState.record, Function.update_self, hcur'] at hs ⊢
      exact hI.sender_cur P h1 hs
    · simp only [GameState.record, Function.update_of_ne hQ] at hs ⊢
      exact hI.sender_cur Q h1 hs
  trans_inv r hr := by
    simp only [GameState.record, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨rfl, le_rfl, fun h1 => ?_⟩
      exact hI.sender_cur P h1 (AuthL10.sendsIn_of_succ_false hsend0)
    · exact hI.trans_inv r hr
  comp_inv := AuthL10.comp_inv_record es.g (2 + Δcka) P st' _ false rfl hI.comp_inv

private theorem UnsplitInvDF.record_new [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) {P : Party}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hqep : es.g.epoch P + 1 ≤ qep)
    {s₁ : Ctx Γ T (Option Sig) SS RS M E}
    (hs1_st : s₁.st = es.g.st)
    (hs1_win : s₁.win = es.g.win)
    (hs1_ep : s₁.epoch = Function.update es.g.epoch P (es.g.epoch P + 1))
    (hs1_trans : s₁.trans = es.g.trans)
    (hs1_comp : ∀ pos ∈ s₁.comp, healedBy s₁.tL (2 + Δcka) pos.epoch = false)
    (γ' : Γ) (Tm : T) (σ' : Option Sig) (kVal : K) (vS' : Option SS)
    (m_msg : M) (e_ct : E) (h' : PRNGBucketState T Sig K I)
    (hσ' : σ'.isSome = true)
    (hcache' : h'.cache = Function.update es.h.cache (es.g.epoch P + 1) (some (Tm, σ', kVal))) :
    let m := es.g.epoch P + 1
    let st' : VP Γ T (Option Sig) SS RS :=
      { es.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := vS' }
    let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, ((m, some Tm), e_ct)⟩
    UnsplitInvDF Δcka qep { es with g := s₁.record (2 + Δcka) P st' recE false, h := h' } := by
  obtain ⟨hepO, hmax⟩ := hI.synced_of_sendsIn_succ hsend
  have hs1P : s₁.epoch P = es.g.epoch P + 1 := by simp [hs1_ep]
  have hs1O : s₁.epoch P.other = es.g.epoch P := by
    rw [hs1_ep, Function.update_of_ne (Party.other_ne P), hepO]
  have hmax1 : max (s₁.epoch .A) (s₁.epoch .B) = es.g.epoch P + 1 := by
    cases P with
    | A => change s₁.epoch .B = es.g.epoch .A at hs1O; rw [hs1P, hs1O]; omega
    | B => change s₁.epoch .A = es.g.epoch .B at hs1O; rw [hs1O, hs1P]; omega
  refine
    { abort_false := hI.abort_false
      win_false := by simp [GameState.record, hs1_win, hI.win_false]
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hI.id_eq P]
        · simp [GameState.record, hQ, hs1_st, hI.id_eq Q]
      tcur_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, Party.other_ne P, hs1_st, hs1O, ← hepO, hI.tcur_eq P.other]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hσ']
        · simp [GameState.record, hQ, hs1_st, hI.root_some Q]
      cache_some := fun k Tc σc kc hk => by
        rw [hcache'] at hk
        by_cases hkP : k = es.g.epoch P + 1
        · subst k
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hk
          rcases hk with ⟨_, rfl, _⟩
          exact hσ'
        · simp only [Function.update_of_ne hkP] at hk
          exact hI.cache_some k Tc σc kc hk
      epoch_le_qep := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P, hqep]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, hs1O, ← hepO, hI.epoch_le_qep P.other]
      cache_gt := fun k hk => by
        simp only [GameState.record, hmax1] at hk
        have hne : k ≠ es.g.epoch P + 1 := by omega
        rw [hcache', Function.update_of_ne hne]
        exact hI.cache_gt k (by omega)
      epoch_le := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P, hs1O]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, Party.other_other, hs1P, hs1O]; omega
      epoch_sends := fun Q hlt => by
        simp only [GameState.record] at hlt ⊢
        by_cases hQ : Q = P
        · subst Q; rw [hs1P]; exact hsend
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; rw [Party.other_other, hs1P, hs1O] at hlt; omega
      sender_cur := fun Q h1 hs => by
        simp only [GameState.record] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q; simp [hs1P, isHonestHdrPRNGBucket, hcache']
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q
          rw [hs1O, ← hepO] at h1 hs ⊢
          simp only [Function.update_of_ne (Party.other_ne P), hs1_st]
          have hprev := hI.sender_cur P.other h1 hs
          have hne : es.g.epoch P.other ≠ es.g.epoch P + 1 := by omega
          simpa [isHonestHdrPRNGBucket, hcache', Function.update_of_ne hne] using hprev
      trans_inv := fun r hr => by
        simp only [GameState.record, hs1_trans, List.mem_cons] at hr
        rcases hr with rfl | hr
        · refine ⟨hs1P.symm, le_rfl, fun _ => ?_⟩
          simp [isHonestHdrPRNGBucket, hcache']
        · obtain ⟨ht1, hle_r, hhon_r⟩ := hI.trans_inv r hr
          have hle_s1 : es.g.epoch r.pos.sender ≤ s₁.epoch r.pos.sender := by
            rw [hs1_ep]
            by_cases hS : r.pos.sender = P
            · subst hS; simp
            · simp [hS]
          refine ⟨ht1, le_trans hle_r hle_s1, fun h1 => ?_⟩
          have hprev := hhon_r h1
          have hle_max : es.g.epoch r.pos.sender ≤ es.g.epoch P := by
            rw [← hmax]
            cases r.pos.sender with
            | A => exact le_max_left _ _
            | B => exact le_max_right _ _
          have hne : r.ct.1.1 ≠ es.g.epoch P + 1 := by omega
          simpa [isHonestHdrPRNGBucket, hcache', Function.update_of_ne hne] using hprev
      comp_inv := AuthL10.comp_inv_record s₁ (2 + Δcka) P _ _ false rfl hs1_comp }

private theorem UnsplitInvDF.accept_old [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) {P : Party} {pos : Pos}
    (hle : pos.epoch ≤ es.g.epoch P)
    (st' : VP Γ T (Option Sig) SS RS)
    (hid' : st'.id = P) (htcur' : st'.tcur = es.g.epoch P)
    (hroot' : st'.root = (es.g.st P).root) (hcur' : st'.curCkaMsg = (es.g.st P).curCkaMsg) :
    UnsplitInvDF Δcka qep { es with g := es.g.accept P st' pos } := by
  have hep_eq : (es.g.accept P st' pos).epoch = es.g.epoch := by
    funext Q
    by_cases hQ : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, Nat.max_eq_left hle]
    · simp [GameState.accept, GameState.delete, hQ]
  refine
    { abort_false := hI.abort_false
      win_false := hI.win_false
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hid']
        · simp [GameState.accept, GameState.delete, hQ, hI.id_eq Q]
      tcur_eq := fun Q => by
        rw [hep_eq]
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, htcur']
        · simp [GameState.accept, GameState.delete, hQ, hI.tcur_eq Q]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hroot', hI.root_some P]
        · simp [GameState.accept, GameState.delete, hQ, hI.root_some Q]
      cache_some := hI.cache_some
      epoch_le_qep := fun Q => by rw [hep_eq]; exact hI.epoch_le_qep Q
      cache_gt := fun m hm => by rw [hep_eq] at hm; exact hI.cache_gt m hm
      epoch_le := fun Q => by rw [hep_eq]; exact hI.epoch_le Q
      epoch_sends := fun Q hlt => by rw [hep_eq] at hlt ⊢; exact hI.epoch_sends Q hlt
      sender_cur := fun Q h1 hs => by
        rw [hep_eq] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q
          simp only [GameState.accept, GameState.delete, Function.update_self, hcur']
          exact hI.sender_cur P h1 hs
        · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ]
          exact hI.sender_cur Q h1 hs
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        rw [hep_eq]
        exact hI.trans_inv r hr.1
      comp_inv := by
        intro pos' hp'
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hp'
        exact hI.comp_inv pos' hp'.1 }

private theorem UnsplitInvDF.accept_new [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) {P : Party} {pos : Pos}
    (heq_m : pos.epoch = es.g.epoch P + 1)
    (hle_other : pos.epoch ≤ es.g.epoch P.other)
    (hsendP : P.sendsIn pos.epoch = false)
    (st' : VP Γ T (Option Sig) SS RS)
    (hid' : st'.id = P) (htcur' : st'.tcur = pos.epoch)
    (hroot' : st'.root.isSome = true) :
    UnsplitInvDF Δcka qep { es with g := es.g.accept P st' pos } := by
  have hepO : es.g.epoch P.other = es.g.epoch P + 1 := by
    have hbound := hI.epoch_le P.other
    rw [Party.other_other] at hbound
    omega
  have hacc_ep : ∀ Q, (es.g.accept P st' pos).epoch Q = es.g.epoch P + 1 := by
    intro Q
    by_cases hQ : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, heq_m]
    · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
      subst Q; simp [GameState.accept, GameState.delete, Party.other_ne P, hepO]
  have hmax_before : max (es.g.epoch .A) (es.g.epoch .B) = es.g.epoch P + 1 := by
    cases P with
    | A => change es.g.epoch .B = es.g.epoch .A + 1 at hepO; omega
    | B => change es.g.epoch .A = es.g.epoch .B + 1 at hepO; omega
  refine
    { abort_false := hI.abort_false
      win_false := hI.win_false
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hid']
        · simp [GameState.accept, GameState.delete, hQ, hI.id_eq Q]
      tcur_eq := fun Q => by
        rw [hacc_ep Q]
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, htcur', heq_m]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.accept, GameState.delete, Party.other_ne P, hI.tcur_eq P.other, hepO]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hroot']
        · simp [GameState.accept, GameState.delete, hQ, hI.root_some Q]
      cache_some := hI.cache_some
      epoch_le_qep := fun Q => by rw [hacc_ep Q, ← hepO]; exact hI.epoch_le_qep P.other
      cache_gt := fun m hm => by
        rw [hacc_ep .A, hacc_ep .B, max_self] at hm
        exact hI.cache_gt m (by omega)
      epoch_le := fun Q => by rw [hacc_ep Q, hacc_ep Q.other]; omega
      epoch_sends := fun Q hlt => by rw [hacc_ep Q, hacc_ep Q.other] at hlt; omega
      sender_cur := fun Q h1 hs => by
        rw [hacc_ep Q] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q; rw [← heq_m, hsendP] at hs; simp at hs
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q
          rw [← hepO] at h1 hs ⊢
          simp only [GameState.accept, GameState.delete, Function.update_of_ne (Party.other_ne P)]
          exact hI.sender_cur P.other h1 hs
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        obtain ⟨ht1, hle_r, hhon_r⟩ := hI.trans_inv r hr.1
        have hle_acc : es.g.epoch r.pos.sender ≤ (es.g.accept P st' pos).epoch r.pos.sender := by
          rw [hacc_ep r.pos.sender, ← hmax_before]
          cases r.pos.sender with
          | A => exact le_max_left _ _
          | B => exact le_max_right _ _
        exact ⟨ht1, le_trans hle_r hle_acc, hhon_r⟩
      comp_inv := by
        intro pos' hp'
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hp'
        exact hI.comp_inv pos' hp'.1 }

private theorem UnsplitInvDF.afterCorr [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) (P : Party)
    (h' : PRNGBucketState T Sig K I) (hcache' : h'.cache = es.h.cache) :
    UnsplitInvDF Δcka qep { es with g := es.g.afterCorr P, h := h' } where
  abort_false := hI.abort_false
  win_false := hI.win_false
  id_eq := hI.id_eq
  tcur_eq := hI.tcur_eq
  root_some := hI.root_some
  cache_some m Tc σc kc hk := hI.cache_some m Tc σc kc (hcache' ▸ hk)
  epoch_le_qep := hI.epoch_le_qep
  cache_gt m hm := hcache' ▸ hI.cache_gt m hm
  epoch_le := hI.epoch_le
  epoch_sends := hI.epoch_sends
  sender_cur Q h1 hs := by
    have hprev := hI.sender_cur Q h1 hs
    simpa [isHonestHdrPRNGBucket, GameState.afterCorr, GameState.leak, hcache'] using hprev
  trans_inv r hr := by
    simp only [GameState.afterCorr, GameState.leak] at hr ⊢
    obtain ⟨h1, h2, h3⟩ := hI.trans_inv r hr
    exact ⟨h1, h2, fun hge => by simpa [isHonestHdrPRNGBucket, hcache'] using h3 hge⟩
  comp_inv := AuthL10.comp_inv_afterCorr es.g (2 + Δcka) (by omega) P
    (fun r hr => (hI.trans_inv r hr).2.1) hI.comp_inv

private def PostTHLeakDF {St Msg C : Type} (tL : Option ℕ) (g : GameState St Msg C) : Prop :=
  ∃ l ∈ g.leaks, ltOpt tL l = true ∧ ∃ cur, g.tL = some cur ∧ l ≤ cur

private theorem PostTHLeakDF.leak {St Msg C : Type} {tL : Option ℕ} {g : GameState St Msg C}
    (hPL : PostTHLeakDF tL g) (m : ℕ) : PostTHLeakDF tL (g.leak m) := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  refine ⟨l, List.mem_cons_of_mem _ hl_mem, hlt, max cur m, ?_, le_trans hle (le_max_left _ _)⟩
  simp [GameState.leak, htL, CryptoGames.SM.maxOpt]

private theorem PostTHLeakDF.afterCorr_preserve {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (hPL : PostTHLeakDF tL g) (P : Party) :
    PostTHLeakDF tL (g.afterCorr P) := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  refine ⟨l, List.mem_cons_of_mem _ hl_mem, hlt, max cur (max (g.epoch .A) (g.epoch .B)), ?_,
    le_trans hle (le_max_left _ _)⟩
  simp [GameState.afterCorr, GameState.leak, htL, CryptoGames.SM.maxOpt]

private theorem PostTHLeakDF.afterCorr_of_ge_tH {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (P : Party)
    (hge : healEpoch tL ≤ max (g.epoch .A) (g.epoch .B)) :
    PostTHLeakDF tL (g.afterCorr P) := by
  let eMax := max (g.epoch .A) (g.epoch .B)
  let L := CryptoGames.SM.maxOpt g.tL eMax
  have heMax_le : eMax ≤ L := by
    dsimp only [L]; cases g.tL <;> simp [CryptoGames.SM.maxOpt]
  have hlt : ltOpt tL L = true := by
    cases tL with
    | none => rfl
    | some l =>
      simp only [healEpoch] at hge
      simp only [ltOpt, decide_eq_true_eq]
      omega
  refine ⟨L, ?_, hlt, L, ?_, le_rfl⟩
  · simp [GameState.afterCorr, GameState.leak, L, eMax]
  · simp [GameState.afterCorr, GameState.leak, L, eMax]

private theorem authOK_false_of_postTHLeak_df {St Msg C : Type} {Δcka : ℕ} {tL : Option ℕ}
    {g g' : GameState St Msg C} (P : Party)
    (hPL : PostTHLeakDF tL g)
    (hsafe : g.safeInj (2 + Δcka) = true)
    (hleaks : g'.leaks = g.leaks) :
    authLosingConditionsAvoided (2 + Δcka) tL (g.epoch P + 1) g' = false := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  simp only [GameState.safeInj, htL, healedBy, decide_eq_true_eq] at hsafe
  have hmin : min (g.epoch .A) (g.epoch .B) ≤ g.epoch P := by cases P <;> simp
  have hlt_win : l < g.epoch P + 1 := by omega
  have hl_mem' : l ∈ g'.leaks := hleaks ▸ hl_mem
  by_contra htrue
  simp only [Bool.not_eq_false] at htrue
  unfold authLosingConditionsAvoided at htrue
  simp only [Bool.and_eq_true] at htrue
  have hall := List.all_eq_true.mp htrue.1.2 l hl_mem'
  simp [hlt, hlt_win] at hall

private theorem startRecv_main_eq_hybrid_of_honest_df
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (Tn : T)
    (h0 : PRNGBucketState T Sig K I)
    (hhon : isHonestHdrPRNGBucket h0 (t0, some Tn) = true)
    (hc_some : ∀ m Tc σc kc, h0.cache m = some (Tc, σc, kc) → σc.isSome = true) :
    ∃ σc' kVal,
      σc'.isSome = true ∧
      ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startRecv ctx P t0 γ0 σv0 Tn).run h0 =
        pure (some (some ((cka.receive γ0 Tn).1, σc', fs.initReceiver kVal)), h0) ∧
      ((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).startRecv ctx P t0 γ0 σv0 Tn).run h0 =
        pure (some (some ((cka.receive γ0 Tn).1, σc', fs.initReceiver kVal)), h0) := by
  rcases hcache : h0.cache t0 with _ | ⟨Tc, σc, kVal⟩
  · simp [isHonestHdrPRNGBucket, hcache] at hhon
  · have hTc : Tc = Tn := by simpa [isHonestHdrPRNGBucket, hcache] using hhon
    subst Tc
    have hσc := hc_some t0 Tn σc kVal hcache
    rcases σc with _ | σ
    · simp at hσc
    · refine ⟨some σ, kVal, rfl, ?_, ?_⟩
      · simp [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hcache, resolveCorrRoot,
          StateT.run_bind, StateT.run_get, StateT.run_pure]
      · simp [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hcache, resolveCorrRoot,
          StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem vRecv_main_hybrid_of_not_newForged_df
    [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (s : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E)))
    (h0 : PRNGBucketState T Sig K I)
    (hc_some : ∀ m Tc σc kc, h0.cache m = some (Tc, σc, kc) → σc.isSome = true)
    (hnf : (decide (c.1.1 = s.tcur + 1) && !isHonestHdrPRNGBucket h0 c.1) = false) :
    ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c rec).run h0 =
      pure (some none, h0) ∧
     (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c rec).run h0 =
      pure (some none, h0)) ∨
    (∃ st' i' m',
      ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c rec).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0) ∧
       (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c rec).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0)) ∧
      s.id.sendsIn c.1.1 = false ∧
      c.1.1 ≤ s.tcur + 1 ∧
      st'.id = s.id ∧
      st'.tcur = max s.tcur c.1.1 ∧
      st'.curCkaMsg = s.curCkaMsg ∧
      (c.1.1 = s.tcur + 1 → st'.root.isSome = true) ∧
      (c.1.1 ≠ s.tcur + 1 → st'.root = s.root)) := by
  unfold vRecv
  by_cases hsend : s.id.sendsIn c.1.1 = true
  · left; constructor <;> simp only [hsend, Bool.true_or, ↓reduceIte, StateT.run_pure]
  · simp only [Bool.not_eq_true] at hsend
    by_cases hgt : s.tcur + 1 < c.1.1
    · left
      constructor <;>
        simp only [hsend, Bool.false_or, decide_eq_true hgt, ↓reduceIte, StateT.run_pure]
    · have hgt_f : decide (s.tcur + 1 < c.1.1) = false := decide_eq_false hgt
      have h_fsRecv : ∀ ctx' P' t' rs h e ic,
          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).fsRecv
            ctx' P' t' rs h e ic = pure (some (fs.receive rs h e)) := fun _ _ _ _ _ _ _ => rfl
      have hm_fsRecv : (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)).fsRecv =
          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).fsRecv := rfl
      by_cases hnew : c.1.1 = s.tcur + 1
      · have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = x :=
          fun x y => by split <;> [rfl; contradiction]
        have hhon : isHonestHdrPRNGBucket h0 c.1 = true := by simpa [hnew] using hnf
        rcases hTn : c.1.2 with _ | Tn
        · simp [isHonestHdrPRNGBucket, hTn] at hhon
        · have hc_pair : (c.1.1, some Tn) = c.1 := Prod.ext rfl hTn.symm
          have hhon' : isHonestHdrPRNGBucket h0 (c.1.1, some Tn) = true := hc_pair.symm ▸ hhon
          obtain ⟨σc', kVal, hσc', hsH, hsM⟩ := startRecv_main_eq_hybrid_of_honest_df
            cka prng fs Δcka qep tL par (healEpoch tL) ctx P c.1.1 s.γ s.root Tn h0 hhon' hc_some
          rcases hfs : fs.receive (fs.initReceiver kVal) c.1 c.2 with _ | ⟨v', i', m'⟩
          · left; constructor
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                Function.update_self, h_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, hsM, StateT.run_pure, pure_bind,
                Function.update_self, hm_fsRecv, h_fsRecv, hfs]
          · right
            let s₁ : VP Γ T (Option Sig) SS RS :=
              { s with tcur := c.1.1, γ := (cka.receive s.γ Tn).1, root := σc',
                       vR := Function.update s.vR c.1.1 (some (fs.initReceiver kVal)) }
            refine ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, i', m',
              ⟨?_, ?_⟩, hsend, by omega, rfl, by dsimp [s₁]; omega, rfl,
              fun _ => hσc', fun hne => absurd hnew hne⟩
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                Function.update_self, h_fsRecv, hfs, s₁]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, hsM, StateT.run_pure, pure_bind,
                Function.update_self, hm_fsRecv, h_fsRecv, hfs, s₁]
      · have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = y :=
          fun x y => by split <;> [contradiction; rfl]
        rcases hvR : s.vR c.1.1 with _ | v
        · left; constructor <;>
            simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, StateT.run_pure, pure_bind, hvR]
        · rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · left; constructor
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_pure, pure_bind, hvR, h_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_pure, pure_bind, hvR, hm_fsRecv, h_fsRecv, hfs]
          · right
            refine ⟨{ s with vR := Function.update s.vR c.1.1 (some v') }, i', m',
              ⟨?_, ?_⟩, hsend, by omega, rfl, by dsimp; omega, rfl,
              fun heq => absurd heq hnew, fun _ => rfl⟩
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_pure, pure_bind, hvR, h_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_pure, pure_bind, hvR, hm_fsRecv, h_fsRecv, hfs]

private theorem healEpoch_lt_of_admissible_ne_df (Δbucket : ℕ) (hΔ : 2 ≤ Δbucket)
    (tL : Option ℕ) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hadm : lastLeakGuessAdmissible Δbucket tL t0 = true)
    (hne : (tL.isSome && decide (t0 = healEpoch tL)) = false) :
    healEpoch tL < t0 := by
  cases tL with
  | none => simp only [healEpoch]; omega
  | some l =>
    have hne' : t0 ≠ l + 2 := by
      intro heq; subst heq; simp [healEpoch] at hne
    simp [lastLeakGuessAdmissible, healedBy, healEpoch] at hadm ⊢
    omega

private theorem vRecv_newForged_cases_df
    [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (s : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (h0 : PRNGBucketState T Sig K I)
    (hroot : s.root.isSome = true)
    (hqep : s.tcur ≤ qep)
    (hnf : (decide (c.1.1 = s.tcur + 1) && !isHonestHdrPRNGBucket h0 c.1) = true) :
    ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c none).run h0 =
      pure (some none, h0) ∧
     (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c none).run h0 =
      pure (some none, h0)) ∨
    ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c none).run h0 =
      pure (none, h0)) ∨
    (∃ st' i' m',
      (vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c none).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0) ∧
      (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)) ctx P s c none).run h0 =
        pure (some none, h0) ∧
      inStage2Bucket Δcka tL par c.1.1 = true ∧
      c.1.1 = s.tcur + 1) := by
  have hnew : c.1.1 = s.tcur + 1 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnf; exact hnf.1
  have hhon_f : isHonestHdrPRNGBucket h0 c.1 = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnf; exact hnf.2
  have hgt_f : decide (s.tcur + 1 < c.1.1) = false := decide_eq_false (by omega)
  have hqep_f : decide (qep + 1 < c.1.1) = false := decide_eq_false (by omega)
  have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = x :=
    fun x y => by split <;> [rfl; contradiction]
  have h_fsRecv : ∀ ctx' P' t' rs h e ic,
      (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).fsRecv
        ctx' P' t' rs h e ic = pure (some (fs.receive rs h e)) := fun _ _ _ _ _ _ _ => rfl
  rcases hroot_eq : s.root with _ | σ
  · simp [hroot_eq] at hroot
  · unfold vRecv
    by_cases hsend : s.id.sendsIn c.1.1 = true
    · left; constructor <;> simp only [hsend, Bool.true_or, ↓reduceIte, StateT.run_pure]
    · simp only [Bool.not_eq_true] at hsend
      rcases hTn : c.1.2 with _ | Tn
      · left; constructor <;>
          simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            hnew_ite, StateT.run_pure, pure_bind]
      · by_cases hinB : inStage2Bucket Δcka tL par c.1.1 = true
        · have hadm : lastLeakGuessAdmissible (3 + Δcka) tL c.1.1 = true := by
            simp only [inStage2Bucket, Bool.and_eq_true] at hinB; exact hinB.1
          have hinBGen : (lastLeakGuessAdmissible (3 + Δcka) tL c.1.1 &&
              (partyPar (Party.senderOf c.1.1) == par)) = true := hinB
          by_cases htH : (tL.isSome && decide (c.1.1 = healEpoch tL)) = true
          · have hsH : ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 = pure (none, h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, hqep_f, Bool.not_false, hinBGen, Bool.and_self,
                  ↓reduceIte, htH, StateT.run_pure]
              · have htc_ne : tCached ≠ Tn := by
                  intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hqep_f, Bool.not_false,
                  hinBGen, Bool.and_self, htH, StateT.run_pure]
            right; left
            simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind]
          · simp only [Bool.not_eq_true] at htH
            have hlt_tH : healEpoch tL < c.1.1 :=
              healEpoch_lt_of_admissible_ne_df (3 + Δcka) (by omega) tL c.1.1 (by omega) hadm htH
            have hsM : ((hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, htH, Bool.and_false, Bool.false_eq_true,
                  ↓reduceIte, StateT.run_pure]
              · have htc_ne : tCached ≠ Tn := by
                  intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, htH, Bool.and_false,
                  Bool.false_eq_true, StateT.run_pure]
            let kk := cka.receive s.γ Tn
            let p := prng.up σ kk.2
            have hsH : ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 =
                pure (some (some (kk.1, some p.1, fs.initReceiver p.2)), h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, hqep_f, Bool.not_false, hinBGen, Bool.and_self,
                  ↓reduceIte, htH, Bool.false_eq_true, decide_eq_true hlt_tH, Bool.or_true,
                  hroot_eq, resolveCorrRoot, StateT.run_pure, kk, p]
              · have htc_ne : tCached ≠ Tn := by
                  intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hqep_f, Bool.not_false,
                  hinBGen, Bool.and_self, htH, Bool.false_eq_true, decide_eq_true hlt_tH,
                  Bool.or_true, hroot_eq, resolveCorrRoot, StateT.run_pure, kk, p]
            rcases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with _ | ⟨v', i', m'⟩
            · left; refine ⟨?_, ?_⟩
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                  Function.update_self, h_fsRecv, hfs]
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, StateT.run_bind, hsM, StateT.run_pure, pure_bind]
            · right; right
              let s₁ : VP Γ T (Option Sig) SS RS :=
                { s with tcur := c.1.1, γ := kk.1, root := some p.1,
                         vR := Function.update s.vR c.1.1 (some (fs.initReceiver p.2)) }
              refine ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, i', m',
                ?_, ?_, hinB, hnew⟩
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                  Function.update_self, h_fsRecv, hfs, s₁]
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, StateT.run_bind, hsM, StateT.run_pure, pure_bind]
        · simp only [Bool.not_eq_true] at hinB
          have hinBGen : (lastLeakGuessAdmissible (3 + Δcka) tL c.1.1 &&
              (partyPar (Party.senderOf c.1.1) == par)) = false := hinB
          have hinBGen2 : inStage2BucketGen (3 + Δcka) tL par c.1.1 = false := hinB
          have hsH : ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
              ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
            rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
            · simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                StateT.run_get, pure_bind, hcache, hinBGen, Bool.and_false, Bool.false_eq_true,
                ↓reduceIte, StateT.run_pure]
            · have htc_ne : tCached ≠ Tn := by
                intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
              simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, StateT.run_bind,
                StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hinBGen, Bool.and_false,
                Bool.false_eq_true, StateT.run_pure]
          have hsM : ((hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
              ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
            rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
            · simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, StateT.run_bind,
                StateT.run_get, pure_bind, hcache, hinBGen2, Bool.and_false, Bool.false_and,
                Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
            · have htc_ne : tCached ≠ Tn := by
                intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
              simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, StateT.run_bind,
                StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hinBGen2, Bool.and_false,
                Bool.false_and, Bool.false_eq_true, StateT.run_pure]
          left; constructor
          · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, StateT.run_bind, hsH, StateT.run_pure, pure_bind]
          · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, StateT.run_bind, hsM, StateT.run_pure, pure_bind]

private theorem liftH_run_df
    {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS α : Type}
    (x : HM tspec HS α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) :=
  rfl

private theorem commitE_trivial_run_df
    {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (hcom : ∀ s P old new, hk.commit s P old new = pure (some new))
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS) :
    (commitE hk s P old new pos).run es = pure (some (s.accept P new pos), es) := by
  have hAcc_st : { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
    have hup : Function.update (s.accept P new pos).st P new = (s.accept P new pos).st := by
      simp [GameState.accept]
    rw [hup]
  have hes_eq : { es with h := es.h } = es := by cases es; rfl
  simp only [commitE, liftH_run_df, hcom, StateT.run_bind, StateT.run_pure, pure_bind,
    hAcc_st]

private theorem startSend_support_df
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ) (γ : Γ) (σv : Option Sig)
    (r0 : Option CCoins) (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {out : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K}
    (hout : out ∈ support ((simulateQ (AuthL11.pImpl prng)
      (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startSend
        ctx P m γ σv r0).run h0)).run sp)) :
    out.1.1 = none ∨
      ∃ coins σ' kVal,
        out.1.1 = some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', fs.initSender kVal) ∧
        σ'.isSome = true ∧
        out.1.2.cache = Function.update h0.cache m (some ((cka.send γ coins).2.1, σ', kVal)) := by
  unfold hooksPRNGBucketHybrid hooksPRNGBucketHybridGen at hout
  dsimp only at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  let h_lc : PRNGBucketState T Sig K I :=
    if (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < m)) = true then
      { h0 with lc := some (m - 1) }
    else h0
  have hlc_cache : h_lc.cache = h0.cache := by dsimp only [h_lc]; split <;> rfl
  have hout_lc : out ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((match r0 with
        | some coins => do
          let c := cka.send γ coins
          match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par (healEpoch tL) m (postLeak tL ctx) c.2.2 σv with
          | none => return none
          | some (σ', kVal) =>
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache m (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)
        | none => do
          let coins ← StateT.lift (sampleT CCoins)
          let c := cka.send γ coins
          match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par (healEpoch tL) m (postLeak tL ctx) c.2.2 σv with
          | none => return none
          | some (σ', kVal) =>
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache m (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run h_lc)).run sp) := by
    dsimp only [h_lc]
    by_cases hcond : (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < m)) = true <;>
      simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
        pure_bind] at hout ⊢ <;>
      exact hout
  have hcoins : ∃ coins : CCoins, out ∈ support (do
      let p ← (simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid prng (3 + Δcka) tL par (healEpoch tL) m (postLeak tL ctx)
          (cka.send γ coins).2.2 σv).run h_lc)).run sp
      (simulateQ (AuthL11.pImpl prng)
        (StateT.run (match p.1.1 with
          | none => pure none
          | some (σ', kVal) => do
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache m (some ((cka.send γ coins).2.1, σ', kVal)) }
            return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', fs.initSender kVal))
          p.1.2)).run p.2) := by
    cases r0 with
    | some coins =>
      simp only [StateT.run_bind, simulateQ_bind] at hout_lc
      exact ⟨coins, hout_lc⟩
    | none =>
      simp only [StateT.run_bind, simulateQ_bind, bind_assoc,
        AuthL11.simulateQ_pImpl_run_lift_sampleT, pure_bind] at hout_lc
      rw [mem_support_bind_iff] at hout_lc
      rcases hout_lc with ⟨coins, _, hout'⟩
      exact ⟨coins, hout'⟩
  rcases hcoins with ⟨coins, hout'⟩
  rw [mem_support_bind_iff] at hout'
  rcases hout' with ⟨⟨⟨rootAns, h₁⟩, sp₁⟩, hroot_mem, hout2⟩
  obtain ⟨hcache1, hsome1⟩ := rootPRNGBucketHybrid_at_tH_mem_support prng (3 + Δcka) tL par m
    (postLeak tL ctx) (cka.send γ coins).2.2 σv h_lc sp hroot_mem
  cases rootAns with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    exact Or.inl rfl
  | some pOut =>
    rcases pOut with ⟨σ', kVal⟩
    have hσ' : σ'.isSome = true := hsome1 σ' kVal rfl
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    refine Or.inr ⟨coins, σ', kVal, rfl, hσ', ?_⟩
    dsimp only
    rw [hcache1, hlc_cache]

private theorem implEDFPaperBucketMode_transmit_main_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × M × Option CCoins)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
      (.inr (.inl (.inl (.inl (.inl (.inl x))))))).run (es, none)) =
    (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
      (.inr (.inl (.inl (.inl (.inl (.inl x))))))).run (es, none)) := by
  have hv : vSend (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)) =
      vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) := rfl
  simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
    QueryImpl.add_apply, transmitEBucket, hv]

private theorem implEDFPaperBucketMode_transmit_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × M × Option CCoins)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
      (.inr (.inl (.inl (.inl (.inl (.inl x))))))).run (es, none)) =
    (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
      (.inr (.inl (.inl (.inl (.inl (.inl x))))))).run (es, none)) := by
  have hv : vSend (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL)) =
      vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) := rfl
  simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
    implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket, hv]

private theorem implEDFPaperBucketMode_chall_eq
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (x : Party × M × M × Option CCoins)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (((implEDFPaperBucketMode hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL par)
      gMain isHonestHdrPRNGBucket)
      (.inr (.inl (.inl (.inl (.inl (.inr x))))))).run (es, none)) = pure (none, (es, none)) := by
  cases gMain <;>
    simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      QueryImpl.add_apply, challEBucket, StateT.run_pure]

private theorem transmit_support_unsplitInv_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (r0 : Option CCoins)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hI : UnsplitInvDF Δcka qep es)
    {r : (Option (Header T × E) ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r0)))))))).run (es, none))).run sp)) :
    r.1.2.1.abort = true ∨
      ∃ es', r.1.2 = (es', none) ∧ UnsplitInvDF Δcka qep es' ∧
        (PostTHLeakDF tL es.g → PostTHLeakDF tL es'.g) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have h_fsSend : ∀ ctx' P' t' ss h m ic,
      (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).fsSend
        ctx' P' t' ss h m ic = pure (some (fs.send ss h m)) := fun _ _ _ _ _ _ _ => rfl
  simp only [implEDFPaperBucketMode, withWinEpDFMode, ↓reduceIte, withWinEpDF,
    dfQueryTargetEpoch, implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
    StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hab0, hwin0, Bool.or_self,
    Bool.false_eq_true] at hr
  by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
  · by_cases hqep : qep < es.g.epoch P + 1
    · simp only [GameState.epMgmt, hsend, hqep, ↓reduceIte, StateT.run_pure] at hr
      rcases hr with rfl
      exact Or.inr ⟨es, by simp [hwin0], hI, id⟩
    · have hqep_m : es.g.epoch P + 1 ≤ qep := by omega
      have hep := AuthL10.epMgmt_eq_epMgmtNew es.g (2 + Δcka) qep P r0.isSome hsend hqep
      let s₁ := AuthL10.epMgmtNew es.g (2 + Δcka) P r0.isSome
      have hs1_st : s₁.st = es.g.st := AuthL10.epMgmtNew_st es.g (2 + Δcka) P r0.isSome
      have hs1_epP : s₁.epoch P = es.g.epoch P + 1 := by
        simp [s₁, AuthL10.epMgmtNew_epoch]
      simp only [hep, vSend, AuthL10.epMgmtNew_st, hidP, htcurP, hsend, ↓reduceIte,
        liftH_run_df, StateT.run_bind, pure_bind, bind_assoc, simulateQ_bind] at hr
      rw [mem_support_bind_iff] at hr
      rcases hr with ⟨⟨⟨ans, h'⟩, sp'⟩, hans_mem, hr2⟩
      rcases startSend_support_df cka prng fs Δcka qep tL par s₁ P (es.g.epoch P + 1)
          (es.g.st P).γ (es.g.st P).root r0 es.h sp hans_mem with
        hnone | ⟨coins, σ', kVal, hsome, hσ', hcache'⟩
      · dsimp only at hnone; subst hnone
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
        rcases hr2 with rfl
        exact Or.inl rfl
      · dsimp only at hsome hcache'; subst hsome
        simp only [h_fsSend, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
        rcases hr2 with rfl
        right
        have hs1_win : s₁.win = es.g.win := by dsimp only [s₁, AuthL10.epMgmtNew]; split <;> rfl
        have hs1_ep : s₁.epoch = Function.update es.g.epoch P (es.g.epoch P + 1) :=
          AuthL10.epMgmtNew_epoch es.g (2 + Δcka) P r0.isSome
        have hs1_trans : s₁.trans = es.g.trans := AuthL10.epMgmtNew_trans es.g (2 + Δcka) P r0.isSome
        have hs1_comp := AuthL10.comp_inv_epMgmtNew es.g (2 + Δcka) P r0.isSome hI.comp_inv
        let cOut := cka.send (es.g.st P).γ coins
        let vp0 := es.g.st P
        let vp1 : VP Γ T (Option Sig) SS RS :=
          { vp0 with
            tcur := es.g.epoch P + 1
            γ := cOut.1
            curCkaMsg := some cOut.2.1
            root := σ'
            vS := some (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).1 }
        have hInv' := UnsplitInvDF.record_new hI hsend hqep_m hs1_st hs1_win hs1_ep hs1_trans hs1_comp
          cOut.1 cOut.2.1 σ' kVal
          (some (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).1)
          m_msg
          (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).2
          h' hσ' hcache'
        let rec1 : Record M (Header T × E) :=
          ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg,
            ((es.g.epoch P + 1, some cOut.2.1),
              (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).2)⟩
        let es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) :=
          { es with g := s₁.record (2 + Δcka) P vp1 rec1 false, h := h' }
        have hwin_rec : (s₁.record (2 + Δcka) P vp1 rec1 false).win = false := by
          simp [GameState.record, hs1_win, hwin0]
        refine ⟨es', ?_, ?_, ?_⟩
        · dsimp only [es', cOut, vp0, vp1, rec1, s₁] at hwin_rec hs1_epP ⊢
          simp [hs1_epP, hidP, hab0]
        · dsimp only [es', cOut, vp0, vp1, rec1] at hInv' ⊢
          simpa [hs1_epP, hidP, hab0] using hInv'
        · intro hPL
          dsimp only [es', GameState.record, s₁, AuthL10.epMgmtNew]
          split
          · obtain ⟨l, hl_mem, hlt, cur, htL, hle⟩ := PostTHLeakDF.leak hPL (es.g.epoch P + 1)
            exact ⟨l, hl_mem, hlt, cur, htL, hle⟩
          · exact hPL
  · simp only [Bool.not_eq_true] at hsend
    have hqep0 : ¬ qep < es.g.epoch P := by have := hI.epoch_le_qep P; omega
    have hep : es.g.epMgmt (2 + Δcka) qep P r0.isSome = some es.g := by
      simp [GameState.epMgmt, hsend, hqep0]
    let vp0 := es.g.st P
    rcases hvS : (es.g.st P).vS with _ | v
    · simp only [hep, vSend, hidP, htcurP, hsend, Bool.false_eq_true, ↓reduceIte, hvS,
        liftH_run_df, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      rcases hr with rfl
      let es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) :=
        { es with g := (es.g.record (2 + Δcka) P vp0
            ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m_msg, ((es.g.epoch P, vp0.curCkaMsg), default)⟩ false) }
      refine Or.inr ⟨es', ?_, ?_, ?_⟩
      · dsimp only [es', vp0]; simp [GameState.record, hwin0]
      · have hInv' := UnsplitInvDF.record_same hI hsend vp0 m_msg default hidP htcurP rfl rfl
        simpa [es', vp0, htcurP, hab0] using hInv'
      · rintro ⟨l, hl_mem, hlt, cur, htL, hle⟩
        exact ⟨l, hl_mem, hlt, cur, htL, hle⟩
    · simp only [hep, vSend, hidP, htcurP, hsend, Bool.false_eq_true, ↓reduceIte, hvS, h_fsSend,
        liftH_run_df, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      rcases hr with rfl
      let fe := fs.send v (es.g.epoch P, vp0.curCkaMsg) m_msg
      let es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) :=
        { es with g := (es.g.record (2 + Δcka) P { vp0 with vS := some fe.1 }
            ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m_msg, ((es.g.epoch P, vp0.curCkaMsg), fe.2)⟩ false) }
      refine Or.inr ⟨es', ?_, ?_, ?_⟩
      · dsimp only [es', vp0, fe]; simp [GameState.record, hwin0, hidP, htcurP]
      · have hInv' := UnsplitInvDF.record_same hI hsend { vp0 with vS := some fe.1 } m_msg fe.2
          hidP htcurP rfl rfl
        simpa [es', vp0, fe, hidP, htcurP, hab0] using hInv'
      · rintro ⟨l, hl_mem, hlt, cur, htL, hle⟩
        exact ⟨l, hl_mem, hlt, cur, htL, hle⟩

private theorem deliverE_eq_and_unsplitInv_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) :
    ∃ out es',
      ((deliverE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        fs.maxSkip (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') ∧
      ((deliverE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        fs.maxSkip (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') ∧
      UnsplitInvDF Δcka qep es' ∧
      es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have hes_h0 : ({ g := es.g, h := es.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) = es := by
    cases es; dsimp only at hab0; subst hab0; rfl
  have hes_acc : ∀ (g1 : Ctx Γ T (Option Sig) SS RS M E),
      ({ g := g1, h := es.h, abort := false } :
        EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) =
      { es with g := g1 } :=
    fun g1 => by cases es; dsimp only at hab0; subst hab0; rfl
  cases hr : es.g.inTransit P.other c with
  | none =>
    refine ⟨none, es, ?_, ?_, hI, rfl, rfl⟩ <;>
      simp only [deliverE, StateT.run_bind, StateT.run_get, pure_bind,
        hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, StateT.run_pure]
  | some r =>
    obtain ⟨hmem, hsender, hct⟩ := AuthL10.inTransit_some_props hr
    obtain ⟨ht1, hle_other, hhon_r⟩ := hI.trans_inv r hmem
    rw [hct] at ht1 hhon_r
    rw [hsender] at hle_other
    have hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false := by
      by_cases h1 : c.1.1 = (es.g.st P).tcur + 1
      · have hhon : isHonestHdrPRNGBucket es.h c.1 = true := hhon_r (by omega)
        simp [h1, hhon]
      · simp [h1]
    rcases vRecv_main_hybrid_of_not_newForged_df cka prng fs Δcka qep tL par es.g P (es.g.st P) c
        (some r) es.h hI.cache_some hnf with ⟨hvH, hvM⟩ |
        ⟨st', i', m', ⟨hvH, hvM⟩, hsend0, hle1, hid', htcur', hcur', hroot_new, hroot_old⟩
    · refine ⟨some .rejected, es, ?_, ?_, hI, rfl, rfl⟩
      · simp only [deliverE, liftH_run_df, bucketAuthCfg, StateT.run_bind, StateT.run_get,
          pure_bind, hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvH, hes_h0, StateT.run_pure]
      · simp only [deliverE, liftH_run_df, bucketAuthCfg, StateT.run_bind, StateT.run_get,
          pure_bind, hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvM, hes_h0, StateT.run_pure]
    · have hcomH := commitE_trivial_run_df
        (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' r.pos es
      have hcomM := commitE_trivial_run_df
        (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' r.pos es
      refine ⟨some (.accepted c.1.1 i'
          (if es.g.chall.contains r.pos then none else some m')),
        { es with g := es.g.accept P st' r.pos }, ?_, ?_, ?_, rfl, rfl⟩
      · simp only [deliverE, liftH_run_df, bucketAuthCfg, StateT.run_bind, StateT.run_get,
          pure_bind, hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvH, hes_h0, hcomH, StateT.run_modify, StateT.run_pure, hes_acc]
      · simp only [deliverE, liftH_run_df, bucketAuthCfg, StateT.run_bind, StateT.run_get,
          pure_bind, hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvM, hes_h0, hcomM, StateT.run_modify, StateT.run_pure, hes_acc]
      · rw [hidP] at hid' hsend0
        rw [htcurP] at hle1 htcur' hroot_new hroot_old
        by_cases hnew : r.pos.epoch = es.g.epoch P + 1
        · have htcur_new : st'.tcur = r.pos.epoch := by omega
          exact UnsplitInvDF.accept_new hI hnew hle_other (ht1 ▸ hsend0) st' hid' htcur_new
            (hroot_new (ht1.trans hnew))
        · have hle_ep : r.pos.epoch ≤ es.g.epoch P := by omega
          have htcur_old : st'.tcur = es.g.epoch P := by omega
          exact UnsplitInvDF.accept_old hI hle_ep st' hid' htcur_old
            (hroot_old (fun heq => hnew (ht1.symm.trans heq))) hcur'

private theorem deliver_step_all_three_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) :
    ∃ out es',
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inl (.inr (P, c))))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inl (.inr (P, c))))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inl (.inr (P, c))))))).run (es, none)) =
        pure (out, (es', none)) ∧
      UnsplitInvDF Δcka qep es' ∧
      es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks := by
  obtain ⟨out, es', hdH, hdM, hI', htL', hleaks'⟩ :=
    deliverE_eq_and_unsplitInv_df cka prng fs Δcka qep tL par P c hI
  have hdF : ((deliverE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
      fs.maxSkip (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') := hdH
  have hwin' := hI'.win_false
  refine ⟨out, es', ?_, ?_, ?_, hI', htL', hleaks'⟩
  · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      QueryImpl.add_apply, hdH, hwin']
  · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      QueryImpl.add_apply, hdM, hwin']
  · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
      QueryImpl.add_apply, hdF]

private theorem injectE_eq_of_isNewForged_false_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false) :
    ∃ out es',
      ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') ∧
      ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') ∧
      es'.abort = false ∧
      (es'.g.win = false →
        UnsplitInvDF Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have hes_h : { es with h := es.h } = es := by cases es; rfl
  by_cases hguard :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
  · refine ⟨none, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩ <;>
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
  · simp only [Bool.not_eq_true] at hguard
    have hsafe0 : es.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
      exact hguard.2
    rcases vRecv_main_hybrid_of_not_newForged_df cka prng fs Δcka qep tL par es.g P (es.g.st P) c
        none es.h hI.cache_some hnf with ⟨hvH, hvM⟩ |
        ⟨st', i', m', ⟨hvH, hvM⟩, hsend0, hle1, hid', htcur', hcur', _, hroot_old⟩
    · refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
      · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, StateT.run_pure]
      · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvM, StateT.run_pure]
    · rw [hidP] at hid' hsend0
      rw [htcurP] at hle1 htcur' hroot_old
      have hqep_ok : ¬ (qep + 1 < c.1.1) := by have := hI.epoch_le_qep P; omega
      let pos : Pos := ⟨P.other, c.1.1, i'⟩
      by_cases htriv : es.g.trivial (2 + Δcka) pos = true
      · have hne_succ : c.1.1 ≠ es.g.epoch P + 1 := by
          intro heq
          have htf := AuthL10.trivial_false_of_safeInj es.g (2 + Δcka) P i' hsafe0 hI.comp_inv
          dsimp only [pos] at htriv
          rw [heq] at htriv; rw [htriv] at htf; cases htf
        have hle_ep : pos.epoch ≤ es.g.epoch P := by dsimp only [pos]; omega
        have htcur_old : st'.tcur = es.g.epoch P := by omega
        have hcomH := commitE_trivial_run_df
          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
        have hcomM := commitE_trivial_run_df
          (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
          (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
        refine ⟨some (.accepted c.1.1 i' (some m')),
          { es with g := es.g.accept P st' pos }, ?_, ?_, hab0,
          fun _ => ⟨UnsplitInvDF.accept_old hI hle_ep st' hid' htcur_old (hroot_old hne_succ) hcur', rfl, rfl⟩⟩
        · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
            hguard, Bool.false_eq_true, ↓reduceIte, hvH, hqep_ok,
            pos, htriv, hcomH, StateT.run_modify, StateT.run_pure]
        · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
            hguard, Bool.false_eq_true, ↓reduceIte, hvM, hqep_ok,
            pos, htriv, hcomM, StateT.run_modify, StateT.run_pure]
      · simp only [Bool.not_eq_true] at htriv
        by_cases hinj : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c.1.1 = true
        · refine ⟨some .rejected, { es with g := { es.g with win := true } },
            ?_, ?_, hab0, fun hw => by simp at hw⟩
          · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvH, hqep_ok,
              pos, htriv, hinj, StateT.run_modify, StateT.run_pure]
          · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvM, hqep_ok,
              pos, htriv, hinj, StateT.run_modify, StateT.run_pure]
        · simp only [Bool.not_eq_true] at hinj
          refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
          · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvH, hqep_ok,
              pos, htriv, hinj, StateT.run_pure]
          · simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvM, hqep_ok,
              pos, htriv, hinj, StateT.run_pure]

private theorem inject_step_of_isNewForged_false_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false) :
    (∃ out es',
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      UnsplitInvDF Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) ∨
    (∃ out es',
      es'.g.win = true ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', some c.1.1)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', some c.1.1))) := by
  obtain ⟨out, es', hiH, hiM, _, hwin_imp⟩ :=
    injectE_eq_of_isNewForged_false_df cka prng fs Δcka qep tL par P c hI hnf
  have hiF : ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (out, es') := hiH
  have hwin0 := hI.win_false
  cases hwin' : es'.g.win
  · obtain ⟨hI', htL', hleaks'⟩ := hwin_imp hwin'
    left
    refine ⟨out, es', ?_, ?_, ?_, hI', htL', hleaks'⟩
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiH, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiM, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiF, hwin']
  · right
    refine ⟨out, es', hwin', ?_, ?_⟩
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
        implEDFPaperBucketRaw, QueryImpl.add_apply, hiH, hwin0, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
        implEDFPaperBucketRaw, QueryImpl.add_apply, hiM, hwin0, hwin']

private theorem inject_step_of_isNewForged_true_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true) :
    (∃ out,
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es, none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es, none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es, none))) ∨
    ((((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (none, ({ es with abort := true }, none))) ∨
    (es.g.safeInj (2 + Δcka) = true ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (some .rejected,
          ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1))) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (some .rejected,
          ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1)))) := by
  have hwin0 := hI.win_false
  have htcurP := hI.tcur_eq P
  have hes_h : { es with h := es.h } = es := by cases es; rfl
  by_cases hguard :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
  · have hiH : ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (none, es) := by
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    have hiM : ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (none, es) := by
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    have hiF : ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (none, es) := hiH
    left
    refine ⟨none, ?_, ?_, ?_⟩
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiH, hwin0]
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiM, hwin0]
    · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiF, hwin0]
  · simp only [Bool.not_eq_true] at hguard
    have hsafe0 : es.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
      exact hguard.2
    have hqep_tcur : (es.g.st P).tcur ≤ qep := by rw [htcurP]; exact hI.epoch_le_qep P
    rcases vRecv_newForged_cases_df cka prng fs Δcka qep tL par es.g P (es.g.st P) c es.h
        (hI.root_some P) hqep_tcur hnf with ⟨hvH, hvM⟩ | hvAbort |
        ⟨st', i', m', hvH, _, hinB, hnew⟩
    · have hiH : ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (some .rejected, es) := by
        simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, StateT.run_pure]
      have hiM : ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (some .rejected, es) := by
        simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvM, StateT.run_pure]
      have hiF : ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es = pure (some .rejected, es) := hiH
      left
      refine ⟨some .rejected, ?_, ?_, ?_⟩
      · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
          QueryImpl.add_apply, hiH, hwin0]
      · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
          QueryImpl.add_apply, hiM, hwin0]
      · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
          QueryImpl.add_apply, hiF, hwin0]
    · have hiH : ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es =
          pure (none, { es with abort := true }) := by
        simp only [injectE, liftH_run_df, abortE, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvAbort, StateT.run_modify, StateT.run_pure]
      right; left
      simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hiH, hwin0]
    · have hnew_ep : c.1.1 = es.g.epoch P + 1 := by rw [← htcurP]; exact hnew
      have hhon_f : isHonestHdrPRNGBucket es.h c.1 = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnf; exact hnf.2
      have hqep_ok : ¬ (qep + 1 < c.1.1) := by have := hI.epoch_le_qep P; omega
      have htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false := by
        rw [hnew_ep]
        exact AuthL10.trivial_false_of_safeInj es.g (2 + Δcka) P i' hsafe0 hI.comp_inv
      have hinj : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c.1.1 = true := hinB
      have hiH : ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es =
          pure (some .rejected, { es with g := { es.g with win := true } }) := by
        simp only [injectE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, hqep_ok,
          htriv, hinj, StateT.run_modify, StateT.run_pure]
      have hiF : ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c)).run es =
          pure (some .rejected, { es with g := { es.g with win := true } }) := hiH
      right; right
      refine ⟨hsafe0, ?_, ?_⟩
      · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
          implEDFPaperBucketRaw, QueryImpl.add_apply, hiH, hwin0, hnew_ep]
      · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
          QueryImpl.add_apply, hiF, hwin0, hnew_ep, htcurP, hhon_f]

private theorem deliverForgeE_eq_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c c' : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) :
    ∃ out es',
      ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c, c')).run es = pure (out, es') ∧
      ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c, c')).run es = pure (out, es') ∧
      es'.abort = false ∧
      (es'.g.win = false →
        UnsplitInvDF Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have hes_h0 : ({ g := es.g, h := es.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) = es := by
    cases es; dsimp only at hab0; subst hab0; rfl
  have hes_acc : ∀ (g1 : Ctx Γ T (Option Sig) SS RS M E),
      ({ g := g1, h := es.h, abort := false } :
        EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) =
      { es with g := g1 } :=
    fun g1 => by cases es; dsimp only at hab0; subst hab0; rfl
  cases hr : es.g.inTransit P.other c with
  | none =>
    refine ⟨none, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩ <;>
      simp only [deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind,
        hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, StateT.run_pure]
  | some r =>
    by_cases hguard :
        ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || (c.1 != c'.1)) = true
    · refine ⟨none, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩ <;>
        simp only [deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind,
          hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, StateT.run_pure]
    · simp only [Bool.not_eq_true] at hguard
      have hc_hdr : c.1 = c'.1 := by
        simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        exact hguard.2
      obtain ⟨hmem, hsender, hct⟩ := AuthL10.inTransit_some_props hr
      obtain ⟨ht1, hle_other, hhon_r⟩ := hI.trans_inv r hmem
      rw [hct, hc_hdr] at ht1 hhon_r
      rw [hsender] at hle_other
      have hnf : (decide (c'.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c'.1) = false := by
        by_cases h1 : c'.1.1 = (es.g.st P).tcur + 1
        · have hhon : isHonestHdrPRNGBucket es.h c'.1 = true := hhon_r (by omega)
          simp [h1, hhon]
        · simp [h1]
      rcases vRecv_main_hybrid_of_not_newForged_df cka prng fs Δcka qep tL par es.g P (es.g.st P) c'
          none es.h hI.cache_some hnf with ⟨hvH, hvM⟩ |
          ⟨st', i', m', ⟨hvH, hvM⟩, hsend0, hle1, hid', htcur', hcur', hroot_new, hroot_old⟩
      · refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
        · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
            hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvH, hes_h0,
            StateT.run_pure]
        · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
            hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvM, hes_h0,
            StateT.run_pure]
      · by_cases hqep_chk : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
        · refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
          · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvH, hes_h0,
              hqep_chk, StateT.run_pure]
          · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
              hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvM, hes_h0,
              hqep_chk, StateT.run_pure]
        · simp only [Bool.not_eq_true] at hqep_chk
          let pos : Pos := ⟨P.other, c'.1.1, i'⟩
          by_cases htriv : es.g.trivial (2 + Δcka) pos = true
          · have hcomH := commitE_trivial_run_df
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
            have hcomM := commitE_trivial_run_df
              (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
              (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
            refine ⟨some (.accepted c'.1.1 i' (some m')),
              { es with g := es.g.accept P st' pos }, ?_, ?_, hab0, fun _ => ⟨?_, rfl, rfl⟩⟩
            · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvH, hes_h0,
                hqep_chk, pos, htriv, hcomH, StateT.run_modify, StateT.run_pure, hes_acc]
            · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvM, hes_h0,
                hqep_chk, pos, htriv, hcomM, StateT.run_modify, StateT.run_pure, hes_acc]
            · rw [hidP] at hid' hsend0
              rw [htcurP] at hle1 htcur' hroot_new hroot_old
              by_cases hnew : pos.epoch = es.g.epoch P + 1
              · have htcur_new : st'.tcur = pos.epoch := by dsimp only [pos] at hnew ⊢; omega
                exact UnsplitInvDF.accept_new hI hnew (by dsimp only [pos]; omega) hsend0 st'
                  hid' htcur_new (hroot_new hnew)
              · have hle_ep : pos.epoch ≤ es.g.epoch P := by dsimp only [pos] at hnew ⊢; omega
                have htcur_old : st'.tcur = es.g.epoch P := by dsimp only [pos] at hnew; omega
                exact UnsplitInvDF.accept_old hI hle_ep st' hid' htcur_old (hroot_old hnew) hcur'
          · simp only [Bool.not_eq_true] at htriv
            by_cases hinj : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c'.1.1 = true
            · refine ⟨some .rejected, { es with g := { es.g with win := true } },
                ?_, ?_, hab0, fun hw => by simp at hw⟩
              · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                  hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvH, hes_h0,
                  hqep_chk, pos, htriv, hinj, StateT.run_modify, StateT.run_pure, hes_acc]
              · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                  hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvM, hes_h0,
                  hqep_chk, pos, htriv, hinj, StateT.run_modify, StateT.run_pure, hes_acc]
            · simp only [Bool.not_eq_true] at hinj
              refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
              · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                  hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvH, hes_h0,
                  hqep_chk, pos, htriv, hinj, StateT.run_pure]
              · simp only [deliverForgeE, liftH_run_df, StateT.run_bind, StateT.run_get, pure_bind,
                  hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, hguard, hvM, hes_h0,
                  hqep_chk, pos, htriv, hinj, StateT.run_pure]

private theorem deliverForge_step_cases_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (c c' : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) :
    (∃ out es',
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inr (P, c, c')))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inr (P, c, c')))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inr (P, c, c')))).run (es, none)) =
        pure (out, (es', none)) ∧
      UnsplitInvDF Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) ∨
    (∃ out es',
      es'.g.win = true ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inr (P, c, c')))).run (es, none)) =
        pure (out, (es', some c'.1.1)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inr (P, c, c')))).run (es, none)) =
        pure (out, (es', some c'.1.1))) := by
  obtain ⟨out, es', hdH, hdM, _, hwin_imp⟩ :=
    deliverForgeE_eq_df cka prng fs Δcka qep tL par P c c' hI
  have hdF : ((deliverForgeE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep (bucketAuthCfg Δcka tL par)) (P, c, c')).run es = pure (out, es') := hdH
  have hwin0 := hI.win_false
  cases hwin' : es'.g.win
  · obtain ⟨hI', htL', hleaks'⟩ := hwin_imp hwin'
    left
    refine ⟨out, es', ?_, ?_, ?_, hI', htL', hleaks'⟩
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hdH, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hdM, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
        QueryImpl.add_apply, hdF]
  · right
    refine ⟨out, es', hwin', ?_, ?_⟩
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
        implEDFPaperBucketRaw, QueryImpl.add_apply, hdH, hwin0, hwin']
    · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, dfQueryTargetEpoch,
        implEDFPaperBucketRaw, QueryImpl.add_apply, hdM, hwin0, hwin']

private theorem corrPaper_step_cases_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (hI : UnsplitInvDF Δcka qep es) :
    (es.g.corrAllowedPaper P = false ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inr P)))).run (es, none)) =
        pure (none, (es, none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
        (.inr (.inl (.inr P)))).run (es, none)) =
        pure (none, (es, none)) ∧
      (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
        (.inr (.inl (.inr P)))).run (es, none)) =
        pure (none, (es, none))) ∨
    (es.g.corrAllowedPaper P = true ∧
      ∃ stOut h',
        UnsplitInvDF Δcka qep { es with g := es.g.afterCorr P, h := h' } ∧
        (((implEDFPaperBucketMode (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
          (.inr (.inl (.inr P)))).run (es, none)) =
          pure (some stOut, ({ es with g := es.g.afterCorr P, h := h' }, none)) ∧
        (((implEDFPaperBucketMode (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket)
          (.inr (.inl (.inr P)))).run (es, none)) =
          pure (some stOut, ({ es with g := es.g.afterCorr P, h := h' }, none)) ∧
        (max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL →
          h' = es.h ∧
          (((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket)
            (.inr (.inl (.inr P)))).run (es, none)) =
            pure (some stOut, ({ es with g := es.g.afterCorr P, h := es.h }, none)))) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have htcurP := hI.tcur_eq P
  cases hcorr : es.g.corrAllowedPaper P
  · left
    refine ⟨rfl, ?_, ?_, ?_⟩ <;>
      simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
        QueryImpl.add_apply, corrEPaperBucket, hab0, hwin0, hcorr, StateT.run_bind,
        StateT.run_get, StateT.run_pure]
  · right
    have hrootP := hI.root_some P
    rcases hroot_eq : (es.g.st P).root with _ | σ
    · simp [hroot_eq] at hrootP
    · let stOut := realParty (es.g.st P) (es.g.st P).γ σ (es.g.st P).vS (es.g.st P).vR
      let cond1 := !decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone
      let h1 : PRNGBucketState T Sig K I :=
        if cond1 then { es.h with corrRoot := some ((es.g.st P).tcur, σ) } else es.h
      let cond2 := !postLeak tL es.g && es.h.lc.isNone && !decide ((es.g.st P).tcur < healEpoch tL)
      let h' : PRNGBucketState T Sig K I :=
        if cond2 then { h1 with lc := some (es.g.st P).tcur } else h1
      have hcache' : h'.cache = es.h.cache := by
        dsimp only [h', h1]; split <;> split <;> rfl
      have hrevH : ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).reveal
          es.g P (es.g.st P)).run es.h = pure (some stOut, h') := by
        dsimp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, h', h1, cond1, cond2, stOut]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hroot_eq, resolveCorrRoot]
        split <;> split <;> simp [StateT.run_bind, StateT.run_modify, StateT.run_pure]
      have hrevM : ((hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL)).reveal
          es.g P (es.g.st P)).run es.h = pure (some stOut, h') := hrevH
      have hwin_after : (es.g.afterCorr P).win = false := hwin0
      refine ⟨rfl, stOut, h', UnsplitInvDF.afterCorr hI P h' hcache', ?_, ?_, ?_⟩
      · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
          QueryImpl.add_apply, corrEPaperBucket, hab0, hwin0, hwin_after, hcorr,
          hrevH, StateT.run_bind, StateT.run_get, StateT.run_modify]
      · simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
          QueryImpl.add_apply, corrEPaperBucket, hab0, hwin0, hwin_after, hcorr,
          hrevM, StateT.run_bind, StateT.run_get, StateT.run_modify]
      · intro hlt_max
        have hep_le : es.g.epoch P ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
          cases P <;> simp
        have htcur_lt : (es.g.st P).tcur < healEpoch tL := by omega
        have hltA : es.g.epoch .A < healEpoch tL := (Nat.le_max_left _ _).trans_lt hlt_max
        have hltB : es.g.epoch .B < healEpoch tL := (Nat.le_max_right _ _).trans_lt hlt_max
        have hh' : h' = es.h := by
          dsimp only [h', h1, cond1, cond2]; simp [htcur_lt]
        have hrevF : ((hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL)).reveal
            es.g P (es.g.st P)).run es.h = pure (some stOut, es.h) := by
          simp [hooksPRNGBucketForgedHdr, hooksPRNGBucketForgedHdrGen,
            not_le_of_gt htcur_lt, not_le_of_gt hltA, not_le_of_gt hltB,
            hroot_eq, stOut, StateT.run_pure]
        refine ⟨hh', ?_⟩
        simp [implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
          QueryImpl.add_apply, corrEPaperBucket, hab0, hwin0, hcorr,
          hrevF, StateT.run_bind, StateT.run_get, StateT.run_modify]

private theorem unsplit_le_main_of_post_tH_leak_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hI : UnsplitInvDF Δcka qep es)
    (hPL : PostTHLeakDF tL es.g) :
    𝒟[runPostPBucketDF prng (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        Δcka qep fs.maxSkip tL par true true oa (es, none) sp] {true} ≤
      𝒟[runPostPBucketDF prng (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
        Δcka qep fs.maxSkip tL par true true oa (es, none) sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing es sp with
  | pure a => exact le_rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      dsimp only [runPostPBucketDF]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc,
        implEDFPaperBucketMode_frozen_inl prng _ Δcka qep fs.maxSkip tL par true n (es, none) sp,
        pure_bind]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun u _ => ih u es sp hI hPL
    | inr q' =>
      rcases q' with ((((⟨P, m_msg, r0⟩ | x) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
      · dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, bind_assoc,
          implEDFPaperBucketMode_transmit_main_eq cka prng fs Δcka qep tL par (P, m_msg, r0) es]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun r hr => ?_
        rcases transmit_support_unsplitInv_df cka prng fs Δcka qep tL par P m_msg r0 hI hr with
          hab | ⟨es', hes', hI', hPL_imp⟩
        · have hpost : postPBucketDF Δcka tL true r.1.2 = false := by
            rcases hr2 : r.1.2 with ⟨es1, w1⟩
            have hab1 : es1.abort = true := by simpa [hr2] using hab
            cases w1 <;> simp [postPBucketDF, authOutBucketPaperAt, authOutBucketPaper,
              authOutBucket, authOut, hab1]
          have hdead := runPostPBucketDF_dead_zero prng
            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            Δcka qep fs.maxSkip tL par true true (cont r.1.1) r.1.2 r.2 (Or.inl hab) hpost
          dsimp only [runPostPBucketDF] at hdead
          rw [hdead]
          exact zero_le
        · rw [hes']
          exact ih r.1.1 es' r.2 hI' (hPL_imp hPL)
      · dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, implEDFPaperBucketMode_chall_eq,
          pure_bind]
        exact ih none es sp hI hPL
      · obtain ⟨out, es', hdH, hdM, _, hI', htL', hleaks'⟩ :=
          deliver_step_all_three_df cka prng fs Δcka qep tL par P c hI
        have hPL' : PostTHLeakDF tL es'.g := by
          rcases hPL with ⟨l, hl, hlt, cur, htL0, hle⟩
          exact ⟨l, hleaks' ▸ hl, hlt, cur, htL'.trans htL0, hle⟩
        dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, hdH, hdM, pure_bind]
        exact ih out es' sp hI' hPL'
      · by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true
        · rcases inject_step_of_isNewForged_true_df cka prng fs Δcka qep tL par P c hI hnf with
            ⟨out, hiH, hiM, _⟩ | hiAbort | ⟨hsafe0, hiH, _⟩
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              pure_bind]
            exact ih out es sp hI hPL
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiAbort,
              pure_bind]
            have hdead := runPostPBucketDF_dead_zero prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true true
              (cont none) ({ es with abort := true }, none) sp (Or.inl rfl) rfl
            dsimp only [runPostPBucketDF] at hdead
            rw [hdead]
            exact zero_le
          · have hauth_f : authLosingConditionsAvoided (2 + Δcka) tL (es.g.epoch P + 1)
                { es.g with win := true } = false :=
              authOK_false_of_postTHLeak_df P hPL hsafe0 rfl
            have hpost_f : postPBucketDF Δcka tL true
                ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1)) = false := by
              simp [postPBucketDF, authOutBucketPaperAt, authOutBucketPaper, authOutBucket,
                authOut, hauth_f]
            dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH,
              pure_bind]
            have hdead := runPostPBucketDF_dead_zero prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true true (cont (some .rejected))
              ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1))
              sp (Or.inr rfl) hpost_f
            dsimp only [runPostPBucketDF] at hdead
            rw [hdead]
            exact zero_le
        · simp only [Bool.not_eq_true] at hnf
          rcases inject_step_of_isNewForged_false_df cka prng fs Δcka qep tL par P c hI hnf with
            ⟨out, es', hiH, hiM, _, hI', htL', hleaks'⟩ | ⟨out, es', hwin', hiH, hiM⟩
          · have hPL' : PostTHLeakDF tL es'.g := by
              rcases hPL with ⟨l, hl, hlt, cur, htL0, hle⟩
              exact ⟨l, hleaks' ▸ hl, hlt, cur, htL'.trans htL0, hle⟩
            dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              pure_bind]
            exact ih out es' sp hI' hPL'
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              pure_bind]
            have hfrz := runPostPBucketDF_frozen_eq prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true true true (cont out) es' (some c.1.1) sp (Or.inr hwin')
            dsimp only [runPostPBucketDF] at hfrz
            rw [hfrz]
      · rcases corrPaper_step_cases_df cka prng fs Δcka qep tL par P hI with
          ⟨_, hcH, hcM, _⟩ | ⟨_, stOut, h', hI', hcH, hcM, _⟩
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
            pure_bind]
          exact ih none es sp hI hPL
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
            pure_bind]
          exact ih (some stOut) { es with g := es.g.afterCorr P, h := h' } sp hI'
            (PostTHLeakDF.afterCorr_preserve hPL P)
      · rcases deliverForge_step_cases_df cka prng fs Δcka qep tL par P c c' hI with
          ⟨out, es', hdH, hdM, _, hI', htL', hleaks'⟩ | ⟨out, es', hwin', hdH, hdM⟩
        · have hPL' : PostTHLeakDF tL es'.g := by
            rcases hPL with ⟨l, hl, hlt, cur, htL0, hle⟩
            exact ⟨l, hleaks' ▸ hl, hlt, cur, htL'.trans htL0, hle⟩
          dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hdH, hdM,
            pure_bind]
          exact ih out es' sp hI' hPL'
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hdH, hdM,
            pure_bind]
          have hfrz := runPostPBucketDF_frozen_eq prng
            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
            Δcka qep fs.maxSkip tL par true true true (cont out) es' (some c'.1.1) sp (Or.inr hwin')
          dsimp only [runPostPBucketDF] at hfrz
          rw [hfrz]

private theorem unsplit_le_main_add_forgedHdr_from_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hI : UnsplitInvDF Δcka qep es) :
    𝒟[runPostPBucketDF prng (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        Δcka qep fs.maxSkip tL par true true oa (es, none) sp] {true} ≤
      𝒟[runPostPBucketDF prng (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
          Δcka qep fs.maxSkip tL par true true oa (es, none) sp] {true} +
        𝒟[runPostPBucketDF prng (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
          Δcka qep fs.maxSkip tL par false false oa (es, none) sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing es sp with
  | pure a =>
    dsimp only [runPostPBucketDF, postPBucketDF, authOutBucketPaperAt, authOutBucketPaper,
      authOutBucket]
    simp
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      dsimp only [runPostPBucketDF]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc,
        implEDFPaperBucketMode_frozen_inl prng _ Δcka qep fs.maxSkip tL par _ n (es, none) sp,
        pure_bind]
      exact evalDist_bind_le_add_of_support_2a _ _ _ _ fun u _ => ih u es sp hI
    | inr q' =>
      rcases q' with ((((⟨P, m_msg, r0⟩ | x) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
      · dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, bind_assoc,
          implEDFPaperBucketMode_transmit_main_eq cka prng fs Δcka qep tL par (P, m_msg, r0) es,
          implEDFPaperBucketMode_transmit_forged_eq cka prng fs Δcka qep tL par (P, m_msg, r0) es]
        refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun r hr => ?_
        rcases transmit_support_unsplitInv_df cka prng fs Δcka qep tL par P m_msg r0 hI hr with
          hab | ⟨es', hes', hI', _⟩
        · have hpost : postPBucketDF Δcka tL true r.1.2 = false := by
            rcases hr2 : r.1.2 with ⟨es1, w1⟩
            have hab1 : es1.abort = true := by simpa [hr2] using hab
            cases w1 <;> simp [postPBucketDF, authOutBucketPaperAt, authOutBucketPaper,
              authOutBucket, authOut, hab1]
          have hdead := runPostPBucketDF_dead_zero prng
            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            Δcka qep fs.maxSkip tL par true true (cont r.1.1) r.1.2 r.2 (Or.inl hab) hpost
          dsimp only [runPostPBucketDF] at hdead
          rw [hdead]
          exact zero_le
        · rw [hes']
          exact ih r.1.1 es' r.2 hI'
      · dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, implEDFPaperBucketMode_chall_eq,
          pure_bind]
        exact ih none es sp hI
      · obtain ⟨out, es', hdH, hdM, hdF, hI', _, _⟩ :=
          deliver_step_all_three_df cka prng fs Δcka qep tL par P c hI
        dsimp only [runPostPBucketDF]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, hdH, hdM, hdF, pure_bind]
        exact ih out es' sp hI'
      · by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true
        · rcases inject_step_of_isNewForged_true_df cka prng fs Δcka qep tL par P c hI hnf with
            ⟨out, hiH, hiM, hiF⟩ | hiAbort | ⟨_, hiH, hiF⟩
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM, hiF,
              pure_bind]
            exact ih out es sp hI
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiAbort,
              pure_bind]
            have hdead := runPostPBucketDF_dead_zero prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true true
              (cont none) ({ es with abort := true }, none) sp (Or.inl rfl) rfl
            dsimp only [runPostPBucketDF] at hdead
            rw [hdead]
            exact zero_le
          · have hle_forged := runPostPBucketDF_frozen_le_forged prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true false (cont (some .rejected))
              { es with g := { es.g with win := true } } (some (es.g.epoch P + 1)) sp (Or.inr rfl)
            dsimp only [runPostPBucketDF] at hle_forged ⊢
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiF,
              pure_bind]
            exact hle_forged.trans le_add_self
        · simp only [Bool.not_eq_true] at hnf
          rcases inject_step_of_isNewForged_false_df cka prng fs Δcka qep tL par P c hI hnf with
            ⟨out, es', hiH, hiM, hiF, hI', _, _⟩ | ⟨out, es', hwin', hiH, hiM⟩
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM, hiF,
              pure_bind]
            exact ih out es' sp hI'
          · dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              pure_bind]
            have hfrz := runPostPBucketDF_frozen_eq prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
              Δcka qep fs.maxSkip tL par true true true (cont out) es' (some c.1.1) sp (Or.inr hwin')
            dsimp only [runPostPBucketDF] at hfrz
            rw [hfrz]
            exact le_self_add
      · rcases corrPaper_step_cases_df cka prng fs Δcka qep tL par P hI with
          ⟨_, hcH, hcM, hcF⟩ | ⟨_, stOut, h', hI', hcH, hcM, hlt_imp⟩
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM, hcF,
            pure_bind]
          exact ih none es sp hI
        · by_cases hlt_max : max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL
          · obtain ⟨hh', hcF⟩ := hlt_imp hlt_max
            subst hh'
            dsimp only [runPostPBucketDF]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM, hcF,
              pure_bind]
            exact ih (some stOut) { es with g := es.g.afterCorr P, h := es.h } sp hI'
          · have hge_max : healEpoch tL ≤ max (es.g.epoch .A) (es.g.epoch .B) := by omega
            have hPL' : PostTHLeakDF tL (es.g.afterCorr P) := PostTHLeakDF.afterCorr_of_ge_tH P hge_max
            have hle_main := unsplit_le_main_of_post_tH_leak_df cka prng fs Δcka qep tL par
              (cont (some stOut)) { es with g := es.g.afterCorr P, h := h' } sp hI' hPL'
            dsimp only [runPostPBucketDF] at hle_main ⊢
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
              pure_bind]
            exact hle_main.trans le_self_add
      · rcases deliverForge_step_cases_df cka prng fs Δcka qep tL par P c c' hI with
          ⟨out, es', hdH, hdM, hdF, hI', _, _⟩ | ⟨out, es', hwin', hdH, hdM⟩
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hdH, hdM, hdF,
            pure_bind]
          exact ih out es' sp hI'
        · dsimp only [runPostPBucketDF]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hdH, hdM,
            pure_bind]
          have hfrz := runPostPBucketDF_frozen_eq prng
            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
            Δcka qep fs.maxSkip tL par true true true (cont out) es' (some c'.1.1) sp (Or.inr hwin')
          dsimp only [runPostPBucketDF] at hfrz
          rw [hfrz]
          exact le_self_add

private theorem initPRNGBucketHybrid_support_unsplitInv_df
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (sp0 : PRFPRNG.GameState Sig I K)
    {out : (Option (VP Γ T (Option Sig) SS RS × VP Γ T (Option Sig) SS RS) ×
      PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hout : out ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((initPRNGBucketHybrid (T := T) cka prng fs lam (3 + Δcka) tL par
        (healEpoch tL)).run {})).run sp0)) :
    ∀ vA vB, out.1.1 = some (vA, vB) →
      UnsplitInvDF (M := M) (E := E) Δcka qep
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false },
          h := out.1.2 } := by
  unfold initPRNGBucketHybrid at hout
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind,
    bind_assoc, pure_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨kc, _, ⟨⟨rootAns, h₁⟩, sp₁⟩, hroot_mem, hout2⟩
  obtain ⟨hcache1, hsome1⟩ := rootPRNGBucketHybrid_at_tH_mem_support prng (3 + Δcka) tL par 0
    false lam none {} kc.2 hroot_mem
  cases rootAns with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    intro _ _ h; cases h
  | some pOut =>
    rcases pOut with ⟨σ0, k0⟩
    have hσ0 : σ0.isSome = true := hsome1 σ0 k0 rfl
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    rintro vA vB hv
    simp only [Option.some.injEq] at hv
    have hvA : vA = (mkParties (cka.initA kc.1) (cka.initB kc.1) σ0
        (fs.initSender k0) (fs.initReceiver k0)).1 := congrArg Prod.fst hv.symm
    have hvB : vB = (mkParties (cka.initA kc.1) (cka.initB kc.1) σ0
        (fs.initSender k0) (fs.initReceiver k0)).2 := congrArg Prod.snd hv.symm
    subst hvA hvB
    refine
      { abort_false := rfl
        win_false := rfl
        id_eq := fun P => by cases P <;> rfl
        tcur_eq := fun P => by cases P <;> rfl
        root_some := fun P => by cases P <;> exact hσ0
        cache_some := fun m Tc σc kc' hk => by
          rw [hcache1] at hk; cases hk
        epoch_le_qep := fun _ => Nat.zero_le _
        cache_gt := fun m _ => by rw [hcache1]
        epoch_le := fun _ => Nat.zero_le _
        epoch_sends := fun _ h => by simp at h
        sender_cur := fun _ h => by simp at h
        trans_inv := fun _ h => by simp at h
        comp_inv := fun _ h => by simp at h }

private theorem unsplit_prng_false_le_main_add_forgedHdr_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
          (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} +
        𝒟[PRFPRNG.branch prng false
          (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng =
      AuthL11.pImpl prng := rfl
  have himplH : implEDFPaperBucket
      (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) =
    implEDFPaperBucketMode
      (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket := rfl
  have himplM : implEDFPaperBucket
      (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) =
    implEDFPaperBucketMode
      (hooksPRNGBucketMain cka prng fs Δcka qep tL par (healEpoch tL))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket := rfl
  unfold PRFPRNG.branch redPRNGAuthDFPaperBucketHybrid redPRNGAuthDFPaperBucketHybridAt
    redPRNGAuthDFPaperBucketMain redPRNGAuthDFPaperBucketForgedHdr
    engRunDFPaperBucket engRunDFPaperBucketMode
  rw [himplH, himplM]
  simp only [StateT.run'_eq, hpImpl, StateT.run_bind, StateT.run_pure, simulateQ_bind,
    simulateQ_pure, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun kr _ => ?_
  refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun out hout => ?_
  have hInit := initPRNGBucketHybrid_support_unsplitInv_df (M := M) (E := E) cka prng fs lam
    Δcka qep tL par { σ := prng.init kr, b := false } hout
  rcases out with ⟨⟨vs, h⟩, sp1⟩
  cases vs with
  | none =>
    simp [StateT.run_pure, simulateQ_pure]
  | some vp =>
    rcases vp with ⟨vA, vB⟩
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc]
    exact unsplit_le_main_add_forgedHdr_from_df cka prng fs Δcka qep tL par A
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } sp1
      (hInit vA vB rfl)

/-- Hop-2a split (`t = healEpoch tL`, paper engine): ideal CKA (`b = true`) on
`redCKAAuthDFPaperBucket` splits into real PRF-PRNG (`b = false`) on `Main` (`gMain = true`) plus
`ForgedHdr` (`gMain = false`) at `t = healEpoch tL`. -/
theorem cka_branch_true_redCKAAuthDFPaperBucket_le_main_add_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
          (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} +
      𝒟[PRFPRNG.branch prng false
          (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} :=
  let _ := hc
  (cka_branch_true_redCKAAuthDFPaperBucket_le_prng_false_impl cka prng fs lam Δcka qep tL par A).trans
    (unsplit_prng_false_le_main_add_forgedHdr_df cka prng fs lam Δcka qep tL par A)

/-- Engine end-state type of the paper bucket PRNG games. -/
private abbrev BSt (Γ T Sig SS RS M E I K : Type) :=
  EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ

/-- Generic-output `Main` reduction (hooks/init of `redPRNGAuthDFPaperBucketMain` at `t0`, output `out`). -/
private def redMainOut [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (out : BSt Γ T Sig SS RS M E I K → Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t0) {} false A
    return match r with
      | none => false
      | some (_, st) => out st

private theorem T1_main_eq_out [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A =
      redMainOut cka prng fs lam Δcka qep tL par t0 (authOutBucketPaperAt (2 + Δcka) tL t0) A := rfl

private theorem T1_branch_out_le_add [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (b : Bool) (f g₁ g₂ : BSt Γ T Sig SS RS M E I K → Bool)
    (hfg : ∀ st, f st = true → g₁ st = true ∨ g₂ st = true)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng b (redMainOut cka prng fs lam Δcka qep tL par t0 f A)] {true} ≤
      𝒟[PRFPRNG.branch prng b (redMainOut cka prng fs lam Δcka qep tL par t0 g₁ A)] {true} +
      𝒟[PRFPRNG.branch prng b (redMainOut cka prng fs lam Δcka qep tL par t0 g₂ A)] {true} := by
  have hBind : ∀ {α : Type} (p : ProbComp α) (F G₁ G₂ : α → ProbComp Bool),
      (∀ a ∈ support p, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) →
      𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
    intro α p F G₁ G₂ h
    induction p using OracleComp.inductionOn with
    | pure a =>
      simpa only [pure_bind] using h a (by simp)
    | query_bind t r ih =>
      simp only [bind_assoc, evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
          Measurable.of_discrete.aemeasurable]
      calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
          ≤ ∫⁻ u, (𝒟[r u >>= G₁] {true} + 𝒟[r u >>= G₂] {true}) ∂𝒟[query t] :=
            MeasureTheory.lintegral_mono fun u =>
              ih u fun a ha => h a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)
        _ = (∫⁻ u, 𝒟[r u >>= G₁] {true} ∂𝒟[query t]) +
            (∫⁻ u, 𝒟[r u >>= G₂] {true} ∂𝒟[query t]) :=
            MeasureTheory.lintegral_add_left Measurable.of_discrete _
  have hBool : ∀ (b₀ b₁ b₂ : Bool), (b₀ = true → b₁ = true ∨ b₂ = true) →
      𝒟[(Pure.pure b₀ : ProbComp Bool)] {true} ≤
        𝒟[(Pure.pure b₁ : ProbComp Bool)] {true} +
        𝒟[(Pure.pure b₂ : ProbComp Bool)] {true} := by
    intro b₀ b₁ b₂ hb
    cases b₀ <;> cases b₁ <;> cases b₂ <;> simp_all
  unfold PRFPRNG.branch redMainOut
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, simulateQ_bind,
    simulateQ_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine hBind _ _ _ _ fun kr _ => ?_
  refine hBind _ _ _ _ fun out _ => ?_
  cases hout : out.1 with
  | none =>
    exact hBool false false false (fun h => nomatch h)
  | some p =>
    rcases p with ⟨_, st⟩
    exact hBool (f st) (g₁ st) (g₂ st) (hfg st)

private theorem authOutBucketPaperAt_le_lcOpt_or_succ [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δ : ℕ) (tL : Option ℕ) (t : ℕ)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ) :
    authOutBucketPaperAt Δ tL t st =
      ((authOutBucketPaper Δ tL st && decide (st.1.h.lc = some t)) ||
        authOutBucketPaperAt Δ tL (t + 1) st) := by
  simp only [authOutBucketPaperAt]
  cases authOutBucketPaper Δ tL st with
  | false => simp
  | true =>
    cases st.1.h.lc with
    | none => simp
    | some e =>
      simp only [Bool.true_and]
      by_cases he : e = t
      · subst he; simp
      · have : decide (some e = some t) = false := decide_eq_false (by simp [he])
        rw [this, Bool.false_or]
        by_cases hle : t ≤ e
        · have hle' : t + 1 ≤ e := by omega
          simp [hle, hle']
        · have hle' : ¬ (t + 1 ≤ e) := by omega
          simp [hle, hle']


private theorem evalDist_bind_sum_add_le_main {α : Type} (p : ProbComp α) (s : Finset ℕ)
    (G : ℕ → α → ProbComp Bool) (G₀ F : α → ProbComp Bool)
    (h : ∀ a ∈ support p, (∑ t ∈ s, 𝒟[G t a] {true}) + 𝒟[G₀ a] {true} ≤ 𝒟[F a] {true}) :
    (∑ t ∈ s, 𝒟[p >>= G t] {true}) + 𝒟[p >>= G₀] {true} ≤ 𝒟[p >>= F] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
    calc (∑ i ∈ s, ∫⁻ u, 𝒟[r u >>= G i] {true} ∂𝒟[query t]) +
          ∫⁻ u, 𝒟[r u >>= G₀] {true} ∂𝒟[query t]
        = (∫⁻ u, (∑ i ∈ s, 𝒟[r u >>= G i] {true}) ∂𝒟[query t]) +
          ∫⁻ u, 𝒟[r u >>= G₀] {true} ∂𝒟[query t] := by
          rw [lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
      _ = ∫⁻ u, ((∑ i ∈ s, 𝒟[r u >>= G i] {true}) + 𝒟[r u >>= G₀] {true}) ∂𝒟[query t] := by
          rw [← lintegral_add_left (Finset.measurable_sum _ fun _ _ => Measurable.of_discrete)]
      _ ≤ ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t] := by
          refine lintegral_mono fun u => ih u fun a ha => h a ?_
          rw [MonadAttach.mem_support_bind]
          exact ⟨u, by simp, ha⟩

private theorem sum_localAuthDFPaperBucketMainLcEq_add_none_le
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (a b : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    (∑ t ∈ Finset.Ico a b,
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true}) +
    𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par none A] {true} ≤
      𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} := by
  dsimp only [localAuthDFPaperBucketMainLcEq, localAuthDFPaperBucketMain]
  refine evalDist_bind_sum_add_le_main _ (Finset.Ico a b) _ _ _ fun r _ => ?_
  cases r with
  | none => simp
  | some p =>
    rcases p with ⟨_, st⟩
    cases hw : authOutBucketPaper (2 + Δcka) tL st with
    | false => simp [hw]
    | true =>
      cases hlc : st.1.h.lc with
      | none =>
        simp [hw, hlc]
      | some e =>
        by_cases he : e ∈ Finset.Ico a b
        · rw [Finset.sum_eq_single e
            (fun t _ hne => by simp [hw, hlc, Ne.symm hne])
            (fun hnot => False.elim (hnot he))]
          simp [hw, hlc]
        · rw [Finset.sum_eq_zero (fun t ht => by
            have hne : e ≠ t := fun h => he (h ▸ ht)
            simp [hw, hlc, hne])]
          simp [hw, hlc]

private theorem prng_ico_telescope_with_loss [DecidableEq I]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (B : ℕ → PRFPRNG.Adversary Sig I K) (L : ℕ → ℝ≥0∞)
    (a k : ℕ)
    (hStep : ∀ t, a ≤ t → t < a + k →
      𝒟[PRFPRNG.branch prng true (B t)] {true} ≤
        L t + 𝒟[PRFPRNG.branch prng false (B (t + 1))] {true}) :
    𝒟[PRFPRNG.branch prng false (B a)] {true} ≤
      (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
      (∑ t ∈ Finset.Ico a (a + k), L t) +
      𝒟[PRFPRNG.branch prng true (B (a + k))] {true} := by
  have hOne : ∀ t, 𝒟[PRFPRNG.branch prng false (B t)] {true} ≤
      PRFPRNG.advantage prng (B t) + 𝒟[PRFPRNG.branch prng true (B t)] {true} := fun t => by
    rw [PRFPRNG.advantage_eq_boolDist, Measure.boolDist_comm, add_comm (Measure.boolDist _ _)]
    exact Measure.apply_true_le_add_boolDist _ _
  induction k with
  | zero =>
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero,
      Finset.sum_Ico_succ_top (le_refl a), zero_add]
    exact hOne a
  | succ k ih =>
    have ih' := ih (fun t ht1 ht2 => hStep t ht1 (by omega))
    have hStepK := hStep (a + k) (by omega) (by omega)
    have hNext := hOne (a + k + 1)
    have hSumAdv : ∑ t ∈ Finset.Ico a (a + (k + 1) + 1), PRFPRNG.advantage prng (B t) =
        (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
        PRFPRNG.advantage prng (B (a + k + 1)) := by
      have heq : a + (k + 1) + 1 = (a + k + 1) + 1 := by omega
      rw [heq, Finset.sum_Ico_succ_top (by omega)]
    have hSumL : ∑ t ∈ Finset.Ico a (a + (k + 1)), L t =
        (∑ t ∈ Finset.Ico a (a + k), L t) + L (a + k) := by
      have heq : a + (k + 1) = (a + k) + 1 := by omega
      rw [heq, Finset.sum_Ico_succ_top (by omega)]
    rw [hSumAdv, hSumL]
    calc 𝒟[PRFPRNG.branch prng false (B a)] {true}
        ≤ (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
            (∑ t ∈ Finset.Ico a (a + k), L t) +
            𝒟[PRFPRNG.branch prng true (B (a + k))] {true} := ih'
      _ ≤ (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
            (∑ t ∈ Finset.Ico a (a + k), L t) +
            (L (a + k) +
              (PRFPRNG.advantage prng (B (a + k + 1)) +
                𝒟[PRFPRNG.branch prng true (B (a + k + 1))] {true})) :=
          add_le_add le_rfl (hStepK.trans (add_le_add le_rfl hNext))
      _ = ((∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
            PRFPRNG.advantage prng (B (a + k + 1))) +
          ((∑ t ∈ Finset.Ico a (a + k), L t) + L (a + k)) +
          𝒟[PRFPRNG.branch prng true (B (a + k + 1))] {true} := by ac_rfl


private theorem resolveCorrRoot_eq_of_syncTopRaw_main
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) (P : Party) (s : Sig)
    (hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = some s) :
    s = (esL.g.st P).root := by
  cases hrP : (esP.g.st P).root with
  | some σ0 =>
    rw [hrP, resolveCorrRoot] at hres
    exact (hsync.vp_rel P).root_eq s (Option.some.inj hres ▸ hrP)
  | none =>
    rw [hrP, resolveCorrRoot] at hres
    cases hcr : esP.h.corrRoot with
    | none => simp [hcr] at hres
    | some p =>
      rcases p with ⟨eC, σC⟩; rw [hcr] at hres; dsimp only at hres
      split at hres
      · rename_i h_eq; rw [beq_iff_eq] at h_eq; injection hres with hs
        exact hs.symm.trans ((hsync.corrRoot_rel eC σC hcr).2.1 P h_eq)
      · cases hres

private theorem postLeak_epMgmt_of_sendsIn_false_main {St Msg C : Type}
    {Δ qep : ℕ} {P : Party} {bad : Bool} {g s₁ : SM.GameState St Msg C}
    (hns : P.sendsIn (g.epoch P + 1) = false) (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold SM.GameState.epMgmt at hep; simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split at hep <;> simp at hep; exact hep.symm

private theorem run_commitE_PRNGBucketMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]

private theorem run_commitE_LocalBucketMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (s : Ctx Γ T Sig SS RS M E) (P : Party)
    (old new : VP Γ T Sig SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) :
    (commitE (hooksLocalBucketMain cka prng fs Δcka qep tL par) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksLocalBucketMain, hooksLocalBucket]

private def StartRecvPostBucketTopMain
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep e : ℕ) (tn0 : T)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (rP : (Option (Option (Γ × Option Sig × RS)) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Option (Γ × Sig × RS)) × LocalBucketState T Sig K I) : Prop :=
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧ rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
  ∃ γ' σP σL k,
    rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
    rL.1 = some (some (γ', σL, fs.initReceiver k)) ∧
    (∀ s, σP = some s → s = σL) ∧ rP.2.σ = sp.σ ∧ rP.2.b = true ∧
    rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
    rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧ rP.2.table = rL.2.fTable (qep + 1) ∧
    (∀ σp σl kc, hP.cache (e + 1) = some (tn0, σp, kc) → hL.cache (e + 1) = some (tn0, σl, kc) →
      σP = resolveCorrRoot hP (e + 1) σp ∧ σL = σl)

private theorem leComp_startRecvBucketTopMain
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {e : ℕ} {P : Party} {tn0 : T}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl) :
    AuthL11.LeComp (StartRecvPostBucketTopMain fs qep e tn0 hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1)).startRecv
          gP P (e + 1) vpP.γ vpP.root tn0).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        (((hooksLocalBucketMain cka prng fs Δcka qep tL par).startRecv
          gL P (e + 1) vpL.γ vpL.root tn0).run hL)) := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksLocalBucketMain; dsimp only
  rw [hvp.γ_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hoff :
      AuthL11.LeComp (StartRecvPostBucketTopMain fs qep e tn0 hP sp hL)
        ((simulateQ (AuthL11.pImpl prng)
          (StateT.run (if !(qep + 1 < e + 1) && inStage2BucketGen (3 + Δcka) tL par (e + 1) &&
                (tL.isSome && decide (e + 1 = healEpoch tL)) then
              (pure none : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
                (Option (Option (Γ × Option Sig × RS))))
            else
              pure (some none)) hP)).run sp)
        (simulateQ AuthL11.lImpl
          (StateT.run (if !(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
                (tL.isSome && decide (e + 1 = healEpoch tL)) then
              (pure none : HM AuthL11.nilSpec (LocalBucketState T Sig K I)
                (Option (Option (Γ × Sig × RS))))
            else
              pure (some none)) hL)) := by
    change AuthL11.LeComp (StartRecvPostBucketTopMain fs qep e tn0 hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        (StateT.run (if !(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
              (tL.isSome && decide (e + 1 = healEpoch tL)) then
            (pure none : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
              (Option (Option (Γ × Option Sig × RS))))
          else
            pure (some none)) hP)).run sp) _
    by_cases hc_abort : (!(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
        (tL.isSome && decide (e + 1 = healEpoch tL))) = true
    · simp only [hc_abort, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · simp only [hc_abort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  rcases hcache (e + 1) with ⟨hcP, hcL⟩ | ⟨Tc, σp, σl, k, hcP, hcL, hσ_rel⟩
  · conv => arg 2; rw [hcP]
    conv => arg 3; rw [hcL]
    exact hoff
  · conv => arg 2; rw [hcP]
    conv => arg 3; rw [hcL]
    by_cases hTc : Tc = tn0
    · subst hTc
      conv => arg 2; simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      conv => arg 3; simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tc).1,
        resolveCorrRoot hP (e + 1) σp, σl, k, rfl, rfl, ?_, rfl, hb, rfl, rfl, rfl, rfl, rfl, hft, htop,
        fun σp' σl' kc hp hl => by rw [hcP] at hp; rw [hcL] at hl; cases hp; cases hl; exact ⟨rfl, rfl⟩⟩))
      intro s hs; cases σp with
      | some s0 => simp only [resolveCorrRoot, Option.some.injEq] at hs; subst s; exact hσ_rel s0 rfl
      | none =>
        cases hcr : hP.corrRoot with
        | none => simp [resolveCorrRoot, hcr] at hs
        | some ec =>
          rcases ec with ⟨eC, σC⟩; simp only [resolveCorrRoot, hcr] at hs
          by_cases heq : (e + 1 == eC) = true
          · simp only [heq, ↓reduceIte, Option.some.injEq] at hs
            have heq' := eq_of_beq heq; subst heq'
            exact hs.symm.trans (hcr_cache (e + 1) σC hcr Tc σl k hcL)
          · simp [heq] at hs
    · conv => arg 2; simp only [hTc, ↓reduceIte]
      conv => arg 3; simp only [hTc, ↓reduceIte]
      exact hoff

private theorem leComp_vRecvBucketTopMain
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {c : Header T × E} {rec : Option (SM.Record M (Header T × E))}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl) :
    AuthL11.LeComp (VRecvRelBucketTop qep e P c vpP vpL hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
          gP P vpP c rec).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((vRecv (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          gL P vpL c rec).run hL)) := by
  unfold vRecv; dsimp only; rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hguard : (P.sendsIn c.1.1 || decide (e + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop⟩))
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    have hns : P.sendsIn c.1.1 = false := Bool.eq_false_iff.mpr hguard.1
    have htle : c.1.1 ≤ e + 1 := Nat.le_of_not_lt hguard.2
    by_cases hnew : c.1.1 = e + 1
    · simp only [hnew, ↓reduceIte]
      have hmax : max e (e + 1) = e + 1 := Nat.max_eq_right (Nat.le_succ e)
      cases hTn : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop⟩))
      | some Tn =>
        simp only [StateT.run_bind, simulateQ_bind]
        have hns_e1 : P.sendsIn (e + 1) = false := hnew ▸ hns
        refine (leComp_startRecvBucketTopMain cka prng fs Δcka qep tL par hvp hcache hft htop
          hb hcr_cache).bind ?_
        rintro ⟨⟨res_srP, hP1⟩, sp1⟩ ⟨res_srL, hL1⟩ hsr
        rcases hsr with hnone | ⟨hP_none, hL_none, rfl, rfl, rfl⟩ |
          ⟨γ', σP, σL, k, hP_some, hL_some, hσ_rel, hσ1, hb1, hcP1, hcr1, hlcP1, hcL1, hlcL1,
            hft1, htop1, hcache_hit⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop⟩))
        · dsimp only at hP_some hL_some; subst hP_some hL_some
          simp only [pure_bind, Function.update_self, hooksPRNGBucketMain,
            hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen, hooksLocalBucketMain, hooksLocalBucket]
          cases hfs : fs.receive (fs.initReceiver k) c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure
              (Or.inr (Or.inl ⟨rfl, rfl, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htop1⟩))
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]; refine AuthL11.LeComp.pure ?_
            dsimp only [VRecvRelBucketTop]; rw [hnew, hmax]
            refine Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_e1, ?_,
              hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htop1, fun hle_e => by omega, ?_⟩)
            · refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_, hσ_rel⟩
              intro t'; dsimp only; rw [Function.update_idem, Function.update_idem]
              by_cases ht' : t' = e + 1
              · subst ht'; simp only [Function.update_self]
              · simp only [Function.update_of_ne ht', hvp.vR_eq t']
            · intro _; refine ⟨⟨Tn, hTn⟩, fun tn0 σp σl kc htn0 hcP_eq hcL_eq => ?_⟩
              rw [hTn] at htn0; cases htn0; exact hcache_hit σp σl kc hcP_eq hcL_eq
    · simp only [hnew, ↓reduceIte, pure_bind]
      have htle_e : c.1.1 ≤ e := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max e c.1.1 = e := Nat.max_eq_left htle_e
      rcases hvRL : vpL.vR c.1.1 with _ | rs
      · have hvRP : vpP.vR c.1.1 = none := (hvp.vR_eq c.1.1).trans hvRL
        simp only [hvRP, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop⟩))
      · have hvRP : vpP.vR c.1.1 = some rs := (hvp.vR_eq c.1.1).trans hvRL
        simp only [hvRP, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
          hooksLocalBucketMain, hooksLocalBucket, pure_bind]
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop⟩))
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htop,
            fun _ => ⟨rfl, rfl, rfl⟩, fun heq => False.elim (hnew heq)⟩))
          rw [hmax]
          refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            ?_, hvp.root_eq⟩
          intro t'; dsimp only
          by_cases ht' : t' = c.1.1
          · subst ht'; simp only [Function.update_self]
          · simp only [Function.update_of_ne ht', hvp.vR_eq t']

private theorem leComp_transmitEBucketMain_top
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × M × Option CCoins)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((transmitEBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep arg).run esL)) := by
  change AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
    ((simulateQ (AuthL11.pImpl prng)
      ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1))
        (2 + Δcka) qep arg).run esP)).run sp)
    (simulateQ AuthL11.lImpl
      ((transmitEBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
        (2 + Δcka) qep arg).run esL))
  rcases arg with ⟨P, m, r_coins⟩; unfold transmitEBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁P, s₁L, h1, h2, hs₁_er, hs₁P_st, hs₁L_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · obtain ⟨hs₁_qep, he1_qep⟩ := epMgmt_le_qep hsync.epoch_le_qep h2
      simp only [h1, h2, hs₁P_st, hs₁L_st, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind,
        bind_assoc]
      have hheq : P.sendsIn (esL.g.epoch P + 1) = true →
          esL.g.epoch P = esL.g.epoch P.other :=
        AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
      have he_lt : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 < qep + 1 := by
        intro hsends; have := he1_qep hsends; omega
      have hpl_cr : P.sendsIn (esL.g.epoch P + 1) = true →
          esP.h.corrRoot.isSome = true → postLeak tL s₁L = true :=
        fun _ hcr => postLeak_epMgmt (hsync.corrRoot_pl hcr) h2
      have hσ_res : P.sendsIn (esL.g.epoch P + 1) = true →
          ∀ s, resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = some s →
            s = (esL.g.st P).root :=
        fun _ s hres => resolveCorrRoot_eq_of_syncTopRaw_main hsync P s hres
      have hσ_sp : P.sendsIn (esL.g.epoch P + 1) = true →
          (postLeak tL s₁L = false ∨ resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = none) →
          esP.h.corrRoot = none ∧ sp.σ = (esL.g.st P).root := by
        intro hsends hdisj
        have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
          (AuthL11.max_epoch_eq_of_eq (hheq hsends)).symm
        rcases hdisj with hpl_s1 | hres_none
        · have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
            rw [postLeak_epMgmt ht h2] at hpl_s1; cases hpl_s1
          have hcr0 : esP.h.corrRoot = none := Option.not_isSome_iff_eq_none.mp fun hcr => by
            rw [hsync.corrRoot_pl hcr] at hpl0; cases hpl0
          exact ⟨hcr0, ((hsync.pl_false_max hpl0).1 P hmax).symm⟩
        · rcases hsync.root_max P hmax with hrP_some | hcr_max | ⟨_, hcr0, hroot_sp⟩
          · rw [hrP_some, resolveCorrRoot] at hres_none; cases hres_none
          · cases hrP : (esP.g.st P).root with
            | some _ => rw [hrP, resolveCorrRoot] at hres_none; cases hres_none
            | none => simp [hrP, resolveCorrRoot, hcr_max, ← hmax] at hres_none
          · exact ⟨hcr0, hroot_sp.symm⟩
      refine (leComp_vSendBucketTop cka prng fs Δcka qep tL par (eraseSt_postLeak hs₁_er)
        (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
        he_lt hpl_cr hσ_res hσ_sp).bind ?_
      rintro ⟨⟨res_vsP, hP1⟩, sp1⟩ ⟨res_vsL, hL1⟩ hvs
      rcases hvs with hnone | ⟨vpP', vpL', c, hP_eq, hL_eq, hc_hdr, hvp', hc_rel, hb1,
        hft1, htop1, hsends_props, hns_props⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine AuthL11.LeComp.pure ?_
        have hrec_eq : (⟨⟨P, s₁P.epoch P, s₁P.idx P + 1⟩, m, c⟩ : Record M (Header T × E)) =
            ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩ := by
          rw [AuthL11.eraseSt_epoch hs₁_er, AuthL11.eraseSt_idx hs₁_er]
        let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩
        rw [hrec_eq]
        have hs₁_ep : s₁L.epoch P = if P.sendsIn (esL.g.epoch P + 1) then esL.g.epoch P + 1
            else esL.g.epoch P := by rw [hs₁_ep_fn]; split <;> simp
        have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
          intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
        have hs₁_comp := hs₁_comp_imp hsync.comp_inv
        have her_rec : AuthL11.eraseSt (s₁P.record (2 + Δcka) P vpP' recL false) =
            AuthL11.eraseSt (s₁L.record (2 + Δcka) P vpL' recL false) :=
          AuthL11.eraseSt_record hs₁_er (2 + Δcka) P vpP' vpL' recL false
        have hvp_rec : ∀ Q, RelVPBucket ((s₁L.record (2 + Δcka) P vpL' recL false).epoch Q) Q
            ((s₁P.record (2 + Δcka) P vpP' recL false).st Q)
            ((s₁L.record (2 + Δcka) P vpL' recL false).st Q) := by
          intro Q; dsimp only [SM.GameState.record]
          by_cases hQ : Q = P
          · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
          · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st]; exact hsync.vp_rel Q
        have htr_ep : ∀ r ∈ (s₁L.record (2 + Δcka) P vpL' recL false).trans,
            r.pos.epoch ≤ (s₁L.record (2 + Δcka) P vpL' recL false).epoch r.pos.sender ∧
              r.ct.1.1 = r.pos.epoch := by
          intro r hr; dsimp only [SM.GameState.record] at hr ⊢
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact ⟨le_rfl, by dsimp only [recL]; rw [hc_hdr, hs₁_ep]⟩
          · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
            refine ⟨?_, h_eq⟩
            by_cases hQ : r.pos.sender = P
            · rw [hQ, hs₁_ep]; rw [hQ] at h_le; split <;> omega
            · rw [hs₁_ep_other _ hQ]; exact h_le
        by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
        · obtain ⟨hpl_f, hpl_t, ⟨T', k, hT', hcP_self, hcL_self⟩, hcP_other, hcL_other,
            hlcP1, hlcL1⟩ := hsends_props hsends
          have heq_other := hheq hsends
          have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P :=
            AuthL11.max_epoch_eq_of_eq heq_other
          have hs₁_ep_eq : s₁L.epoch = Function.update esL.g.epoch P (esL.g.epoch P + 1) := by
            rw [hs₁_ep_fn]; simp [hsends]
          have hmax_new : max (s₁L.epoch .A) (s₁L.epoch .B) = esL.g.epoch P + 1 := by
            rw [hs₁_ep_eq, AuthL11.max_epoch_update_succ heq_other]
          have hQ_e1 : ∀ Q, s₁L.epoch Q = esL.g.epoch P + 1 → Q = P := by
            intro Q hQ; rw [hs₁_ep_eq] at hQ
            by_cases hQP : Q = P
            · exact hQP
            · rw [Function.update_of_ne hQP] at hQ
              cases Q <;> cases P <;> simp [Party.other] at hQP heq_other hQ <;> omega
          refine Or.inr ⟨rfl, ⟨hsync.abortP, hsync.abortL, her_rec, hvp_rec, hc_rel, hft1, htop1, hb1,
            hs₁_qep, AuthL11.comp_inv_record s₁L (2 + Δcka) P vpL' _ false rfl hs₁_comp, htr_ep,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨by dsimp only; rw [hlcP1, hlcL1, hsync.lc_inv.1], fun e he => by
              dsimp only at he; rw [hlcL1] at he
              split at he
              · injection he with he; subst he; exact hsync.epoch_le_qep P
              · exact hsync.lc_inv.2 e he⟩⟩⟩
          · intro Q hns_Q hpos_Q Tc hTc
            dsimp only [SM.GameState.record] at hns_Q hpos_Q hTc ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte] at hTc ⊢
              rw [hT'] at hTc; cases hTc; exact ⟨vpL'.root, k, hcL_self⟩
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcL_other _ hne]; exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · intro r hr hpos_r Tc hTc
            dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · dsimp only at hTc ⊢; rw [hc_hdr] at hTc; dsimp only at hTc
              rw [hs₁_ep, hsends]; simp only [↓reduceIte]; rw [hT'] at hTc; cases hTc
              exact ⟨vpL'.root, k, hcL_self⟩
            · have hr_mem : r ∈ esL.g.trans := hs₁_trans ▸ hr'
              have hr_le := (hsync.trans_epoch r hr_mem).1
              have hne : r.pos.epoch ≠ esL.g.epoch P + 1 := by
                cases hS : r.pos.sender <;> cases P <;>
                  simp [Party.other, hS] at heq_other hr_le ⊢ <;> omega
              rw [hcL_other _ hne]; exact hsync.trans_cache r hr_mem hpos_r Tc hTc
          · intro Q; dsimp only [SM.GameState.record]; rw [hs₁_ep_eq]
            cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
          · intro Q hlt_Q; dsimp only [SM.GameState.record] at hlt_Q ⊢; rw [hs₁_ep_eq] at hlt_Q ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hsends
            · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          · intro Q1 Q2 heq_ep; dsimp only [SM.GameState.record] at heq_ep ⊢
            have hQ12 : Q1 = Q2 := by
              rw [hs₁_ep_eq] at heq_ep
              cases Q1 <;> cases Q2 <;> cases P <;> simp [Party.other] at heq_other heq_ep ⊢ <;> omega
            subst hQ12; rfl
          · intro Q Tc σc k0 hc_eq; dsimp only [SM.GameState.record] at hc_eq ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [hs₁_ep, hsends] at hc_eq
              simp only [↓reduceIte] at hc_eq; rw [hcL_self] at hc_eq; injection hc_eq with hc_eq
              exact (Prod.mk.inj (Prod.mk.inj hc_eq).2).1.symm
            · simp only [Function.update_of_ne hQ, hs₁L_st]; rw [hs₁_ep_other Q hQ] at hc_eq
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcL_other _ hne] at hc_eq; exact hsync.cache_rootL Q Tc σc k0 hc_eq
          · intro hcr1_none Q Tc σp k0 hc_eq
            dsimp only [SM.GameState.record] at hcr1_none hc_eq ⊢
            have hcr0_none : esP.h.corrRoot = none := by
              cases hpl_s1 : postLeak tL s₁L
              · have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
                  rw [postLeak_epMgmt ht h2] at hpl_s1; cases hpl_s1
                exact Option.not_isSome_iff_eq_none.mp fun hcr => by
                  rw [hsync.corrRoot_pl hcr] at hpl0; cases hpl0
              · rcases (hpl_t hpl_s1).2 with hcr_eq | ⟨hcr0, _⟩
                · exact hcr_eq.symm.trans hcr1_none
                · exact hcr0
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [hs₁_ep, hsends] at hc_eq
              simp only [↓reduceIte] at hc_eq; rw [hcP_self] at hc_eq; injection hc_eq with hc_eq
              exact (Prod.mk.inj (Prod.mk.inj hc_eq).2).1
            · simp only [Function.update_of_ne hQ, hs₁P_st]; rw [hs₁_ep_other Q hQ] at hc_eq
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcP_other _ hne] at hc_eq; exact hsync.cache_rootP_none hcr0_none Q Tc σp k0 hc_eq
          · intro hcr1_some; dsimp only [SM.GameState.record] at hcr1_some ⊢
            cases hpl_s1 : postLeak tL s₁L
            · rw [(hpl_f hpl_s1).2.2] at hcr1_some; cases hcr1_some
            · exact hpl_s1
          · intro eC σC hcr1_eq; dsimp only [SM.GameState.record] at hcr1_eq ⊢
            have hpl_s1 : postLeak tL s₁L = true := by
              cases hp : postLeak tL s₁L
              · rw [(hpl_f hp).2.2] at hcr1_eq; cases hcr1_eq
              · rfl
            rw [hmax_new]
            rcases (hpl_t hpl_s1).2 with hcr_eq | ⟨_, hcr_new⟩
            · rw [hcr_eq] at hcr1_eq
              obtain ⟨heC_le, heC_root, heC_cache⟩ := hsync.corrRoot_rel eC σC hcr1_eq
              rw [hmax_old] at heC_le
              refine ⟨by omega, fun Q hQ_ep => ?_, fun Tc σl k0 hc_eq => ?_⟩
              · have hQP : Q ≠ P := by intro rfl; rw [hs₁_ep, hsends] at hQ_ep; simp at hQ_ep; omega
                simp only [Function.update_of_ne hQP, hs₁L_st]
                rw [hs₁_ep_other Q hQP] at hQ_ep; exact heC_root Q hQ_ep
              · rw [hcL_other eC (by omega)] at hc_eq; exact heC_cache Tc σl k0 hc_eq
            · rw [hcr_new] at hcr1_eq; injection hcr1_eq with hpair
              rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
              refine ⟨by omega, fun Q hQ_ep => ?_, fun Tc σl k0 hc_eq => ?_⟩
              · have hQP : Q ≠ P := by intro rfl; rw [hs₁_ep, hsends] at hQ_ep; simp at hQ_ep
                simp only [Function.update_of_ne hQP, hs₁L_st]
                rw [hs₁_ep_other Q hQP] at hQ_ep; exact hsync.same_epoch_rootL P Q hQ_ep.symm
              · rw [hcL_other _ (by omega)] at hc_eq
                exact (hsync.cache_rootL P Tc σl k0 hc_eq).symm
          · intro Q hge his; dsimp only [SM.GameState.record] at hge his ⊢
            cases hpl_s1 : postLeak tL s₁L
            · by_cases hQ : Q = P
              · subst Q; simp only [Function.update_self] at his
                rw [hs₁_ep, hsends] at hge; simp only [↓reduceIte] at hge
                have hnlt : ¬ (esL.g.epoch P + 1 < healEpoch tL) := by omega
                simp [(hpl_f hpl_s1).1, hnlt] at his
              · simp only [Function.update_of_ne hQ, hs₁P_st] at his; rw [hs₁_ep_other Q hQ] at hge
                have := postLeak_epMgmt (hsync.root_ge_tH_pl Q hge his) h2
                rw [hpl_s1] at this; cases this
            · exact hpl_s1
          · intro hcr1_none Q0 hge his
            dsimp only [SM.GameState.record] at hcr1_none hge his ⊢
            have hpl_s1 : postLeak tL s₁L = true := by
              cases hp : postLeak tL s₁L
              · by_cases hQ0 : Q0 = P
                · subst Q0; simp only [Function.update_self] at his
                  rw [hs₁_ep, hsends] at hge; simp only [↓reduceIte] at hge
                  have hnlt : ¬ (esL.g.epoch P + 1 < healEpoch tL) := by omega
                  simp [(hpl_f hp).1, hnlt] at his
                · simp only [Function.update_of_ne hQ0, hs₁P_st] at his; rw [hs₁_ep_other Q0 hQ0] at hge
                  have := postLeak_epMgmt (hsync.root_ge_tH_pl Q0 hge his) h2
                  rw [hp] at this; cases this
              · rfl
            have hvpP_some : vpP'.root = some vpL'.root := (hpl_t hpl_s1).1
            rw [hmax_new]
            refine ⟨fun Q hQ => ?_, fun Tc σl k0 hc_eq => ?_⟩
            · rw [hQ_e1 Q hQ]; simp only [Function.update_self]; exact hvpP_some
            · rw [hcL_self] at hc_eq; injection hc_eq with hc_eq
              rcases Prod.mk.inj hc_eq with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, _⟩
              exact ⟨k, by rw [hcP_self, hvpP_some]⟩
          · intro Q hQ_max; dsimp only [SM.GameState.record] at hQ_max ⊢
            rw [hmax_new] at hQ_max ⊢; rw [hQ_e1 Q hQ_max]; simp only [Function.update_self]
            cases hpl_s1 : postLeak tL s₁L
            · obtain ⟨hvpP_r, hsp_σ, hcr_n⟩ := hpl_f hpl_s1
              by_cases hlt : esL.g.epoch P + 1 < healEpoch tL
              · exact Or.inl (by simp [hvpP_r, hlt])
              · exact Or.inr (Or.inr ⟨by simp [hvpP_r, hlt], hcr_n, hsp_σ.symm⟩)
            · exact Or.inl (hpl_t hpl_s1).1
          · intro Tc σc k0 hc_max; dsimp only [SM.GameState.record] at hc_max ⊢
            rw [hmax_new] at hc_max ⊢; rw [hcL_self] at hc_max; injection hc_max with hc_max
            rcases Prod.mk.inj hc_max with ⟨rfl, hrest⟩
            rcases Prod.mk.inj hrest with ⟨rfl, _⟩
            cases hpl_s1 : postLeak tL s₁L
            · obtain ⟨hvpP_r, hsp_σ, hcr_n⟩ := hpl_f hpl_s1
              by_cases hlt : esL.g.epoch P + 1 < healEpoch tL
              · exact Or.inl ⟨k, by rw [hcP_self]; simp [hvpP_r, hlt]⟩
              · exact Or.inr (Or.inr ⟨hcr_n, hsp_σ.symm⟩)
            · exact Or.inl ⟨k, by rw [hcP_self, (hpl_t hpl_s1).1]⟩
          · intro hpl_s1; dsimp only [SM.GameState.record] at hpl_s1
            have hsp_σ := (hpl_f hpl_s1).2.1
            refine ⟨fun Q hQ => ?_, fun Tc σc k0 hc => ?_⟩
            · dsimp only [SM.GameState.record] at hQ ⊢; rw [hmax_new] at hQ
              rw [hQ_e1 Q hQ]; simp only [Function.update_self]; exact hsp_σ.symm
            · dsimp only [SM.GameState.record] at hc; rw [hmax_new, hcL_self] at hc
              injection hc with hc
              exact (Prod.mk.inj (Prod.mk.inj hc).2).1.symm.trans hsp_σ.symm
        · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
          obtain ⟨hhP1, hsp_eq, hhL1, hvpP_r, hvpL_r, hcur_eq⟩ := hns_props hns
          dsimp only at hhP1 hsp_eq hhL1; subst hhP1 hsp_eq hhL1
          have hs₁L_eq : s₁L = esL.g := postLeak_epMgmt_of_sendsIn_false_main hns h2
          subst hs₁L_eq
          have hrP_rec : ∀ Q, ((s₁P.record (2 + Δcka) P vpP' recL false).st Q).root =
              (esP.g.st Q).root := by
            intro Q; dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hvpP_r]
            · simp only [Function.update_of_ne hQ, hs₁P_st]
          have hrL_rec : ∀ Q, ((esL.g.record (2 + Δcka) P vpL' recL false).st Q).root =
              (esL.g.st Q).root := by
            intro Q; dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hvpL_r]
            · simp only [Function.update_of_ne hQ]
          refine Or.inr ⟨rfl, ⟨hsync.abortP, hsync.abortL, her_rec, hvp_rec, hc_rel, hft1, htop1, hb1,
            hs₁_qep, AuthL11.comp_inv_record esL.g (2 + Δcka) P vpL' _ false rfl hs₁_comp, htr_ep,
            ?_, ?_, hsync.epoch_le, hsync.epoch_sends,
            fun Q1 Q2 heq => by dsimp only at heq ⊢; rw [hrL_rec Q1, hrL_rec Q2]; exact hsync.same_epoch_rootL Q1 Q2 heq,
            fun Q Tc σc k0 hc => by dsimp only at hc ⊢; rw [hrL_rec Q]; exact hsync.cache_rootL Q Tc σc k0 hc,
            fun hcr Q Tc σp k0 hc => by dsimp only at hcr hc ⊢; rw [hrP_rec Q]; exact hsync.cache_rootP_none hcr Q Tc σp k0 hc,
            hsync.corrRoot_pl,
            fun eC σC hcr => by
              obtain ⟨h1, h2, h3⟩ := hsync.corrRoot_rel eC σC hcr
              exact ⟨h1, fun Q hQ => by dsimp only at hQ ⊢; rw [hrL_rec Q]; exact h2 Q hQ, h3⟩,
            fun Q hge his => by dsimp only at hge his ⊢; rw [hrP_rec Q] at his; exact hsync.root_ge_tH_pl Q hge his,
            fun hcr Q0 hge his => by
              dsimp only at hcr hge his ⊢; rw [hrP_rec Q0] at his
              obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr Q0 hge his
              exact ⟨fun Q hQ => by rw [hrP_rec Q, hrL_rec Q]; exact hm1 Q hQ, hm2⟩,
            fun Q hQ => by dsimp only at hQ ⊢; rw [hrP_rec Q, hrL_rec Q]; exact hsync.root_max Q hQ,
            hsync.cache_max,
            fun hpl => by
              obtain ⟨hp1, hp2⟩ := hsync.pl_false_max hpl
              exact ⟨fun Q hQ => by dsimp only at hQ ⊢; rw [hrL_rec Q]; exact hp1 Q hQ, hp2⟩,
            hsync.lc_inv⟩⟩
          · intro Q hns_Q hpos_Q Tc hTc; dsimp only [SM.GameState.record] at hns_Q hpos_Q hTc ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self] at hTc
              rw [hcur_eq] at hTc; exact hsync.vp_curCka P hns hpos_Q Tc hTc
            · simp only [Function.update_of_ne hQ] at hTc
              exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · intro r hr hpos_r Tc hTc; dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · dsimp only at hpos_r hTc ⊢; rw [hc_hdr] at hTc; dsimp only at hTc
              rw [hcur_eq] at hTc; exact hsync.vp_curCka P hns hpos_r Tc hTc
            · exact hsync.trans_cache r hr' hpos_r Tc hTc

private theorem leComp_deliverEMain_top [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng) ((deliverE
        (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1)) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl ((deliverE (hooksLocalBucketMain cka prng fs Δcka qep tL par) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c⟩; unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none => simp only [StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esP.g.mustBeCorrect fs.maxSkip P r = esL.g.mustBeCorrect fs.maxSkip P r := by
        simp [SM.GameState.mustBeCorrect, AuthL11.eraseSt_comp hsync.g_eq,
          AuthL11.eraseSt_maxAcc hsync.g_eq]
      simp only [hmust_eq, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecvBucketTopMain cka prng fs Δcka qep tL par
        (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
        (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
      rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
      rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htop1⟩ |
        ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
          hft1, htop1, hroot_le, hnew_hit⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_none hL_none; subst hP_none hL_none
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hs1 := syncTopRaw_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1
        by_cases hmust : ((bucketAuthCfg Δcka tL par : SM.Config M).deliverWin &&
            esL.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_set_win hs1⟩)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
      · dsimp only at hP_some hL_some; subst hP_some hL_some
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucketMain, run_commitE_LocalBucketMain,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [AuthL11.eraseSt_chall hsync.g_eq]
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
        have hs_acc := syncTopRaw_of_vRecv_accept hsync hr_pos_ep htle hns hvp'
          hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1 hroot_le hnew_hit (fun hnew => by
            refine ⟨by rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1, fun tn0 htn0 => ?_⟩
            have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2]; exact htn0
            rw [← hnew, ← hr_pos_ep]
            exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2)
        by_cases hwin_cond : (((bucketAuthCfg Δcka tL par : SM.Config M).deliverWin &&
            esL.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg))) = true
        · simp only [hwin_cond, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_set_win hs_acc⟩)
        · simp only [hwin_cond, Bool.false_eq_true, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs_acc⟩)

private theorem leComp_injectEMain_top
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((injectE (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esL.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    refine (leComp_vRecvBucketTopMain cka prng fs Δcka qep tL par
      (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
      (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htop1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
        hft1, htop1, hroot_le, hnew_hit⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none; subst hP_none hL_none
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1⟩)
    · dsimp only at hP_some hL_some; subst hP_some hL_some
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      have hs1 := syncTopRaw_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
      · simp only [hqep, ↓reduceIte]
        rw [AuthL11.eraseSt_trivial hsync.g_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq; rw [heq] at htriv
            have htf := AuthL11.trivial_false_of_safeInj esL.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv; cases htriv
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketMain,
            run_commitE_LocalBucketMain, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncTopRaw_of_vRecv_accept hsync rfl htle hns hvp' hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1
              hroot_le hnew_hit (fun heq => False.elim (hne_e1 heq))⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_set_win hs1⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)

private theorem leComp_deliverForgeEMain_top
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E) × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((deliverForgeE (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_comp hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      rw [AuthL11.eraseSt_inTransit hsync.g_eq]
      by_cases hrej : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos ||
          (c.1 != c'.1)) = true
      · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hrej, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
        have hhdr_eq : c.1 = c'.1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hrej
          exact hrej.2
        have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
          unfold SM.GameState.inTransit at htr
          have hfind := List.find?_some htr
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
          exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
        refine (leComp_vRecvBucketTopMain cka prng fs Δcka qep tL par
          (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
          (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
        rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
        rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htop1⟩ |
          ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
            hft1, htop1, hroot_le, hnew_hit⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1⟩)
        · dsimp only at hP_some hL_some; subst hP_some hL_some
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
          have hs1 := syncTopRaw_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1
          by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
          · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
          · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
            rw [AuthL11.eraseSt_trivial hsync.g_eq]
            by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketMain,
                run_commitE_LocalBucketMain, StateT.run_pure, StateT.run_modify, pure_bind,
                simulateQ_pure]
              have hr_ep := hsync.trans_epoch r hr_mem.1
              have hc'_ep : c'.1.1 = r.pos.epoch := by
                simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hbad_ep
                exact hbad_ep.2
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
                syncTopRaw_of_vRecv_accept hsync rfl htle hns hvp' hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htop1
                  hroot_le hnew_hit (fun hnew => by
                    refine ⟨by rw [hc'_ep, ← hr_mem.2.1]; exact hr_ep.1, fun tn0 htn0 => ?_⟩
                    have hct2 : r.ct.1.2 = some tn0 := by
                      rw [hr_mem.2.2, hhdr_eq]; exact htn0
                    rw [← hnew, hc'_ep]
                    exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2)⟩)
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c'.1.1 = true
              · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncTopRaw_set_win hs1⟩)
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)

private theorem leComp_corrEPaperBucketMain_top
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (P : Party)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1)) P).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((corrEPaperBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par) P).run esL)) := by
  change AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
    ((simulateQ (AuthL11.pImpl prng)
      ((corrEPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1)) P).run esP)).run sp)
    (simulateQ AuthL11.lImpl
      ((corrEPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par) P).run esL))
  unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_corrAllowedPaper hsync.g_eq P]
  by_cases hguard : (false || esL.g.win || !esL.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
    have hb_eq : b_sp = true := hsync.sp_b; subst hb_eq
    have hac_er := AuthL11.eraseSt_afterCorr hsync.g_eq P
    have hvp := hsync.vp_rel P
    have hep_eq : esP.g.epoch = esL.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
    have hpl_eq : postLeak tL esP.g = postLeak tL esL.g := eraseSt_postLeak hsync.g_eq
    have hps_eq : realParty (esP.g.st P) (esP.g.st P).γ (esL.g.st P).root (esP.g.st P).vS (esP.g.st P).vR =
        realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
      dsimp only [realParty]
      rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq, funext hvp.vR_eq]
    have hcomp_ac := AuthL11.comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
      (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv
    simp only [StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc,
      hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
      StateT.run_get, pure_bind]
    rw [hvp.tcur_P, hvp.tcur_L, hep_eq, hpl_eq]
    cases hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root with
    | some σ =>
      have hσ_eq := resolveCorrRoot_eq_of_syncTopRaw_main hsync P σ hres; subst hσ_eq
      simp only [hsync.lc_inv.1]
      by_cases hcond : (!(decide (esL.g.epoch P < healEpoch tL)) && esP.h.corrRoot.isNone) = true
      · have hcond' := hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Option.isNone_iff_eq_none, not_lt] at hcond'
        obtain ⟨hge, hcr_none⟩ := hcond'
        have his : ((esP.g.st P).root).isSome = true := by
          cases hr : (esP.g.st P).root <;> simp [resolveCorrRoot, hr, hcr_none] at hres ⊢
        have hpl_true : postLeak tL esL.g = true := hsync.root_ge_tH_pl P hge his
        obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr_none P hge his
        have hpl_ac : postLeak tL (esL.g.afterCorr P) = true := postLeak_afterCorr_of_ge_healEpoch hge
        have he_le_max : esL.g.epoch P ≤ max ((esL.g.afterCorr P).epoch .A) ((esL.g.afterCorr P).epoch .B) := by
          dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; cases P <;> omega
        simp only [hcond, hpl_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, pure_bind]
        refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
          ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
            hsync.table_top, rfl, hsync.epoch_le_qep, hcomp_ac,
            hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
            hsync.same_epoch_rootL, hsync.cache_rootL,
            fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
            fun eC σC hcr => (by
              dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
              exact ⟨he_le_max, fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
            fun _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
            fun Q hQ => Or.inl (hm1 Q hQ), fun Tc σc k hc => Or.inl (hm2 Tc σc k hc),
            fun hpl => (by rw [hpl_ac] at hpl; cases hpl), hsync.lc_inv⟩⟩)
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        by_cases hlc_c : ((!postLeak tL esL.g && esL.h.lc.isNone) &&
            !(decide (esL.g.epoch P < healEpoch tL))) = true
        · simp only [hlc_c, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
              hsync.table_top, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
              fun hcr => postLeak_afterCorr_mono (hsync.corrRoot_pl hcr), hsync.corrRoot_rel,
              fun Q hge his => postLeak_afterCorr_mono (hsync.root_ge_tH_pl Q hge his),
              hsync.some_mono_max, hsync.root_max, hsync.cache_max,
              fun hpl => hsync.pl_false_max (Bool.eq_false_iff.mpr fun ht => (by
                rw [postLeak_afterCorr_mono ht] at hpl; cases hpl)),
              ⟨rfl, fun e he => (by
                dsimp only at he; injection he with he; subst he; exact hsync.epoch_le_qep P)⟩⟩⟩)
        · simp only [hlc_c, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
              hsync.table_top, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
              fun hcr => postLeak_afterCorr_mono (hsync.corrRoot_pl hcr), hsync.corrRoot_rel,
              fun Q hge his => postLeak_afterCorr_mono (hsync.root_ge_tH_pl Q hge his),
              hsync.some_mono_max, hsync.root_max, hsync.cache_max,
              fun hpl => hsync.pl_false_max (Bool.eq_false_iff.mpr fun ht => (by
                rw [postLeak_afterCorr_mono ht] at hpl; cases hpl)), hsync.lc_inv⟩⟩)
    | none =>
      simp only [hsync.lc_inv.1]
      by_cases hcond : ((!postLeak tL esL.g && esP.h.corrRoot.isNone &&
          !(decide (esL.g.epoch P < healEpoch tL))) &&
          (esL.g.epoch P == max (esL.g.epoch .A) (esL.g.epoch .B))) = true
      · have hcond' := hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Option.isNone_iff_eq_none, not_lt, beq_iff_eq] at hcond'
        rcases hcond' with ⟨⟨⟨hpl0, hcr_none⟩, hge⟩, he_max⟩
        have hpl_ac : postLeak tL (esL.g.afterCorr P) = true := postLeak_afterCorr_of_ge_healEpoch hge
        have hge_dec : decide (esL.g.epoch P < healEpoch tL) = false := decide_eq_false (not_lt.mpr hge)
        simp only [hcond, ↓reduceIte, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc]
        cases prf_sp
        · have hσ_eq : σ_sp = (esL.g.st P).root := ((hsync.pl_false_max hpl0).1 P he_max).symm
          subst hσ_eq
          cases hlc_n : esL.h.lc.isNone
          · simp only [hpl0, hge_dec, Bool.not_false, Bool.true_and, Bool.and_true,
              Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
              ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
                hsync.table_top, rfl, hsync.epoch_le_qep, hcomp_ac,
                hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
                hsync.same_epoch_rootL, hsync.cache_rootL,
                fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
                fun eC σC hcr => (by
                  dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                  exact ⟨(by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; omega),
                    fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                    fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
                fun _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
                fun Q hQ => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hQ ⊢
                  rw [he_max, hsync.same_epoch_rootL P Q (he_max.trans hQ.symm)])),
                fun Tc σc k hc => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hc ⊢
                  rw [he_max, (hsync.cache_rootL P Tc σc k (he_max.symm ▸ hc)).symm])),
                fun hpl => (by rw [hpl_ac] at hpl; cases hpl), hsync.lc_inv⟩⟩)
          · simp only [hpl0, hge_dec, Bool.not_false, Bool.and_true,
              Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
              ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
                hsync.table_top, rfl, hsync.epoch_le_qep, hcomp_ac,
                hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
                hsync.same_epoch_rootL, hsync.cache_rootL,
                fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
                fun eC σC hcr => (by
                  dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                  exact ⟨(by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; omega),
                    fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                    fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
                fun _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
                fun Q hQ => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hQ ⊢
                  rw [he_max, hsync.same_epoch_rootL P Q (he_max.trans hQ.symm)])),
                fun Tc σc k hc => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hc ⊢
                  rw [he_max, (hsync.cache_rootL P Tc σc k (he_max.symm ▸ hc)).symm])),
                fun hpl => (by rw [hpl_ac] at hpl; cases hpl),
                ⟨rfl, fun e he => (by
                  dsimp only at he; injection he with he; subst he; exact hsync.epoch_le_qep P)⟩⟩⟩)
        · simp only [↓reduceIte, pure_bind, abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          pure_bind, abortE, StateT.run_bind, StateT.run_modify]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private theorem leComp_implEDFPaperBucketRawMain_top
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng) ((implEDFPaperBucketRaw
        (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esP)).run sp)
      (simulateQ AuthL11.lImpl ((implEDFPaperBucketRaw
        (hooksLocalBucketMain cka prng fs Δcka qep tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esL)) := by
  rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
  · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, AuthL11.lImpl, StateT.run_lift,
      simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · exact leComp_transmitEBucketMain_top cka prng fs Δcka qep tL par arg hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · exact leComp_deliverEMain_top cka prng fs Δcka qep tL par arg hsync
  · exact leComp_injectEMain_top cka prng fs Δcka qep tL par arg hsync
  · exact leComp_corrEPaperBucketMain_top cka prng fs Δcka qep tL par P hsync
  · exact leComp_deliverForgeEMain_top cka prng fs Δcka qep tL par df hsync

private def StepRelBucketTopMain (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) {α : Type}
    (x : (α × (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K)
    (y : α × (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) : Prop :=
  x.1.2.1.abort = true ∨ (x.1.1 = y.1 ∧ x.1.2.2 = y.2.2 ∧ SyncTopRaw prng Δcka qep tL x.1.2.1 x.2 y.2.1)

private def stepPBucketTopMain [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (AuthL11.pImpl prng) ((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
    (implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) q).run stP)).run sp

private def stepLBucketTopMain [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp ((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) :=
  simulateQ AuthL11.lImpl ((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
    (implEDFPaperBucketRaw (hooksLocalBucketMain cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) q).run stL)

private theorem leComp_stepPBucketTopMain_stepLBucketTopMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncTopRaw prng Δcka qep tL stP.1 sp stL.1) :
    AuthL11.LeComp (StepRelBucketTopMain prng Δcka qep tL)
      (stepPBucketTopMain cka prng fs Δcka qep tL par q stP sp)
      (stepLBucketTopMain cka prng fs Δcka qep tL par q stL) := by
  rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
  dsimp only at hwinEp hsync; subst hwinEp
  unfold stepPBucketTopMain stepLBucketTopMain withWinEpDF
  simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine (leComp_implEDFPaperBucketRawMain_top cka prng fs Δcka qep tL par q hsync).bind ?_
  rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨hu, hsync'⟩)
  · exact AuthL11.LeComp.pure (Or.inl hab)
  · dsimp only at hu; subst hu
    rw [AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_win hsync'.g_eq]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)

private theorem stepPBucketTopMain_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) (hab : stP.1.abort = true) :
    ∀ r ∈ support (stepPBucketTopMain cka prng fs Δcka qep tL par q stP sp),
      r.1.2.1.abort = true := by
  intro r hr; rcases stP with ⟨esP, winEpP⟩; dsimp only at hab
  rcases q with n | (((((q | q) | q) | q) | P) | df)
  · simp [stepPBucketTopMain, withWinEpDF, implEDFPaperBucketRaw,
      coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind, simulateQ_query,
      map_eq_bind_pure_comp, bind_assoc] at hr
    rcases hr with ⟨_, _, rfl⟩; exact hab
  · simp [stepPBucketTopMain, withWinEpDF, implEDFPaperBucketRaw, transmitEBucket, hab] at hr
    rcases hr with rfl; exact hab
  · simp [stepPBucketTopMain, withWinEpDF, implEDFPaperBucketRaw, challEBucket] at hr
    rcases hr with rfl; exact hab
  all_goals
    simp [stepPBucketTopMain, withWinEpDF, implEDFPaperBucketRaw,
      deliverE, injectE, corrEPaperBucket, deliverForgeE, hab] at hr
    rcases hr with rfl; exact hab

private def runPBucketTopMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (AuthL11.pImpl prng)
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par (qep + 1))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stP)).run sp
  pure (authOutBucketPaperAt (2 + Δcka) tL (qep + 1) r.1.2)

private def runLBucketTopMainNone
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFPaperBucketRaw (hooksLocalBucketMain cka prng fs Δcka qep tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stL)
  pure (authOutBucketPaper (2 + Δcka) tL r.2 && decide (r.2.1.h.lc = none))

private theorem runPBucketTopMain_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketTopMain cka prng fs Δcka qep tL par (pure b) stP sp =
      pure (authOutBucketPaperAt (2 + Δcka) tL (qep + 1) stP) := by simp [runPBucketTopMain]

private theorem runLBucketTopMainNone_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketTopMainNone cka prng fs Δcka qep tL par (pure b) stL =
      pure (authOutBucketPaper (2 + Δcka) tL stL && decide (stL.1.h.lc = none)) := by
  simp [runLBucketTopMainNone]

private theorem runPBucketTopMain_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketTopMain cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stP sp =
      stepPBucketTopMain cka prng fs Δcka qep tL par q stP sp >>= fun r =>
        runPBucketTopMain cka prng fs Δcka qep tL par (k r.1.1) r.1.2 r.2 := by
  simp [runPBucketTopMain, stepPBucketTopMain, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runLBucketTopMainNone_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketTopMainNone cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stL =
      stepLBucketTopMain cka prng fs Δcka qep tL par q stL >>= fun r =>
        runLBucketTopMainNone cka prng fs Δcka qep tL par (k r.1) r.2 := by
  simp [runLBucketTopMainNone, stepLBucketTopMain, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPBucketTopMain_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K} (hab : stP.1.abort = true) :
    𝒟[runPBucketTopMain cka prng fs Δcka qep tL par oa stP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stP sp with
  | pure b =>
    rw [runPBucketTopMain_pure]
    rcases stP with ⟨esP, winEpP⟩; dsimp only at hab
    cases winEpP <;> simp [authOutBucketPaperAt, authOutBucketPaper, authOutBucket, authOut, hab]
  | query_bind q k ih =>
    rw [runPBucketTopMain_query_bind]
    exact AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPBucketTopMain_abort cka prng fs Δcka qep tL par q stP sp hab r hr)

private theorem runPBucketTopMain_le_runLBucketTopMainNone
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncTopRaw prng Δcka qep tL stP.1 sp stL.1) :
    𝒟[runPBucketTopMain cka prng fs Δcka qep tL par oa stP sp] {true} ≤
      𝒟[runLBucketTopMainNone cka prng fs Δcka qep tL par oa stL] {true} := by
  induction oa using OracleComp.inductionOn generalizing stP sp stL with
  | pure b' =>
    rw [runPBucketTopMain_pure, runLBucketTopMainNone_pure]
    rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
    dsimp only at hwinEp hsync; subst hwinEp
    have houtBase : authOutBucketPaper (2 + Δcka) tL (esP, winEpP) =
        authOutBucketPaper (2 + Δcka) tL (esL, winEpP) := by
      cases winEpP with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketPaper, authOutBucket, authOut]
        rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
          AuthL11.eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    have hout_eq : authOutBucketPaperAt (2 + Δcka) tL (qep + 1) (esP, winEpP) =
        (authOutBucketPaper (2 + Δcka) tL (esL, winEpP) && decide (esL.h.lc = none)) := by
      unfold authOutBucketPaperAt
      rw [houtBase, hsync.lc_inv.1]
      cases hlc : esL.h.lc with
      | none => simp
      | some e =>
        simp [Nat.not_le.mpr (Nat.lt_succ_of_le (hsync.lc_inv.2 e hlc))]
    rw [hout_eq]
  | query_bind q k ih =>
    rw [runPBucketTopMain_query_bind, runLBucketTopMainNone_query_bind]
    refine leComp_stepPBucketTopMain_stepLBucketTopMain cka prng fs Δcka qep tL par q
      hwinEp hsync _ _ ?_
    rintro ⟨⟨uP, stP'⟩, sp'⟩ ⟨uL, stL'⟩ (hab | ⟨hu, hwinEp', hsync'⟩)
    · rw [runPBucketTopMain_abort cka prng fs Δcka qep tL par (k uP) hab]; exact zero_le
    · dsimp only at hu; subst hu; exact ih uP hwinEp' hsync'

private theorem syncTopRaw_init_main
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (γA γB : Γ) (ss : SS) (rs : RS) (σP : Option Sig) (σL : Sig)
    (hP0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    (hL0 : LocalBucketState T Sig K I) (hσ_rel : ∀ s, σP = some s → s = σL)
    (hσP_eq : σP = if 0 < healEpoch tL then some σL else none)
    (hsp_σ : sp0.σ = σL) (hcr0 : hP0.corrRoot = none) (hb0 : sp0.b = true)
    (hcP0 : hP0.cache = fun _ => none) (hlcP0 : hP0.lc = none)
    (hcL0 : hL0.cache = fun _ => none) (hlcL0 : hL0.lc = none)
    (hft0 : ∀ t', t' < qep + 1 → hP0.fTable t' = hL0.fTable t')
    (htop0 : sp0.table = hL0.fTable (qep + 1)) :
    SyncTopRaw (M := M) (E := E) prng Δcka qep tL
      { g := { st := fun P => match P with | .A => (mkParties γA γB σP ss rs).1 | .B => (mkParties γA γB σP ss rs).2, b := false }, h := hP0 } sp0
      { g := { st := fun P => match P with | .A => (mkParties γA γB σL ss rs).1 | .B => (mkParties γA γB σL ss rs).2, b := false }, h := hL0 } := by
  refine ⟨rfl, rfl, rfl,
    fun P => (by cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hσ_rel⟩),
    fun t' => (by rw [hcP0, hcL0]; exact Or.inl ⟨rfl, rfl⟩),
    hft0, htop0, hb0, fun _ => (by simp),
    fun _ hpos => (by cases hpos), fun _ hr => (by cases hr),
    fun _ _ hpos => (by simp at hpos), fun _ hr => (by cases hr),
    fun _ => (by simp), fun _ hlt => (by simp at hlt),
    fun P Q _ => (by cases P <;> cases Q <;> rfl),
    fun _ _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc),
    fun _ _ _ _ _ hc => (by dsimp only at hc; rw [hcP0] at hc; cases hc),
    fun hcr => (by dsimp only at hcr; rw [hcr0] at hcr; cases hcr),
    fun _ _ hcr => (by dsimp only at hcr; rw [hcr0] at hcr; cases hcr),
    fun P hge his => ?_, fun _ P hge his => ?_, fun P _ => ?_,
    fun _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc),
    fun _ => ⟨fun P _ => (by cases P <;> exact hsp_σ.symm),
      fun _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc)⟩,
    ⟨by dsimp only; rw [hlcP0, hlcL0], fun _ he => by dsimp only at he; rw [hlcL0] at he; cases he⟩⟩
  · dsimp only at hge; have hnlt : ¬ (0 < healEpoch tL) := by omega
    cases P <;> simp [mkParties, hσP_eq, hnlt] at his
  · dsimp only at hge; have hnlt : ¬ (0 < healEpoch tL) := by omega
    cases P <;> simp [mkParties, hσP_eq, hnlt] at his
  · by_cases hlt : 0 < healEpoch tL
    · exact Or.inl (by cases P <;> simp [mkParties, hσP_eq, hlt])
    · exact Or.inr (Or.inr ⟨by cases P <;> simp [mkParties, hσP_eq, hlt],
        hcr0, by cases P <;> exact hsp_σ.symm⟩)

private theorem prng_branch_true_redPRNGAuthDFPaperBucketHybridMain_top_le_lcEq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (_htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (qep + 1) A)] {true} ≤
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some (qep + 1)) A] {true} +
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par none A] {true} := by
  refine le_trans ?_ le_add_self
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuthDFPaperBucketMain
    localAuthDFPaperBucketMainLcEq engRunDFPaperBucket initPRNGBucketHybrid initLocalBucket
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    AuthL11.simulateQ_pImpl_run_lift_sampleT, AuthL11.simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootBucketTop (T := T) prng (3 + Δcka) qep tL par 0 false lam none (prng.init kr)
    ({} : PRNGBucketState T Sig K I) { σ := prng.init kr, b := true }
    ({} : LocalBucketState T Sig K I) (by omega) (Nat.zero_lt_succ qep) rfl (fun _ _ => rfl) rfl
    (by simp) (fun _ h => by simp [resolveCorrRoot] at h) (fun _ => ⟨rfl, rfl⟩)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL⟩, hL0⟩ hrel0
  rcases hrel0 with hnone | ⟨σP, σL', k', hres_eq, hL_eq, hσ_rel, hpl_f, _, hb0, hcP0, hlcP0, hcL0, hlcL0, hft0, htop0⟩
  · dsimp only at hnone; subst hnone; simp
  · dsimp only at hres_eq hL_eq; injection hL_eq with hσL_eq hk_eq; subst hres_eq hσL_eq hk_eq
    obtain ⟨hσP_eq, hsp_σ, hcr0⟩ := hpl_f rfl
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc, Function.comp_apply]
    exact runPBucketTopMain_le_runLBucketTopMainNone (stP := (_, none)) (stL := (_, none))
      cka prng fs Δcka qep tL par A rfl
      (syncTopRaw_init_main prng Δcka qep tL (cka.initA kc) (cka.initB kc)
        (fs.initSender kL) (fs.initReceiver kL) σP σL hP0 sp0 hL0
        hσ_rel hσP_eq hsp_σ hcr0 hb0 hcP0 hlcP0 hcL0 hlcL0 hft0 htop0)


private theorem T1_gate_split [DecidableEq T] [DecidableEq M] [DecidableEq E] (Δ : ℕ) (tL : Option ℕ) (t : ℕ)
    (st : BSt Γ T Sig SS RS M E I K) :
    authOutBucketPaperAt Δ tL t st =
      ((authOutBucketPaper Δ tL st && decide (st.1.h.lc = some t)) ||
        authOutBucketPaperAt Δ tL (t + 1) st) :=
  authOutBucketPaperAt_le_lcOpt_or_succ Δ tL t st

private theorem receiverOf_eq_of_partyPar_senderOf_eq {e1 e2 : ℕ}
    (h : partyPar (Party.senderOf e1) = partyPar (Party.senderOf e2)) :
    Party.receiverOf e1 = Party.receiverOf e2 := by
  unfold Party.senderOf at h
  unfold Party.receiverOf Party.senderOf Party.other
  split_ifs at h ⊢ <;> simp_all [partyPar]

private theorem receiverOf_sendsIn_false (n : ℕ) :
    (Party.receiverOf n).sendsIn n = false := by
  dsimp only [Party.receiverOf, Party.senderOf, Party.other, Party.sendsIn]
  by_cases h : n % 2 = 1
  · have hne : n % 2 ≠ 0 := by omega
    simp [h]
  · have heq : n % 2 = 0 := by omega
    simp [heq]

private theorem ltOpt_of_healEpoch_le {tL : Option ℕ} {e : ℕ} (h : healEpoch tL ≤ e) :
    ltOpt tL e = true := by
  cases tL with
  | none => rfl
  | some l => simp [healEpoch] at h; simp [ltOpt]; omega

private def DoomedLcEqMain [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
      (PRNGBucketState T Sig K I) × Option ℕ) : Prop :=
  let es := st.1
  es.abort = true ∨
  (es.g.win = true ∧ (es.h.lc ≠ some t ∨ authOutBucketPaper (2 + Δcka) tL st = false)) ∨
  (es.g.win = false ∧ es.h.lc.isSome = true ∧ es.h.lc ≠ some t) ∨
  (es.g.win = false ∧ (Party.receiverOf (t + 1), t) ∈ es.g.corrs ∧
    partyPar (Party.senderOf (t + 1)) = par) ∨
  (es.g.win = false ∧ es.h.lc = none ∧
    (∀ Q, (es.g.st Q).id = Q ∧ (es.g.st Q).tcur = es.g.epoch Q) ∧
    (∀ r ∈ es.g.trans, r.ct.1.1 = r.pos.epoch) ∧
    ((∀ Q, t + 1 ≤ es.g.epoch Q) ∨
      (partyPar (Party.senderOf (t + 1)) = par ∧
        t + 1 ≤ es.g.epoch (Party.senderOf (t + 1)) ∧
        t ≤ es.g.epoch (Party.receiverOf (t + 1)))))

private theorem outLcEqMain_eq_false_of_doomed [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
      (PRNGBucketState T Sig K I) × Option ℕ}
    (hd : DoomedLcEqMain Δcka tL par t st) :
    (authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = some t)) = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨_, hlc | hout⟩ | ⟨hwin, _⟩ | ⟨hwin, _⟩ | ⟨hwin, _⟩
  · dsimp only at hab; cases winEp <;> simp [authOutBucketPaper, authOutBucket, authOut, hab]
  · simp [hlc]
  · simp [hout]
  all_goals
    dsimp only at hwin
    cases winEp <;> simp [authOutBucketPaper, authOutBucket, authOut, hwin]

private def stepPBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
      (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :=
  (simulateQ (AuthL11.pImpl prng)
    (((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
        (implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) q).run stP)).run sp

private theorem liftH_run_main
    {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS α : Type}
    (x : HM tspec HS α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) :=
  rfl

private theorem commitE_main_run
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  have hcom : ∀ s' P' old' new',
      (hooksPRNGBucketMain cka prng fs Δcka qep tL par t).commit s' P' old' new' =
        pure (some new') := fun _ _ _ _ => rfl
  have hAcc_st : { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
    have hup : Function.update (s.accept P new pos).st P new = (s.accept P new pos).st := by
      simp [GameState.accept]
    rw [hup]
  have hes_eq : { es with h := es.h } = es := by cases es; rfl
  simp only [commitE, liftH_run_main, hcom, StateT.run_bind, StateT.run_pure, pure_bind,
    hAcc_st]

private theorem stepPBucketLcEqMain_of_raw_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (es es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (ans : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q)
    (hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run es) = pure (ans, es'))
    {r : ((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K}
    (hr : r ∈ support (stepPBucketLcEqMain cka prng fs Δcka qep tL par t q (es, winEp) sp)) :
    r = ((ans, (es', if (!es.g.win && es'.g.win) = true
      then dfQueryTargetEpoch (fun c => c.1.1) q else winEp)), sp) := by
  simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, hraw, pure_bind,
    StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
  exact hr

private theorem stepPBucketLcEqMain_state_eq_of_abort_or_win
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
      (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K)
    (habw : stP.1.abort = true ∨ stP.1.g.win = true) :
    ∀ r ∈ support (stepPBucketLcEqMain cka prng fs Δcka qep tL par t q stP sp),
      r.1.2 = stP := by
  intro r hr
  rcases stP with ⟨es, winEp⟩
  dsimp only at habw
  have hcond : (es.abort || es.g.win) = true := by
    rcases habw with h | h <;> simp [h]
  rcases q with n | (((((q | q) | q) | q) | P) | df)
  · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
      QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
      AuthL11.pImpl, bind_assoc, pure_bind,
      simulateQ_pure] at hr
    rw [StateT.run_bind, mem_support_bind_iff] at hr
    rcases hr with ⟨⟨u, sp1⟩, _, hr2⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr2
    subst hr2
    simp
  · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
        (.inr (.inl (.inl (.inl (.inl (.inl q))))))).run es) = pure (none, es) := by
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
        StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure]
    have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
    subst heq; simp
  · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
        (.inr (.inl (.inl (.inl (.inl (.inr q))))))).run es) = pure (none, es) := by
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure]
    have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
    subst heq; simp
  · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
        (.inr (.inl (.inl (.inl (.inr q)))))).run es) = pure (none, es) := by
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure]
    have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
    subst heq; simp
  · by_cases hinj : (es.abort || es.g.win || (es.g.inTransit q.1.other q.2).isSome ||
        !es.g.safeInj (2 + Δcka)) = true
    · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
          (.inr (.inl (.inl (.inr q))))).run es) = pure (none, es) := by
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
          StateT.run_bind, StateT.run_get, pure_bind, hinj, ↓reduceIte, StateT.run_pure]
      have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
      subst heq; simp
    · exfalso; rcases habw with h | h <;> simp [h] at hinj
  · by_cases hcr : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
    · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
          (.inr (.inl (.inr P)))).run es) = pure (none, es) := by
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
          StateT.run_bind, StateT.run_get, pure_bind, hcr, ↓reduceIte, StateT.run_pure]
      have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
      subst heq; simp
    · exfalso; rcases habw with h | h <;> simp [h] at hcr
  · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
        (.inr (.inr df))).run es) = pure (none, es) := by
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure]
    have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
    subst heq; simp

/-! ### Pure `vRecv` / `deliverE` / `injectE` / `deliverForgeE` Lemmas for `hooksPRNGBucketMain` -/

private theorem vRecv_main_run
    [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E)))
    (h0 : PRNGBucketState T Sig K I) :
    ∃ ans : Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)),
      (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) ctx P vp c rec).run h0 =
        pure (ans, h0) ∧
      (∀ vp' t' i' m', ans = some (some (vp', t', i', m')) →
        t' = c.1.1 ∧ vp.id.sendsIn c.1.1 = false ∧ c.1.1 ≤ vp.tcur + 1 ∧
        vp'.id = vp.id ∧ vp'.tcur = max vp.tcur c.1.1) := by
  unfold vRecv
  have h_fsRecv : ∀ ctx' P' t' rs hdr e ic,
      (hooksPRNGBucketMain cka prng fs Δcka qep tL par t).fsRecv ctx' P' t' rs hdr e ic =
        pure (some (fs.receive rs hdr e)) := fun _ _ _ _ _ _ _ => rfl
  by_cases hg : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
    simp only [hg, ↓reduceIte, StateT.run_pure]
  · have hsends_f : vp.id.sendsIn c.1.1 = false := by
      cases hs : vp.id.sendsIn c.1.1
      · rfl
      · simp [hs] at hg
    have hle1 : c.1.1 ≤ vp.tcur + 1 := by
      by_contra hgt
      have hd : decide (vp.tcur + 1 < c.1.1) = true := decide_eq_true (by omega)
      simp [hd] at hg
    by_cases hn : c.1.1 = vp.tcur + 1
    · have hite : ∀ {α : Type} (x y : α), (if c.1.1 = vp.tcur + 1 then x else y) = x :=
        fun x y => by split <;> [rfl; contradiction]
      rcases htn : c.1.2 with _ | tn0
      · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
        simp only [hg, Bool.false_eq_true, ↓reduceIte, hite,
          pure_bind, StateT.run_pure]
      · have hsr : ∃ sr : Option (Option (Γ × Option Sig × RS)),
            ((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).startRecv
              ctx P c.1.1 vp.γ vp.root tn0).run h0 = pure (sr, h0) := by
          unfold hooksPRNGBucketMain hooksPRNGBucketMainGen
          dsimp only
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases h0.cache c.1.1 with
          | none =>
            split_ifs <;> exact ⟨_, StateT.run_pure _ _⟩
          | some entry =>
            rcases entry with ⟨tCached, σc, kVal⟩
            by_cases hteq : tCached = tn0
            · simp only [hteq, ↓reduceIte]
              exact ⟨_, StateT.run_pure _ _⟩
            · simp only [hteq, ↓reduceIte]
              split_ifs <;> exact ⟨_, StateT.run_pure _ _⟩
        rcases hsr with ⟨sr, hsr_eq⟩
        rcases sr with _ | (_ | ⟨γ', σ', rs⟩)
        · refine ⟨none, ?_, by intro _ _ _ _ h; cases h⟩
          simp only [hg, Bool.false_eq_true, ↓reduceIte, hite,
            StateT.run_bind, hsr_eq, pure_bind, StateT.run_pure]
        · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
          simp only [hg, Bool.false_eq_true, ↓reduceIte, hite,
            StateT.run_bind, hsr_eq, pure_bind, StateT.run_pure]
        · have hupd : Function.update vp.vR c.1.1 (some rs) c.1.1 = some rs := by simp
          rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨rs', i', m'⟩
          · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
            simp only [hg, Bool.false_eq_true, ↓reduceIte, hite,
              StateT.run_bind, hsr_eq, pure_bind, hupd, h_fsRecv, hfs, StateT.run_pure]
          · let vp1 : VP Γ T (Option Sig) SS RS :=
              { vp with
                γ := γ'
                root := σ'
                tcur := c.1.1
                vR := Function.update (Function.update vp.vR c.1.1 (some rs)) c.1.1 (some rs') }
            refine ⟨some (some (vp1, c.1.1, i', m')), ?_, ?_⟩
            · simp only [vp1, hg, Bool.false_eq_true, ↓reduceIte, hite,
                StateT.run_bind, hsr_eq, pure_bind, hupd, h_fsRecv, hfs, StateT.run_pure]
            · intro vp' t' i0 m0 heq
              injection heq with heq1
              injection heq1 with heq2
              rcases heq2 with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨rfl, hsends_f, hle1, rfl, by dsimp only [vp1]; omega⟩
    · have hite : ∀ {α : Type} (x y : α), (if c.1.1 = vp.tcur + 1 then x else y) = y :=
        fun x y => by split <;> [contradiction; rfl]
      rcases hvr : vp.vR c.1.1 with _ | rs
      · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
        simp only [hg, Bool.false_eq_true, ↓reduceIte, hite, hvr,
          pure_bind, StateT.run_pure]
      · rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨rs', i', m'⟩
        · refine ⟨some none, ?_, by intro _ _ _ _ h; cases h⟩
          simp only [hg, Bool.false_eq_true, ↓reduceIte, hite, hvr,
            h_fsRecv, hfs, pure_bind, StateT.run_pure]
        · let vp1 : VP Γ T (Option Sig) SS RS :=
            { vp with vR := Function.update vp.vR c.1.1 (some rs') }
          refine ⟨some (some (vp1, c.1.1, i', m')), ?_, ?_⟩
          · simp only [vp1, hg, Bool.false_eq_true, ↓reduceIte, hite, hvr,
              h_fsRecv, hfs, pure_bind, StateT.run_pure]
          · intro vp' t' i0 m0 heq
            injection heq with heq1
            injection heq1 with heq2
            rcases heq2 with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨rfl, hsends_f, hle1, rfl, by dsimp only [vp1]; omega⟩

private theorem deliverE_main_cases
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (P : Party) (c : Header T × E)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (hab : es.abort = false) (hwin : es.g.win = false) :
    ∃ ans es',
      ((deliverE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        fs.maxSkip (bucketAuthCfg Δcka tL par) (P, c)).run es) = pure (ans, es') ∧
      (es' = es ∨
       es' = { es with abort := true } ∨
       ∃ rec vp',
         es.g.inTransit P.other c = some rec ∧
         es' = { es with g := es.g.accept P vp' rec.pos } ∧
         vp'.id = (es.g.st P).id ∧ vp'.tcur = max (es.g.st P).tcur c.1.1) := by
  rcases es with ⟨g, h, abort⟩
  dsimp only at hab hwin
  subst hab
  rcases htr : g.inTransit P.other c with _ | rec
  · refine ⟨none, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
    simp only [deliverE, StateT.run_bind, StateT.run_get, pure_bind,
      hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, StateT.run_pure]
  · obtain ⟨ansv, hv_run, hv_props⟩ := vRecv_main_run cka prng fs Δcka qep tL par t
      g P (g.st P) c (some rec) h
    rcases ansv with _ | (_ | ⟨vp', t', i', m'⟩)
    · refine ⟨none, ⟨g, h, true⟩, ?_, Or.inr (Or.inl rfl)⟩
      simp only [deliverE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
        hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hv_run,
        abortE, StateT.run_modify, StateT.run_pure]
    · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
      simp only [deliverE, liftH_run_main, bucketAuthCfg, StateT.run_bind, StateT.run_get,
        pure_bind, hwin, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
        htr, hv_run, StateT.run_pure]
    · obtain ⟨rfl, _, _, hid', htcur'⟩ := hv_props vp' t' i' m' rfl
      have hcom := commitE_main_run cka prng fs Δcka qep tL par t g P (g.st P) vp' rec.pos ⟨g, h, false⟩
      refine ⟨some (.accepted c.1.1 i' (if g.chall.contains rec.pos then none else some m')),
        ⟨g.accept P vp' rec.pos, h, false⟩, ?_,
        Or.inr (Or.inr ⟨rec, vp', rfl, rfl, hid', htcur'⟩)⟩
      simp only [deliverE, liftH_run_main, bucketAuthCfg, StateT.run_bind, StateT.run_get,
        pure_bind, hwin, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
        htr, hv_run, hcom, StateT.run_modify, StateT.run_pure]

private theorem injectE_main_cases
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (P : Party) (c : Header T × E)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (hab : es.abort = false) (hwin : es.g.win = false) :
    ∃ ans es',
      ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run es) = pure (ans, es') ∧
      (es' = es ∨
       es' = { es with abort := true } ∨
       (∃ vp' i',
         es' = { es with g := es.g.accept P vp' ⟨P.other, c.1.1, i'⟩ } ∧
         vp'.id = (es.g.st P).id ∧ vp'.tcur = max (es.g.st P).tcur c.1.1) ∨
       (es' = { es with g := { es.g with win := true } } ∧
        (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c.1.1 = true ∧
        (es.g.st P).id.sendsIn c.1.1 = false ∧ c.1.1 ≤ (es.g.st P).tcur + 1 ∧
        ∃ i', es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false)) := by
  rcases es with ⟨g, h, abort⟩
  dsimp only at hab hwin
  subst hab
  by_cases hg : ((g.inTransit P.other c).isSome || !g.safeInj (2 + Δcka)) = true
  · have hg' : (false || g.win || (g.inTransit P.other c).isSome ||
        !g.safeInj (2 + Δcka)) = true := by
      simp only [hwin, Bool.or_self, Bool.false_or]; exact hg
    refine ⟨none, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
    simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hg', ↓reduceIte, StateT.run_pure]
  · have hg' : (false || g.win || (g.inTransit P.other c).isSome ||
        !g.safeInj (2 + Δcka)) = false := by
      simp only [Bool.not_eq_true] at hg
      simp only [hwin, Bool.or_self, Bool.false_or]; exact hg
    obtain ⟨ansv, hv_run, hv_props⟩ := vRecv_main_run cka prng fs Δcka qep tL par t
      g P (g.st P) c none h
    rcases ansv with _ | (_ | ⟨vp', t', i', m'⟩)
    · refine ⟨none, ⟨g, h, true⟩, ?_, Or.inr (Or.inl rfl)⟩
      simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
        hg', Bool.false_eq_true, ↓reduceIte, hv_run, abortE,
        StateT.run_modify, StateT.run_pure]
    · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
      simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
        hg', Bool.false_eq_true, ↓reduceIte, hv_run, StateT.run_pure]
    · obtain ⟨rfl, hsends_f, hle1, hid', htcur'⟩ := hv_props vp' t' i' m' rfl
      by_cases hqep : qep + 1 < c.1.1
      · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
        simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
          hg', Bool.false_eq_true, ↓reduceIte, hv_run, hqep, StateT.run_pure]
      · by_cases htriv : g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hcom := commitE_main_run cka prng fs Δcka qep tL par t
            g P (g.st P) vp' ⟨P.other, c.1.1, i'⟩ ⟨g, h, false⟩
          refine ⟨some (.accepted c.1.1 i' (some m')),
            ⟨g.accept P vp' ⟨P.other, c.1.1, i'⟩, h, false⟩, ?_,
            Or.inr (Or.inr (Or.inl ⟨vp', i', rfl, hid', htcur'⟩))⟩
          simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
            hg', Bool.false_eq_true, ↓reduceIte, hv_run, hqep, htriv, hcom,
            StateT.run_modify, StateT.run_pure]
        · simp only [Bool.not_eq_true] at htriv
          by_cases hinj : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c.1.1 = true
          · refine ⟨some .rejected, ⟨{ g with win := true }, h, false⟩, ?_,
              Or.inr (Or.inr (Or.inr ⟨rfl, hinj, hsends_f, hle1, i', htriv⟩))⟩
            simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
              hg', Bool.false_eq_true, ↓reduceIte, hv_run, hqep, htriv, hinj,
              StateT.run_modify, StateT.run_pure]
          · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
            simp only [injectE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
              hg', Bool.false_eq_true, ↓reduceIte, hv_run, hqep, htriv, hinj,
              StateT.run_pure]

private theorem deliverForgeE_main_cases
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (P : Party) (c c' : Header T × E)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (hab : es.abort = false) (hwin : es.g.win = false) :
    ∃ ans es',
      ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run es) = pure (ans, es') ∧
      (es' = es ∨
       es' = { es with abort := true } ∨
       (∃ vp' i',
         es' = { es with g := es.g.accept P vp' ⟨P.other, c'.1.1, i'⟩ } ∧
         vp'.id = (es.g.st P).id ∧ vp'.tcur = max (es.g.st P).tcur c'.1.1) ∨
       (∃ rec i',
         es.g.inTransit P.other c = some rec ∧
         c'.1.1 = rec.pos.epoch ∧
         es' = { es with g := { es.g with win := true } } ∧
         (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c'.1.1 = true ∧
         (es.g.st P).id.sendsIn c'.1.1 = false ∧ c'.1.1 ≤ (es.g.st P).tcur + 1 ∧
         es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = false)) := by
  rcases es with ⟨g, h, abort⟩
  dsimp only at hab hwin
  subst hab
  rcases htr : g.inTransit P.other c with _ | rec
  · refine ⟨none, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
    simp only [deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind,
      hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, StateT.run_pure]
  · by_cases hrej : ((g.inTransit P.other c').isSome || g.comp.contains rec.pos ||
        (c.1 != c'.1)) = true
    · refine ⟨none, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
      simp only [deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind,
        hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, StateT.run_pure]
    · obtain ⟨ansv, hv_run, hv_props⟩ := vRecv_main_run cka prng fs Δcka qep tL par t
        g P (g.st P) c' none h
      rcases ansv with _ | (_ | ⟨vp', t', i', m'⟩)
      · refine ⟨none, ⟨g, h, true⟩, ?_, Or.inr (Or.inl rfl)⟩
        simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
          hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
          abortE, StateT.run_modify, StateT.run_pure]
      · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
        simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
          hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
          StateT.run_pure]
      · obtain ⟨rfl, hsends_f, hle1, hid', htcur'⟩ := hv_props vp' t' i' m' rfl
        by_cases hqep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != rec.pos.epoch)) = true
        · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
          simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
            hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
            hqep, StateT.run_pure]
        · have heq_ep : c'.1.1 = rec.pos.epoch := by
            simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hqep
            exact hqep.2
          by_cases htriv : g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
          · have hcom := commitE_main_run cka prng fs Δcka qep tL par t
              g P (g.st P) vp' ⟨P.other, c'.1.1, i'⟩ ⟨g, h, false⟩
            refine ⟨some (.accepted c'.1.1 i' (some m')),
              ⟨g.accept P vp' ⟨P.other, c'.1.1, i'⟩, h, false⟩, ?_,
              Or.inr (Or.inr (Or.inl ⟨vp', i', rfl, hid', htcur'⟩))⟩
            simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
              hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
              hqep, htriv, hcom, StateT.run_modify, StateT.run_pure]
          · simp only [Bool.not_eq_true] at htriv
            by_cases hinj : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c'.1.1 = true
            · refine ⟨some .rejected, ⟨{ g with win := true }, h, false⟩, ?_,
                Or.inr (Or.inr (Or.inr ⟨rec, i', rfl, heq_ep, rfl, hinj, hsends_f, hle1, htriv⟩))⟩
              simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
                hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
                hqep, htriv, hinj, StateT.run_modify, StateT.run_pure]
            · refine ⟨some .rejected, ⟨g, h, false⟩, ?_, Or.inl rfl⟩
              simp only [deliverForgeE, liftH_run_main, StateT.run_bind, StateT.run_get, pure_bind,
                hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr, hrej, hv_run,
                hqep, htriv, hinj, StateT.run_pure]

/-! ### Support Lemmas for `startSend`, `vSend`, and `reveal` (`lc` Evolution) -/

private theorem mem_support_liftPBucket_state
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (q : PRFPRNG.AdversaryComp Sig I K α)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (α × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((liftPBucket q).run h0)).run sp)) :
    r.1.2 = h0 := by
  rw [simulateQ_pImpl_liftPBucket, StateT.run_bind] at hr
  rw [mem_support_bind_iff] at hr
  rcases hr with ⟨⟨_, sp1⟩, _, hr2⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr2
  subst hr2; rfl

private theorem support_lookupPRNGBucketF_lc
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (ep : ℕ) (ik : I)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((lookupPRNGBucketF ep ik).run h0)).run sp)) :
    r.1.2.lc = h0.lc := by
  unfold lookupPRNGBucketF at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases hlk : (h0.fTable ep).lookup ik with
  | some k =>
    simp only [hlk, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | none =>
    simp only [hlk] at hr
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind,
      AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc, mem_support_bind_iff] at hr
    rcases hr with ⟨k, _, hr2⟩
    simp only [pure_bind] at hr2
    subst hr2; rfl

private theorem support_rootPRNGBucketHybrid_lc
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t t0 : ℕ) (pl : Bool) (ik0 : I) (σv0 : Option Sig)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((rootPRNGBucketHybrid prng Δbucket tL par t t0 pl ik0 σv0).run h0)).run sp)) :
    r.1.2.lc = h0.lc := by
  unfold rootPRNGBucketHybrid at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hc1 : t < t0
  · simp only [hc1, ↓reduceIte] at hr
    cases hres : resolveCorrRoot h0 (t0 - 1) σv0 with
    | none =>
      simp only [hres, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    | some σ =>
      simp only [hres, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
  · simp only [hc1, ↓reduceIte] at hr
    by_cases hc2 : (pl || h0.corrRoot.isSome) = true
    · simp only [hc2, ↓reduceIte] at hr
      cases hres : resolveCorrRoot h0 (t0 - 1) σv0 with
      | some σ =>
        simp only [hres, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      | none =>
        simp only [hres, StateT.run_bind, simulateQ_bind] at hr
        rw [mem_support_bind_iff] at hr
        rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, hm1, hm2⟩
        have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
        subst h1
        cases o with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
          subst hm2; rfl
        | some σOut =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
          subst hm2; rfl
    · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hr
      by_cases hc3 : t0 = t
      · simp only [hc3, ↓reduceIte] at hr
        by_cases hc3a : (tL.isSome && decide (t = healEpoch tL)) = true
        · simp only [hc3a, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
          have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
          subst h1
          cases o1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
            subst hm2; rfl
          | some kOut =>
            simp only [StateT.run_bind, simulateQ_bind] at hm2
            rw [mem_support_bind_iff] at hm2
            rcases hm2 with ⟨⟨⟨o2, h2⟩, sp2⟩, hm3, hm4⟩
            have hh2 : h2 = h0 := mem_support_liftPBucket_state prng _ h0 sp1 hm3
            subst h2
            cases o2 <;>
              (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm4;
               subst hm4; rfl)
        · simp only [hc3a, Bool.false_eq_true, ↓reduceIte] at hr
          by_cases hc3b : inStage2BucketGen Δbucket tL par t = true
          · simp only [hc3b, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [mem_support_bind_iff] at hr
            rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
            have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
            subst h1
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
              subst hm2; rfl
            | some p =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
              subst hm2; rfl
          · simp only [hc3b, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [mem_support_bind_iff] at hr
            rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
            have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
            subst h1
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
              subst hm2; rfl
            | some kOut =>
              simp only [StateT.run_bind, simulateQ_bind] at hm2
              rw [mem_support_bind_iff] at hm2
              rcases hm2 with ⟨⟨⟨o2, h2⟩, sp2⟩, hm3, hm4⟩
              have hh2 : h2 = h0 := mem_support_liftPBucket_state prng _ h0 sp1 hm3
              subst h2
              cases o2 <;>
                (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm4;
                 subst hm4; rfl)
      · simp only [hc3, ↓reduceIte] at hr
        by_cases hc4 : (!decide (t0 < healEpoch tL)) = true
        · simp only [hc4, ↓reduceIte] at hr
          by_cases hc4a : (tL.isSome && decide (t0 = healEpoch tL)) = true
          · simp only [hc4a, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [mem_support_bind_iff] at hr
            rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
            have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
            subst h1
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
              subst hm2; rfl
            | some _ =>
              simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind,
                AuthL11.pImpl, bind_assoc, pure_bind,
                StateT.run_pure, simulateQ_pure] at hm2
              rw [mem_support_bind_iff] at hm2
              rcases hm2 with ⟨_, _, hm3⟩
              simp only [support_pure, Set.mem_singleton_iff] at hm3
              subst hm3; rfl
          · simp only [hc4a, Bool.false_eq_true, ↓reduceIte] at hr
            by_cases hc4b : inStage2BucketGen Δbucket tL par t0 = true
            · simp only [hc4b, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
              rw [mem_support_bind_iff] at hr
              rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
              have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
              subst h1
              cases o1 with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
                subst hm2; rfl
              | some _ =>
                simp only [StateT.run_bind, simulateQ_bind] at hm2
                rw [mem_support_bind_iff] at hm2
                rcases hm2 with ⟨⟨⟨kOut, h2⟩, sp2⟩, hm3, hm4⟩
                have hh2 := support_lookupPRNGBucketF_lc prng t0 ik0 h0 sp1 hm3
                simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm4
                subst hm4; exact hh2
            · simp only [hc4b, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
              rw [mem_support_bind_iff] at hr
              rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
              have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
              subst h1
              cases o1 <;>
                (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2;
                 subst hm2; rfl)
        · simp only [hc4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨o1, h1⟩, sp1⟩, hm1, hm2⟩
          have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
          subst h1
          cases o1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
            subst hm2; rfl
          | some kOut =>
            simp only [StateT.run_bind, simulateQ_bind] at hm2
            rw [mem_support_bind_iff] at hm2
            rcases hm2 with ⟨⟨⟨o2, h2⟩, sp2⟩, hm3, hm4⟩
            have hh2 : h2 = h0 := mem_support_liftPBucket_state prng _ h0 sp1 hm3
            subst h2
            cases o2 <;>
              (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm4;
               subst hm4; rfl)

private theorem support_startSend_main_lc
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Γ)
    (σv0 : Option Sig) (r0 : Option CCoins)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).startSend
        ctx P t0 γ0 σv0 r0).run h0)).run sp)) :
    r.1.2.lc = if (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true
      then some (t0 - 1) else h0.lc := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen at hr
  dsimp only at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  let h_lc : PRNGBucketState T Sig K I :=
    if (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true then
      { h0 with lc := some (t0 - 1) }
    else h0
  have hlc_val : h_lc.lc = if (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true
      then some (t0 - 1) else h0.lc := by
    dsimp only [h_lc]; split <;> rfl
  have hr_lc : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((match r0 with
        | some coins => do
          let c := cka.send γ0 coins
          match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par t t0 (postLeak tL ctx) c.2.2 σv0 with
          | none => return none
          | some (σ', kVal) =>
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)
        | none => do
          let coins ← StateT.lift (sampleT CCoins)
          let c := cka.send γ0 coins
          match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par t t0 (postLeak tL ctx) c.2.2 σv0 with
          | none => return none
          | some (σ', kVal) =>
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run h_lc)).run sp) := by
    dsimp only [h_lc]
    by_cases hcond : (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true <;>
      simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
        pure_bind] at hr ⊢ <;>
      exact hr
  have hcoins : ∃ coins : CCoins, r ∈ support (do
      let p ← (simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid prng (3 + Δcka) tL par t t0 (postLeak tL ctx)
          (cka.send γ0 coins).2.2 σv0).run h_lc)).run sp
      (simulateQ (AuthL11.pImpl prng)
        (StateT.run (match p.1.1 with
          | none => pure none
          | some (σ', kVal) => do
            modify fun (s : PRNGBucketState T Sig K I) =>
              { s with cache := Function.update s.cache t0 (some ((cka.send γ0 coins).2.1, σ', kVal)) }
            return some ((cka.send γ0 coins).1, (cka.send γ0 coins).2.1, σ', fs.initSender kVal))
          p.1.2)).run p.2) := by
    cases r0 with
    | some coins =>
      simp only [StateT.run_bind, simulateQ_bind] at hr_lc
      exact ⟨coins, hr_lc⟩
    | none =>
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind,
        AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc, mem_support_bind_iff] at hr_lc
      rcases hr_lc with ⟨coins, _, hr'⟩
      simp only [pure_bind, StateT.run_bind, simulateQ_bind] at hr'
      exact ⟨coins, hr'⟩
  rcases hcoins with ⟨coins, hr'⟩
  rw [mem_support_bind_iff] at hr'
  rcases hr' with ⟨⟨⟨rootAns, h1⟩, sp1⟩, hroot_mem, hr2⟩
  have hh1 := support_rootPRNGBucketHybrid_lc prng (3 + Δcka) tL par t t0
    (postLeak tL ctx) (cka.send γ0 coins).2.2 σv0 h_lc sp hroot_mem
  cases rootAns with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
    subst hr2; exact hh1.trans hlc_val
  | some pOut =>
    rcases pOut with ⟨σ', kVal⟩
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
    subst hr2; exact hh1.trans hlc_val

private theorem support_vSend_main_props
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (m : M) (r0 : Option CCoins)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((vSend (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        ctx P vp m none r0).run h0)).run sp)) :
    (r.1.2.lc = if vp.id.sendsIn (vp.tcur + 1) = true then
        (if (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < vp.tcur + 1)) = true
          then some vp.tcur else h0.lc)
      else h0.lc) ∧
    (∀ vp' ct, r.1.1 = some (vp', ct) →
      vp'.id = vp.id ∧
      vp'.tcur = (if vp.id.sendsIn (vp.tcur + 1) = true then vp.tcur + 1 else vp.tcur) ∧
      ct.1.1 = (if vp.id.sendsIn (vp.tcur + 1) = true then vp.tcur + 1 else vp.tcur)) := by
  have h_fsSend : ∀ ctx' P' t' ss hdr msg ic,
      (hooksPRNGBucketMain cka prng fs Δcka qep tL par t).fsSend ctx' P' t' ss hdr msg ic =
        pure (some (fs.send ss hdr msg)) := fun _ _ _ _ _ _ _ => rfl
  unfold vSend at hr
  by_cases hs : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr ⊢
    rw [mem_support_bind_iff] at hr
    rcases hr with ⟨⟨⟨ans1, h1⟩, sp1⟩, hrs1, hrs2⟩
    have hss_lc := support_startSend_main_lc cka prng fs Δcka qep tL par t
      ctx P (vp.tcur + 1) vp.γ vp.root r0 h0 sp hrs1
    dsimp only at hss_lc
    have hsub : vp.tcur + 1 - 1 = vp.tcur := by omega
    rw [hsub] at hss_lc
    cases ans1 with
    | none =>
      simp only [] at hrs2
      subst hrs2
      exact ⟨hss_lc, by intro _ _ h; cases h⟩
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss'⟩
      simp only [h_fsSend, StateT.run_pure, pure_bind,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hrs2
      subst hrs2
      refine ⟨hss_lc, ?_⟩
      intro vp' ct heq
      injection heq with heq1
      rcases heq1 with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  · have hs_f : vp.id.sendsIn (vp.tcur + 1) = false := by
      cases h : vp.id.sendsIn (vp.tcur + 1) <;> [rfl; contradiction]
    simp only [hs_f, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr ⊢
    cases hvS : vp.vS with
    | none =>
      rw [hvS] at hr
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨rfl, ?_⟩
      intro vp' ct heq
      injection heq with heq1
      rcases heq1 with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    | some ss =>
      rw [hvS] at hr
      simp only [h_fsSend, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨rfl, ?_⟩
      intro vp' ct heq
      injection heq with heq1
      rcases heq1 with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

private theorem support_reveal_main_lc
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS)
    (h0 : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (Option (PartyState Γ T Sig SS RS) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).reveal
        ctx P vp).run h0)).run sp)) :
    r.1.1 = none ∨
    r.1.2.lc = (if ((!postLeak tL ctx && h0.lc.isNone) &&
        !(decide (vp.tcur < healEpoch tL))) = true
      then some vp.tcur else h0.lc) := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases hres : resolveCorrRoot h0 vp.tcur vp.root with
  | some σ =>
    simp only [hres] at hr
    by_cases hc1 : (!(decide (vp.tcur < healEpoch tL)) && h0.corrRoot.isNone) = true
    · simp only [hc1, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind] at hr
      by_cases hc2 : ((!postLeak tL ctx && h0.lc.isNone) &&
          !(decide (vp.tcur < healEpoch tL))) = true
      · simp only [hc2, ↓reduceIte, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr ⊢
        subst hr; exact Or.inr rfl
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr ⊢
        subst hr; exact Or.inr rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hr
      by_cases hc2 : ((!postLeak tL ctx && h0.lc.isNone) &&
          !(decide (vp.tcur < healEpoch tL))) = true
      · simp only [hc2, ↓reduceIte, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr ⊢
        subst hr; exact Or.inr rfl
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr ⊢
        subst hr; exact Or.inr rfl
  | none =>
    simp only [hres] at hr
    by_cases hcond : (((!postLeak tL ctx && h0.corrRoot.isNone) &&
        !(decide (vp.tcur < healEpoch tL))) &&
        (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
    · simp only [hcond, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
      rw [mem_support_bind_iff] at hr
      rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, hm1, hm2⟩
      have hh1 : h1 = h0 := mem_support_liftPBucket_state prng _ h0 sp hm1
      subst h1
      cases o with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2
        subst hm2; exact Or.inl rfl
      | some σOut =>
        have h_npl : (!postLeak tL ctx) = true := by simp only [Bool.and_eq_true] at hcond; exact hcond.1.1.1
        have h_nge : (!(decide (vp.tcur < healEpoch tL))) = true := by
          simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
        simp only [h_npl, h_nge, Bool.true_and, Bool.and_true]
        simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hm2
        by_cases hlc0 : h0.lc.isNone = true
        · simp only [hlc0, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2 ⊢
          subst hm2; exact Or.inr rfl
        · simp only [hlc0, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hm2 ⊢
          subst hm2; exact Or.inr rfl
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl rfl

/-! ### Step-Preservation of `DoomedLcEqMain` -/

private theorem stepPBucketLcEqMain_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) (htH : healEpoch tL ≤ t)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
      (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K)
    (hd : DoomedLcEqMain Δcka tL par t stP) :
    ∀ r ∈ support (stepPBucketLcEqMain cka prng fs Δcka qep tL par t q stP sp),
      DoomedLcEqMain Δcka tL par t r.1.2 := by
  intro r hr
  by_cases habw : stP.1.abort = true ∨ stP.1.g.win = true
  · have hst := stepPBucketLcEqMain_state_eq_of_abort_or_win
      cka prng fs Δcka qep tL par t q stP sp habw r hr
    rw [hst]; exact hd
  · push Not at habw
    rcases stP with ⟨es, winEp⟩
    dsimp only at habw
    have hab : es.abort = false := by cases h : es.abort <;> [rfl; exact False.elim (habw.1 h)]
    have hwin : es.g.win = false := by cases h : es.g.win <;> [rfl; exact False.elim (habw.2 h)]
    dsimp only [DoomedLcEqMain] at hd
    rcases hd with hab' | ⟨hwin', _⟩ | ⟨_, hlc_isSome, hlc_ne_t⟩ |
        ⟨_, hcorr_mem, hpar_eq⟩ |
        ⟨_, hlc_none, hvp_inv, htr_inv, hep_inv⟩
    · exact False.elim (habw.1 hab')
    · exact False.elim (habw.2 hwin')
    · -- Branch 3: `es.h.lc.isSome = true ∧ es.h.lc ≠ some t` (`lc.isNone = false`, so `lc` never changes!)
      have hlc_isNone_f : es.h.lc.isNone = false := by
        cases h : es.h.lc with
        | none => simp [h] at hlc_isSome
        | some _ => rfl
      have hstay3 : ∀ w', DoomedLcEqMain Δcka tL par t (es, w') :=
        fun _ => Or.inr (Or.inr (Or.inl ⟨hwin, hlc_isSome, hlc_ne_t⟩))
      have hpres3 : ∀ (es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
          (PRNGBucketState T Sig K I)) (w' : Option ℕ),
          (es'.abort = true ∨ es'.h.lc = es.h.lc) →
          DoomedLcEqMain Δcka tL par t (es', w') := by
        intro es' w' hlc_or
        rcases hlc_or with hab' | hlc_eq
        · exact Or.inl hab'
        · by_cases hw' : es'.g.win = true
          · exact Or.inr (Or.inl ⟨hw', Or.inl (hlc_eq ▸ hlc_ne_t)⟩)
          · have hw'_f : es'.g.win = false := by cases h : es'.g.win <;> [rfl; contradiction]
            exact Or.inr (Or.inr (Or.inl ⟨hw'_f, hlc_eq ▸ hlc_isSome, hlc_eq ▸ hlc_ne_t⟩))
      rcases q with n | (((((q | q) | q) | q) | P) | df)
      · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
          AuthL11.pImpl, bind_assoc, pure_bind,
          simulateQ_pure] at hr
        rw [StateT.run_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨⟨_, sp1⟩, _, hr2⟩
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr2
        subst hr2; exact hstay3 _
      · rcases q with ⟨P, m_msg, r0⟩
        simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, transmitEBucket, StateT.run_bind, StateT.run_get, pure_bind,
          hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hr
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r0.isSome with _ | s₁
        · simp only [hep, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hstay3 _
        · simp only [hep, liftH_run_main, StateT.run_bind, pure_bind, bind_assoc,
            simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨vout, h1⟩, sp1⟩, hr1, hr2⟩
          obtain ⟨hlc1, _⟩ := support_vSend_main_props cka prng fs Δcka qep tL par t
            s₁ P (s₁.st P) m_msg r0 es.h sp hr1
          dsimp only at hlc1
          have hh1 : h1.lc = es.h.lc := by simp [hlc1, hlc_isNone_f]
          cases vout with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some vc =>
            rcases vc with ⟨vp', ct⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact hpres3 _ _ (Or.inr hh1)
      · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
            (.inr (.inl (.inl (.inl (.inl (.inr q))))))).run es) = pure (none, es) := by
          simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure]
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
        subst heq; exact hstay3 _
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, _, rfl, _, _⟩
        · exact hstay3 _
        · exact Or.inl rfl
        · exact hpres3 _ _ (Or.inr rfl)
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := injectE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inr (P, c))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, rfl, _, _⟩ | ⟨rfl, _, _, _, _⟩
        · exact hstay3 _
        · exact Or.inl rfl
        · exact hpres3 _ _ (Or.inr rfl)
        · exact hpres3 _ _ (Or.inr rfl)
      · by_cases hcr : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
        · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
              (.inr (.inl (.inr P)))).run es) = pure (none, es) := by
            simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
              StateT.run_bind, StateT.run_get, pure_bind, hcr, ↓reduceIte, StateT.run_pure]
          have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
          subst heq; exact hstay3 _
        · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
            QueryImpl.add_apply, corrEPaperBucket, liftH_run_main, StateT.run_bind, StateT.run_get,
            pure_bind, bind_assoc, hcr, Bool.false_eq_true, ↓reduceIte, simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, hr1, hr2⟩
          have hrev := support_reveal_main_lc cka prng fs Δcka qep tL par t
            es.g P (es.g.st P) es.h sp hr1
          dsimp only at hrev
          cases o with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some pst =>
            rcases hrev with hnone | hlc1
            · cases hnone
            · have hh1 : h1.lc = es.h.lc := by simp [hlc1, hlc_isNone_f]
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact hpres3 _ _ (Or.inr hh1)
      · rcases df with ⟨P, c, c'⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverForgeE_main_cases cka prng fs Δcka qep tL par t P c c' es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inr (P, c, c'))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, rfl, _, _⟩ | ⟨_, _, _, _, rfl, _, _, _, _⟩
        · exact hstay3 _
        · exact Or.inl rfl
        · exact hpres3 _ _ (Or.inr rfl)
        · exact hpres3 _ _ (Or.inr rfl)
    · -- Branch 4: `win = false ∧ (Party.receiverOf (t + 1), t) ∈ corrs ∧ partyPar (senderOf (t + 1)) = par`
      have hstay4 : ∀ w', DoomedLcEqMain Δcka tL par t (es, w') :=
        fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hcorr_mem, hpar_eq⟩)))
      have hwin_imp : ∀ (es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
          (PRNGBucketState T Sig K I)) (tWin : ℕ),
          (bucketAuthCfg Δcka tL par : SM.Config M).injectFull tWin = true →
          (Party.receiverOf (t + 1), t) ∈ es'.g.corrs →
          authOutBucketPaper (2 + Δcka) tL (es', some tWin) = false := by
        intro es' tWin hinj hmem
        have hin : inStage2Bucket Δcka tL par tWin = true := hinj
        simp only [inStage2Bucket, Bool.and_eq_true, beq_iff_eq] at hin
        have hpar_tWin : partyPar (Party.senderOf tWin) = par := hin.2
        have hrec := receiverOf_eq_of_partyPar_senderOf_eq (hpar_tWin.trans hpar_eq.symm)
        have hlt_t := ltOpt_of_healEpoch_le htH
        have hall : es'.g.corrs.all
            (fun pe => !(pe.1 == Party.receiverOf tWin && ltOpt tL pe.2)) = false :=
          List.all_eq_false.mpr ⟨(Party.receiverOf (t + 1), t), hmem, by simp [hrec, hlt_t]⟩
        unfold authOutBucketPaper authOutBucket authOut SM.authLosingConditionsAvoided
        dsimp only
        rw [hall]; simp
      rcases q with n | (((((q | q) | q) | q) | P) | df)
      · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
          AuthL11.pImpl, bind_assoc, pure_bind,
          simulateQ_pure] at hr
        rw [StateT.run_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨⟨_, sp1⟩, _, hr2⟩
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr2
        subst hr2; exact hstay4 _
      · rcases q with ⟨P, m_msg, r0⟩
        simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, transmitEBucket, StateT.run_bind, StateT.run_get, pure_bind,
          hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hr
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r0.isSome with _ | s₁
        · simp only [hep, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hstay4 _
        · have hcorrs_ep : s₁.corrs = es.g.corrs ∧ s₁.win = es.g.win := by
            unfold SM.GameState.epMgmt at hep
            by_cases hs : P.sendsIn (es.g.epoch P + 1) = true
            · simp only [hs, ↓reduceIte] at hep
              split at hep
              · cases hep
              · split at hep <;> injection hep with hep <;> subst hep <;> exact ⟨rfl, rfl⟩
            · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
              split at hep <;> simp at hep; subst hep; exact ⟨rfl, rfl⟩
          simp only [hep, liftH_run_main, StateT.run_bind, pure_bind, bind_assoc,
            simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨vout, h1⟩, sp1⟩, _, hr2⟩
          cases vout with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some vc =>
            rcases vc with ⟨vp', ct⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2
            refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, hpar_eq⟩)))
            · dsimp only [SM.GameState.record]; simp [hcorrs_ep.2, hwin]
            · dsimp only [SM.GameState.record]; rw [hcorrs_ep.1]; exact hcorr_mem
      · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
            (.inr (.inl (.inl (.inl (.inl (.inr q))))))).run es) = pure (none, es) := by
          simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure]
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
        subst heq; exact hstay4 _
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, _, rfl, _, _⟩
        · exact hstay4 _
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hcorr_mem, hpar_eq⟩)))
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := injectE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inr (P, c))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, rfl, _, _⟩ | ⟨rfl, hinj, _, _, _⟩
        · exact hstay4 _
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hcorr_mem, hpar_eq⟩)))
        · simp only [hwin, Bool.not_false, Bool.true_and, ↓reduceIte, dfQueryTargetEpoch]
          exact Or.inr (Or.inl ⟨rfl, Or.inr (hwin_imp _ c.1.1 hinj hcorr_mem)⟩)
      · by_cases hcr : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
        · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
              (.inr (.inl (.inr P)))).run es) = pure (none, es) := by
            simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
              StateT.run_bind, StateT.run_get, pure_bind, hcr, ↓reduceIte, StateT.run_pure]
          have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
          subst heq; exact hstay4 _
        · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
            QueryImpl.add_apply, corrEPaperBucket, liftH_run_main, StateT.run_bind, StateT.run_get,
            pure_bind, bind_assoc, hcr, Bool.false_eq_true, ↓reduceIte, simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, _, hr2⟩
          cases o with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some _ =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, List.mem_cons_of_mem _ hcorr_mem, hpar_eq⟩)))
      · rcases df with ⟨P, c, c'⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverForgeE_main_cases cka prng fs Δcka qep tL par t P c c' es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inr (P, c, c'))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨_, _, rfl, _, _⟩ | ⟨_, _, _, _, rfl, hinj, _, _, _⟩
        · exact hstay4 _
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hcorr_mem, hpar_eq⟩)))
        · simp only [hwin, Bool.not_false, Bool.true_and, ↓reduceIte, dfQueryTargetEpoch]
          exact Or.inr (Or.inl ⟨rfl, Or.inr (hwin_imp _ c'.1.1 hinj hcorr_mem)⟩)
    · -- Branch 5: `win = false ∧ lc = none ∧ vp_inv ∧ tr_inv ∧ ep_inv`
      have hstay5 : ∀ w', DoomedLcEqMain Δcka tL par t (es, w') :=
        fun _ => Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hlc_none, hvp_inv, htr_inv, hep_inv⟩)))
      have hacc_b5 : ∀ P vp' pos (w' : Option ℕ),
          vp'.id = P → vp'.tcur = max (es.g.epoch P) pos.epoch →
          DoomedLcEqMain Δcka tL par t ({ es with g := es.g.accept P vp' pos }, w') := by
        intro P vp' pos w' hid1 htcur1
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hlc_none, ?_, ?_, ?_⟩)))
        · intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQ : Q = P
          · subst Q; simp [Function.update_self, hid1, htcur1]
          · simp only [Function.update_of_ne hQ]; exact hvp_inv Q
        · intro rec' hrec'
          simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hrec'
          exact htr_inv rec' hrec'.1
        · have hmono : ∀ Q, es.g.epoch Q ≤ (es.g.accept P vp' pos).epoch Q := by
            intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
            by_cases hQ : Q = P
            · subst Q; simp [Function.update_self]
            · simp [Function.update_of_ne hQ]
          rcases hep_inv with hall | ⟨hpar, hs_ge, hr_ge⟩
          · exact Or.inl fun Q => (hall Q).trans (hmono Q)
          · exact Or.inr ⟨hpar, hs_ge.trans (hmono _), hr_ge.trans (hmono _)⟩
      rcases q with n | (((((q | q) | q) | q) | P) | df)
      · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
          AuthL11.pImpl, bind_assoc, pure_bind,
          simulateQ_pure] at hr
        rw [StateT.run_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨⟨_, sp1⟩, _, hr2⟩
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr2
        subst hr2; exact hstay5 _
      · rcases q with ⟨P, m_msg, r0⟩
        simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
          QueryImpl.add_apply, transmitEBucket, StateT.run_bind, StateT.run_get, pure_bind,
          hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hr
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r0.isSome with _ | s₁
        · simp only [hep, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hstay5 _
        · have hs₁_st_tr : s₁.st = es.g.st ∧ s₁.trans = es.g.trans := by
            unfold SM.GameState.epMgmt at hep
            by_cases hs : P.sendsIn (es.g.epoch P + 1) = true
            · simp only [hs, ↓reduceIte] at hep
              split at hep
              · cases hep
              · split at hep <;> injection hep with hep <;> subst hep <;> exact ⟨rfl, rfl⟩
            · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
              split at hep <;> simp at hep; subst hep; exact ⟨rfl, rfl⟩
          simp only [hep, hs₁_st_tr.1, liftH_run_main, StateT.run_bind, pure_bind, bind_assoc,
            simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨vout, h1⟩, sp1⟩, hr1, hr2⟩
          obtain ⟨hlc1, hvp_out⟩ := support_vSend_main_props cka prng fs Δcka qep tL par t
            s₁ P (es.g.st P) m_msg r0 es.h sp hr1
          dsimp only at hlc1 hvp_out
          have hidP := (hvp_inv P).1
          have htcurP := (hvp_inv P).2
          cases vout with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some vc =>
            rcases vc with ⟨vp', ct⟩
            obtain ⟨hid', htcur', hct_hdr⟩ := hvp_out vp' ct rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2
            by_cases hs : P.sendsIn (es.g.epoch P + 1) = true
            · have hs_vp : (es.g.st P).id.sendsIn ((es.g.st P).tcur + 1) = true := by
                rw [hidP, htcurP]; exact hs
              simp only [hs_vp, ↓reduceIte] at hlc1 htcur' hct_hdr
              rw [hidP] at hid'; rw [htcurP] at hlc1 htcur' hct_hdr
              have hP_ge : t + 1 ≤ es.g.epoch P := by
                rcases hep_inv with hall | ⟨_, hs_ge, hr_ge⟩
                · exact hall P
                · by_cases hPs : P = Party.senderOf (t + 1)
                  · rw [hPs]; exact hs_ge
                  · have hPr : P = Party.receiverOf (t + 1) := by
                      cases P <;> cases hS : Party.senderOf (t + 1) <;>
                        simp [Party.receiverOf, hS, Party.other] at hPs ⊢
                    rw [hPr] at hs ⊢
                    have hne_t : es.g.epoch (Party.receiverOf (t + 1)) ≠ t := by
                      intro heq; rw [heq, receiverOf_sendsIn_false] at hs; cases hs
                    omega
              have hs₁_props : s₁.win = es.g.win ∧
                  s₁.epoch = Function.update es.g.epoch P (es.g.epoch P + 1) := by
                unfold SM.GameState.epMgmt at hep
                simp only [hs, ↓reduceIte] at hep
                split at hep
                · cases hep
                · split at hep <;> injection hep with hep <;> subst hep <;> exact ⟨rfl, rfl⟩
              by_cases hcond_lc : (postLeak tL s₁ && es.h.lc.isNone && decide (healEpoch tL < es.g.epoch P + 1)) = true
              · simp only [hcond_lc, ↓reduceIte] at hlc1
                refine Or.inr (Or.inr (Or.inl ⟨?_, by simp [hlc1], ?_⟩))
                · dsimp only [SM.GameState.record]; simp [hs₁_props.1, hwin]
                · rw [hlc1]; simp; omega
              · simp only [hcond_lc, Bool.false_eq_true, ↓reduceIte] at hlc1
                rw [hlc_none] at hlc1
                refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hlc1, ?_, ?_, ?_⟩)))
                · dsimp only [SM.GameState.record]; simp [hs₁_props.1, hwin]
                · intro Q; dsimp only [SM.GameState.record]; rw [hs₁_st_tr.1, hs₁_props.2]
                  by_cases hQ : Q = P
                  · subst Q; simp [Function.update_self, hid', htcur']
                  · simp only [Function.update_of_ne hQ]; exact hvp_inv Q
                · intro rec' hrec'; dsimp only [SM.GameState.record] at hrec'
                  rcases List.mem_cons.mp hrec' with rfl | hrec''
                  · simp [hs₁_props.2, hct_hdr]
                  · exact htr_inv rec' (hs₁_st_tr.2 ▸ hrec'')
                · have hmono : ∀ Q, es.g.epoch Q ≤ (s₁.record (2 + Δcka) P vp'
                      ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, ct⟩ false).epoch Q := by
                    intro Q; dsimp only [SM.GameState.record]; rw [hs₁_props.2]
                    by_cases hQ : Q = P
                    · subst Q; simp [Function.update_self]
                    · simp [Function.update_of_ne hQ]
                  rcases hep_inv with hall | ⟨hpar, hs_ge, hr_ge⟩
                  · exact Or.inl fun Q => (hall Q).trans (hmono Q)
                  · exact Or.inr ⟨hpar, hs_ge.trans (hmono _), hr_ge.trans (hmono _)⟩
            · have hns : P.sendsIn (es.g.epoch P + 1) = false := by
                cases h : P.sendsIn (es.g.epoch P + 1) <;> [rfl; contradiction]
              have hns_vp : (es.g.st P).id.sendsIn ((es.g.st P).tcur + 1) = false := by
                rw [hidP, htcurP]; exact hns
              have hs₁_eq : s₁ = es.g := by
                unfold SM.GameState.epMgmt at hep
                simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
                split at hep <;> simp at hep; exact hep.symm
              subst hs₁_eq
              simp only [hns_vp, Bool.false_eq_true, ↓reduceIte, hlc_none] at hlc1 htcur' hct_hdr
              rw [hidP] at hid'; rw [htcurP] at htcur' hct_hdr
              refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hlc1, ?_, ?_, hep_inv⟩)))
              · intro Q; dsimp only [SM.GameState.record]
                by_cases hQ : Q = P
                · subst Q; simp [Function.update_self, hid', htcur']
                · simp only [Function.update_of_ne hQ]; exact hvp_inv Q
              · intro rec' hrec'; dsimp only [SM.GameState.record] at hrec'
                rcases List.mem_cons.mp hrec' with rfl | hrec''
                · exact hct_hdr
                · exact htr_inv rec' hrec''
      · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
            (.inr (.inl (.inl (.inl (.inl (.inr q))))))).run es) = pure (none, es) := by
          simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure]
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
        subst heq; exact hstay5 _
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨rec, vp', htr, rfl, hid', htcur'⟩
        · exact hstay5 _
        · exact Or.inl rfl
        · obtain ⟨hmem, _, hct⟩ := AuthL10.inTransit_some_props htr
          have hrec_ep : rec.pos.epoch = c.1.1 := by
            have := htr_inv rec hmem; rw [hct] at this; exact this.symm
          rw [(hvp_inv P).1] at hid'; rw [(hvp_inv P).2, ← hrec_ep] at htcur'
          exact hacc_b5 P vp' rec.pos _ hid' htcur'
      · rcases q with ⟨P, c⟩
        obtain ⟨ans, es', hrun, hcases⟩ := injectE_main_cases cka prng fs Δcka qep tL par t P c es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inl (.inl (.inr (P, c))))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨vp', i', rfl, hid', htcur'⟩ | ⟨rfl, _, _, _, _⟩
        · exact hstay5 _
        · exact Or.inl rfl
        · rw [(hvp_inv P).1] at hid'; rw [(hvp_inv P).2] at htcur'
          exact hacc_b5 P vp' ⟨P.other, c.1.1, i'⟩ _ hid' htcur'
        · exact Or.inr (Or.inl ⟨rfl, Or.inl (by simp [hlc_none])⟩)
      · by_cases hcr : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
        · have hraw : ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
              (.inr (.inl (.inr P)))).run es) = pure (none, es) := by
            simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
              StateT.run_bind, StateT.run_get, pure_bind, hcr, ↓reduceIte, StateT.run_pure]
          have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t _ es es winEp sp _ hraw hr
          subst heq; exact hstay5 _
        · simp only [stepPBucketLcEqMain, withWinEpDF, StateT.run_mk, implEDFPaperBucketRaw,
            QueryImpl.add_apply, corrEPaperBucket, liftH_run_main, StateT.run_bind, StateT.run_get,
            pure_bind, bind_assoc, hcr, Bool.false_eq_true, ↓reduceIte, simulateQ_bind] at hr
          rw [mem_support_bind_iff] at hr
          rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, hr1, hr2⟩
          have hrev := support_reveal_main_lc cka prng fs Δcka qep tL par t
            es.g P (es.g.st P) es.h sp hr1
          dsimp only at hrev
          cases o with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact Or.inl rfl
          | some _ =>
            rcases hrev with hnone | hlc1
            · cases hnone
            · rw [(hvp_inv P).2] at hlc1
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2
              by_cases hP_ge : t + 1 ≤ es.g.epoch P
              · by_cases hc_lc : ((!postLeak tL es.g && es.h.lc.isNone) &&
                    !(decide (es.g.epoch P < healEpoch tL))) = true
                · simp only [hc_lc, ↓reduceIte] at hlc1
                  refine Or.inr (Or.inr (Or.inl ⟨hwin, by simp [hlc1], ?_⟩))
                  rw [hlc1]; simp; omega
                · simp only [hc_lc, Bool.false_eq_true, ↓reduceIte] at hlc1
                  rw [hlc_none] at hlc1
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hlc1, hvp_inv, htr_inv, hep_inv⟩)))
              · rcases hep_inv with hall | ⟨hpar, hs_ge, hr_ge⟩
                · exact absurd (hall P) hP_ge
                · have hP_rec : P = Party.receiverOf (t + 1) := by
                    by_cases hPs : P = Party.senderOf (t + 1)
                    · subst P; exact absurd hs_ge hP_ge
                    · cases P <;> cases hS : Party.senderOf (t + 1) <;>
                        simp [Party.receiverOf, hS, Party.other] at hPs ⊢
                  subst hP_rec
                  have hep_eq : es.g.epoch (Party.receiverOf (t + 1)) = t := by omega
                  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, ?_, hpar⟩)))
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
                  rw [hep_eq]
                  exact List.mem_cons_self
      · rcases df with ⟨P, c, c'⟩
        obtain ⟨ans, es', hrun, hcases⟩ := deliverForgeE_main_cases cka prng fs Δcka qep tL par t P c c' es hab hwin
        have heq := stepPBucketLcEqMain_of_raw_pure cka prng fs Δcka qep tL par t
          (.inr (.inr (P, c, c'))) es es' winEp sp ans hrun hr
        subst heq
        rcases hcases with rfl | rfl | ⟨vp', i', rfl, hid', htcur'⟩ | ⟨_, _, _, _, rfl, _, _, _, _⟩
        · exact hstay5 _
        · exact Or.inl rfl
        · rw [(hvp_inv P).1] at hid'; rw [(hvp_inv P).2] at htcur'
          exact hacc_b5 P vp' ⟨P.other, c'.1.1, i'⟩ _ hid' htcur'
        · exact Or.inr (Or.inl ⟨rfl, Or.inl (by simp [hlc_none])⟩)

private def runPBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (AuthL11.pImpl prng)
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stP)).run sp
  pure (authOutBucketPaper (2 + Δcka) tL r.1.2 && decide (r.1.2.1.h.lc = some t))

private theorem runPBucketLcEqMain_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (b : Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketLcEqMain cka prng fs Δcka qep tL par t (pure b) stP sp =
      pure (authOutBucketPaper (2 + Δcka) tL stP && decide (stP.1.h.lc = some t)) := by
  simp [runPBucketLcEqMain]

private theorem runPBucketLcEqMain_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketLcEqMain cka prng fs Δcka qep tL par t (liftM (OracleSpec.query q) >>= k) stP sp =
      stepPBucketLcEqMain cka prng fs Δcka qep tL par t q stP sp >>= fun r =>
        runPBucketLcEqMain cka prng fs Δcka qep tL par t (k r.1.1) r.1.2 r.2 := by
  simp [runPBucketLcEqMain, stepPBucketLcEqMain, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPBucketLcEqMain_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    (hd : DoomedLcEqMain Δcka tL par t stP) :
    𝒟[runPBucketLcEqMain cka prng fs Δcka qep tL par t oa stP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stP sp with
  | pure b =>
    rw [runPBucketLcEqMain_pure, outLcEqMain_eq_false_of_doomed hd]
    simp
  | query_bind q k ih =>
    rw [runPBucketLcEqMain_query_bind]
    exact AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPBucketLcEqMain_doomed cka prng fs Δcka qep tL par t htH q stP sp hd r hr)


private theorem senderOf_of_sendsIn_true_n2 {P : Party} {n : ℕ} (h : P.sendsIn n = true) :
    P = Party.senderOf n := by
  unfold Party.sendsIn at h
  unfold Party.senderOf
  cases P <;> by_cases hodd : (n % 2 == 1) = true <;> simp_all [beq_iff_eq]

private theorem other_senderOf_eq_receiverOf_n2 (n : ℕ) :
    (Party.senderOf n).other = Party.receiverOf n := by
  simp [Party.senderOf, Party.receiverOf, Party.other]


/-! ### Part 2: `SyncMainLcEq` Coupling for `T1_lcSlice_le_local` -/

private theorem leComp_lookupBucketF_lcEq_ne
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t t0 : ℕ) (ik : I)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t') (hne : t0 ≠ t) :
    AuthL11.LeComp (fun rP rL =>
        rP.1.1 = rL.1 ∧ rP.2 = sp ∧
        rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
        rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
        (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧
        rL.2.fTable t = hL.fTable t)
      ((simulateQ (AuthL11.pImpl prng)
        ((lookupPRNGBucketF (T := T) (Sig := Sig) t0 ik).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((lookupLocalBucketF (T := T) (Sig := Sig) t0 ik).run hL)) := by
  unfold lookupPRNGBucketF lookupLocalBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft t0 hne]
  cases hlk : (hL.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩
    · by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · simp [hne.symm]

private theorem leComp_challPrf_lookupLocalBucketF
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t : ℕ) (ik : I)
    (sp : PRFPRNG.GameState Sig I K) (hL : LocalBucketState T Sig K I)
    (hb : sp.b = true) (htab : sp.table = hL.fTable t) :
    AuthL11.LeComp
      (fun (r1 : Option (Sig × K) × PRFPRNG.GameState Sig I K)
           (r2 : K × LocalBucketState T Sig K I) =>
        r1.1 = none ∨
        (r1.1 = some ((prng.up sp.σ ik).1, r2.1) ∧
          r2.2.cache = hL.cache ∧ r2.2.lc = hL.lc ∧
          r1.2.σ = sp.σ ∧ r1.2.b = true ∧
          (∀ t', t' ≠ t → r2.2.fTable t' = hL.fTable t') ∧
          r1.2.table = r2.2.fTable t))
      ((PRFPRNG.challPrfImpl prng ik).run sp)
      (simulateQ AuthL11.lImpl
        ((lookupLocalBucketF (T := T) (Sig := Sig) t ik).run hL)) := by
  rw [AuthL11.run_challPrfImpl]
  by_cases hbad : (sp.corr || sp.prng) = true
  · simp only [hbad, ↓reduceIte]
    exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · unfold lookupLocalBucketF
    simp only [hbad, hb, Bool.false_eq_true, ↓reduceIte, htab,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases hlk : (hL.fTable t).lookup ik with
    | some k =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩)
    | none =>
      simp only [StateT.run_bind, simulateQ_bind,
        AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc]
      refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
      simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩)
      · simp [ht']
      · simp

private theorem leComp_rootBucketLcEq
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig) (σ0 : Sig) (hP : PRNGBucketState T Sig K I)
    (sp : PRFPRNG.GameState Sig I K) (hL : LocalBucketState T Sig K I)
    (hΔ : 2 ≤ Δbucket) (htH : healEpoch tL ≤ t) (ht0 : t0 < qep + 1) (hb : sp.b = true)
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t') (htab : sp.table = hL.fTable t)
    (hpl_cr : hP.corrRoot.isSome = true → pl = true)
    (hσ_res : ∀ s, resolveCorrRoot hP (t0 - 1) σv0 = some s → s = σ0)
    (hge_t_some : t < t0 → σv0 = some σ0)
    (hgt_t_mode : t < t0 → pl = true ∨
      (t0 = t + 1 ∧ (partyPar (Party.senderOf (t + 1)) == par) = false))
    (hσ_sp : t0 ≤ t → (pl = false ∨ resolveCorrRoot hP (t0 - 1) σv0 = none) →
      hP.corrRoot = none ∧ sp.σ = σ0) :
    AuthL11.LeComp (fun rP rL =>
        rP.1.1 = none ∨
        ∃ σP σL k, rP.1.1 = some (σP, k) ∧ rL.1 = (σL, k) ∧ (∀ s, σP = some s → s = σL) ∧
          (t ≤ t0 → σP = some σL) ∧
          (pl = false → rP.1.2.corrRoot = none ∧
            (t0 < t → σP = (if t0 < healEpoch tL then some σL else none) ∧ rP.2.σ = σL)) ∧
          (pl = true → σP = some σL ∧ (rP.1.2.corrRoot = hP.corrRoot ∨
            (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (t0 - 1, σ0)))) ∧
          rP.2.b = true ∧ rP.1.2.cache = hP.cache ∧ rP.1.2.lc = hP.lc ∧
          rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
          (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧
          rP.2.table = rL.2.fTable t)
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t t0 pl ik0 σv0).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((rootLocalBucket (T := T) prng Δbucket qep tL par t0 pl ik0 σ0).run hL)) := by
  unfold rootPRNGBucketHybrid rootLocalBucket
  rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
  dsimp only at hb htab hσ_sp; subst hb
  have hnot_qep_lt : ¬ (qep + 1 < t0) := by omega
  by_cases ht_lt : t < t0
  · have hσv0 : σv0 = some σ0 := hge_t_some ht_lt
    subst hσv0
    have hres_eq : resolveCorrRoot hP (t0 - 1) (some σ0) = some σ0 := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, ht_lt, hnot_qep_lt,
      decide_false, Bool.or_false, ↓reduceIte, hres_eq]
    rcases hgt_t_mode ht_lt with rfl | ⟨ht0_eq, hpar_f⟩
    · simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
        (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
        (fun _ => rfl), (by intro h; cases h), (fun _ => ⟨rfl, Or.inl rfl⟩),
        rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
    · subst ht0_eq
      cases pl
      · have hcr_none : hP.corrRoot = none :=
          Option.not_isSome_iff_eq_none.mp fun hcr => by cases hpl_cr hcr
        have his_tH : (tL.isSome && decide (t + 1 = healEpoch tL)) = false := by
          simp [show t + 1 ≠ healEpoch tL by omega]
        have hin_f : inStage2BucketGen Δbucket tL par (t + 1) = false := by
          simp [inStage2BucketGen, hpar_f]
        simp only [Bool.false_eq_true, his_tH, hin_f, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
          (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (fun _ => rfl), (fun _ => ⟨hcr_none, fun h => by omega⟩), (by intro h; cases h),
          rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
      · simp only [StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
          (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (fun _ => rfl), (by intro h; cases h), (fun _ => ⟨rfl, Or.inl rfl⟩),
          rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
  · have ht0_le : t0 ≤ t := Nat.le_of_not_lt ht_lt
    simp only [StateT.run_bind, StateT.run_get, pure_bind, ht_lt, hnot_qep_lt,
      decide_false, Bool.or_false, ↓reduceIte]
    cases pl
    · obtain ⟨hcr_none, hσ0⟩ := hσ_sp ht0_le (Or.inl rfl); subst hσ0
      simp only [hcr_none, Option.isSome_none, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      by_cases ht0_eq : t0 = t
      · subst ht0_eq
        simp only [↓reduceIte]
        by_cases his_tH : (tL.isSome && decide (t0 = healEpoch tL)) = true
        · simp only [his_tH, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_challPrngQuery,
            AuthL11.run_challPrngImpl_none, AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc]
          refine AuthL11.LeComp.sample_bind ($ᵗ I) fun ir _ => ?_
          cases prf_sp
          · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
            refine AuthL11.LeComp.sample_bind ($ᵗ K) fun kOut _ => ?_
            simp only [pure_bind, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
              AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc,
              Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ir).1, (prng.up σ_sp ir).1, kOut,
              rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl), (fun _ => rfl),
              (fun _ => ⟨hcr_none, fun h => by omega⟩), (by intro h; cases h),
              rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [his_tH, Bool.false_eq_true, ↓reduceIte]
          by_cases hin : inStage2BucketGen Δbucket tL par t0 = true
          · simp only [hin, ↓reduceIte, StateT.run_bind, simulateQ_bind,
              simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_challPrfQuery, bind_assoc]
            refine (leComp_challPrf_lookupLocalBucketF prng t0 ik0
              { σ := σ_sp, b := true, corr := corr_sp, prng := prng_sp, prf := prf_sp, table := table_sp }
              hL rfl htab).bind ?_
            rintro ⟨res_prf, sp1⟩ ⟨kL, hL1⟩ hprf
            rcases hprf with hnone | ⟨hres_eq, hcL1, hlcL1, hσ1, hb1, hft1, htab1⟩
            · dsimp only at hnone; subst hnone
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
            · dsimp only at hres_eq; subst hres_eq
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).1, kL,
                rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl), (fun _ => rfl),
                (fun _ => ⟨hcr_none, fun h => by omega⟩), (by intro h; cases h),
                hb1, rfl, rfl, hcL1, hlcL1,
                fun t' ht' => (hft t' ht').trans (hft1 t' ht').symm, htab1⟩)
          · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
              simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
              AuthL11.run_processImpl_some, bind_assoc]
            cases prf_sp
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
                StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
                AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc,
                simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).1,
                (prng.up σ_sp ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
                (fun _ => rfl), (fun _ => ⟨hcr_none, fun h => by omega⟩), (by intro h; cases h),
                rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
            · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have ht0_lt : t0 < t := Nat.lt_of_le_of_ne ht0_le ht0_eq
        simp only [ht0_eq, ↓reduceIte]
        by_cases hge_tH : (!(t0 < healEpoch tL)) = true
        · have hnot_lt_tH : ¬ (t0 < healEpoch tL) := by simpa using hge_tH
          simp only [hge_tH, ↓reduceIte]
          by_cases his_tH : (tL.isSome && decide (t0 = healEpoch tL)) = true
          · simp only [his_tH, ↓reduceIte, StateT.run_bind, simulateQ_bind,
              simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
              AuthL11.run_processImpl_none, bind_assoc]
            cases prf_sp
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
                AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc]
              refine AuthL11.LeComp.sample_bind ($ᵗ I) fun ir _ => ?_
              simp only [pure_bind, StateT.run_bind, simulateQ_bind,
                AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
              refine AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
              simp only [StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ_sp ir).1, kRand, rfl, rfl,
                (fun _ h => by cases h), (fun h => by omega),
                (fun _ => ⟨hcr_none, fun _ => ⟨by simp [hnot_lt_tH], rfl⟩⟩),
                (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
            · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [his_tH, Bool.false_eq_true, ↓reduceIte]
            by_cases hin : inStage2BucketGen Δbucket tL par t0 = true
            · simp only [hin, ↓reduceIte, StateT.run_bind, simulateQ_bind,
                simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
                AuthL11.run_processImpl_some, bind_assoc]
              cases prf_sp
              · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
                  StateT.run_bind, simulateQ_bind]
                refine (leComp_lookupBucketF_lcEq_ne prng t t0 ik0 hP
                  { σ := (prng.up σ_sp ik0).1, b := true, corr := corr_sp, prng := prng_sp,
                    prf := false, table := table_sp } hL hft ht0_eq).bind ?_
                rintro ⟨⟨kP, hP1⟩, sp1⟩ ⟨kL, hL1⟩ ⟨hk, hsp1, hcP1, hcr1, hlcP1, hcL1, hlcL1, hft1, htab1⟩
                subst hk hsp1; simp only [StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ_sp ik0).1, kP, rfl, rfl,
                  (fun _ h => by cases h), (fun h => by omega),
                  (fun _ => ⟨hcr1.trans hcr_none, fun _ => ⟨by simp [hnot_lt_tH], rfl⟩⟩),
                  (by intro h; cases h), rfl, hcP1, hlcP1, hcL1, hlcL1, hft1, by rw [htab1, ← htab]⟩)
              · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
            · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
                simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
                AuthL11.run_processImpl_some, bind_assoc]
              cases prf_sp
              · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).2,
                  rfl, rfl, (fun _ h => by cases h), (fun h => by omega),
                  (fun _ => ⟨hcr_none, fun _ => ⟨by simp [hnot_lt_tH], rfl⟩⟩),
                  (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
              · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · have hlt_tH : t0 < healEpoch tL := by simp at hge_tH; exact hge_tH
          have his_tH : (tL.isSome && decide (t0 = healEpoch tL)) = false := by simp [Nat.ne_of_lt hlt_tH]
          have hin_false : inStage2BucketGen Δbucket tL par t0 = false := by
            cases tL with
            | none => simp [healEpoch] at hlt_tH
            | some l => simp [healEpoch] at hlt_tH; simp [inStage2BucketGen, lastLeakGuessAdmissible]; omega
          simp only [hge_tH, his_tH, hin_false, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            simulateQ_bind, simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
            AuthL11.run_processImpl_some, bind_assoc]
          cases prf_sp
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind,
              simulateQ_bind, simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_corrQuery,
              AuthL11.run_corrImpl, bind_assoc, simulateQ_pure, StateT.run_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).1,
              (prng.up σ_sp ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl), (fun h => by omega),
              (fun _ => ⟨hcr_none, fun _ => ⟨by simp [hlt_tH], rfl⟩⟩), (by intro h; cases h),
              rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · simp only [Bool.true_or, ↓reduceIte]
      cases hres : resolveCorrRoot hP (t0 - 1) σv0 with
      | some σ =>
        have hσ_eq : σ = σ0 := hσ_res σ hres; subst hσ_eq
        simp only [StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ ik0).1, (prng.up σ ik0).1,
          (prng.up σ ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl), (fun _ => rfl),
          (by intro h; cases h), (fun _ => ⟨rfl, Or.inl rfl⟩), rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
      | none =>
        obtain ⟨hcr_none, hσ0⟩ := hσ_sp ht0_le (Or.inr hres); subst hσ0
        simp only [StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc]
        cases prf_sp
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).1,
            (prng.up σ_sp ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl), (fun _ => rfl),
            (by intro h; cases h), (fun _ => ⟨rfl, Or.inr ⟨hcr_none, rfl⟩⟩),
            rfl, rfl, rfl, rfl, rfl, hft, htab⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private def StartSendPostBucketLcEq
    (fs : FSAEADScheme K SS RS (Header T) M E) (t : ℕ) (tL : Option ℕ) (pl : Bool) (e : ℕ)
    (σ0 : Sig) (hP : PRNGBucketState T Sig K I) (hL : LocalBucketState T Sig K I)
    (rP : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Γ × T × Sig × SS) × LocalBucketState T Sig K I) : Prop :=
  rP.1.1 = none ∨
  ∃ γ' T' σP σL k,
    rP.1.1 = some (γ', T', σP, fs.initSender k) ∧ rL.1 = some (γ', T', σL, fs.initSender k) ∧
    (∀ s, σP = some s → s = σL) ∧
    (t ≤ e + 1 → σP = some σL) ∧
    (pl = false → rP.1.2.corrRoot = none ∧
      (e + 1 < t → σP = (if e + 1 < healEpoch tL then some σL else none) ∧ rP.2.σ = σL)) ∧
    (pl = true → σP = some σL ∧ (rP.1.2.corrRoot = hP.corrRoot ∨
      (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, σ0)))) ∧
    rP.2.b = true ∧ (∀ t', RelCacheBucket (rP.1.2.cache t') (rL.2.cache t')) ∧
    rP.1.2.cache (e + 1) = some (T', σP, k) ∧ (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t') ∧
    rL.2.cache (e + 1) = some (T', σL, k) ∧ (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
    rP.1.2.lc = (if pl && hP.lc.isNone && decide (healEpoch tL < e + 1) then some e else hP.lc) ∧
    rL.2.lc = (if pl && hL.lc.isNone && decide (healEpoch tL < e + 1) then some e else hL.lc) ∧
    (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧ rP.2.table = rL.2.fTable t

private theorem leComp_startSendBucketLcEq
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS} {r_coins : Option CCoins}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (htH : healEpoch tL ≤ t)
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t')
    (htab : sp.table = hL.fTable t) (hb : sp.b = true) (he_lt : e + 1 < qep + 1)
    (hpl_cr : hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_res : ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hge_t_some : t < e + 1 → vpP.root = some vpL.root)
    (hgt_t_mode : t < e + 1 → postLeak tL gL = true ∨
      (e + 1 = t + 1 ∧ (partyPar (Party.senderOf (t + 1)) == par) = false))
    (hσ_sp : e + 1 ≤ t → (postLeak tL gL = false ∨ resolveCorrRoot hP e vpP.root = none) →
      hP.corrRoot = none ∧ sp.σ = vpL.root) :
    AuthL11.LeComp (StartSendPostBucketLcEq fs t tL (postLeak tL gL) e vpL.root hP hL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startSend
          gP P (e + 1) vpP.γ vpP.root r_coins).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        (((hooksLocalBucket cka prng fs Δcka qep tL par).startSend
          gL P (e + 1) vpL.γ vpL.root r_coins).run hL)) := by
  let hP0 : PRNGBucketState T Sig K I :=
    if postLeak tL gL && hP.lc.isNone && decide (healEpoch tL < e + 1) then { hP with lc := some e }
    else hP
  let hL0 : LocalBucketState T Sig K I :=
    if postLeak tL gL && hL.lc.isNone && decide (healEpoch tL < e + 1) then { hL with lc := some e }
    else hL
  have hcP0 : hP0.cache = hP.cache := by dsimp only [hP0]; split_ifs <;> rfl
  have hcr0 : hP0.corrRoot = hP.corrRoot := by dsimp only [hP0]; split_ifs <;> rfl
  have hft0 : ∀ t', t' ≠ t → hP0.fTable t' = hL0.fTable t' := by
    intro t' ht'; dsimp only [hP0, hL0]; split_ifs <;> exact hft t' ht'
  have htab0 : sp.table = hL0.fTable t := by dsimp only [hL0]; split_ifs <;> exact htab
  have hcL0 : hL0.cache = hL.cache := by dsimp only [hL0]; split_ifs <;> rfl
  have hres0 : resolveCorrRoot hP0 = resolveCorrRoot hP := by
    funext ep sv; simp [resolveCorrRoot, hcr0]
  have hlcP0 : hP0.lc = (if postLeak tL gL && hP.lc.isNone && decide (healEpoch tL < e + 1) then
      some e else hP.lc) := by dsimp only [hP0]; split_ifs <;> rfl
  have hlcL0 : hL0.lc = (if postLeak tL gL && hL.lc.isNone && decide (healEpoch tL < e + 1) then
      some e else hL.lc) := by dsimp only [hL0]; split_ifs <;> rfl
  have hbody : ∀ (coins : CCoins),
      AuthL11.LeComp (StartSendPostBucketLcEq fs t tL (postLeak tL gL) e vpL.root hP hL)
        ((simulateQ (AuthL11.pImpl prng)
          ((do
            let c := cka.send vpP.γ coins
            match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par t (e + 1)
                (postLeak tL gL) c.2.2 vpP.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketState T Sig K I =>
                { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hP0)).run sp)
        (simulateQ AuthL11.lImpl
          ((do
            let c := cka.send vpL.γ coins
            let (σ', kVal) ← rootLocalBucket prng (3 + Δcka) qep tL par (e + 1)
              (postLeak tL gL) c.2.2 vpL.root
            modify fun s : LocalBucketState T Sig K I =>
              { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run hL0)) := by
    intro coins
    rw [hvp.γ_eq]; simp only [StateT.run_bind, simulateQ_bind]
    refine (leComp_rootBucketLcEq prng (3 + Δcka) qep tL par t (e + 1) (postLeak tL gL)
      (cka.send vpL.γ coins).2.2 vpP.root vpL.root hP0 sp hL0 (by omega) htH he_lt hb hft0 htab0
      (fun h => hpl_cr (hcr0 ▸ h)) (fun s hs => hσ_res s (hres0 ▸ hs))
      hge_t_some hgt_t_mode
      (fun hle h => by obtain ⟨h1, h2⟩ := hσ_sp hle (hres0 ▸ h); exact ⟨hcr0.trans h1, h2⟩)).bind ?_
    rintro ⟨⟨res_root, hP1⟩, sp1⟩ ⟨⟨σL, kL⟩, hL1⟩ hroot
    rcases hroot with hnone | ⟨σP, σL', k, hres_P, hres_L, hσ_rel, hge_some, hpl_f, hpl_t,
      hb1, hcP1, hlcP1, hcL1, hlcL1, hft1, htab1⟩
    · dsimp only at hnone; subst hnone
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hres_P hres_L; cases hres_L; subst hres_P
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨(cka.send vpL.γ coins).1, (cka.send vpL.γ coins).2.1,
        σP, σL, kL, rfl, rfl, hσ_rel, hge_some, hpl_f,
        (fun hpl => ⟨(hpl_t hpl).1, by rw [hcr0] at hpl_t; exact (hpl_t hpl).2⟩),
        hb1, ?_, by simp, ?_, by simp, ?_, hlcP1.trans hlcP0, hlcL1.trans hlcL0, hft1, htab1⟩)
      · intro t'; dsimp only
        by_cases ht' : t' = e + 1
        · subst ht'; simp only [Function.update_self]; exact Or.inr ⟨_, σP, σL, kL, rfl, rfl, hσ_rel⟩
        · rw [Function.update_of_ne ht', Function.update_of_ne ht', hcP1, hcL1, hcP0, hcL0]
          exact hcache t'
      · intro t' ht'; dsimp only; rw [Function.update_of_ne ht', hcP1, hcP0]
      · intro t' ht'; dsimp only; rw [Function.update_of_ne ht', hcL1, hcL0]
  have hrunP : ∀ {α} (k : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) α),
      ((do
        if (postLeak tL gL && hP.lc.isNone && decide (healEpoch tL < e + 1)) = true then
          modify fun s : PRNGBucketState T Sig K I => { s with lc := some ((e + 1) - 1) }
        k).run hP) = k.run hP0 := by
    intro α k; dsimp only [hP0]
    split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind, Nat.add_sub_cancel]
  have hrunL : ∀ {α} (k : HM AuthL11.nilSpec (LocalBucketState T Sig K I) α),
      ((do
        if (postLeak tL gL && hL.lc.isNone && decide (healEpoch tL < e + 1)) = true then
          modify fun s : LocalBucketState T Sig K I => { s with lc := some ((e + 1) - 1) }
        k).run hL) = k.run hL0 := by
    intro α k; dsimp only [hL0]
    split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind, Nat.add_sub_cancel]
  cases r_coins with
  | some coins =>
    unfold hooksPRNGBucketHybrid hooksPRNGBucketHybridGen hooksLocalBucket; dsimp only
    simp only [hg_pl, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hrunP, hrunL]
    exact hbody coins
  | none =>
    unfold hooksPRNGBucketHybrid hooksPRNGBucketHybridGen hooksLocalBucket; dsimp only
    simp only [hg_pl, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hrunP, hrunL, StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc, bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    simp only [pure_bind]; exact hbody coins

private def VSendRelBucketLcEq (t : ℕ) (tL : Option ℕ) (pl : Bool) (e : ℕ) (P : Party)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (rP : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (VP Γ T Sig SS RS × (Header T × E)) × LocalBucketState T Sig K I) : Prop :=
  let e' := if P.sendsIn (e + 1) then e + 1 else e
  rP.1.1 = none ∨
  ∃ vpP' vpL' c,
    rP.1.1 = some (vpP', c) ∧ rL.1 = some (vpL', c) ∧ c.1 = (e', vpL'.curCkaMsg) ∧
    RelVPBucket e' P vpP' vpL' ∧ (∀ t', RelCacheBucket (rP.1.2.cache t') (rL.2.cache t')) ∧
    rP.2.b = true ∧ (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable t ∧
    (P.sendsIn (e + 1) = true →
      (t ≤ e + 1 → vpP'.root = some vpL'.root) ∧
      (pl = false → rP.1.2.corrRoot = none ∧
        (e + 1 < t → vpP'.root = (if e + 1 < healEpoch tL then some vpL'.root else none) ∧
          rP.2.σ = vpL'.root)) ∧
      (pl = true → vpP'.root = some vpL'.root ∧
        (rP.1.2.corrRoot = hP.corrRoot ∨
          (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, vpL.root)))) ∧
      (∃ T' k, vpL'.curCkaMsg = some T' ∧
        rP.1.2.cache (e + 1) = some (T', vpP'.root, k) ∧
        rL.2.cache (e + 1) = some (T', vpL'.root, k)) ∧
      (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t') ∧
      (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
      rP.1.2.lc = (if pl && hP.lc.isNone && decide (healEpoch tL < e + 1) then some e else hP.lc) ∧
      rL.2.lc = (if pl && hL.lc.isNone && decide (healEpoch tL < e + 1) then some e else hL.lc)) ∧
    (P.sendsIn (e + 1) = false →
      rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL ∧
      vpP'.root = vpP.root ∧ vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg)

private theorem leComp_vSendBucketLcEq
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS} {m : M} {r_coins : Option CCoins}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (htH : healEpoch tL ≤ t)
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t')
    (htab : sp.table = hL.fTable t) (hb : sp.b = true)
    (he_lt : P.sendsIn (e + 1) = true → e + 1 < qep + 1)
    (hpl_cr : P.sendsIn (e + 1) = true → hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_res : P.sendsIn (e + 1) = true →
      ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hge_t_some : P.sendsIn (e + 1) = true → t < e + 1 → vpP.root = some vpL.root)
    (hgt_t_mode : P.sendsIn (e + 1) = true → t < e + 1 → postLeak tL gL = true ∨
      (e + 1 = t + 1 ∧ (partyPar (Party.senderOf (t + 1)) == par) = false))
    (hσ_sp : P.sendsIn (e + 1) = true → e + 1 ≤ t →
      (postLeak tL gL = false ∨ resolveCorrRoot hP e vpP.root = none) →
      hP.corrRoot = none ∧ sp.σ = vpL.root) :
    AuthL11.LeComp (VSendRelBucketLcEq t tL (postLeak tL gL) e P vpP vpL hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
          gP P vpP m none r_coins).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((vSend (hooksLocalBucket cka prng fs Δcka qep tL par)
          gL P vpL m none r_coins).run hL)) := by
  unfold vSend
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hsends : P.sendsIn (e + 1) = true
  · simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind]
    refine (leComp_startSendBucketLcEq cka prng fs Δcka qep tL par t htH hg_pl hvp hcache hft htab hb
      (he_lt hsends) (hpl_cr hsends) (hσ_res hsends) (hge_t_some hsends)
      (hgt_t_mode hsends) (hσ_sp hsends)).bind ?_
    rintro ⟨⟨res_ssP, hP1⟩, sp1⟩ ⟨res_ssL, hL1⟩ hss
    rcases hss with hnone | ⟨γ', T', σP, σL, k, hP_eq, hL_eq, hσ_rel, hge_some, hpl_f, hpl_t, hb1,
      hc_rel, hcP_self, hcP_other, hcL_self, hcL_other, hlcP1, hlcL1, hft1, htab1⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
      simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
        pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hsends]), ?_, hc_rel,
        hb1, hft1, htab1, ?_, (fun hns => by rw [hsends] at hns; cases hns)⟩)
      · simp only [hsends, ↓reduceIte]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, hσ_rel⟩
      · intro _
        exact ⟨hge_some, hpl_f, hpl_t, ⟨T', k, rfl, hcP_self, hcL_self⟩,
          hcP_other, hcL_other, hlcP1, hlcL1⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have hns : P.sendsIn (e + 1) = false := Bool.eq_false_iff.mpr hsends
    rcases hvSL : vpL.vS with _ | ss
    · have hvSP : vpP.vS = none := hvp.vS_eq.trans hvSL
      simp only [hvSP, hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb,
        hft, htab, (fun hs => absurd hs hsends), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]; exact hvp
    · have hvSP : vpP.vS = some ss := hvp.vS_eq.trans hvSL
      simp only [hvSP, hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
        hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb,
        hft, htab, (fun hs => absurd hs hsends), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hvp.id_P, rfl, hvp.id_L, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_eq⟩

private structure SyncMainLcEq
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) : Prop where
  abortP : esP.abort = false
  abortL : esL.abort = false
  g_eq : AuthL11.eraseSt esP.g = AuthL11.eraseSt esL.g
  vp_rel : ∀ P, RelVPBucket (esL.g.epoch P) P (esP.g.st P) (esL.g.st P)
  cache_rel : ∀ t', RelCacheBucket (esP.h.cache t') (esL.h.cache t')
  fTable_ne : ∀ t0, t0 ≠ t → esP.h.fTable t0 = esL.h.fTable t0
  table_t : sp.table = esL.h.fTable t
  sp_b : sp.b = true
  epoch_le_qep : ∀ P, esL.g.epoch P ≤ qep
  comp_inv : ∀ pos ∈ esL.g.comp, SM.healedBy esL.g.tL (2 + Δcka) pos.epoch = false
  trans_epoch : ∀ r ∈ esL.g.trans,
    r.pos.epoch ≤ esL.g.epoch r.pos.sender ∧ r.ct.1.1 = r.pos.epoch
  vp_curCka : ∀ P, P.sendsIn (esL.g.epoch P + 1) = false → 0 < esL.g.epoch P →
    ∀ Tc, (esL.g.st P).curCkaMsg = some Tc →
      ∃ σc k, esL.h.cache (esL.g.epoch P) = some (Tc, σc, k)
  trans_cache : ∀ r ∈ esL.g.trans, 0 < r.pos.epoch →
    ∀ Tc, r.ct.1.2 = some Tc →
      ∃ σc k, esL.h.cache r.pos.epoch = some (Tc, σc, k)
  epoch_le : ∀ P, esL.g.epoch P ≤ esL.g.epoch P.other + 1
  epoch_sends : ∀ P, esL.g.epoch P.other < esL.g.epoch P → P.sendsIn (esL.g.epoch P) = true
  same_epoch_rootL : ∀ P Q, esL.g.epoch P = esL.g.epoch Q → (esL.g.st P).root = (esL.g.st Q).root
  cache_rootL : ∀ P Tc σc k, esL.h.cache (esL.g.epoch P) = some (Tc, σc, k) → σc = (esL.g.st P).root
  cache_rootP_none : esP.h.corrRoot = none →
    ∀ P Tc σp k, esP.h.cache (esL.g.epoch P) = some (Tc, σp, k) → (esP.g.st P).root = σp
  corrRoot_pl : esP.h.corrRoot.isSome = true → postLeak tL esL.g = true
  corrRoot_rel : ∀ eC σC, esP.h.corrRoot = some (eC, σC) →
    eC ≤ max (esL.g.epoch .A) (esL.g.epoch .B) ∧
    (∀ P, esL.g.epoch P = eC → σC = (esL.g.st P).root) ∧
    (∀ Tc σl k, esL.h.cache eC = some (Tc, σl, k) → σC = σl)
  root_ge_t : ∀ P, t ≤ esL.g.epoch P → (esP.g.st P).root = some (esL.g.st P).root
  cache_ge_t : ∀ e', t ≤ e' → ∀ Tc σc k, esL.h.cache e' = some (Tc, σc, k) →
    ∃ k', esP.h.cache e' = some (Tc, some σc, k')
  root_ge_tH_lt_t_pl : ∀ P, healEpoch tL ≤ esL.g.epoch P → esL.g.epoch P < t →
    ((esP.g.st P).root).isSome = true → postLeak tL esL.g = true
  some_mono_max : esP.h.corrRoot = none →
    ∀ P, healEpoch tL ≤ esL.g.epoch P → ((esP.g.st P).root).isSome = true →
      (∀ Q, esL.g.epoch Q = max (esL.g.epoch .A) (esL.g.epoch .B) →
        (esP.g.st Q).root = some (esL.g.st Q).root) ∧
      (∀ Tc σl k, esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σl, k) →
        ∃ k', esP.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, some σl, k'))
  root_max : ∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) →
    (esP.g.st P).root = some (esL.g.st P).root ∨
    esP.h.corrRoot = some (max (esL.g.epoch .A) (esL.g.epoch .B), (esL.g.st P).root) ∨
    ((esP.g.st P).root = none ∧ esP.h.corrRoot = none ∧ (esL.g.st P).root = sp.σ)
  cache_max : ∀ Tc σc k,
    esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σc, k) →
    (∃ k', esP.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, some σc, k')) ∨
    esP.h.corrRoot = some (max (esL.g.epoch .A) (esL.g.epoch .B), σc) ∨
    (esP.h.corrRoot = none ∧ σc = sp.σ)
  pl_false_max_lt_t : max (esL.g.epoch .A) (esL.g.epoch .B) < t → postLeak tL esL.g = false →
    (∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) → (esL.g.st P).root = sp.σ) ∧
    (∀ Tc σc k, esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σc, k) → σc = sp.σ)
  lc_eq : esP.h.lc = esL.h.lc
  pl_false_lc_none : postLeak tL esL.g = false → esP.h.lc = none

private def StepRelLcEqRaw {α : Type}
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (rP : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
      PRFPRNG.GameState Sig I K)
    (rL : α × EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) : Prop :=
  rP.1.2.abort = true ∨ (rP.1.1 = rL.1 ∧ SyncMainLcEq prng Δcka qep tL t rP.1.2 rP.2 rL.2)

private theorem resolveCorrRoot_eq_of_syncMainLcEq
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ} {t : ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) (P : Party) (s : Sig)
    (hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = some s) :
    s = (esL.g.st P).root := by
  cases hrP : (esP.g.st P).root with
  | some σ0 =>
    rw [hrP, resolveCorrRoot] at hres
    exact (hsync.vp_rel P).root_eq s (Option.some.inj hres ▸ hrP)
  | none =>
    rw [hrP, resolveCorrRoot] at hres
    cases hcr : esP.h.corrRoot with
    | none => simp [hcr] at hres
    | some p =>
      rcases p with ⟨eC, σC⟩; rw [hcr] at hres; dsimp only at hres
      split at hres
      · rename_i h_eq; rw [beq_iff_eq] at h_eq; injection hres with hs
        exact hs.symm.trans ((hsync.corrRoot_rel eC σC hcr).2.1 P h_eq)
      · cases hres

private theorem syncMainLcEq_h_step
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ} {t : ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp sp1 : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    {hP1 : PRNGBucketState T Sig K I} {hL1 : LocalBucketState T Sig K I}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL)
    (hcP1 : hP1.cache = esP.h.cache) (hcr1 : hP1.corrRoot = esP.h.corrRoot)
    (hlcP1 : hP1.lc = esP.h.lc) (hcL1 : hL1.cache = esL.h.cache) (hlcL1 : hL1.lc = esL.h.lc)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' ≠ t → hP1.fTable t' = hL1.fTable t')
    (htab1 : sp1.table = hL1.fTable t) :
    SyncMainLcEq prng Δcka qep tL t { esP with h := hP1 } sp1 { esL with h := hL1 } :=
  ⟨hsync.abortP, hsync.abortL, hsync.g_eq, hsync.vp_rel,
    fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t',
    hft1, htab1, hb1, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    fun P h1 h2 Tc h3 => by rw [hcL1]; exact hsync.vp_curCka P h1 h2 Tc h3,
    fun r hr h1 Tc h2 => by rw [hcL1]; exact hsync.trans_cache r hr h1 Tc h2,
    hsync.epoch_le, hsync.epoch_sends, hsync.same_epoch_rootL,
    fun P Tc σc k hc => hsync.cache_rootL P Tc σc k (hcL1 ▸ hc),
    fun hcr P Tc σp k hc => hsync.cache_rootP_none (hcr1 ▸ hcr) P Tc σp k (hcP1 ▸ hc),
    fun hcr => hsync.corrRoot_pl (hcr1 ▸ hcr),
    fun eC σC hcr => by
      obtain ⟨h1, h2, h3⟩ := hsync.corrRoot_rel eC σC (hcr1 ▸ hcr)
      exact ⟨h1, h2, fun Tc σl k hc => h3 Tc σl k (hcL1 ▸ hc)⟩,
    hsync.root_ge_t,
    fun e' he' Tc σc k hc => by
      obtain ⟨k', hk'⟩ := hsync.cache_ge_t e' he' Tc σc k (hcL1 ▸ hc)
      exact ⟨k', by rw [hcP1]; exact hk'⟩,
    hsync.root_ge_tH_lt_t_pl,
    fun hcr P hge his => by
      obtain ⟨h1, h2⟩ := hsync.some_mono_max (hcr1 ▸ hcr) P hge his
      exact ⟨h1, fun Tc σl k hc => by rw [hcP1]; exact h2 Tc σl k (hcL1 ▸ hc)⟩,
    fun P hmax => by
      rcases hsync.root_max P hmax with h1 | h2 | ⟨h3, h4, h5⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (hcr1.trans h2))
      · exact Or.inr (Or.inr ⟨h3, hcr1.trans h4, h5.trans hσ1.symm⟩),
    fun Tc σc k hc => by
      rcases hsync.cache_max Tc σc k (hcL1 ▸ hc) with ⟨k', h1⟩ | h2 | ⟨h3, h4⟩
      · exact Or.inl ⟨k', by rw [hcP1]; exact h1⟩
      · exact Or.inr (Or.inl (hcr1.trans h2))
      · exact Or.inr (Or.inr ⟨hcr1.trans h3, h4.trans hσ1.symm⟩),
    fun hlt hpl => ⟨fun P hmax => ((hsync.pl_false_max_lt_t hlt hpl).1 P hmax).trans hσ1.symm,
      fun Tc σc k hc => ((hsync.pl_false_max_lt_t hlt hpl).2 Tc σc k (hcL1 ▸ hc)).trans hσ1.symm⟩,
    by rw [hlcP1, hlcL1]; exact hsync.lc_eq,
    fun hpl => hlcP1.trans (hsync.pl_false_lc_none hpl)⟩

private theorem syncMainLcEq_set_win [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ} {t : ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) :
    SyncMainLcEq prng Δcka qep tL t
      { esP with g := { esP.g with win := true } } sp
      { esL with g := { esL.g with win := true } } := by
  have hg := hsync.g_eq
  refine ⟨hsync.abortP, hsync.abortL, ?_, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
    hsync.table_t, hsync.sp_b, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
    hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
    hsync.corrRoot_pl, hsync.corrRoot_rel, hsync.root_ge_t, hsync.cache_ge_t,
    hsync.root_ge_tH_lt_t_pl, hsync.some_mono_max,
    hsync.root_max, hsync.cache_max, hsync.pl_false_max_lt_t, hsync.lc_eq, hsync.pl_false_lc_none⟩
  simp [AuthL11.eraseSt, AuthL11.eraseSt_epoch hg, AuthL11.eraseSt_idx hg,
    AuthL11.eraseSt_tL hg, AuthL11.eraseSt_trans hg, AuthL11.eraseSt_chall hg,
    AuthL11.eraseSt_comp hg, AuthL11.eraseSt_maxAcc hg, AuthL11.eraseSt_b hg,
    AuthL11.eraseSt_leaks hg, AuthL11.eraseSt_corrs hg]

private theorem run_commitE_PRNGBucketMain_n2
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]

private theorem run_commitE_LocalBucketMain_n2
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (s : Ctx Γ T Sig SS RS M E) (P : Party)
    (old new : VP Γ T Sig SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) :
    (commitE (hooksLocalBucketMain cka prng fs Δcka qep tL par) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksLocalBucketMain, hooksLocalBucket]

private theorem syncMainLcEq_of_vRecv_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ} {t : ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp sp1 : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    {hP1 : PRNGBucketState T Sig K I} {hL1 : LocalBucketState T Sig K I}
    {P : Party} {c : Header T × E}
    {vpP' : VP Γ T (Option Sig) SS RS} {vpL' : VP Γ T Sig SS RS} {pos : SM.Pos}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL)
    (hpos_ep : pos.epoch = c.1.1) (htle : c.1.1 ≤ esL.g.epoch P + 1) (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPBucket (max (esL.g.epoch P) c.1.1) P vpP' vpL')
    (hcP1 : hP1.cache = esP.h.cache) (hcr1 : hP1.corrRoot = esP.h.corrRoot)
    (hlcP1 : hP1.lc = esP.h.lc) (hcL1 : hL1.cache = esL.h.cache) (hlcL1 : hL1.lc = esL.h.lc)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' ≠ t → hP1.fTable t' = hL1.fTable t')
    (htab1 : sp1.table = hL1.fTable t)
    (hroot_le : c.1.1 ≤ esL.g.epoch P →
      vpP'.root = (esP.g.st P).root ∧ vpL'.root = (esL.g.st P).root ∧
        vpL'.curCkaMsg = (esL.g.st P).curCkaMsg)
    (hnew_hit : c.1.1 = esL.g.epoch P + 1 →
      (∃ tn0, c.1.2 = some tn0) ∧
        ∀ tn0 σp σl kc, c.1.2 = some tn0 → esP.h.cache (esL.g.epoch P + 1) = some (tn0, σp, kc) →
          esL.h.cache (esL.g.epoch P + 1) = some (tn0, σl, kc) →
          vpP'.root = resolveCorrRoot esP.h (esL.g.epoch P + 1) σp ∧ vpL'.root = σl)
    (hnew_other : c.1.1 = esL.g.epoch P + 1 →
      c.1.1 ≤ esL.g.epoch P.other ∧
        ∀ tn0, c.1.2 = some tn0 → ∃ σc kc, esL.h.cache (esL.g.epoch P + 1) = some (tn0, σc, kc)) :
    SyncMainLcEq prng Δcka qep tL t
      { esP with g := esP.g.accept P vpP' pos, h := hP1 } sp1
      { esL with g := esL.g.accept P vpL' pos, h := hL1 } := by
  have hacc_ep : (esL.g.accept P vpL' pos).epoch =
      Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    rw [hpos_ep]
  by_cases hnew : c.1.1 = esL.g.epoch P + 1
  · have hc_le := (hnew_other hnew).1
    have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
      have := hsync.epoch_le P.other; rw [Party.other_other] at this; omega
    have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
      cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
    obtain ⟨⟨tn0, htn0⟩, hhit⟩ := hnew_hit hnew
    obtain ⟨σl, kc, hcL_e1⟩ := (hnew_other hnew).2 tn0 htn0
    obtain ⟨σp0, hcP_e1, hσ_rel0⟩ : ∃ σp0,
        esP.h.cache (esL.g.epoch P + 1) = some (tn0, σp0, kc) ∧ (∀ s, σp0 = some s → s = σl) := by
      rcases hsync.cache_rel (esL.g.epoch P + 1) with ⟨_, hcL_none⟩ | ⟨Tc', σp, σl', k', hcP_eq, hcL_eq', hσ_rel⟩
      · rw [hcL_e1] at hcL_none; cases hcL_none
      · rw [hcL_e1] at hcL_eq'; injection hcL_eq' with hcL_eq'
        rcases Prod.mk.inj hcL_eq' with ⟨hTc', hrest⟩
        rcases Prod.mk.inj hrest with ⟨hσl', hk'⟩; subst Tc' σl' k'
        exact ⟨σp, hcP_eq, hσ_rel⟩
    obtain ⟨hvpP_r, hvpL_r⟩ := hhit tn0 σp0 σl kc htn0 hcP_e1 hcL_e1
    have hσl_other : σl = (esL.g.st P.other).root :=
      hsync.cache_rootL P.other tn0 σl kc (heq_other.symm ▸ hcL_e1)
    have hmax_e1 : max (esL.g.epoch P) c.1.1 = esL.g.epoch P + 1 := by omega
    have hvpL_other : vpL'.root = (esL.g.st P.other).root := hvpL_r.trans hσl_other
    have hep_new : ∀ Q, (esL.g.accept P vpL' pos).epoch Q = esL.g.epoch P + 1 := by
      intro Q; rw [hacc_ep, hmax_e1]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self]
      · simp only [Function.update_of_ne hQ]
        have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
        rw [hQo, heq_other]
    have hrL_new : ∀ Q, ((esL.g.accept P vpL' pos).st Q).root = (esL.g.st P.other).root := by
      intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, hvpL_other]
      · simp only [Function.update_of_ne hQ]
        have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
        rw [hQo]
    have hrP_new_none : esP.h.corrRoot = none →
        ∀ Q, ((esP.g.accept P vpP' pos).st Q).root = (esP.g.st P.other).root := by
      intro hcr Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self]
        have hres_eq : resolveCorrRoot esP.h (esL.g.epoch P + 1) σp0 = σp0 := by cases σp0 <;> simp [resolveCorrRoot, hcr]
        rw [hvpP_r, hres_eq, hsync.cache_rootP_none hcr P.other tn0 σp0 kc (heq_other.symm ▸ hcP_e1)]
      · simp only [Function.update_of_ne hQ]
        have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
        rw [hQo]
    have hmax_new : max ((esL.g.accept P vpL' pos).epoch .A) ((esL.g.accept P vpL' pos).epoch .B) =
        max (esL.g.epoch .A) (esL.g.epoch .B) := by rw [hep_new .A, hep_new .B, Nat.max_self, hmax_old]
    refine ⟨hsync.abortP, hsync.abortL, AuthL11.eraseSt_accept hsync.g_eq P vpP' vpL' pos,
      ?_, fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t', hft1, htab1, hb1,
      fun Q => by dsimp only; rw [hep_new Q, ← heq_other]; exact hsync.epoch_le_qep P.other,
      AuthL11.comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv, ?_, ?_, ?_,
      fun Q => by dsimp only; rw [hep_new Q, hep_new Q.other]; omega,
      fun Q hlt => by dsimp only at hlt ⊢; rw [hep_new Q, hep_new Q.other] at hlt; omega,
      fun Q1 Q2 _ => by dsimp only; rw [hrL_new Q1, hrL_new Q2], ?_, ?_,
      fun hcr => by dsimp only [SM.GameState.accept, postLeak] at hcr ⊢; rw [hcr1] at hcr; exact hsync.corrRoot_pl hcr,
      ?_, ?_,
      fun e' he' Tc σc k hc => by
        dsimp only at hc ⊢; rw [hcP1]
        exact hsync.cache_ge_t e' he' Tc σc k (hcL1 ▸ hc),
      ?_, ?_, ?_, ?_, ?_,
      by rw [hlcP1, hlcL1]; exact hsync.lc_eq,
      fun hpl => by dsimp only [SM.GameState.accept, postLeak] at hpl ⊢; exact hlcP1.trans (hsync.pl_false_lc_none hpl)⟩
    · intro Q; dsimp only; rw [hacc_ep]; dsimp only [SM.GameState.accept]
      by_cases hQ : Q = P <;> [subst Q; skip]
      · simp only [Function.update_self]; exact hvp'
      · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
    · intro r' hr'; dsimp only at hr' ⊢; rw [hacc_ep]
      simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'
      obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1; refine ⟨?_, h2⟩
      by_cases hQ : r'.pos.sender = P
      · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
      · rw [Function.update_of_ne hQ]; exact h1
    · intro Q hns_Q hpos_Q Tc hTc; dsimp only at hns_Q hpos_Q hTc ⊢; rw [hcL1]; dsimp only [SM.GameState.accept] at hTc
      by_cases hQ : Q = P
      · subst Q; rw [hep_new P, sendsIn_succ_true_of_false P (esL.g.epoch P + 1) (hnew ▸ hns)] at hns_Q; cases hns_Q
      · rw [hacc_ep] at hns_Q hpos_Q ⊢; simp only [Function.update_of_ne hQ] at hns_Q hpos_Q hTc ⊢
        exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
    · intro r' hr' hpos_r Tc hTc; dsimp only at hr' ⊢; rw [hcL1]
      simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'
      exact hsync.trans_cache r' hr'.1 hpos_r Tc hTc
    · intro Q Tc σc k hc_eq; dsimp only at hc_eq ⊢; rw [hep_new Q, hcL1] at hc_eq; rw [hrL_new Q]
      exact hsync.cache_rootL P.other Tc σc k (heq_other.symm ▸ hc_eq)
    · intro hcr_none Q Tc σp k hc_eq; dsimp only at hcr_none hc_eq ⊢
      rw [hcr1] at hcr_none; rw [hep_new Q, hcP1] at hc_eq; rw [hrP_new_none hcr_none Q]
      exact hsync.cache_rootP_none hcr_none P.other Tc σp k (heq_other.symm ▸ hc_eq)
    · intro eC σC hcr_eq; dsimp only at hcr_eq ⊢; rw [hcr1] at hcr_eq; rw [hmax_new, hcL1]
      obtain ⟨heC_le, heC_root, heC_cache⟩ := hsync.corrRoot_rel eC σC hcr_eq
      exact ⟨heC_le, fun Q hQ_ep => by rw [hep_new Q] at hQ_ep; rw [hrL_new Q]; exact heC_root P.other (heq_other.trans hQ_ep), heC_cache⟩
    · intro Q hge_t; dsimp only at hge_t ⊢; rw [hep_new Q] at hge_t; rw [hrL_new Q]
      by_cases hQ : Q = P
      · subst Q; dsimp only [SM.GameState.accept]; simp only [Function.update_self]
        obtain ⟨k', hcP_some⟩ := hsync.cache_ge_t (esL.g.epoch P + 1) hge_t tn0 σl kc hcL_e1
        rw [hcP_e1] at hcP_some; injection hcP_some with hcP_some
        rcases Prod.mk.inj hcP_some with ⟨_, hrest⟩; rcases Prod.mk.inj hrest with ⟨hσp0, _⟩; subst σp0
        simp [resolveCorrRoot, hvpP_r, hσl_other]
      · dsimp only [SM.GameState.accept, SM.GameState.delete]; simp only [Function.update_of_ne hQ]
        have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
        rw [hQo]; exact hsync.root_ge_t P.other (heq_other.symm ▸ hge_t)
    · intro Q hge his_lt his; dsimp only at hge his_lt his ⊢; dsimp only [SM.GameState.accept, postLeak]
      by_cases hcr_some : esP.h.corrRoot.isSome = true
      · exact hsync.corrRoot_pl hcr_some
      · have hcr_none := Option.not_isSome_iff_eq_none.mp hcr_some
        rw [hep_new Q] at hge his_lt; rw [hrP_new_none hcr_none Q] at his
        exact hsync.root_ge_tH_lt_t_pl P.other (heq_other.symm ▸ hge) (heq_other.symm ▸ his_lt) his
    · intro hcr_none Q0 hge his; dsimp only at hcr_none hge his ⊢
      rw [hcr1] at hcr_none; rw [hep_new Q0] at hge; rw [hrP_new_none hcr_none Q0] at his; rw [hmax_new, hcP1, hcL1]
      obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr_none P.other (heq_other.symm ▸ hge) his
      exact ⟨fun Q _ => by rw [hrP_new_none hcr_none Q, hrL_new Q]; exact hm1 P.other (heq_other.trans hmax_old.symm), hm2⟩
    · intro Q hQ_max; dsimp only at hQ_max ⊢; rw [hmax_new] at hQ_max ⊢
      by_cases hQ : Q = P
      · subst Q; dsimp only [SM.GameState.accept]; simp only [Function.update_self]
        rcases hsync.cache_max tn0 σl kc (hmax_old.symm ▸ hcL_e1) with ⟨k', hcP_some⟩ | hcr_max | ⟨hcr_none, hσl_sp⟩
        · rw [hmax_old, hcP_e1] at hcP_some; injection hcP_some with hcP_some
          rcases Prod.mk.inj hcP_some with ⟨_, hrest⟩; rcases Prod.mk.inj hrest with ⟨hσp0, _⟩; subst σp0
          exact Or.inl (by simp [resolveCorrRoot, hvpP_r, hvpL_r])
        · exact Or.inr (Or.inl (by rw [hcr1, hvpL_r]; exact hcr_max))
        · cases σp0 with
          | some s0 => exact Or.inl (by simp [resolveCorrRoot, hvpP_r, hvpL_r, hσ_rel0 s0 rfl])
          | none => exact Or.inr (Or.inr ⟨by simp [resolveCorrRoot, hvpP_r, hcr_none], hcr1.trans hcr_none, hvpL_r.trans (hσl_sp.trans hσ1.symm)⟩)
      · dsimp only [SM.GameState.accept, SM.GameState.delete]; simp only [Function.update_of_ne hQ]
        have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
        rw [hQo]; rcases hsync.root_max P.other (heq_other.trans hmax_old.symm) with h1 | h2 | ⟨h3, h4, h5⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl (hcr1.trans h2))
        · exact Or.inr (Or.inr ⟨h3, hcr1.trans h4, h5.trans hσ1.symm⟩)
    · intro Tc σc k hc_max; dsimp only at hc_max ⊢; rw [hmax_new, hcL1] at hc_max; rw [hmax_new]
      rcases hsync.cache_max Tc σc k hc_max with ⟨k', h1⟩ | h2 | ⟨h3, h4⟩
      · exact Or.inl ⟨k', by rw [hcP1]; exact h1⟩
      · exact Or.inr (Or.inl (hcr1.trans h2))
      · exact Or.inr (Or.inr ⟨hcr1.trans h3, h4.trans hσ1.symm⟩)
    · intro hlt_max hpl; dsimp only at hlt_max; dsimp only [SM.GameState.accept, postLeak] at hpl
      rw [hmax_new] at hlt_max
      obtain ⟨hp1, hp2⟩ := hsync.pl_false_max_lt_t hlt_max hpl
      exact ⟨fun Q _ => by rw [hrL_new Q]; exact (hp1 P.other (heq_other.trans hmax_old.symm)).trans hσ1.symm,
        fun Tc σc k hc => by dsimp only at hc; rw [hmax_new, hcL1] at hc; exact (hp2 Tc σc k hc).trans hσ1.symm⟩
  · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
    have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
    have hep_old : (esL.g.accept P vpL' pos).epoch = esL.g.epoch := by rw [hacc_ep, hmax_e, Function.update_eq_self]
    have hrP_old : ∀ Q, ((esP.g.accept P vpP' pos).st Q).root = (esP.g.st Q).root := by
      intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQ : Q = P <;> [subst Q; skip] <;> simp [Function.update_self, Function.update_of_ne, (hroot_le htle_e).1, *]
    have hrL_old : ∀ Q, ((esL.g.accept P vpL' pos).st Q).root = (esL.g.st Q).root := by
      intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQ : Q = P <;> [subst Q; skip] <;> simp [Function.update_self, Function.update_of_ne, (hroot_le htle_e).2.1, *]
    have hcurL_old : ∀ Q, ((esL.g.accept P vpL' pos).st Q).curCkaMsg = (esL.g.st Q).curCkaMsg := by
      intro Q; dsimp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQ : Q = P <;> [subst Q; skip] <;> simp [Function.update_self, Function.update_of_ne, (hroot_le htle_e).2.2, *]
    refine ⟨hsync.abortP, hsync.abortL, AuthL11.eraseSt_accept hsync.g_eq P vpP' vpL' pos,
      ?_, fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t', hft1, htab1, hb1,
      fun Q => by dsimp only; rw [hep_old]; exact hsync.epoch_le_qep Q,
      AuthL11.comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv,
      fun r' hr' => by dsimp only at hr' ⊢; rw [hep_old]; simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'; exact hsync.trans_epoch r' hr'.1,
      fun Q h1 h2 Tc h3 => by dsimp only at h1 h2 h3 ⊢; rw [hep_old] at h1 h2 ⊢; rw [hcurL_old Q] at h3; rw [hcL1]; exact hsync.vp_curCka Q h1 h2 Tc h3,
      fun r' hr' h1 Tc h2 => by dsimp only at hr' ⊢; rw [hcL1]; simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'; exact hsync.trans_cache r' hr'.1 h1 Tc h2,
      fun Q => by dsimp only; rw [hep_old]; exact hsync.epoch_le Q,
      fun Q hlt => by dsimp only at hlt ⊢; rw [hep_old] at hlt ⊢; exact hsync.epoch_sends Q hlt,
      fun Q1 Q2 heq => by dsimp only at heq ⊢; rw [hep_old] at heq; rw [hrL_old Q1, hrL_old Q2]; exact hsync.same_epoch_rootL Q1 Q2 heq,
      fun Q Tc σc k hc => by dsimp only at hc ⊢; rw [hep_old, hcL1] at hc; rw [hrL_old Q]; exact hsync.cache_rootL Q Tc σc k hc,
      fun hcr Q Tc σp k hc => by dsimp only at hcr hc ⊢; rw [hcr1] at hcr; rw [hep_old, hcP1] at hc; rw [hrP_old Q]; exact hsync.cache_rootP_none hcr Q Tc σp k hc,
      fun hcr => by dsimp only [SM.GameState.accept, postLeak] at hcr ⊢; rw [hcr1] at hcr; exact hsync.corrRoot_pl hcr,
      ?_,
      fun Q hge_t => by dsimp only at hge_t ⊢; rw [hep_old] at hge_t; rw [hrP_old Q, hrL_old Q]; exact hsync.root_ge_t Q hge_t,
      fun e' he' Tc σc k hc => by
        dsimp only at hc ⊢; rw [hcP1]
        exact hsync.cache_ge_t e' he' Tc σc k (hcL1 ▸ hc),
      fun Q hge hlt his => by dsimp only at hge hlt his ⊢; rw [hep_old] at hge hlt; rw [hrP_old Q] at his; exact hsync.root_ge_tH_lt_t_pl Q hge hlt his,
      ?_, ?_, ?_, ?_,
      by rw [hlcP1, hlcL1]; exact hsync.lc_eq,
      fun hpl => by dsimp only [SM.GameState.accept, postLeak] at hpl ⊢; exact hlcP1.trans (hsync.pl_false_lc_none hpl)⟩
    · intro Q; dsimp only; rw [hep_old]; dsimp only [SM.GameState.accept]
      by_cases hQ : Q = P <;> [subst Q; skip]
      · simp only [Function.update_self]; exact hmax_e ▸ hvp'
      · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
    · intro eC σC hcr; dsimp only at hcr ⊢; rw [hcr1] at hcr; rw [hep_old, hcL1]
      obtain ⟨h1, h2, h3⟩ := hsync.corrRoot_rel eC σC hcr
      exact ⟨h1, fun Q hQ => by rw [hrL_old Q]; exact h2 Q hQ, h3⟩
    · intro hcr Q0 hge his; dsimp only at hcr hge his ⊢
      rw [hcr1] at hcr; rw [hep_old] at hge ⊢; rw [hrP_old Q0] at his; rw [hcP1, hcL1]
      obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr Q0 hge his
      exact ⟨fun Q hQ => by rw [hrP_old Q, hrL_old Q]; exact hm1 Q hQ, hm2⟩
    · intro Q hQ; dsimp only at hQ ⊢; rw [hep_old] at hQ ⊢; rw [hrP_old Q, hrL_old Q]
      rcases hsync.root_max Q hQ with h1 | h2 | ⟨h3, h4, h5⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (hcr1.trans h2))
      · exact Or.inr (Or.inr ⟨h3, hcr1.trans h4, h5.trans hσ1.symm⟩)
    · intro Tc σc k hc; dsimp only at hc ⊢; rw [hep_old, hcL1] at hc; rw [hep_old]
      rcases hsync.cache_max Tc σc k hc with ⟨k', h1⟩ | h2 | ⟨h3, h4⟩
      · exact Or.inl ⟨k', by rw [hcP1]; exact h1⟩
      · exact Or.inr (Or.inl (hcr1.trans h2))
      · exact Or.inr (Or.inr ⟨hcr1.trans h3, h4.trans hσ1.symm⟩)
    · intro hlt_max hpl; dsimp only at hlt_max; dsimp only [SM.GameState.accept, postLeak] at hpl
      rw [hep_old] at hlt_max
      obtain ⟨hp1, hp2⟩ := hsync.pl_false_max_lt_t hlt_max hpl
      exact ⟨fun Q hQ => by dsimp only at hQ ⊢; rw [hep_old] at hQ; rw [hrL_old Q]; exact (hp1 Q hQ).trans hσ1.symm,
        fun Tc σc k hc => by dsimp only at hc; rw [hep_old, hcL1] at hc; exact (hp2 Tc σc k hc).trans hσ1.symm⟩

private def StartRecvPostBucketLcEqMain
    (fs : FSAEADScheme K SS RS (Header T) M E) (t e : ℕ) (tn0 : T)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (rP : (Option (Option (Γ × Option Sig × RS)) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Option (Γ × Sig × RS)) × LocalBucketState T Sig K I) : Prop :=
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧ rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
  ∃ γ' σP σL k,
    rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
    rL.1 = some (some (γ', σL, fs.initReceiver k)) ∧
    (∀ s, σP = some s → s = σL) ∧ rP.2.σ = sp.σ ∧ rP.2.b = true ∧
    rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
    rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
    (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧ rP.2.table = rL.2.fTable t ∧
    (∀ σp σl kc, hP.cache (e + 1) = some (tn0, σp, kc) → hL.cache (e + 1) = some (tn0, σl, kc) →
      σP = resolveCorrRoot hP (e + 1) σp ∧ σL = σl)

private theorem leComp_startRecvBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {e : ℕ} {P : Party} {tn0 : T}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t')
    (htab : sp.table = hL.fTable t) (hb : sp.b = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl) :
    AuthL11.LeComp (StartRecvPostBucketLcEqMain fs t e tn0 hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).startRecv
          gP P (e + 1) vpP.γ vpP.root tn0).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        (((hooksLocalBucketMain cka prng fs Δcka qep tL par).startRecv
          gL P (e + 1) vpL.γ vpL.root tn0).run hL)) := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksLocalBucketMain; dsimp only
  rw [hvp.γ_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hoff :
      AuthL11.LeComp (StartRecvPostBucketLcEqMain fs t e tn0 hP sp hL)
        ((simulateQ (AuthL11.pImpl prng)
          (StateT.run (if !(qep + 1 < e + 1) && inStage2BucketGen (3 + Δcka) tL par (e + 1) &&
                (tL.isSome && decide (e + 1 = healEpoch tL)) then
              (pure none : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
                (Option (Option (Γ × Option Sig × RS))))
            else
              pure (some none)) hP)).run sp)
        (simulateQ AuthL11.lImpl
          (StateT.run (if !(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
                (tL.isSome && decide (e + 1 = healEpoch tL)) then
              (pure none : HM AuthL11.nilSpec (LocalBucketState T Sig K I)
                (Option (Option (Γ × Sig × RS))))
            else
              pure (some none)) hL)) := by
    change AuthL11.LeComp (StartRecvPostBucketLcEqMain fs t e tn0 hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        (StateT.run (if !(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
              (tL.isSome && decide (e + 1 = healEpoch tL)) then
            (pure none : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
              (Option (Option (Γ × Option Sig × RS))))
          else
            pure (some none)) hP)).run sp) _
    by_cases hc_abort : (!(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) &&
        (tL.isSome && decide (e + 1 = healEpoch tL))) = true
    · simp only [hc_abort, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · simp only [hc_abort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  rcases hcache (e + 1) with ⟨hcP, hcL⟩ | ⟨Tc, σp, σl, k, hcP, hcL, hσ_rel⟩
  · conv => arg 2; rw [hcP]
    conv => arg 3; rw [hcL]
    exact hoff
  · conv => arg 2; rw [hcP]
    conv => arg 3; rw [hcL]
    by_cases hTc : Tc = tn0
    · subst hTc
      conv => arg 2; simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      conv => arg 3; simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tc).1,
        resolveCorrRoot hP (e + 1) σp, σl, k, rfl, rfl, ?_, rfl, hb, rfl, rfl, rfl, rfl, rfl, hft, htab,
        fun σp' σl' kc hp hl => by rw [hcP] at hp; rw [hcL] at hl; cases hp; cases hl; exact ⟨rfl, rfl⟩⟩))
      intro s hs; cases σp with
      | some s0 => simp only [resolveCorrRoot, Option.some.injEq] at hs; subst s; exact hσ_rel s0 rfl
      | none =>
        cases hcr : hP.corrRoot with
        | none => simp [resolveCorrRoot, hcr] at hs
        | some ec =>
          rcases ec with ⟨eC, σC⟩; simp only [resolveCorrRoot, hcr] at hs
          by_cases heq : (e + 1 == eC) = true
          · simp only [heq, ↓reduceIte, Option.some.injEq] at hs
            have heq' := eq_of_beq heq; subst heq'
            exact hs.symm.trans (hcr_cache (e + 1) σC hcr Tc σl k hcL)
          · simp [heq] at hs
    · conv => arg 2; simp only [hTc, ↓reduceIte]
      conv => arg 3; simp only [hTc, ↓reduceIte]
      exact hoff

private def VRecvRelBucketLcEqMain (t e : ℕ) (P : Party) (c : Header T × E)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (rP : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Option (VP Γ T Sig SS RS × ℕ × ℕ × M)) × LocalBucketState T Sig K I) : Prop :=
  let t0 := c.1.1
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧
    rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
    rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧ rP.2.b = true ∧ rP.2.σ = sp.σ ∧
    (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable t) ∨
  ∃ vpP' vpL' i' m',
    rP.1.1 = some (some (vpP', t0, i', m')) ∧ rL.1 = some (some (vpL', t0, i', m')) ∧
    t0 ≤ e + 1 ∧ P.sendsIn t0 = false ∧ RelVPBucket (max e t0) P vpP' vpL' ∧
    rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
    rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧ rP.2.b = true ∧ rP.2.σ = sp.σ ∧
    (∀ t', t' ≠ t → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable t ∧
    (t0 ≤ e → vpP'.root = vpP.root ∧ vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg) ∧
    (t0 = e + 1 → (∃ tn0, c.1.2 = some tn0) ∧
      ∀ tn0 σp σl kc, c.1.2 = some tn0 → hP.cache (e + 1) = some (tn0, σp, kc) →
        hL.cache (e + 1) = some (tn0, σl, kc) →
        vpP'.root = resolveCorrRoot hP (e + 1) σp ∧ vpL'.root = σl)

private theorem leComp_vRecvBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {c : Header T × E} {rec : Option (SM.Record M (Header T × E))}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' ≠ t → hP.fTable t' = hL.fTable t')
    (htab : sp.table = hL.fTable t) (hb : sp.b = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl) :
    AuthL11.LeComp (VRecvRelBucketLcEqMain t e P c vpP vpL hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          gP P vpP c rec).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((vRecv (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          gL P vpL c rec).run hL)) := by
  unfold vRecv; dsimp only; rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hguard : (P.sendsIn c.1.1 || decide (e + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab⟩))
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    have hns : P.sendsIn c.1.1 = false := Bool.eq_false_iff.mpr hguard.1
    have htle : c.1.1 ≤ e + 1 := Nat.le_of_not_lt hguard.2
    by_cases hnew : c.1.1 = e + 1
    · simp only [hnew, ↓reduceIte]
      have hmax : max e (e + 1) = e + 1 := Nat.max_eq_right (Nat.le_succ e)
      cases hTn : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab⟩))
      | some Tn =>
        simp only [StateT.run_bind, simulateQ_bind]
        have hns_e1 : P.sendsIn (e + 1) = false := hnew ▸ hns
        refine (leComp_startRecvBucketLcEqMain cka prng fs Δcka qep tL par t hvp hcache hft htab
          hb hcr_cache).bind ?_
        rintro ⟨⟨res_srP, hP1⟩, sp1⟩ ⟨res_srL, hL1⟩ hsr
        rcases hsr with hnone | ⟨hP_none, hL_none, rfl, rfl, rfl⟩ |
          ⟨γ', σP, σL, k, hP_some, hL_some, hσ_rel, hσ1, hb1, hcP1, hcr1, hlcP1, hcL1, hlcL1,
            hft1, htab1, hcache_hit⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab⟩))
        · dsimp only at hP_some hL_some; subst hP_some hL_some
          simp only [pure_bind, Function.update_self, hooksPRNGBucketMain,
            hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen, hooksLocalBucketMain, hooksLocalBucket]
          cases hfs : fs.receive (fs.initReceiver k) c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure
              (Or.inr (Or.inl ⟨rfl, rfl, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htab1⟩))
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]; refine AuthL11.LeComp.pure ?_
            dsimp only [VRecvRelBucketLcEqMain]; rw [hnew, hmax]
            refine Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_e1, ?_,
              hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htab1, fun hle_e => by omega, ?_⟩)
            · refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_, hσ_rel⟩
              intro t'; dsimp only; rw [Function.update_idem, Function.update_idem]
              by_cases ht' : t' = e + 1
              · subst ht'; simp only [Function.update_self]
              · simp only [Function.update_of_ne ht', hvp.vR_eq t']
            · intro _; refine ⟨⟨Tn, hTn⟩, fun tn0 σp σl kc htn0 hcP_eq hcL_eq => ?_⟩
              rw [hTn] at htn0; cases htn0; exact hcache_hit σp σl kc hcP_eq hcL_eq
    · simp only [hnew, ↓reduceIte, pure_bind]
      have htle_e : c.1.1 ≤ e := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max e c.1.1 = e := Nat.max_eq_left htle_e
      rcases hvRL : vpL.vR c.1.1 with _ | rs
      · have hvRP : vpP.vR c.1.1 = none := (hvp.vR_eq c.1.1).trans hvRL
        simp only [hvRP, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab⟩))
      · have hvRP : vpP.vS = vpP.vS ∧ vpP.vR c.1.1 = some rs := ⟨rfl, (hvp.vR_eq c.1.1).trans hvRL⟩
        simp only [hvRP.2, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
          hooksLocalBucketMain, hooksLocalBucket, pure_bind]
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab⟩))
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, rfl, rfl, rfl, hb, rfl, hft, htab,
            fun _ => ⟨rfl, rfl, rfl⟩, fun heq => False.elim (hnew heq)⟩))
          rw [hmax]
          refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            ?_, hvp.root_eq⟩
          intro t'; dsimp only
          by_cases ht' : t' = c.1.1
          · subst ht'; simp only [Function.update_self]
          · simp only [Function.update_of_ne ht', hvp.vR_eq t']

private theorem leComp_deliverEMain_lcEq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) :
    AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
      ((simulateQ (AuthL11.pImpl prng) ((deliverE
        (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl ((deliverE (hooksLocalBucketMain cka prng fs Δcka qep tL par) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c⟩; unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none => simp only [StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esP.g.mustBeCorrect fs.maxSkip P r = esL.g.mustBeCorrect fs.maxSkip P r := by
        simp [SM.GameState.mustBeCorrect, AuthL11.eraseSt_comp hsync.g_eq,
          AuthL11.eraseSt_maxAcc hsync.g_eq]
      simp only [hmust_eq, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecvBucketLcEqMain cka prng fs Δcka qep tL par t
        (hsync.vp_rel P) hsync.cache_rel hsync.fTable_ne hsync.table_t hsync.sp_b
        (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
      rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
      rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htab1⟩ |
        ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
          hft1, htab1, hroot_le, hnew_hit⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_none hL_none; subst hP_none hL_none
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hs1 := syncMainLcEq_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1
        by_cases hmust : ((bucketAuthCfg Δcka tL par : SM.Config M).deliverWin &&
            esL.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_set_win hs1⟩)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
      · dsimp only at hP_some hL_some; subst hP_some hL_some
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucketMain_n2, run_commitE_LocalBucketMain_n2,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [AuthL11.eraseSt_chall hsync.g_eq]
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
        have hs_acc := syncMainLcEq_of_vRecv_accept hsync hr_pos_ep htle hns hvp'
          hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1 hroot_le hnew_hit (fun hnew => by
            refine ⟨by rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1, fun tn0 htn0 => ?_⟩
            have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2]; exact htn0
            rw [← hnew, ← hr_pos_ep]
            exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2)
        by_cases hwin_cond : (((bucketAuthCfg Δcka tL par : SM.Config M).deliverWin &&
            esL.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg))) = true
        · simp only [hwin_cond, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_set_win hs_acc⟩)
        · simp only [hwin_cond, Bool.false_eq_true, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs_acc⟩)

private theorem leComp_injectEMain_lcEq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) :
    AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
      ((simulateQ (AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((injectE (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esL.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    refine (leComp_vRecvBucketLcEqMain cka prng fs Δcka qep tL par t
      (hsync.vp_rel P) hsync.cache_rel hsync.fTable_ne hsync.table_t hsync.sp_b
      (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htab1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
        hft1, htab1, hroot_le, hnew_hit⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none; subst hP_none hL_none
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1⟩)
    · dsimp only at hP_some hL_some; subst hP_some hL_some
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      have hs1 := syncMainLcEq_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
      · simp only [hqep, ↓reduceIte]
        rw [AuthL11.eraseSt_trivial hsync.g_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq; rw [heq] at htriv
            have htf := AuthL11.trivial_false_of_safeInj esL.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv; cases htriv
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketMain_n2,
            run_commitE_LocalBucketMain_n2, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncMainLcEq_of_vRecv_accept hsync rfl htle hns hvp' hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1
              hroot_le hnew_hit (fun heq => False.elim (hne_e1 heq))⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_set_win hs1⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)

private theorem leComp_deliverForgeEMain_lcEq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E) × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) :
    AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((deliverForgeE (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_comp hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      rw [AuthL11.eraseSt_inTransit hsync.g_eq]
      by_cases hrej : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos ||
          (c.1 != c'.1)) = true
      · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hrej, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
        have hhdr_eq : c.1 = c'.1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hrej
          exact hrej.2
        have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
          unfold SM.GameState.inTransit at htr
          have hfind := List.find?_some htr
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
          exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
        refine (leComp_vRecvBucketLcEqMain cka prng fs Δcka qep tL par t
          (hsync.vp_rel P) hsync.cache_rel hsync.fTable_ne hsync.table_t hsync.sp_b
          (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)).bind ?_
        rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
        rcases hvr with hnone | ⟨hP_none, hL_none, hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1, hft1, htab1⟩ |
          ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcP1, hcr1, hlcP1, hcL1, hlcL1, hb1, hσ1,
            hft1, htab1, hroot_le, hnew_hit⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1⟩)
        · dsimp only at hP_some hL_some; subst hP_some hL_some
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
          have hs1 := syncMainLcEq_h_step hsync hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1
          by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
          · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
          · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
            rw [AuthL11.eraseSt_trivial hsync.g_eq]
            by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketMain_n2,
                run_commitE_LocalBucketMain_n2, StateT.run_pure, StateT.run_modify, pure_bind,
                simulateQ_pure]
              have hr_ep := hsync.trans_epoch r hr_mem.1
              have hc'_ep : c'.1.1 = r.pos.epoch := by
                simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hbad_ep
                exact hbad_ep.2
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
                syncMainLcEq_of_vRecv_accept hsync rfl htle hns hvp' hcP1 hcr1 hlcP1 hcL1 hlcL1 hb1 hσ1 hft1 htab1
                  hroot_le hnew_hit (fun hnew => by
                    refine ⟨by rw [hc'_ep, ← hr_mem.2.1]; exact hr_ep.1, fun tn0 htn0 => ?_⟩
                    have hct2 : r.ct.1.2 = some tn0 := by
                      rw [hr_mem.2.2, hhdr_eq]; exact htn0
                    rw [← hnew, hc'_ep]
                    exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2)⟩)
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c'.1.1 = true
              · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainLcEq_set_win hs1⟩)
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)

private theorem leComp_corrEPaperBucketMain_lcEq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (P : Party)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL) :
    AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
      ((simulateQ (AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) P).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((corrEPaperBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par) P).run esL)) := by
  change AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
    ((simulateQ (AuthL11.pImpl prng)
      ((corrEPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) P).run esP)).run sp)
    (simulateQ AuthL11.lImpl
      ((corrEPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par) P).run esL))
  unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_corrAllowedPaper hsync.g_eq P]
  by_cases hguard : (false || esL.g.win || !esL.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
    have hb_eq : b_sp = true := hsync.sp_b; subst hb_eq
    have hac_er := AuthL11.eraseSt_afterCorr hsync.g_eq P
    have hvp := hsync.vp_rel P
    have hep_eq : esP.g.epoch = esL.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
    have hpl_eq : postLeak tL esP.g = postLeak tL esL.g := eraseSt_postLeak hsync.g_eq
    have hps_eq : realParty (esP.g.st P) (esP.g.st P).γ (esL.g.st P).root (esP.g.st P).vS (esP.g.st P).vR =
        realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
      dsimp only [realParty]
      rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq, funext hvp.vR_eq]
    have hcomp_ac := AuthL11.comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
      (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv
    have hpl_ac_lt_tH : postLeak tL (esL.g.afterCorr P) = false → esL.g.epoch P < healEpoch tL := by
      intro hpl_ac_f
      by_contra hge
      rw [postLeak_afterCorr_of_ge_healEpoch (Nat.le_of_not_lt hge)] at hpl_ac_f
      cases hpl_ac_f
    simp only [StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc,
      hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
      StateT.run_get, pure_bind]
    rw [hvp.tcur_P, hvp.tcur_L, hep_eq, hpl_eq]
    cases hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root with
    | some σ =>
      have hσ_eq := resolveCorrRoot_eq_of_syncMainLcEq hsync P σ hres; subst hσ_eq
      simp only [hsync.lc_eq]
      by_cases hcond : (!(decide (esL.g.epoch P < healEpoch tL)) && esP.h.corrRoot.isNone) = true
      · have hcond' := hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Option.isNone_iff_eq_none, not_lt] at hcond'
        obtain ⟨hge, hcr_none⟩ := hcond'
        have his : ((esP.g.st P).root).isSome = true := by
          cases hr : (esP.g.st P).root <;> simp [resolveCorrRoot, hr, hcr_none] at hres ⊢
        obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr_none P hge his
        have hpl_ac : postLeak tL (esL.g.afterCorr P) = true := postLeak_afterCorr_of_ge_healEpoch hge
        have he_le_max : esL.g.epoch P ≤ max ((esL.g.afterCorr P).epoch .A) ((esL.g.afterCorr P).epoch .B) := by
          dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; cases P <;> omega
        simp only [hcond, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]
        by_cases hlc_c : ((!postLeak tL esL.g && esL.h.lc.isNone) &&
            !(decide (esL.g.epoch P < healEpoch tL))) = true
        · simp only [hlc_c, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
              hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL,
              fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
              fun eC σC hcr => (by
                dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                exact ⟨he_le_max, fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                  fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
              hsync.root_ge_t, hsync.cache_ge_t,
              fun _ _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
              fun Q hQ => Or.inl (hm1 Q hQ), fun Tc σc k hc => Or.inl (hm2 Tc σc k hc),
              fun _ hpl => (by rw [hpl_ac] at hpl; cases hpl), rfl,
              fun hpl => (by rw [hpl_ac] at hpl; cases hpl)⟩⟩)
        · simp only [hlc_c, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
              hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL,
              fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
              fun eC σC hcr => (by
                dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                exact ⟨he_le_max, fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                  fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
              hsync.root_ge_t, hsync.cache_ge_t,
              fun _ _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
              fun Q hQ => Or.inl (hm1 Q hQ), fun Tc σc k hc => Or.inl (hm2 Tc σc k hc),
              fun _ hpl => (by rw [hpl_ac] at hpl; cases hpl), hsync.lc_eq,
              fun hpl => (by rw [hpl_ac] at hpl; cases hpl)⟩⟩)
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        by_cases hlc_c : ((!postLeak tL esL.g && esL.h.lc.isNone) &&
            !(decide (esL.g.epoch P < healEpoch tL))) = true
        · have hge : healEpoch tL ≤ esL.g.epoch P := by
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hlc_c
            exact hlc_c.2
          have hpl_ac : postLeak tL (esL.g.afterCorr P) = true := postLeak_afterCorr_of_ge_healEpoch hge
          simp only [hlc_c, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
              hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
              fun hcr => postLeak_afterCorr_mono (hsync.corrRoot_pl hcr), hsync.corrRoot_rel,
              hsync.root_ge_t, hsync.cache_ge_t,
              fun Q hge' hlt' his => postLeak_afterCorr_mono (hsync.root_ge_tH_lt_t_pl Q hge' hlt' his),
              hsync.some_mono_max, hsync.root_max, hsync.cache_max,
              fun hlt hpl => (by rw [hpl_ac] at hpl; cases hpl),
              rfl, fun hpl => (by rw [hpl_ac] at hpl; cases hpl)⟩⟩)
        · simp only [hlc_c, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
            ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
              hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
              hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
              hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
              fun hcr => postLeak_afterCorr_mono (hsync.corrRoot_pl hcr), hsync.corrRoot_rel,
              hsync.root_ge_t, hsync.cache_ge_t,
              fun Q hge' hlt' his => postLeak_afterCorr_mono (hsync.root_ge_tH_lt_t_pl Q hge' hlt' his),
              hsync.some_mono_max, hsync.root_max, hsync.cache_max,
              fun hlt hpl => hsync.pl_false_max_lt_t hlt (Bool.eq_false_iff.mpr fun ht => (by
                rw [postLeak_afterCorr_mono ht] at hpl; cases hpl)),
              hsync.lc_eq,
              fun hpl => hsync.pl_false_lc_none (Bool.eq_false_iff.mpr fun ht => (by
                rw [postLeak_afterCorr_mono ht] at hpl; cases hpl))⟩⟩)
    | none =>
      simp only [hsync.lc_eq]
      by_cases hcond : ((!postLeak tL esL.g && esP.h.corrRoot.isNone &&
          !(decide (esL.g.epoch P < healEpoch tL))) &&
          (esL.g.epoch P == max (esL.g.epoch .A) (esL.g.epoch .B))) = true
      · have hcond' := hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Option.isNone_iff_eq_none, not_lt, beq_iff_eq] at hcond'
        rcases hcond' with ⟨⟨⟨hpl0, hcr_none⟩, hge⟩, he_max⟩
        have hlt_t_P : esL.g.epoch P < t := by
          by_contra hge_t
          have hr_some := hsync.root_ge_t P (Nat.le_of_not_lt hge_t)
          simp [hr_some, resolveCorrRoot] at hres
        have hlt_t_max : max (esL.g.epoch .A) (esL.g.epoch .B) < t := he_max ▸ hlt_t_P
        have hpl_ac : postLeak tL (esL.g.afterCorr P) = true := postLeak_afterCorr_of_ge_healEpoch hge
        have hge_dec : decide (esL.g.epoch P < healEpoch tL) = false := decide_eq_false (not_lt.mpr hge)
        simp only [hcond, ↓reduceIte, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc]
        cases prf_sp
        · have hσ_eq : σ_sp = (esL.g.st P).root := ((hsync.pl_false_max_lt_t hlt_t_max hpl0).1 P he_max).symm
          subst hσ_eq
          cases hlc_n : esL.h.lc.isNone
          · simp only [hpl0, hge_dec, Bool.not_false, Bool.true_and, Bool.and_true,
              Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
              ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
                hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
                hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
                hsync.same_epoch_rootL, hsync.cache_rootL,
                fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
                fun eC σC hcr => (by
                  dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                  exact ⟨(by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; omega),
                    fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                    fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
                hsync.root_ge_t, hsync.cache_ge_t,
                fun _ _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
                fun Q hQ => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hQ ⊢
                  rw [he_max, hsync.same_epoch_rootL P Q (he_max.trans hQ.symm)])),
                fun Tc σc k hc => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hc ⊢
                  rw [he_max, (hsync.cache_rootL P Tc σc k (he_max.symm ▸ hc)).symm])),
                fun _ hpl => (by rw [hpl_ac] at hpl; cases hpl), hsync.lc_eq,
                fun hpl => (by rw [hpl_ac] at hpl; cases hpl)⟩⟩)
          · simp only [hpl0, hge_dec, Bool.not_false, Bool.and_true,
              Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
              ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_ne,
                hsync.table_t, rfl, hsync.epoch_le_qep, hcomp_ac,
                hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
                hsync.same_epoch_rootL, hsync.cache_rootL,
                fun hcr => (by dsimp only at hcr; cases hcr), fun _ => hpl_ac,
                fun eC σC hcr => (by
                  dsimp only at hcr; injection hcr with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                  exact ⟨(by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; omega),
                    fun Q hQ => hsync.same_epoch_rootL P Q hQ.symm,
                    fun Tc σl k hc => (hsync.cache_rootL P Tc σl k hc).symm⟩),
                hsync.root_ge_t, hsync.cache_ge_t,
                fun _ _ _ _ => hpl_ac, fun hcr => (by dsimp only at hcr; cases hcr),
                fun Q hQ => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hQ ⊢
                  rw [he_max, hsync.same_epoch_rootL P Q (he_max.trans hQ.symm)])),
                fun Tc σc k hc => Or.inr (Or.inl (by
                  dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hc ⊢
                  rw [he_max, (hsync.cache_rootL P Tc σc k (he_max.symm ▸ hc)).symm])),
                fun _ hpl => (by rw [hpl_ac] at hpl; cases hpl), rfl,
                fun hpl => (by rw [hpl_ac] at hpl; cases hpl)⟩⟩)
        · simp only [↓reduceIte, pure_bind, abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          pure_bind, abortE, StateT.run_bind, StateT.run_modify]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private theorem postLeak_epMgmt_of_sendsIn_false_n2 {St Msg C : Type}
    {g s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hns : P.sendsIn (g.epoch P + 1) = false) (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold SM.GameState.epMgmt at hep; simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split at hep <;> [cases hep; exact (Option.some.inj hep).symm]

private theorem leComp_transmitEBucketMain_lcEq_sync
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (P : Party) (m : M) (r_coins : Option CCoins)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL)
    (hsync_mode : P.sendsIn (esL.g.epoch P + 1) = true → t ≤ esL.g.epoch P →
      ∀ s₁L, esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome = some s₁L →
        postLeak tL s₁L = true ∨
          (esL.g.epoch P = t ∧ (partyPar (Party.senderOf (t + 1)) == par) = false)) :
    AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (P, m, r_coins)).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((transmitEBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (P, m, r_coins)).run esL)) := by
  change AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
    ((simulateQ (AuthL11.pImpl prng)
      ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
        (2 + Δcka) qep (P, m, r_coins)).run esP)).run sp)
    (simulateQ AuthL11.lImpl
      ((transmitEBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
        (2 + Δcka) qep (P, m, r_coins)).run esL))
  unfold transmitEBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁P, s₁L, h1, h2, hs₁_er, hs₁P_st, hs₁L_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · obtain ⟨hs₁_qep, he1_qep⟩ := epMgmt_le_qep hsync.epoch_le_qep h2
      simp only [h1, h2, hs₁P_st, hs₁L_st, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind,
        bind_assoc]
      have hheq : P.sendsIn (esL.g.epoch P + 1) = true →
          esL.g.epoch P = esL.g.epoch P.other :=
        AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
      have he_lt : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 < qep + 1 := by
        intro hsends; have := he1_qep hsends; omega
      have hpl_cr : P.sendsIn (esL.g.epoch P + 1) = true →
          esP.h.corrRoot.isSome = true → postLeak tL s₁L = true :=
        fun _ hcr => postLeak_epMgmt (hsync.corrRoot_pl hcr) h2
      have hσ_res : P.sendsIn (esL.g.epoch P + 1) = true →
          ∀ s, resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = some s →
            s = (esL.g.st P).root :=
        fun _ s hres => resolveCorrRoot_eq_of_syncMainLcEq hsync P s hres
      have hge_t_some : P.sendsIn (esL.g.epoch P + 1) = true →
          t < esL.g.epoch P + 1 → (esP.g.st P).root = some (esL.g.st P).root :=
        fun _ hlt_t => hsync.root_ge_t P (by omega)
      have hgt_t_mode : P.sendsIn (esL.g.epoch P + 1) = true →
          t < esL.g.epoch P + 1 →
          postLeak tL s₁L = true ∨
            (esL.g.epoch P + 1 = t + 1 ∧ (partyPar (Party.senderOf (t + 1)) == par) = false) := by
        intro hsends hlt_t
        rcases hsync_mode hsends (by omega) s₁L h2 with hpl | ⟨he_eq, hpar_f⟩
        · exact Or.inl hpl
        · exact Or.inr ⟨by omega, hpar_f⟩
      have hσ_sp : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 ≤ t →
          (postLeak tL s₁L = false ∨ resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = none) →
          esP.h.corrRoot = none ∧ sp.σ = (esL.g.st P).root := by
        intro hsends he1_le_t hdisj
        have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
          (AuthL11.max_epoch_eq_of_eq (hheq hsends)).symm
        have hlt_max : max (esL.g.epoch .A) (esL.g.epoch .B) < t := by omega
        rcases hdisj with hpl_s1 | hres_none
        · have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
            rw [postLeak_epMgmt ht h2] at hpl_s1; cases hpl_s1
          have hcr0 : esP.h.corrRoot = none := Option.not_isSome_iff_eq_none.mp fun hcr => by
            rw [hsync.corrRoot_pl hcr] at hpl0; cases hpl0
          exact ⟨hcr0, ((hsync.pl_false_max_lt_t hlt_max hpl0).1 P hmax).symm⟩
        · rcases hsync.root_max P hmax with hrP_some | hcr_max | ⟨_, hcr0, hroot_sp⟩
          · rw [hrP_some, resolveCorrRoot] at hres_none; cases hres_none
          · cases hrP : (esP.g.st P).root with
            | some _ => rw [hrP, resolveCorrRoot] at hres_none; cases hres_none
            | none => simp [hrP, resolveCorrRoot, hcr_max, ← hmax] at hres_none
          · exact ⟨hcr0, hroot_sp.symm⟩
      refine (leComp_vSendBucketLcEq cka prng fs Δcka qep tL par t htH (eraseSt_postLeak hs₁_er)
        (hsync.vp_rel P) hsync.cache_rel hsync.fTable_ne hsync.table_t hsync.sp_b
        he_lt hpl_cr hσ_res hge_t_some hgt_t_mode hσ_sp).bind ?_
      rintro ⟨⟨res_vsP, hP1⟩, sp1⟩ ⟨res_vsL, hL1⟩ hvs
      rcases hvs with hnone | ⟨vpP', vpL', c, hP_eq, hL_eq, hc_hdr, hvp', hc_rel, hb1,
        hft1, htab1, hsends_props, hns_props⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine AuthL11.LeComp.pure ?_
        have hrec_eq : (⟨⟨P, s₁P.epoch P, s₁P.idx P + 1⟩, m, c⟩ : Record M (Header T × E)) =
            ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩ := by
          rw [AuthL11.eraseSt_epoch hs₁_er, AuthL11.eraseSt_idx hs₁_er]
        let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩
        rw [hrec_eq]
        have hs₁_ep : s₁L.epoch P = if P.sendsIn (esL.g.epoch P + 1) then esL.g.epoch P + 1
            else esL.g.epoch P := by rw [hs₁_ep_fn]; split <;> simp
        have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
          intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
        have hs₁_comp := hs₁_comp_imp hsync.comp_inv
        have her_rec : AuthL11.eraseSt (s₁P.record (2 + Δcka) P vpP' recL false) =
            AuthL11.eraseSt (s₁L.record (2 + Δcka) P vpL' recL false) :=
          AuthL11.eraseSt_record hs₁_er (2 + Δcka) P vpP' vpL' recL false
        have hvp_rec : ∀ Q, RelVPBucket ((s₁L.record (2 + Δcka) P vpL' recL false).epoch Q) Q
            ((s₁P.record (2 + Δcka) P vpP' recL false).st Q)
            ((s₁L.record (2 + Δcka) P vpL' recL false).st Q) := by
          intro Q; dsimp only [SM.GameState.record]
          by_cases hQ : Q = P
          · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
          · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st]; exact hsync.vp_rel Q
        have htr_ep : ∀ r ∈ (s₁L.record (2 + Δcka) P vpL' recL false).trans,
            r.pos.epoch ≤ (s₁L.record (2 + Δcka) P vpL' recL false).epoch r.pos.sender ∧
              r.ct.1.1 = r.pos.epoch := by
          intro r hr; dsimp only [SM.GameState.record] at hr ⊢
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact ⟨le_rfl, by dsimp only [recL]; rw [hc_hdr, hs₁_ep]⟩
          · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
            refine ⟨?_, h_eq⟩
            by_cases hQ : r.pos.sender = P
            · rw [hQ, hs₁_ep]; rw [hQ] at h_le; split <;> omega
            · rw [hs₁_ep_other _ hQ]; exact h_le
        by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
        · obtain ⟨hge_some, hpl_f, hpl_t, ⟨T', k, hT', hcP_self, hcL_self⟩, hcP_other, hcL_other,
            hlcP1, hlcL1⟩ := hsends_props hsends
          have heq_other := hheq hsends
          have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P :=
            AuthL11.max_epoch_eq_of_eq heq_other
          have hs₁_ep_eq : s₁L.epoch = Function.update esL.g.epoch P (esL.g.epoch P + 1) := by
            rw [hs₁_ep_fn]; simp [hsends]
          have hmax_new : max (s₁L.epoch .A) (s₁L.epoch .B) = esL.g.epoch P + 1 := by
            rw [hs₁_ep_eq, AuthL11.max_epoch_update_succ heq_other]
          have hQ_e1 : ∀ Q, s₁L.epoch Q = esL.g.epoch P + 1 → Q = P := by
            intro Q hQ; rw [hs₁_ep_eq] at hQ
            by_cases hQP : Q = P
            · exact hQP
            · rw [Function.update_of_ne hQP] at hQ
              cases Q <;> cases P <;> simp [Party.other] at hQP heq_other hQ <;> omega
          refine Or.inr ⟨rfl, ⟨hsync.abortP, hsync.abortL, her_rec, hvp_rec, hc_rel, hft1, htab1, hb1,
            hs₁_qep, AuthL11.comp_inv_record s₁L (2 + Δcka) P vpL' _ false rfl hs₁_comp, htr_ep,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            by dsimp only; rw [hlcP1, hlcL1, hsync.lc_eq],
            ?_⟩⟩
          · intro Q hns_Q hpos_Q Tc hTc
            dsimp only [SM.GameState.record] at hns_Q hpos_Q hTc ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte] at hTc ⊢
              rw [hT'] at hTc; cases hTc; exact ⟨vpL'.root, k, hcL_self⟩
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcL_other _ hne]; exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · intro r hr hpos_r Tc hTc
            dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · dsimp only at hTc ⊢; rw [hc_hdr] at hTc; dsimp only at hTc
              rw [hs₁_ep, hsends]; simp only [↓reduceIte]; rw [hT'] at hTc; cases hTc
              exact ⟨vpL'.root, k, hcL_self⟩
            · have hr_mem : r ∈ esL.g.trans := hs₁_trans ▸ hr'
              have hr_le := (hsync.trans_epoch r hr_mem).1
              have hne : r.pos.epoch ≠ esL.g.epoch P + 1 := by
                cases hS : r.pos.sender <;> cases P <;>
                  simp [Party.other, hS] at heq_other hr_le ⊢ <;> omega
              rw [hcL_other _ hne]; exact hsync.trans_cache r hr_mem hpos_r Tc hTc
          · intro Q; dsimp only [SM.GameState.record]; rw [hs₁_ep_eq]
            cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
          · intro Q hlt_Q; dsimp only [SM.GameState.record] at hlt_Q ⊢; rw [hs₁_ep_eq] at hlt_Q ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hsends
            · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          · intro Q1 Q2 heq_ep; dsimp only [SM.GameState.record] at heq_ep ⊢
            have hQ12 : Q1 = Q2 := by
              rw [hs₁_ep_eq] at heq_ep
              cases Q1 <;> cases Q2 <;> cases P <;> simp [Party.other] at heq_other heq_ep ⊢ <;> omega
            subst hQ12; rfl
          · intro Q Tc σc k0 hc_eq; dsimp only [SM.GameState.record] at hc_eq ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [hs₁_ep, hsends] at hc_eq
              simp only [↓reduceIte] at hc_eq; rw [hcL_self] at hc_eq; injection hc_eq with hc_eq
              exact (Prod.mk.inj (Prod.mk.inj hc_eq).2).1.symm
            · simp only [Function.update_of_ne hQ, hs₁L_st]; rw [hs₁_ep_other Q hQ] at hc_eq
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcL_other _ hne] at hc_eq; exact hsync.cache_rootL Q Tc σc k0 hc_eq
          · intro hcr1_none Q Tc σp k0 hc_eq
            dsimp only [SM.GameState.record] at hcr1_none hc_eq ⊢
            have hcr0_none : esP.h.corrRoot = none := by
              cases hpl_s1 : postLeak tL s₁L
              · have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
                  rw [postLeak_epMgmt ht h2] at hpl_s1; cases hpl_s1
                exact Option.not_isSome_iff_eq_none.mp fun hcr => by
                  rw [hsync.corrRoot_pl hcr] at hpl0; cases hpl0
              · rcases (hpl_t hpl_s1).2 with hcr_eq | ⟨hcr0, _⟩
                · exact hcr_eq.symm.trans hcr1_none
                · exact hcr0
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [hs₁_ep, hsends] at hc_eq
              simp only [↓reduceIte] at hc_eq; rw [hcP_self] at hc_eq; injection hc_eq with hc_eq
              exact (Prod.mk.inj (Prod.mk.inj hc_eq).2).1
            · simp only [Function.update_of_ne hQ, hs₁P_st]; rw [hs₁_ep_other Q hQ] at hc_eq
              have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hcP_other _ hne] at hc_eq; exact hsync.cache_rootP_none hcr0_none Q Tc σp k0 hc_eq
          · intro hcr1_some; dsimp only [SM.GameState.record] at hcr1_some ⊢
            cases hpl_s1 : postLeak tL s₁L
            · rw [(hpl_f hpl_s1).1] at hcr1_some; cases hcr1_some
            · exact hpl_s1
          · intro eC σC hcr1_eq; dsimp only [SM.GameState.record] at hcr1_eq ⊢
            have hpl_s1 : postLeak tL s₁L = true := by
              cases hp : postLeak tL s₁L
              · rw [(hpl_f hp).1] at hcr1_eq; cases hcr1_eq
              · rfl
            rw [hmax_new]
            rcases (hpl_t hpl_s1).2 with hcr_eq | ⟨_, hcr_new⟩
            · rw [hcr_eq] at hcr1_eq
              obtain ⟨heC_le, heC_root, heC_cache⟩ := hsync.corrRoot_rel eC σC hcr1_eq
              rw [hmax_old] at heC_le
              refine ⟨by omega, fun Q hQ_ep => ?_, fun Tc σl k0 hc_eq => ?_⟩
              · have hQP : Q ≠ P := by intro rfl; rw [hs₁_ep, hsends] at hQ_ep; simp at hQ_ep; omega
                simp only [Function.update_of_ne hQP, hs₁L_st]
                rw [hs₁_ep_other Q hQP] at hQ_ep; exact heC_root Q hQ_ep
              · rw [hcL_other eC (by omega)] at hc_eq; exact heC_cache Tc σl k0 hc_eq
            · rw [hcr_new] at hcr1_eq; injection hcr1_eq with hpair
              rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
              refine ⟨by omega, fun Q hQ_ep => ?_, fun Tc σl k0 hc_eq => ?_⟩
              · have hQP : Q ≠ P := by intro rfl; rw [hs₁_ep, hsends] at hQ_ep; simp at hQ_ep
                simp only [Function.update_of_ne hQP, hs₁L_st]
                rw [hs₁_ep_other Q hQP] at hQ_ep; exact hsync.same_epoch_rootL P Q hQ_ep.symm
              · rw [hcL_other _ (by omega)] at hc_eq
                exact (hsync.cache_rootL P Tc σl k0 hc_eq).symm
          · intro Q hge_t; dsimp only [SM.GameState.record] at hge_t ⊢
            by_cases hQ : Q = P
            · subst Q; rw [hs₁_ep, hsends] at hge_t; simp only [↓reduceIte] at hge_t
              simp only [Function.update_self]; exact hge_some hge_t
            · simp only [Function.update_of_ne hQ, hs₁P_st, hs₁L_st]
              rw [hs₁_ep_other Q hQ] at hge_t; exact hsync.root_ge_t Q hge_t
          · intro e' hge_t Tc σc k0 hc_eq
            dsimp only at hc_eq ⊢
            by_cases he' : e' = esL.g.epoch P + 1
            · subst he'; rw [hcL_self] at hc_eq; injection hc_eq with hc_eq
              rcases Prod.mk.inj hc_eq with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, _⟩
              exact ⟨k, by rw [hcP_self, hge_some hge_t]⟩
            · rw [hcL_other e' he'] at hc_eq; rw [hcP_other e' he']
              exact hsync.cache_ge_t e' hge_t Tc σc k0 hc_eq
          · intro Q hge hlt his; dsimp only [SM.GameState.record] at hge hlt his ⊢
            cases hpl_s1 : postLeak tL s₁L
            · by_cases hQ : Q = P
              · subst Q; simp only [Function.update_self] at his
                rw [hs₁_ep, hsends] at hge hlt; simp only [↓reduceIte] at hge hlt
                have hnlt : ¬ (esL.g.epoch P + 1 < healEpoch tL) := by omega
                simp [((hpl_f hpl_s1).2 hlt).1, hnlt] at his
              · simp only [Function.update_of_ne hQ, hs₁P_st] at his; rw [hs₁_ep_other Q hQ] at hge hlt
                have := postLeak_epMgmt (hsync.root_ge_tH_lt_t_pl Q hge hlt his) h2
                rw [hpl_s1] at this; cases this
            · exact hpl_s1
          · intro hcr1_none Q0 hge his
            dsimp only [SM.GameState.record] at hcr1_none hge his ⊢
            have hvpP_some : vpP'.root = some vpL'.root := by
              by_cases ht_le_e1 : t ≤ esL.g.epoch P + 1
              · exact hge_some ht_le_e1
              · have he1_lt : esL.g.epoch P + 1 < t := by omega
                have hpl_s1 : postLeak tL s₁L = true := by
                  cases hp : postLeak tL s₁L
                  · by_cases hQ0 : Q0 = P
                    · subst Q0; simp only [Function.update_self] at his
                      rw [hs₁_ep, hsends] at hge; simp only [↓reduceIte] at hge
                      have hnlt : ¬ (esL.g.epoch P + 1 < healEpoch tL) := by omega
                      simp [((hpl_f hp).2 he1_lt).1, hnlt] at his
                    · simp only [Function.update_of_ne hQ0, hs₁P_st] at his
                      rw [hs₁_ep_other Q0 hQ0] at hge
                      have hQ0_lt : esL.g.epoch Q0 < t := by
                        have : esL.g.epoch Q0 ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
                          cases Q0 <;> [exact Nat.le_max_left _ _; exact Nat.le_max_right _ _]
                        omega
                      have := postLeak_epMgmt (hsync.root_ge_tH_lt_t_pl Q0 hge hQ0_lt his) h2
                      rw [hp] at this; cases this
                  · rfl
                exact (hpl_t hpl_s1).1
            rw [hmax_new]
            refine ⟨fun Q hQ => ?_, fun Tc σl k0 hc_eq => ?_⟩
            · rw [hQ_e1 Q hQ]; simp only [Function.update_self]; exact hvpP_some
            · rw [hcL_self] at hc_eq; injection hc_eq with hc_eq
              rcases Prod.mk.inj hc_eq with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, _⟩
              exact ⟨k, by rw [hcP_self, hvpP_some]⟩
          · intro Q hQ_max; dsimp only [SM.GameState.record] at hQ_max ⊢
            rw [hmax_new] at hQ_max ⊢; rw [hQ_e1 Q hQ_max]; simp only [Function.update_self]
            by_cases ht_le_e1 : t ≤ esL.g.epoch P + 1
            · exact Or.inl (hge_some ht_le_e1)
            · have he1_lt : esL.g.epoch P + 1 < t := by omega
              cases hpl_s1 : postLeak tL s₁L
              · have hcr_n := (hpl_f hpl_s1).1
                obtain ⟨hvpP_r, hsp_σ⟩ := (hpl_f hpl_s1).2 he1_lt
                by_cases hlt : esL.g.epoch P + 1 < healEpoch tL
                · exact Or.inl (by simp [hvpP_r, hlt])
                · exact Or.inr (Or.inr ⟨by simp [hvpP_r, hlt], hcr_n, hsp_σ.symm⟩)
              · exact Or.inl (hpl_t hpl_s1).1
          · intro Tc σc k0 hc_max; dsimp only [SM.GameState.record] at hc_max ⊢
            rw [hmax_new] at hc_max ⊢; rw [hcL_self] at hc_max; injection hc_max with hc_max
            rcases Prod.mk.inj hc_max with ⟨rfl, hrest⟩
            rcases Prod.mk.inj hrest with ⟨rfl, _⟩
            by_cases ht_le_e1 : t ≤ esL.g.epoch P + 1
            · exact Or.inl ⟨k, by rw [hcP_self, hge_some ht_le_e1]⟩
            · have he1_lt : esL.g.epoch P + 1 < t := by omega
              cases hpl_s1 : postLeak tL s₁L
              · have hcr_n := (hpl_f hpl_s1).1
                obtain ⟨hvpP_r, hsp_σ⟩ := (hpl_f hpl_s1).2 he1_lt
                by_cases hlt : esL.g.epoch P + 1 < healEpoch tL
                · exact Or.inl ⟨k, by rw [hcP_self]; simp [hvpP_r, hlt]⟩
                · exact Or.inr (Or.inr ⟨hcr_n, hsp_σ.symm⟩)
              · exact Or.inl ⟨k, by rw [hcP_self, (hpl_t hpl_s1).1]⟩
          · intro hlt_max hpl_s1; dsimp only [SM.GameState.record] at hlt_max hpl_s1
            rw [hmax_new] at hlt_max
            have hsp_σ := ((hpl_f hpl_s1).2 hlt_max).2
            refine ⟨fun Q hQ => ?_, fun Tc σc k0 hc => ?_⟩
            · dsimp only [SM.GameState.record] at hQ ⊢; rw [hmax_new] at hQ
              rw [hQ_e1 Q hQ]; simp only [Function.update_self]; exact hsp_σ.symm
            · dsimp only [SM.GameState.record] at hc; rw [hmax_new, hcL_self] at hc
              injection hc with hc
              exact (Prod.mk.inj (Prod.mk.inj hc).2).1.symm.trans hsp_σ.symm
          · intro hpl_s1; dsimp only [SM.GameState.record, postLeak] at hpl_s1 ⊢
            change postLeak tL s₁L = false at hpl_s1
            have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
              rw [postLeak_epMgmt ht h2] at hpl_s1; cases hpl_s1
            rw [hlcP1, hpl_s1]; simp only [Bool.false_and]
            exact hsync.pl_false_lc_none hpl0
        · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
          obtain ⟨hhP1, hsp_eq, hhL1, hvpP_r, hvpL_r, hcur_eq⟩ := hns_props hns
          dsimp only at hhP1 hsp_eq hhL1; subst hhP1 hsp_eq hhL1
          have hs₁L_eq : s₁L = esL.g := postLeak_epMgmt_of_sendsIn_false_n2 hns h2
          subst hs₁L_eq
          have hrP_rec : ∀ Q, ((s₁P.record (2 + Δcka) P vpP' recL false).st Q).root =
              (esP.g.st Q).root := by
            intro Q; dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hvpP_r]
            · simp only [Function.update_of_ne hQ, hs₁P_st]
          have hrL_rec : ∀ Q, ((esL.g.record (2 + Δcka) P vpL' recL false).st Q).root =
              (esL.g.st Q).root := by
            intro Q; dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hvpL_r]
            · simp only [Function.update_of_ne hQ]
          refine Or.inr ⟨rfl, ⟨hsync.abortP, hsync.abortL, her_rec, hvp_rec, hc_rel, hft1, htab1, hb1,
            hs₁_qep, AuthL11.comp_inv_record esL.g (2 + Δcka) P vpL' _ false rfl hs₁_comp, htr_ep,
            ?_, ?_, hsync.epoch_le, hsync.epoch_sends,
            fun Q1 Q2 heq => by dsimp only at heq ⊢; rw [hrL_rec Q1, hrL_rec Q2]; exact hsync.same_epoch_rootL Q1 Q2 heq,
            fun Q Tc σc k0 hc => by dsimp only at hc ⊢; rw [hrL_rec Q]; exact hsync.cache_rootL Q Tc σc k0 hc,
            fun hcr Q Tc σp k0 hc => by dsimp only at hcr hc ⊢; rw [hrP_rec Q]; exact hsync.cache_rootP_none hcr Q Tc σp k0 hc,
            hsync.corrRoot_pl,
            fun eC σC hcr => by
              obtain ⟨h1, h2, h3⟩ := hsync.corrRoot_rel eC σC hcr
              exact ⟨h1, fun Q hQ => by dsimp only at hQ ⊢; rw [hrL_rec Q]; exact h2 Q hQ, h3⟩,
            fun Q hge_t => by dsimp only at hge_t ⊢; rw [hrP_rec Q, hrL_rec Q]; exact hsync.root_ge_t Q hge_t,
            hsync.cache_ge_t,
            fun Q hge hlt his => by dsimp only at hge hlt his ⊢; rw [hrP_rec Q] at his; exact hsync.root_ge_tH_lt_t_pl Q hge hlt his,
            fun hcr Q0 hge his => by
              dsimp only at hcr hge his ⊢; rw [hrP_rec Q0] at his
              obtain ⟨hm1, hm2⟩ := hsync.some_mono_max hcr Q0 hge his
              exact ⟨fun Q hQ => by rw [hrP_rec Q, hrL_rec Q]; exact hm1 Q hQ, hm2⟩,
            fun Q hQ => by dsimp only at hQ ⊢; rw [hrP_rec Q, hrL_rec Q]; exact hsync.root_max Q hQ,
            hsync.cache_max,
            fun hlt_max hpl => by
              obtain ⟨hp1, hp2⟩ := hsync.pl_false_max_lt_t hlt_max hpl
              exact ⟨fun Q hQ => by dsimp only at hQ ⊢; rw [hrL_rec Q]; exact hp1 Q hQ, hp2⟩,
            hsync.lc_eq, hsync.pl_false_lc_none⟩⟩
          · intro Q hns_Q hpos_Q Tc hTc; dsimp only [SM.GameState.record] at hns_Q hpos_Q hTc ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self] at hTc
              rw [hcur_eq] at hTc; exact hsync.vp_curCka P hns hpos_Q Tc hTc
            · simp only [Function.update_of_ne hQ] at hTc
              exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · intro r hr hpos_r Tc hTc; dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · dsimp only at hpos_r hTc ⊢; rw [hc_hdr] at hTc; dsimp only at hTc
              rw [hcur_eq] at hTc; exact hsync.vp_curCka P hns hpos_r Tc hTc
            · exact hsync.trans_cache r hr' hpos_r Tc hTc

private theorem stepPBucketLcEqMain_transmit_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (P : Party) (m : M) (r_coins : Option CCoins)
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {winEpP : Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    {s₁P : Ctx Γ T (Option Sig) SS RS M E}
    {s₁L : Ctx Γ T Sig SS RS M E}
    (hsync : SyncMainLcEq prng Δcka qep tL t esP sp esL)
    (hwinL : esL.g.win = false)
    (h1 : esP.g.epMgmt (2 + Δcka) qep P r_coins.isSome = some s₁P)
    (h2 : esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome = some s₁L)
    (hs₁_er : AuthL11.eraseSt s₁P = AuthL11.eraseSt s₁L)
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true)
    (ht_le : t ≤ esL.g.epoch P)
    (hpl_f : postLeak tL s₁L = false)
    (hnot_mode : ¬ (esL.g.epoch P = t ∧ (partyPar (Party.senderOf (t + 1)) == par) = false)) :
    ∀ r ∈ support (stepPBucketLcEqMain cka prng fs Δcka qep tL par t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r_coins))))))) (esP, winEpP) sp),
      DoomedLcEqMain Δcka tL par t r.1.2 := by
  intro r hr
  have hwinP : esP.g.win = false := (AuthL11.eraseSt_win hsync.g_eq).trans hwinL
  obtain ⟨hs₁P_win, hs₁P_st, hs₁P_tr, hs₁P_ep, hs₁P_ep_other⟩ := epMgmt_preserving_props h1
  have hepP_eq : esP.g.epoch = esL.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
  have htrP_eq : esP.g.trans = esL.g.trans := by
    have := congrArg SM.GameState.trans hsync.g_eq
    simpa [AuthL11.eraseSt] using this
  have hheq : esL.g.epoch P = esL.g.epoch P.other :=
    AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends hsends
  have hpl_s1P : postLeak tL s₁P = false := (eraseSt_postLeak hs₁_er).trans hpl_f
  have hpl0 : postLeak tL esL.g = false := Bool.eq_false_iff.mpr fun ht => by
    rw [postLeak_epMgmt ht h2] at hpl_f; cases hpl_f
  have hlc0 : esP.h.lc = none := hsync.pl_false_lc_none hpl0
  unfold stepPBucketLcEqMain withWinEpDF implEDFPaperBucketRaw at hr
  simp only [QueryImpl.add_apply, transmitEBucket, StateT.run_mk, StateT.run_bind,
    StateT.run_get, pure_bind, hsync.abortP, hwinP, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, Bool.not_false, Bool.true_and, h1, hs₁P_st, AuthL11.run_liftH,
    simulateQ_bind, bind_assoc] at hr
  rw [MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨res_vs, hP1⟩, sp1⟩, hr_vs, hr_rest⟩
  obtain ⟨hlc_vs, hsome_vs⟩ :=
    support_vSend_main_props cka prng fs Δcka qep tL par t s₁P P (esP.g.st P) m r_coins esP.h sp hr_vs
  cases res_vs with
  | none =>
    simp [abortE, StateT.run_modify, StateT.run_pure, simulateQ_pure] at hr_rest
    rcases hr_rest with rfl
    exact Or.inl rfl
  | some p =>
    rcases p with ⟨vpP', ct⟩
    have hwin_rec :
        (s₁P.record (2 + Δcka) P vpP' ⟨⟨P, s₁P.epoch P, s₁P.idx P + 1⟩, m, ct⟩ false).win = false :=
      hs₁P_win.trans hwinP
    simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      simulateQ_pure, hwin_rec, Bool.false_eq_true, ↓reduceIte, support_pure,
      Set.mem_singleton_iff] at hr_rest
    subst hr_rest
    obtain ⟨hvp'_id, hvp'_tcur, hct_ep⟩ := hsome_vs vpP' ct rfl
    rw [(hsync.vp_rel P).id_P] at hvp'_id
    rw [(hsync.vp_rel P).id_P, (hsync.vp_rel P).tcur_P] at hlc_vs hvp'_tcur hct_ep
    simp only [hsends, ↓reduceIte, hpl_s1P, Bool.false_and, hlc0] at hlc_vs hvp'_tcur hct_ep
    have hs₁P_ep_val : s₁P.epoch P = esL.g.epoch P + 1 := by
      rw [hs₁P_ep, hepP_eq, hsends]; simp
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin_rec, hlc_vs, ?_, ?_, ?_⟩)))
    · intro Q
      dsimp only [SM.GameState.record]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, hs₁P_ep_val]
        exact ⟨hvp'_id, hvp'_tcur⟩
      · simp only [Function.update_of_ne hQ, hs₁P_st, hs₁P_ep_other Q hQ, hepP_eq]
        exact ⟨(hsync.vp_rel Q).id_P, (hsync.vp_rel Q).tcur_P⟩
    · intro rec0 hrec0
      dsimp only [SM.GameState.record] at hrec0 ⊢
      rcases List.mem_cons.mp hrec0 with rfl | hr_old
      · dsimp only; rw [hct_ep, hs₁P_ep_val]
      · rw [hs₁P_tr, htrP_eq] at hr_old
        exact (hsync.trans_epoch rec0 hr_old).2
    · dsimp only [SM.GameState.record]
      by_cases ht_lt : t + 1 ≤ esL.g.epoch P
      · refine Or.inl fun Q => ?_
        by_cases hQ : Q = P
        · subst Q; omega
        · have hQo : Q = P.other := by cases Q <;> cases P <;> first | rfl | contradiction
          rw [hs₁P_ep_other Q hQ, hepP_eq, hQo, ← hheq]; omega
      · have he_eq_t : esL.g.epoch P = t := by omega
        have hpar_t : partyPar (Party.senderOf (t + 1)) = par := by
          cases hb : (partyPar (Party.senderOf (t + 1)) == par)
          · exfalso; exact hnot_mode ⟨he_eq_t, hb⟩
          · exact beq_iff_eq.mp hb
        have hP_send : P = Party.senderOf (t + 1) :=
          senderOf_of_sendsIn_true_n2 (he_eq_t ▸ hsends)
        have hPo_recv : P.other = Party.receiverOf (t + 1) := by
          rw [hP_send, other_senderOf_eq_receiverOf_n2]
        refine Or.inr ⟨hpar_t, ?_, ?_⟩
        · rw [← hP_send, hs₁P_ep_val, he_eq_t]
        · have hne_send : Party.receiverOf (t + 1) ≠ P := by
            rw [← hPo_recv]; cases P <;> decide
          rw [hs₁P_ep_other _ hne_send, hepP_eq, ← hPo_recv, ← hheq, he_eq_t]

private def StepRelBucketLcEqMain [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {α : Type}
    (x : (α × (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K)
    (y : α × (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) : Prop :=
  DoomedLcEqMain Δcka tL par t x.1.2 ∨
    (x.1.1 = y.1 ∧ x.1.2.2 = y.2.2 ∧ SyncMainLcEq prng Δcka qep tL t x.1.2.1 x.2 y.2.1)

private def stepLBucketLcEqMain [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp ((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) :=
  simulateQ AuthL11.lImpl ((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
    (implEDFPaperBucketRaw (hooksLocalBucketMain cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) q).run stL)

private theorem leComp_stepPBucketLcEqMain_stepLBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (htH : healEpoch tL ≤ t)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncMainLcEq prng Δcka qep tL t stP.1 sp stL.1) :
    AuthL11.LeComp (StepRelBucketLcEqMain prng Δcka qep tL par t)
      (stepPBucketLcEqMain cka prng fs Δcka qep tL par t q stP sp)
      (stepLBucketLcEqMain cka prng fs Δcka qep tL par q stL) := by
  rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
  dsimp only at hwinEp hsync; subst hwinEp
  have hraw_lift :
      ∀ (q0 : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain),
        AuthL11.LeComp (StepRelLcEqRaw prng Δcka qep tL t)
          ((simulateQ (AuthL11.pImpl prng)
            ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q0).run esP)).run sp)
          (simulateQ AuthL11.lImpl
            ((implEDFPaperBucketRaw (hooksLocalBucketMain cka prng fs Δcka qep tL par)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q0).run esL)) →
        AuthL11.LeComp (StepRelBucketLcEqMain prng Δcka qep tL par t)
          (stepPBucketLcEqMain cka prng fs Δcka qep tL par t q0 (esP, winEpP) sp)
          (stepLBucketLcEqMain cka prng fs Δcka qep tL par q0 (esL, winEpP)) := by
    intro q0 hraw
    unfold stepPBucketLcEqMain stepLBucketLcEqMain withWinEpDF
    simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    refine hraw.bind ?_
    rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨hu, hsync'⟩)
    · exact AuthL11.LeComp.pure (Or.inl (Or.inl hab))
    · dsimp only at hu; subst hu
      rw [AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_win hsync'.g_eq]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)
  rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
  · apply hraw_lift
    simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, AuthL11.lImpl,
      StateT.run_lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · rcases arg with ⟨P, m, r_coins⟩
    by_cases hwinL : esL.g.win = true
    · apply hraw_lift
      have hwinP : esP.g.win = true := (AuthL11.eraseSt_win hsync.g_eq).trans hwinL
      simp [implEDFPaperBucketRaw, transmitEBucket, hsync.abortP, hsync.abortL, hwinP, hwinL]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · have hwinL_f : esL.g.win = false := Bool.eq_false_iff.mpr hwinL
      rcases AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
        ⟨s₁P, s₁L, h1, h2, hs₁_er, _, _, _, _, _⟩
      · apply hraw_lift
        simpa [implEDFPaperBucketRaw] using
          leComp_transmitEBucketMain_lcEq_sync cka prng fs Δcka qep tL par t htH P m r_coins hsync
            (fun _ _ _ hs1 => by rw [h2] at hs1; cases hs1)
      · by_cases hdoom :
            P.sendsIn (esL.g.epoch P + 1) = true ∧
            t ≤ esL.g.epoch P ∧
            postLeak tL s₁L = false ∧
            ¬ (esL.g.epoch P = t ∧ (partyPar (Party.senderOf (t + 1)) == par) = false)
        · rcases hdoom with ⟨hsends, ht_le, hpl_f, hnot_mode⟩
          exact leComp_of_support_left _ _ fun rP hrP _ _ =>
            Or.inl (stepPBucketLcEqMain_transmit_doomed cka prng fs Δcka qep tL par t P m r_coins
              hsync hwinL_f h1 h2 hs₁_er hsends ht_le hpl_f hnot_mode rP hrP)
        · apply hraw_lift
          simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
          refine leComp_transmitEBucketMain_lcEq_sync cka prng fs Δcka qep tL par t htH P m r_coins hsync ?_
          intro hsends ht_le s₁L' hs1'
          rw [h2] at hs1'; injection hs1' with hs1'; subst hs1'
          cases hp : postLeak tL s₁L
          · by_cases hm : esL.g.epoch P = t ∧ (partyPar (Party.senderOf (t + 1)) == par) = false
            · exact Or.inr hm
            · exfalso; exact hdoom ⟨hsends, ht_le, hp, hm⟩
          · exact Or.inl rfl
  · apply hraw_lift
    simp [implEDFPaperBucketRaw, challEBucket]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · apply hraw_lift
    simpa [implEDFPaperBucketRaw] using
      leComp_deliverEMain_lcEq cka prng fs Δcka qep tL par t arg hsync
  · apply hraw_lift
    simpa [implEDFPaperBucketRaw] using
      leComp_injectEMain_lcEq cka prng fs Δcka qep tL par t arg hsync
  · apply hraw_lift
    simpa [implEDFPaperBucketRaw] using
      leComp_corrEPaperBucketMain_lcEq cka prng fs Δcka qep tL par t P hsync
  · apply hraw_lift
    simpa [implEDFPaperBucketRaw] using
      leComp_deliverForgeEMain_lcEq cka prng fs Δcka qep tL par t df hsync

private def runLBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFPaperBucketRaw (hooksLocalBucketMain cka prng fs Δcka qep tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stL)
  pure (authOutBucketPaper (2 + Δcka) tL r.2 && decide (r.2.1.h.lc = some t))

private theorem runLBucketLcEqMain_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (b : Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketLcEqMain cka prng fs Δcka qep tL par t (pure b) stL =
      pure (authOutBucketPaper (2 + Δcka) tL stL && decide (stL.1.h.lc = some t)) := by
  simp [runLBucketLcEqMain]

private theorem runLBucketLcEqMain_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketLcEqMain cka prng fs Δcka qep tL par t (liftM (OracleSpec.query q) >>= k) stL =
      stepLBucketLcEqMain cka prng fs Δcka qep tL par q stL >>= fun r =>
        runLBucketLcEqMain cka prng fs Δcka qep tL par t (k r.1) r.2 := by
  simp [runLBucketLcEqMain, stepLBucketLcEqMain, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPBucketLcEqMain_le_runLBucketLcEqMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncMainLcEq prng Δcka qep tL t stP.1 sp stL.1) :
    𝒟[runPBucketLcEqMain cka prng fs Δcka qep tL par t oa stP sp] {true} ≤
      𝒟[runLBucketLcEqMain cka prng fs Δcka qep tL par t oa stL] {true} := by
  induction oa using OracleComp.inductionOn generalizing stP sp stL with
  | pure b' =>
    rw [runPBucketLcEqMain_pure, runLBucketLcEqMain_pure]
    rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
    dsimp only at hwinEp hsync; subst hwinEp
    have houtBase : authOutBucketPaper (2 + Δcka) tL (esP, winEpP) =
        authOutBucketPaper (2 + Δcka) tL (esL, winEpP) := by
      cases winEpP with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketPaper, authOutBucket, authOut]
        rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
          AuthL11.eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [houtBase, hsync.lc_eq]
  | query_bind q k ih =>
    rw [runPBucketLcEqMain_query_bind, runLBucketLcEqMain_query_bind]
    refine leComp_stepPBucketLcEqMain_stepLBucketLcEqMain cka prng fs Δcka qep tL par t htH q
      hwinEp hsync _ _ ?_
    rintro ⟨⟨uP, stP'⟩, sp'⟩ ⟨uL, stL'⟩ (hd | ⟨hu, hwinEp', hsync'⟩)
    · rw [runPBucketLcEqMain_doomed cka prng fs Δcka qep tL par t htH (k uP) hd]; exact zero_le
    · dsimp only at hu; subst hu; exact ih uP hwinEp' hsync'

private theorem syncMainLcEq_init
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (γA γB : Γ) (ss : SS) (rs : RS) (σP : Option Sig) (σL : Sig)
    (hP0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    (hL0 : LocalBucketState T Sig K I) (hσ_rel : ∀ s, σP = some s → s = σL)
    (hge_some : t ≤ 0 → σP = some σL)
    (hlt_props : 0 < t → σP = (if 0 < healEpoch tL then some σL else none) ∧ sp0.σ = σL)
    (hcr0 : hP0.corrRoot = none) (hb0 : sp0.b = true)
    (hcP0 : hP0.cache = fun _ => none) (hlcP0 : hP0.lc = none)
    (hcL0 : hL0.cache = fun _ => none) (hlcL0 : hL0.lc = none)
    (hft0 : ∀ t', t' ≠ t → hP0.fTable t' = hL0.fTable t')
    (htab0 : sp0.table = hL0.fTable t) :
    SyncMainLcEq (M := M) (E := E) prng Δcka qep tL t
      { g := { st := fun P => match P with | .A => (mkParties γA γB σP ss rs).1 | .B => (mkParties γA γB σP ss rs).2, b := false }, h := hP0 } sp0
      { g := { st := fun P => match P with | .A => (mkParties γA γB σL ss rs).1 | .B => (mkParties γA γB σL ss rs).2, b := false }, h := hL0 } := by
  refine ⟨rfl, rfl, rfl,
    fun P => (by cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hσ_rel⟩),
    fun t' => (by rw [hcP0, hcL0]; exact Or.inl ⟨rfl, rfl⟩),
    hft0, htab0, hb0, fun _ => (by simp),
    fun _ hpos => (by cases hpos), fun _ hr => (by cases hr),
    fun _ _ hpos => (by simp at hpos), fun _ hr => (by cases hr),
    fun _ => (by simp), fun _ hlt => (by simp at hlt),
    fun P Q _ => (by cases P <;> cases Q <;> rfl),
    fun _ _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc),
    fun _ _ _ _ _ hc => (by dsimp only at hc; rw [hcP0] at hc; cases hc),
    fun hcr => (by dsimp only at hcr; rw [hcr0] at hcr; cases hcr),
    fun _ _ hcr => (by dsimp only at hcr; rw [hcr0] at hcr; cases hcr),
    fun P hge => (by dsimp only at hge; cases P <;> exact hge_some hge),
    fun _ _ _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc),
    fun P hge hlt his => ?_, fun _ P hge his => ?_, fun P _ => ?_,
    fun _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc),
    fun hlt_max _ => ?_,
    by dsimp only; rw [hlcP0, hlcL0],
    fun _ => hlcP0⟩
  · dsimp only at hge hlt; have hnlt : ¬ (0 < healEpoch tL) := by omega
    cases P <;> simp [mkParties, (hlt_props hlt).1, hnlt] at his
  · dsimp only at hge
    by_cases ht0 : t ≤ 0
    · exact ⟨fun Q _ => (by cases Q <;> exact hge_some ht0),
        fun _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc)⟩
    · have hlt : 0 < t := by omega
      have hnlt : ¬ (0 < healEpoch tL) := by omega
      cases P <;> simp [mkParties, (hlt_props hlt).1, hnlt] at his
  · by_cases ht0 : t ≤ 0
    · exact Or.inl (by cases P <;> exact hge_some ht0)
    · have hlt : 0 < t := by omega
      obtain ⟨hσP_eq, hsp_σ⟩ := hlt_props hlt
      by_cases hltH : 0 < healEpoch tL
      · exact Or.inl (by cases P <;> simp [mkParties, hσP_eq, hltH])
      · exact Or.inr (Or.inr ⟨by cases P <;> simp [mkParties, hσP_eq, hltH],
          hcr0, by cases P <;> exact hsp_σ.symm⟩)
  · dsimp only at hlt_max
    have hlt : 0 < t := by simpa using hlt_max
    have hsp_σ := (hlt_props hlt).2
    exact ⟨fun P _ => (by cases P <;> exact hsp_σ.symm),
      fun _ _ _ hc => (by dsimp only at hc; rw [hcL0] at hc; cases hc)⟩

private theorem T1_lcSlice_le_local [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) (htH : healEpoch tL ≤ t) (_ht : t < qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redMainOut cka prng fs lam Δcka qep tL par t
        (fun st => authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = some t)) A)] {true} ≤
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  unfold PRFPRNG.branch redMainOut
    localAuthDFPaperBucketMainLcEq engRunDFPaperBucket initPRNGBucketHybrid initLocalBucket
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    AuthL11.simulateQ_pImpl_run_lift_sampleT, AuthL11.simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootBucketLcEq (T := T) prng (3 + Δcka) qep tL par t 0 false lam none (prng.init kr)
    ({} : PRNGBucketState T Sig K I) { σ := prng.init kr, b := true }
    ({} : LocalBucketState T Sig K I) (by omega) htH (Nat.zero_lt_succ qep) rfl (fun _ _ => rfl) rfl
    (by simp) (fun _ h => by simp [resolveCorrRoot] at h)
    (fun hlt => by omega) (fun hlt => by omega) (fun _ _ => ⟨rfl, rfl⟩)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL⟩, hL0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨σP, σL', k', hres_eq, hL_eq, hσ_rel, hge_some, hpl_f, _, hb0, hcP0, hlcP0, hcL0, hlcL0, hft0, htab0⟩
  · dsimp only at hnone; subst hnone; simp
  · dsimp only at hres_eq hL_eq; injection hL_eq with hσL_eq hk_eq; subst hres_eq hσL_eq hk_eq
    obtain ⟨hcr0, hlt_props⟩ := hpl_f rfl
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc, Function.comp_apply]
    exact runPBucketLcEqMain_le_runLBucketLcEqMain (stP := (_, none)) (stL := (_, none))
      cka prng fs Δcka qep tL par t htH A rfl
      (syncMainLcEq_init prng Δcka qep tL t (cka.initA kc) (cka.initB kc)
        (fs.initSender kL) (fs.initReceiver kL) σP σL hP0 sp0 hL0
        hσ_rel hge_some hlt_props hcr0 hb0 hcP0 hlcP0 hcL0 hlcL0 hft0 htab0)


/-! ### 1. Pure `resolveCorrRoot`, `RelStepRoot`, `WinEpInv`, and `DoomedMainDF` Helpers -/

@[simp]
private theorem resolveCorrRoot_some (h : PRNGBucketState T Sig K I) (ep : ℕ) (σ : Sig) :
    resolveCorrRoot h ep (some σ) = some σ := rfl

private theorem resolveCorrRoot_of_corrRoot_none {h : PRNGBucketState T Sig K I}
    (hcr : h.corrRoot = none) (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h ep σv = σv := by
  cases σv <;> simp [resolveCorrRoot, hcr]

private theorem resolveCorrRoot_set_of_isNone {h : PRNGBucketState T Sig K I}
    (hcr : h.corrRoot = none) {ep : ℕ} {σv : Option Sig} {σ : Sig}
    (hres : resolveCorrRoot h ep σv = some σ) (v : ℕ × Sig) :
    resolveCorrRoot { h with corrRoot := some v } ep σv = some σ := by
  cases σv with
  | some s => simpa using hres
  | none => simp [resolveCorrRoot, hcr] at hres

private theorem resolveCorrRoot_eq_of_corrRoot_eq {h1 h2 : PRNGBucketState T Sig K I}
    (hcr : h1.corrRoot = h2.corrRoot) (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h1 ep σv = resolveCorrRoot h2 ep σv := by
  cases σv <;> simp [resolveCorrRoot, hcr]

private theorem ltOpt_of_ge_healEpoch {tL : Option ℕ} {e : ℕ} (hge : healEpoch tL ≤ e) :
    ltOpt tL e = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp only [healEpoch] at hge
    simp only [ltOpt, decide_eq_true_eq]
    omega

private theorem RelStepRoot.eq_of_ne_t_df {tH t : ℕ} {σR_sp : Option Sig} {e : ℕ} {rL rR : Option Sig}
    (hne : e ≠ t) (h : RelStepRoot tH t σR_sp e rL rR) : rL = rR := by
  rcases h with ⟨_, σ, hL, hR⟩ | ⟨_, _, hL, hR⟩ | ⟨heq, _⟩ | ⟨_, σ, hL, hR⟩
  · rw [hL, hR]
  · rw [hL, hR]
  · exact False.elim (hne heq)
  · rw [hL, hR]

private theorem RelStepRoot.some_of_lt_tH_df {tH t : ℕ} {σR_sp : Option Sig} {e : ℕ} {rL rR : Option Sig}
    (htLo : tH ≤ t) (hlt : e < tH) (h : RelStepRoot tH t σR_sp e rL rR) :
    ∃ σ, rL = some σ ∧ rR = some σ := by
  rcases h with ⟨_, h1⟩ | ⟨hle, _⟩ | ⟨heq, _⟩ | ⟨hgt, _⟩
  · exact h1
  · omega
  · omega
  · omega

private theorem RelStepRoot.resolve_after_set_corrRoot_df
    {tH t e : ℕ} {σR_sp : Option Sig} {σC : Sig} {rL rR : Option Sig}
    {hL hR : PRNGBucketState T Sig K I}
    (hge_tH : tH ≤ e)
    (hσC : e ≤ t → σR_sp = some σC)
    (hr : RelStepRoot tH t σR_sp e rL rR) :
    ∃ σOut,
      resolveCorrRoot { hL with corrRoot := some (e, σC) } e rL = some σOut ∧
      resolveCorrRoot { hR with corrRoot := some (e, σC) } e rR = some σOut := by
  rcases hr with ⟨hlt, _⟩ | ⟨_, hlt_t, hrL, hrR⟩ | ⟨heq_t, ⟨σ, hrL, hpin⟩, hrR⟩ | ⟨_, σ, hrL, hrR⟩
  · omega
  · exact ⟨σC, by simp [resolveCorrRoot, hrL], by simp [resolveCorrRoot, hrR]⟩
  · subst e
    have hpin_eq : σR_sp = some σC := hσC le_rfl
    rw [hpin_eq] at hpin
    rcases hpin with h1 | h2
    · cases h1
      exact ⟨σC, by simp [hrL], by simp [resolveCorrRoot, hrR]⟩
    · cases h2
  · exact ⟨σ, by simp [hrL], by simp [hrR]⟩

/-- Winning-epoch invariant for `implEDFPaperBucket` under `bucketAuthCfg Δcka tL par`:
either `win = false ∧ winEp = none`, or `win = true` and `winEp = some tWin` comes from an
`inStage2Bucket` epoch (`lastLeakGuessAdmissible (3 + Δcka) tL tWin = true`). -/
private def WinEpInv (Δcka : ℕ) (tL : Option ℕ) (st : BSt Γ T Sig SS RS M E I K) : Prop :=
  (st.1.g.win = false ∧ st.2 = none) ∨
  (st.1.g.win = true ∧ ∃ tWin, st.2 = some tWin ∧
    lastLeakGuessAdmissible (3 + Δcka) tL tWin = true)

/-- Absorbing doom predicate on `(esL, winEpL)` for `authOutBucketPaperAt (2 + Δcka) tL (t + 1)`. -/
private def DoomedMainDF (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (st : BSt Γ T Sig SS RS M E I K) : Prop :=
  st.1.abort = true ∨
  (∃ e0, st.1.h.lc = some e0 ∧ e0 < t + 1) ∨
  (∀ P : Party, ∃ e, (P, e) ∈ st.1.g.corrs ∧ ltOpt tL e = true) ∨
  (WinEpInv Δcka tL st ∧
    ∃ l ∈ st.1.g.leaks, ltOpt tL l = true ∧
      ∀ tWin, lastLeakGuessAdmissible (3 + Δcka) tL tWin = true → l < tWin)

private theorem authOutBucketPaperAt_eq_false_of_doomedMainDF [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {st : BSt Γ T Sig SS RS M E I K}
    (hd : DoomedMainDF Δcka tL t st) :
    authOutBucketPaperAt (2 + Δcka) tL (t + 1) st = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨e0, hlc, hlt_e0⟩ | hcorrs | ⟨hwinInv, l_bad, hmem_l, hlt_l, hgt_l⟩
  · dsimp only at hab
    cases winEp <;> simp [authOutBucketPaperAt, authOutBucketPaper, authOutBucket, authOut, hab]
  · dsimp only at hlc
    have hdec : decide (t + 1 ≤ e0) = false := decide_eq_false (by omega)
    simp only [authOutBucketPaperAt, hlc, hdec, Bool.and_false]
  · cases winEp with
    | none => simp [authOutBucketPaperAt, authOutBucketPaper, authOutBucket]
    | some tWin =>
      obtain ⟨e, hmem, hlt⟩ := hcorrs (Party.receiverOf tWin)
      have hall_false :
          es.g.corrs.all (fun pe => !(pe.1 == Party.receiverOf tWin && ltOpt tL pe.2)) = false := by
        rw [List.all_eq_false]
        exact ⟨(Party.receiverOf tWin, e), hmem, by simp [hlt]⟩
      simp only [authOutBucketPaperAt, authOutBucketPaper, authOutBucket, authOut,
        SM.authLosingConditionsAvoided, hall_false, Bool.and_false, Bool.false_and]
  · rcases hwinInv with ⟨_, hnone⟩ | ⟨_, tWin, hsome, hadm3⟩
    · dsimp only at hnone; subst hnone
      simp [authOutBucketPaperAt, authOutBucketPaper, authOutBucket]
    · dsimp only at hsome hmem_l; subst hsome
      have hlt_win : l_bad < tWin := hgt_l tWin hadm3
      have hleaks_false :
          es.g.leaks.all (fun l => !(ltOpt tL l && decide (l < tWin))) = false := by
        rw [List.all_eq_false]
        exact ⟨l_bad, hmem_l, by simp [hlt_l, hlt_win]⟩
      simp only [authOutBucketPaperAt, authOutBucketPaper, authOutBucket, authOut,
        SM.authLosingConditionsAvoided, hleaks_false, Bool.and_false, Bool.false_and]

/-! ### 2. Coupling Relations: `VPBaseRelMain`, `ModeMainDF`, `SyncStepMainDF`, `SyncMainDF` -/

private structure VPBaseRelMain (e : ℕ) (P : Party)
    (vpL vpR : VP Γ T (Option Sig) SS RS) : Prop where
  id_L : vpL.id = P
  tcur_L : vpL.tcur = e
  id_R : vpR.id = P
  tcur_R : vpR.tcur = e
  γ_eq : vpL.γ = vpR.γ
  Tcur_eq : vpL.curCkaMsg = vpR.curCkaMsg
  vS_eq : vpL.vS = vpR.vS
  vR_eq : ∀ t', vpL.vR t' = vpR.vR t'

private structure ModePreMain (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop where
  pl_false : postLeak tL esR.g = false
  corrRootL : esL.h.corrRoot = none
  corrRootR : esR.h.corrRoot = none
  lcL_none : esL.h.lc = none
  vp_root : ∀ P, RelStepRoot (healEpoch tL) t
    (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
    (esR.g.epoch P) (esL.g.st P).root (esR.g.st P).root
  cache_rel : ∀ e, RelCacheStep (healEpoch tL) t
    (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
    e (esL.h.cache e) (esR.h.cache e)
  fTable_ne : ∀ t0, t0 ≠ t → esL.h.fTable t0 = esR.h.fTable t0
  table_t : spL.table = esR.h.fTable t
  spL_b : spL.b = true
  spR_b : spR.b = false
  sp_σ_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL.σ = spR.σ
  spR_prf_le : max (esR.g.epoch .A) (esR.g.epoch .B) ≤ t → spR.prf = false
  spR_prng : spR.prng = false
  spR_corr : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) →
    (max (esR.g.epoch .A) (esR.g.epoch .B) ≤ t ∨
      inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → spR.corr = false

private structure ModeAllResolvedMain (tL : Option ℕ)
    (esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    Prop where
  pl_true : postLeak tL esR.g = true
  vp_res : ∀ P, ∃ σ,
    resolveCorrRoot esL.h (esR.g.epoch P) (esL.g.st P).root = some σ ∧
    resolveCorrRoot esR.h (esR.g.epoch P) (esR.g.st P).root = some σ
  cache_res : ∀ e, min (esR.g.epoch .A) (esR.g.epoch .B) < e →
    (esL.h.cache e = none ∧ esR.h.cache e = none) ∨
    ∃ Tc rL rR k σ,
      esL.h.cache e = some (Tc, rL, k) ∧
      esR.h.cache e = some (Tc, rR, k) ∧
      resolveCorrRoot esL.h e rL = some σ ∧
      resolveCorrRoot esR.h e rR = some σ

private def ModePostCorrMain (tL : Option ℕ) (t : ℕ)
    (esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    Prop :=
  postLeak tL esR.g = true ∧
  ∃ (Q_corr : Party) (eC : ℕ) (σC : Sig),
    healEpoch tL ≤ eC ∧
    (Q_corr, eC) ∈ esR.g.corrs ∧
    esL.h.corrRoot = some (eC, σC) ∧
    esR.h.corrRoot = some (eC, σC) ∧
    esR.g.epoch Q_corr = eC ∧
    (∃ σ,
      resolveCorrRoot esL.h (esR.g.epoch Q_corr) (esL.g.st Q_corr).root = some σ ∧
      resolveCorrRoot esR.h (esR.g.epoch Q_corr) (esR.g.st Q_corr).root = some σ) ∧
    esR.g.epoch Q_corr.other + 1 = eC ∧
    Q_corr.sendsIn eC = true ∧
    (eC - 1 ≠ t → (esL.g.st Q_corr.other).root = (esR.g.st Q_corr.other).root) ∧
    (∀ e, eC ≤ e →
      (esL.h.cache e = none ∧ esR.h.cache e = none) ∨
      ∃ Tc rL rR k σ,
        esL.h.cache e = some (Tc, rL, k) ∧
        esR.h.cache e = some (Tc, rR, k) ∧
        resolveCorrRoot esL.h e rL = some σ ∧
        resolveCorrRoot esR.h e rR = some σ)

private inductive ModeMainDF (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop
  | pre (hm : ModePreMain Δcka tL par t esL spL esR spR)
  | allResolved (hm : ModeAllResolvedMain tL esL esR)
  | postCorr (hm : ModePostCorrMain tL t esL esR)

private structure SyncStepMainDF (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop where
  abortL : esL.abort = false
  abortR : esR.abort = false
  g_eq : AuthL11.eraseSt esL.g = AuthL11.eraseSt esR.g
  lc_eq : esL.h.lc = esR.h.lc
  vp_base : ∀ P, VPBaseRelMain (esR.g.epoch P) P (esL.g.st P) (esR.g.st P)
  cache_gt_max : ∀ e, max (esR.g.epoch .A) (esR.g.epoch .B) < e →
    esL.h.cache e = none ∧ esR.h.cache e = none
  epoch_le : ∀ P, esR.g.epoch P ≤ esR.g.epoch P.other + 1
  epoch_sends : ∀ P, esR.g.epoch P.other < esR.g.epoch P → P.sendsIn (esR.g.epoch P) = true
  trans_epoch : ∀ r ∈ esR.g.trans,
    r.pos.epoch ≤ esR.g.epoch r.pos.sender ∧ r.ct.1.1 = r.pos.epoch
  mode : ModeMainDF Δcka tL par t esL spL esR spR

private structure SyncMainDF (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (stL : BSt Γ T Sig SS RS M E I K) (spL : PRFPRNG.GameState Sig I K)
    (stR : BSt Γ T Sig SS RS M E I K) (spR : PRFPRNG.GameState Sig I K) : Prop where
  winEp_eq : stL.2 = stR.2
  winEp_inv : WinEpInv Δcka tL stL
  raw : SyncStepMainDF Δcka tL par t stL.1 spL stR.1 spR

/-! ### 3. `PRFPRNG`, `lookupPRNGBucketF`, and `rootPRNGBucketHybrid` Coupling (with `lc` Preservation) -/

private theorem leComp_lookupBucketF_main
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t t0 : ℕ) (ik : I)
    (hL hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hne : t0 ≠ t)
    (hft : ∀ t', t' ≠ t → hL.fTable t' = hR.fTable t') :
    AuthL11.LeComp
      (fun (r1 : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = r2.1.1 ∧
        r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
        r1.1.2.corrRoot = hL.corrRoot ∧ r2.1.2.corrRoot = hR.corrRoot ∧
        r1.1.2.lc = hL.lc ∧ r2.1.2.lc = hR.lc ∧
        r1.2 = spL ∧ r2.2 = spR ∧
        (∀ t', t' ≠ t → r1.1.2.fTable t' = r2.1.2.fTable t') ∧
        r2.1.2.fTable t = hR.fTable t)
      ((simulateQ (AuthL11.pImpl prng)
        ((lookupPRNGBucketF (T := T) (Sig := Sig) t0 ik).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((lookupPRNGBucketF (T := T) (Sig := Sig) t0 ik).run hR)).run spR) := by
  unfold lookupPRNGBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft t0 hne]
  cases hlk : (hR.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩
    · by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · simp [hne.symm]

private theorem leComp_challPrf_lookupF_main
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t : ℕ) (ik : I)
    (hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hbL : spL.b = true)
    (htab : spL.table = hR.fTable t) :
    AuthL11.LeComp
      (fun (r1 : Option (Sig × K) × PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1 = none ∨
        (r1.1 = some ((prng.up spL.σ ik).1, r2.1.1) ∧
          r2.1.2.cache = hR.cache ∧ r2.1.2.corrRoot = hR.corrRoot ∧
          r2.1.2.lc = hR.lc ∧ r2.2 = spR ∧
          r1.2.σ = spL.σ ∧ r1.2.b = true ∧
          (∀ t', t' ≠ t → r2.1.2.fTable t' = hR.fTable t') ∧
          r1.2.table = r2.1.2.fTable t))
      ((PRFPRNG.challPrfImpl prng ik).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((lookupPRNGBucketF (T := T) (Sig := Sig) t ik).run hR)).run spR) := by
  rw [AuthL11.run_challPrfImpl]
  by_cases hbadL : (spL.corr || spL.prng) = true
  · simp only [hbadL, ↓reduceIte]
    exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · unfold lookupPRNGBucketF
    simp only [hbadL, hbL, Bool.false_eq_true, ↓reduceIte, htab,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases hlk : (hR.fTable t).lookup ik with
    | some k =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩)
    | none =>
      simp only [StateT.run_bind, simulateQ_bind,
        AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
      refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
      simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩)
      · simp [ht']
      · simp

private theorem leComp_rootSend_main_pre
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    {Δbucket : ℕ} {par : Bool}
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t eMax : ℕ) (ik0 : I)
    (rL0 rR0 : Option Sig)
    (hL hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (htH : healEpoch tL ≤ t)
    (hr0 : RelStepRoot (healEpoch tL) t (spPinStep Δbucket tL par t eMax spR.σ) eMax rL0 rR0)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_le : eMax ≤ t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax →
      (eMax ≤ t ∨ inStage2BucketGen Δbucket tL par (t + 1) = true) → spR.corr = false) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ rL' rR' kVal,
          r1.1.1 = some (rL', kVal) ∧ r2.1.1 = some (rR', kVal) ∧
          RelStepRoot (healEpoch tL) t (spPinStep Δbucket tL par t (eMax + 1) r2.2.σ) (eMax + 1) rL' rR' ∧
          (t ≤ eMax →
            spPinStep Δbucket tL par t (eMax + 1) r2.2.σ = spPinStep Δbucket tL par t eMax spR.σ ∨
            spPinStep Δbucket tL par t (eMax + 1) r2.2.σ = none) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          r1.1.2.lc = hL.lc ∧ r2.1.2.lc = hR.lc ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
          (eMax + 1 ≤ t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 →
            (eMax + 1 ≤ t ∨ inStage2BucketGen Δbucket tL par (t + 1) = true) → r2.2.corr = false))
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t (eMax + 1) false ik0 rL0).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par (t + 1) (eMax + 1) false ik0 rR0).run hR)).run spR) := by
  rcases spL with ⟨σL, bL, corrL, prngL, prfL, tabL⟩
  rcases spR with ⟨σR, bR, corrR, prngR, prfR, tabR⟩
  dsimp only at hr0 htab hbL hbR hσ_lt hprfR_le hprngR hcorrR
  subst hbL hbR hprngR htab
  have hresL0 : resolveCorrRoot hL eMax rL0 = rL0 := resolveCorrRoot_of_corrRoot_none hcrL eMax rL0
  have hresR0 : resolveCorrRoot hR eMax rR0 = rR0 := resolveCorrRoot_of_corrRoot_none hcrR eMax rR0
  have hisSomeL : (false || hL.corrRoot.isSome) = false := by simp [hcrL]
  have hisSomeR : (false || hR.corrRoot.isSome) = false := by simp [hcrR]
  by_cases ht_lt : t < eMax + 1
  · by_cases heq_t1 : eMax + 1 = t + 1
    · have heMax_eq : eMax = t := by omega
      subst heMax_eq
      have hcorrR0 : corrR = false := hcorrR htH (Or.inl le_rfl)
      have hprfR0 : prfR = false := hprfR_le le_rfl
      subst hcorrR0 hprfR0
      have hpin0 : spPinStep Δbucket tL par eMax eMax σR = some σR := by simp [spPinStep]
      have hrL0_eq : rL0 = some σR := by
        rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, ⟨σ, hrL, hpin_eq⟩, _⟩ | ⟨h, _⟩
        · omega
        · omega
        · rw [hpin0] at hpin_eq
          rcases hpin_eq with h1 | h2
          · cases h1; exact hrL
          · cases h2
        · omega
      have hnlt_t1 : ¬ (eMax + 1 < eMax + 1) := by omega
      have his_tH_false : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = false := by
        simp [show eMax + 1 ≠ healEpoch tL by omega]
      unfold rootPRNGBucketHybrid
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
        ht_lt, hnlt_t1, hisSomeR, Bool.false_eq_true, ↓reduceIte,
        his_tH_false, hrL0_eq]
      by_cases hin : inStage2BucketGen Δbucket tL par (eMax + 1) = true
      · simp only [hin, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_challPrfQuery, AuthL11.run_challPrfImpl,
          Bool.or_self, Bool.false_eq_true, pure_bind]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σR ik0).1, some (prng.up σR ik0).1,
          (prng.up σR ik0).2, rfl, rfl,
          Or.inr (Or.inr (Or.inr ⟨by omega, (prng.up σR ik0).1, rfl, rfl⟩)),
          (fun _ => Or.inl (by simp [spPinStep, hin])),
          rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
          fun h => by omega, fun h => by omega, rfl, fun _ _ => rfl⟩)
      · have hin_f : inStage2BucketGen Δbucket tL par (eMax + 1) = false :=
          Bool.eq_false_iff.mpr hin
        simp only [hin_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, pure_bind]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σR ik0).1, some (prng.up σR ik0).1,
          (prng.up σR ik0).2, rfl, rfl,
          Or.inr (Or.inr (Or.inr ⟨by omega, (prng.up σR ik0).1, rfl, rfl⟩)),
          (fun _ => Or.inr (by simp [spPinStep, hin_f])),
          rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
          fun h => by omega, fun _ => rfl, rfl,
          (fun _ h => by
            rcases h with h1 | h2
            · omega
            · cases h2)⟩)
    · have ht1_lt : t + 1 < eMax + 1 := by omega
      obtain ⟨σ0, hrL0_eq, hrR0_eq⟩ : ∃ σ0, rL0 = some σ0 ∧ rR0 = some σ0 := by
        rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · omega
        · omega
        · omega
        · exact h
      unfold rootPRNGBucketHybrid
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
        ht_lt, ht1_lt, ↓reduceIte, hrL0_eq, hrR0_eq]
      exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, some (prng.up σ0 ik0).1,
        (prng.up σ0 ik0).2, rfl, rfl,
        Or.inr (Or.inr (Or.inr ⟨ht_lt, (prng.up σ0 ik0).1, rfl, rfl⟩)),
        (fun _ => Or.inl (by
          simp [spPinStep, show ¬ eMax < t by omega, show ¬ eMax ≤ t by omega])),
        rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
        fun h => by omega, fun h => by omega, rfl,
        (fun _ h => hcorrR (by omega) (Or.inr (h.resolve_left (by omega))))⟩)
  · have heMax_lt_t : eMax < t := by omega
    have hprfR := hprfR_le (Nat.le_of_lt heMax_lt_t)
    have hσ_eq := hσ_lt heMax_lt_t
    subst hprfR hσ_eq
    have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
    have hne_t1 : ¬ (eMax + 1 = t + 1) := by omega
    unfold rootPRNGBucketHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
      ht_lt, hnlt_t1, hne_t1, hisSomeL, hisSomeR, Bool.false_eq_true, ↓reduceIte]
    by_cases heq_t : eMax + 1 = t
    · have hge_tH : (!(eMax + 1 < healEpoch tL)) = true := by simp; omega
      simp only [heq_t, ↓reduceIte]
      have hge_t : (!(t < healEpoch tL)) = true := by rw [← heq_t]; exact hge_tH
      have his_eq : (tL.isSome && decide (t = healEpoch tL)) =
          (tL.isSome && decide (eMax + 1 = healEpoch tL)) := by rw [heq_t]
      by_cases his_tH : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = true
      · have his_t : (tL.isSome && decide (t = healEpoch tL)) = true := his_eq.trans his_tH
        simp only [hge_t, his_t, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_challPrngQuery,
          AuthL11.simulateQ_pImpl_processQuery,
          AuthL11.run_challPrngImpl_none, AuthL11.run_processImpl_none,
          Bool.false_eq_true, pure_bind]
        refine AuthL11.LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        cases prfL
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc,
            AuthL11.simulateQ_pImpl_run_lift_sampleT]
          refine AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL Ir).1, none, kRand, rfl, rfl,
            Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σL Ir).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
            fun h => by omega, rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
            fun h => by omega, fun _ => rfl, rfl, fun _ _ => rfl⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have his_t_false : (tL.isSome && decide (t = healEpoch tL)) = false :=
          his_eq.trans (Bool.eq_false_iff.mpr his_tH)
        have hcorrR0 : corrR = false := by
          apply hcorrR _ (Or.inl (Nat.le_of_lt heMax_lt_t))
          cases tL with
          | none => simp [healEpoch]
          | some l =>
            simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at his_tH
            omega
        simp only [hge_t, his_t_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hin : inStage2BucketGen Δbucket tL par t = true
        · simp only [hin, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
            AuthL11.simulateQ_pImpl_challPrfQuery,
            AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
            Bool.false_eq_true, pure_bind]
          refine (leComp_challPrf_lookupF_main prng t ik0 hR
            { σ := σL, b := true, corr := corrL, prng := prngL, prf := prfL, table := hR.fTable t }
            { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false, prf := false,
              table := tabR }
            rfl rfl).bind ?_
          rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
          rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hlcR1, hspR1, hσL1, hbL1, hft1, htab1⟩
          · dsimp only at hnone; subst hnone
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · dsimp only at hresL hcR1 hcrR1 hlcR1 hspR1 hσL1 hbL1 hft1 htab1
            subst hresL hspR1
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, none, kOut, rfl, rfl,
              Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σL ik0).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
              fun h => by omega, rfl, hcR1, hcrL, hcrR1.trans hcrR, rfl, hlcR1,
              fun t0 ht0 => (hft t0 ht0).trans (hft1 t0 ht0).symm, htab1, hbL1, rfl,
              fun h => by omega, fun _ => rfl, rfl, fun _ _ => hcorrR0⟩)
        · simp only [hin, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
            AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some, pure_bind]
          cases prfL
          · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, none, (prng.up σL ik0).2,
              rfl, rfl,
              Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σL ik0).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
              fun h => by omega, rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
              fun h => by omega, fun _ => rfl, rfl, fun _ _ => hcorrR0⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · have heMax1_lt_t : eMax + 1 < t := by omega
      simp only [heq_t, ↓reduceIte]
      by_cases hge_tH : (!(eMax + 1 < healEpoch tL)) = true
      · simp only [hge_tH, ↓reduceIte]
        have hge_tH_prop : healEpoch tL ≤ eMax + 1 := by
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH; omega
        by_cases his_tH : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = true
        · simp only [his_tH, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
            AuthL11.simulateQ_pImpl_processQuery,
            AuthL11.run_processImpl_none, Bool.false_eq_true, pure_bind]
          cases prfL
          · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
            refine AuthL11.LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
            simp only [pure_bind, StateT.run_bind, simulateQ_bind,
              AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
            refine AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨none, none, kRand, rfl, rfl,
              Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
              fun h => by omega, rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
              fun _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · have hcorrR0 : corrR = false := by
            apply hcorrR _ (Or.inl (Nat.le_of_lt heMax_lt_t))
            cases tL with
            | none => simp [healEpoch]
            | some l =>
              simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at his_tH
              omega
          simp only [his_tH, Bool.false_eq_true, ↓reduceIte]
          by_cases hin : inStage2BucketGen Δbucket tL par (eMax + 1) = true
          · simp only [hin, ↓reduceIte,
              StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
              AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
              Bool.false_eq_true, pure_bind]
            cases prfL
            · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
                StateT.run_bind, simulateQ_bind]
              refine (leComp_lookupBucketF_main prng t (eMax + 1) ik0 hL hR
                { σ := (prng.up σL ik0).1, b := true, corr := corrL, prng := prngL,
                  prf := false, table := hR.fTable t }
                { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false,
                  prf := false, table := tabR }
                heq_t hft).bind ?_
              rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩
                ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hlcL1, hlcR1, hspL1, hspR1, hft1, htab1⟩
              dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hlcL1 hlcR1 hspL1 hspR1 hft1 htab1
              subst hk_eq hspL1 hspR1
              simp only [StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
                Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
                fun h => by omega, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR,
                hlcL1, hlcR1, hft1, htab1.symm, rfl, rfl,
                fun _ => rfl, fun _ => rfl, rfl, fun _ _ => hcorrR0⟩)
            · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [hin, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
              AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
              Bool.false_eq_true, pure_bind]
            cases prfL
            · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
                StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨none, none, (prng.up σL ik0).2, rfl, rfl,
                Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
                fun h => by omega, rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
                fun _ => rfl, fun _ => rfl, rfl, fun _ _ => hcorrR0⟩)
            · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have hlt_tH : eMax + 1 < healEpoch tL := by
          by_contra hle; exact hge_tH (by simp [hle])
        simp only [hge_tH, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          Bool.false_eq_true, pure_bind]
        cases prfL
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
            AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, some (prng.up σL ik0).1,
            (prng.up σL ik0).2, rfl, rfl,
            Or.inl ⟨hlt_tH, (prng.up σL ik0).1, rfl, rfl⟩,
            fun h => by omega, rfl, rfl, hcrL, hcrR, rfl, rfl, hft, rfl, rfl, rfl,
            fun _ => rfl, fun _ => rfl, rfl, fun h _ => by omega⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private theorem run_rootSend_main_post
    [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (m t0 : ℕ) (ik0 : I)
    (r0 : Option Sig) (h : PRNGBucketState T Sig K I) (σ : Sig)
    (hres : resolveCorrRoot h (t0 - 1) r0 = some σ) :
    (rootPRNGBucketHybrid prng Δbucket tL par m t0 true ik0 r0).run h =
      pure (some (some (prng.up σ ik0).1, (prng.up σ ik0).2), h) := by
  unfold rootPRNGBucketHybrid
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hres, Bool.true_or, ↓reduceIte]
  split_ifs <;> rfl

private theorem leComp_rootSend_main_postLeak_from_pre
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    {Δbucket : ℕ} {par : Bool}
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t eMax : ℕ) (ik0 : I)
    (rL0 rR0 : Option Sig) (rOtherL rOtherR : Option Sig)
    (hL hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (htLo : healEpoch tL ≤ t)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t (spPinStep Δbucket tL par t eMax spR.σ) eMax rL0 rR0)
    (hrOther : RelStepRoot (healEpoch tL) t (spPinStep Δbucket tL par t eMax spR.σ) eMax rOtherL rOtherR)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_le : eMax ≤ t → spR.prf = false) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ σNew kVal σOther,
          r1.1.1 = some (some σNew, kVal) ∧ r2.1.1 = some (some σNew, kVal) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.lc = hL.lc ∧ r2.1.2.lc = hR.lc ∧
          resolveCorrRoot r1.1.2 eMax rOtherL = some σOther ∧
          resolveCorrRoot r2.1.2 eMax rOtherR = some σOther)
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t (eMax + 1) true ik0 rL0).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par (t + 1) (eMax + 1) true ik0 rR0).run hR)).run spR) := by
  have hresL0 : resolveCorrRoot hL eMax rL0 = rL0 := resolveCorrRoot_of_corrRoot_none hcrL eMax rL0
  have hresR0 : resolveCorrRoot hR eMax rR0 = rR0 := resolveCorrRoot_of_corrRoot_none hcrR eMax rR0
  rcases hr0 with ⟨hlt_tH, σ0, hrL0, hrR0⟩ | ⟨hge_tH, hlt_t, hrL0, hrR0⟩ |
      ⟨heq_t, ⟨σ0, hrL0, hpin0⟩, hrR0⟩ | ⟨hgt_t, σ0, hrL0, hrR0⟩
  · obtain ⟨σO, hrOL, hrOR⟩ : ∃ σO, rOtherL = some σO ∧ rOtherR = some σO := by
      rcases hrOther with ⟨_, h1⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h1
      · omega
      · omega
      · omega
    have hrunL := run_rootSend_main_post (T := T) prng Δbucket tL par t (eMax + 1) ik0 rL0 hL σ0
      (by simp [hrL0])
    have hrunR := run_rootSend_main_post (T := T) prng Δbucket tL par (t + 1) (eMax + 1) ik0 rR0 hR σ0
      (by simp [hrR0])
    rw [hrunL, hrunR]
    simp only [simulateQ_pure, StateT.run_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨(prng.up σ0 ik0).1, (prng.up σ0 ik0).2, σO,
      rfl, rfl, rfl, rfl, rfl, rfl, by simp [hrOL], by simp [hrOR]⟩)
  · have hrOL : rOtherL = none ∧ rOtherR = none := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, _, h1, h2⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · omega
      · exact ⟨h1, h2⟩
      · omega
      · omega
    subst hrL0 hrR0
    have hprfR := hprfR_le (Nat.le_of_lt hlt_t)
    have hσ_eq := hσ_lt hlt_t
    have hnlt_t : ¬ (t < eMax + 1) := by omega
    have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
    unfold rootPRNGBucketHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
      hresL0, hresR0, hnlt_t, hnlt_t1, Bool.true_or, ↓reduceIte,
      simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
      AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, hprfR, hσ_eq,
      Bool.false_eq_true]
    cases hprfL : spL.prf
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
        StateT.run_modify, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨(prng.up spR.σ ik0).1, (prng.up spR.σ ik0).2, spR.σ,
        rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [resolveCorrRoot, hrOL.1], by simp [resolveCorrRoot, hrOL.2]⟩)
    · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · subst eMax
    have hpin_eq : spPinStep Δbucket tL par t t spR.σ = some spR.σ := by simp [spPinStep]
    rw [hpin_eq] at hpin0
    have hσ0_eq : σ0 = spR.σ := by
      rcases hpin0 with h1 | h2
      · cases h1; rfl
      · cases h2
    subst hσ0_eq
    have hrOL : rOtherL = some spR.σ ∧ rOtherR = none := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, ⟨σ', h1, hpin'⟩, h2⟩ | ⟨h, _⟩
      · omega
      · omega
      · rw [hpin_eq] at hpin'
        rcases hpin' with h1' | h2'
        · cases h1'; exact ⟨h1, h2⟩
        · cases h2'
      · omega
    subst hrL0 hrR0
    have hprfR := hprfR_le le_rfl
    have ht_lt : t < t + 1 := by omega
    have hnlt_t1 : ¬ (t + 1 < t + 1) := by omega
    unfold rootPRNGBucketHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
      hresL0, hresR0, ht_lt, hnlt_t1, Bool.true_or, ↓reduceIte,
      simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
      AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, hprfR,
      Bool.false_eq_true, pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨(prng.up spR.σ ik0).1, (prng.up spR.σ ik0).2, spR.σ,
      rfl, rfl, rfl, rfl, rfl, rfl,
      by simp [hrOL.1], by simp [resolveCorrRoot, hrOL.2]⟩)
  · obtain ⟨σO, hrOL, hrOR⟩ : ∃ σO, rOtherL = some σO ∧ rOtherR = some σO := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h1⟩
      · omega
      · omega
      · omega
      · exact h1
    have hrunL := run_rootSend_main_post (T := T) prng Δbucket tL par t (eMax + 1) ik0 rL0 hL σ0
      (by simp [hrL0])
    have hrunR := run_rootSend_main_post (T := T) prng Δbucket tL par (t + 1) (eMax + 1) ik0 rR0 hR σ0
      (by simp [hrR0])
    rw [hrunL, hrunR]
    simp only [simulateQ_pure, StateT.run_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨(prng.up σ0 ik0).1, (prng.up σ0 ik0).2, σO,
      rfl, rfl, rfl, rfl, rfl, rfl, by simp [hrOL], by simp [hrOR]⟩)

/-! ### 4. Hook & Oracle Step Coupling (`vRecv`, `deliverE`, `injectE`, `deliverForgeE`, `transmitEBucket`, `corrEPaperBucket`) -/

@[simp]
private theorem run_commitE_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]

private theorem syncStepMainDF_set_win
    {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    SyncStepMainDF Δcka tL par t
      { esL with g := { esL.g with win := true } } spL
      { esR with g := { esR.g with win := true } } spR := by
  refine ⟨hsync.abortL, hsync.abortR, ?_, hsync.lc_eq, hsync.vp_base, hsync.cache_gt_max,
    hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, ?_⟩
  · have h := hsync.g_eq
    dsimp only [AuthL11.eraseSt] at h ⊢
    rw [congrArg SM.GameState.epoch h, congrArg SM.GameState.idx h,
      congrArg SM.GameState.trans h, congrArg SM.GameState.chall h,
      congrArg SM.GameState.leaks h, congrArg SM.GameState.corrs h,
      congrArg SM.GameState.tL h, congrArg SM.GameState.comp h,
      congrArg SM.GameState.maxAcc h, congrArg SM.GameState.b h]
  · rcases hsync.mode with hm | hm | hm
    · exact .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, hm.lcL_none, hm.vp_root, hm.cache_rel,
        hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spR_prf_le,
        hm.spR_prng, hm.spR_corr⟩
    · exact .allResolved ⟨hm.pl_true, hm.vp_res, hm.cache_res⟩
    · exact .postCorr hm

private theorem syncStepMainDF_of_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    {P : Party} {c : Header T × E}
    {vpL' vpR' : VP Γ T (Option Sig) SS RS} {pos : SM.Pos}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esR.g.epoch P + 1)
    (hvp_base' : VPBaseRelMain (max (esR.g.epoch P) c.1.1) P vpL' vpR')
    (hroot_le : c.1.1 ≤ esR.g.epoch P →
      vpL'.root = (esL.g.st P).root ∧ vpR'.root = (esR.g.st P).root)
    (hnew_cache : c.1.1 = esR.g.epoch P + 1 →
      ∃ Tc rL rR k,
        esL.h.cache c.1.1 = some (Tc, rL, k) ∧
        esR.h.cache c.1.1 = some (Tc, rR, k) ∧
        vpL'.root = resolveCorrRoot esL.h c.1.1 rL ∧
        vpR'.root = resolveCorrRoot esR.h c.1.1 rR) :
    SyncStepMainDF Δcka tL par t
      { esL with g := esL.g.accept P vpL' pos } spL
      { esR with g := esR.g.accept P vpR' pos } spR := by
  have hnew_le_other : c.1.1 = esR.g.epoch P + 1 → c.1.1 ≤ esR.g.epoch P.other := by
    intro hnew
    obtain ⟨Tc, rL, rR, k, _, hcR, _, _⟩ := hnew_cache hnew
    by_contra hgt_not
    have hgt_max : max (esR.g.epoch .A) (esR.g.epoch .B) < c.1.1 := by
      cases P <;> simp [Party.other] at hnew hgt_not ⊢ <;> omega
    have hnone := (hsync.cache_gt_max c.1.1 hgt_max).2
    rw [hcR] at hnone
    cases hnone
  have hacc_ep : (esR.g.accept P vpR' pos).epoch =
      Function.update esR.g.epoch P (max (esR.g.epoch P) c.1.1) := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    rw [hpos_ep]
  have hmax_eq : max ((esR.g.accept P vpR' pos).epoch .A) ((esR.g.accept P vpR' pos).epoch .B) =
      max (esR.g.epoch .A) (esR.g.epoch .B) := by
    rw [hacc_ep]
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      cases P <;> simp [Party.other] at hc_le ⊢ <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self]
  have hmin_le : min (esR.g.epoch .A) (esR.g.epoch .B) ≤
      min ((esR.g.accept P vpR' pos).epoch .A) ((esR.g.accept P vpR' pos).epoch .B) := by
    rw [hacc_ep]
    cases P <;> simp
  refine ⟨hsync.abortL, hsync.abortR,
    AuthL11.eraseSt_accept hsync.g_eq P vpL' vpR' pos, hsync.lc_eq,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q
    dsimp only
    rw [hacc_ep]
    dsimp only [SM.GameState.accept]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact hvp_base'
    · simp only [Function.update_of_ne hQ]; exact hsync.vp_base Q
  · intro e hgt; rw [hmax_eq] at hgt; exact hsync.cache_gt_max e hgt
  · intro Q
    dsimp only
    rw [hacc_ep]
    have hle_P := hsync.epoch_le P
    have hle_other := hsync.epoch_le P.other
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      cases Q <;> cases P <;> simp [Party.other] at hc_le htle hle_P hle_other ⊢ <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self]
      exact hsync.epoch_le Q
  · intro Q hlt_Q
    dsimp only at hlt_Q ⊢
    rw [hacc_ep] at hlt_Q ⊢
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      have heq_other : esR.g.epoch P.other = esR.g.epoch P + 1 := by
        have := hsync.epoch_le P.other
        rw [Party.other_other] at this
        omega
      cases Q <;> cases P <;> simp [Party.other, hnew] at heq_other hlt_Q <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hlt_Q ⊢
      exact hsync.epoch_sends Q hlt_Q
  · intro r' hr'
    dsimp only at hr' ⊢
    rw [hacc_ep]
    simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'
    obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
    refine ⟨?_, h2⟩
    by_cases hQ : r'.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · rcases hsync.mode with hm | hm | hm
    · refine .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, hm.lcL_none, ?_,
        by dsimp only; rw [hmax_eq]; exact hm.cache_rel,
        hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b,
        by dsimp only; rw [hmax_eq]; exact hm.sp_σ_lt,
        by dsimp only; rw [hmax_eq]; exact hm.spR_prf_le,
        hm.spR_prng,
        by dsimp only; rw [hmax_eq]; exact hm.spR_corr⟩
      intro Q
      dsimp only
      rw [hmax_eq]
      dsimp only [SM.GameState.accept, SM.GameState.delete]
      rw [hpos_ep]
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self]
        by_cases hnew : c.1.1 = esR.g.epoch P + 1
        · obtain ⟨Tc, rL, rR, k, hcL, hcR, hrL', hrR'⟩ := hnew_cache hnew
          have hmax_c : max (esR.g.epoch P) c.1.1 = c.1.1 := by omega
          rw [hmax_c, hrL', hrR',
            resolveCorrRoot_of_corrRoot_none hm.corrRootL,
            resolveCorrRoot_of_corrRoot_none hm.corrRootR]
          rcases hm.cache_rel c.1.1 with ⟨hnoneL, _⟩ | ⟨Tc', rL', rR', k', hcL', hcR', hrel⟩
          · rw [hcL] at hnoneL; cases hnoneL
          · rw [hcL] at hcL'; rw [hcR] at hcR'
            cases hcL'; cases hcR'
            exact hrel
        · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
          obtain ⟨hrL', hrR'⟩ := hroot_le htle_e
          rw [Nat.max_eq_left htle_e, hrL', hrR']
          exact hm.vp_root P
      · simp only [Function.update_of_ne hQ]
        exact hm.vp_root Q
    · refine .allResolved ⟨hm.pl_true, ?_, fun e he =>
        hm.cache_res e (lt_of_le_of_lt hmin_le he)⟩
      intro Q
      dsimp only [SM.GameState.accept, SM.GameState.delete]
      rw [hpos_ep]
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self]
        by_cases hnew : c.1.1 = esR.g.epoch P + 1
        · obtain ⟨Tc, rL, rR, k, hcL, hcR, hrL', hrR'⟩ := hnew_cache hnew
          have hmin_lt : min (esR.g.epoch .A) (esR.g.epoch .B) < c.1.1 := by
            cases P <;> simp at hnew ⊢ <;> omega
          rcases hm.cache_res c.1.1 hmin_lt with ⟨hnoneL, _⟩ |
            ⟨Tc', rL', rR', k', σ, hcL', hcR', hresL, hresR⟩
          · rw [hcL] at hnoneL; cases hnoneL
          · rw [hcL] at hcL'; rw [hcR] at hcR'
            cases hcL'; cases hcR'
            have hmax_c : max (esR.g.epoch P) c.1.1 = c.1.1 := by omega
            rw [hmax_c, hrL', hrR', hresL, hresR]
            exact ⟨σ, rfl, rfl⟩
        · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
          obtain ⟨hrL', hrR'⟩ := hroot_le htle_e
          rw [Nat.max_eq_left htle_e, hrL', hrR']
          exact hm.vp_res P
      · simp only [Function.update_of_ne hQ]
        exact hm.vp_res Q
    · rcases hm with ⟨hpl, Q_corr, eC, σC, htH_eC, hmem_corr, hcrL, hcrR,
        hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩
      by_cases hnew : c.1.1 = esR.g.epoch P + 1
      · have hP_ne_Qc : P ≠ Q_corr := by
          intro heq; subst P
          have hc_le := hnew_le_other hnew
          omega
        have hP_eq_Qo : P = Q_corr.other := by
          cases P <;> cases Q_corr <;> first | exact False.elim (hP_ne_Qc rfl) | rfl
        subst P
        have hc_eC : c.1.1 = eC := by omega
        have hacc_both : ∀ Q, (esR.g.accept Q_corr.other vpR' pos).epoch Q = eC := by
          intro Q
          rw [hacc_ep]
          cases Q <;> cases Q_corr <;> simp [Party.other, hc_eC] at hep_Qc hep_Qo ⊢ <;> omega
        refine .allResolved ⟨hpl, ?_, ?_⟩
        · intro Q
          dsimp only
          rw [hacc_both Q]
          dsimp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQ : Q = Q_corr.other
          · subst Q
            simp only [Function.update_self]
            obtain ⟨Tc, rL, rR, k, hcL, hcR, hrL', hrR'⟩ := hnew_cache hnew
            rw [hc_eC] at hcL hcR hrL' hrR'
            rcases hcache_ge eC le_rfl with ⟨hnoneL, _⟩ |
              ⟨Tc', rL', rR', k', σ, hcL', hcR', hresL, hresR⟩
            · rw [hcL] at hnoneL; cases hnoneL
            · rw [hcL] at hcL'; rw [hcR] at hcR'
              cases hcL'; cases hcR'
              rw [hrL', hrR', hresL, hresR]
              exact ⟨σ, rfl, rfl⟩
          · have hQ_eq : Q = Q_corr := by
              cases Q <;> cases Q_corr <;> first | exact False.elim (hQ rfl) | rfl
            subst Q
            simp only [Function.update_of_ne hQ]
            simpa [hep_Qc] using hres_Qc
        · intro e he
          dsimp only at he
          rw [hacc_both .A, hacc_both .B, Nat.min_self] at he
          exact hcache_ge e (Nat.le_of_lt he)
      · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hacc_same : (esR.g.accept P vpR' pos).epoch = esR.g.epoch := by
          rw [hacc_ep, Nat.max_eq_left htle_e, Function.update_eq_self]
        obtain ⟨hrL', hrR'⟩ := hroot_le htle_e
        have hroot_same : ∀ Q,
            ((esL.g.accept P vpL' pos).st Q).root = (esL.g.st Q).root ∧
            ((esR.g.accept P vpR' pos).st Q).root = (esR.g.st Q).root := by
          intro Q
          dsimp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQ : Q = P
          · subst Q; simp [hrL', hrR']
          · simp [Function.update_of_ne hQ]
        refine .postCorr ⟨hpl, Q_corr, eC, σC, htH_eC,
          by dsimp only [SM.GameState.accept, SM.GameState.delete]; exact hmem_corr,
          hcrL, hcrR,
          by dsimp only; rw [hacc_same]; exact hep_Qc, ?_,
          by dsimp only; rw [hacc_same]; exact hep_Qo,
          hsends_Qc, ?_, hcache_ge⟩
        · dsimp only
          rw [hacc_same, (hroot_same Q_corr).1, (hroot_same Q_corr).2]
          exact hres_Qc
        · intro hne
          dsimp only
          rw [(hroot_same Q_corr.other).1, (hroot_same Q_corr.other).2]
          exact hroot_Qo hne

private theorem cache_at_succ_main_df
    {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) (P : Party) :
    let t0 := esR.g.epoch P + 1
    (esL.h.cache t0 = none ∧ esR.h.cache t0 = none) ∨
    ∃ Tc rL rR k,
      esL.h.cache t0 = some (Tc, rL, k) ∧
      esR.h.cache t0 = some (Tc, rR, k) := by
  intro t0
  rcases hsync.mode with hm | hm | hm
  · rcases hm.cache_rel t0 with hnone | ⟨Tc, rL, rR, k, hcL, hcR, _⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR⟩
  · have hmin_lt : min (esR.g.epoch .A) (esR.g.epoch .B) < t0 := by
      change min (esR.g.epoch .A) (esR.g.epoch .B) < esR.g.epoch P + 1
      cases P <;> simp
    rcases hm.cache_res t0 hmin_lt with hnone | ⟨Tc, rL, rR, k, _, hcL, hcR, _, _⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR⟩
  · rcases hm with ⟨_, Q_corr, eC, _, _, _, _, _, hep_Qc, _, hep_Qo, _, _, hcache_ge⟩
    by_cases hP : P = Q_corr
    · subst P
      have hgt : max (esR.g.epoch .A) (esR.g.epoch .B) < t0 := by
        change max (esR.g.epoch .A) (esR.g.epoch .B) < esR.g.epoch Q_corr + 1
        cases Q_corr <;> simp [Party.other] at hep_Qc hep_Qo ⊢ <;> try omega
      exact Or.inl (hsync.cache_gt_max t0 hgt)
    · have hP_Qo : P = Q_corr.other := by
        cases P <;> cases Q_corr <;> first | exact False.elim (hP rfl) | rfl
      subst P
      have ht0_eC : t0 = eC := hep_Qo
      rcases hcache_ge t0 (by omega) with hnone | ⟨Tc, rL, rR, k, _, hcL, hcR, _, _⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR⟩

private theorem run_vRecv_main_df
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR)
    (P : Party) (c : Header T × E)
    (recL recR : Option (SM.Record M (Header T × E))) :
    let runL := (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
      esL.g P (esL.g.st P) c recL).run esL.h
    let runR := (vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1))
      esR.g P (esR.g.st P) c recR).run esR.h
    (runL = pure (none, esL.h) ∧ runR = pure (none, esR.h)) ∨
    (runL = pure (some none, esL.h) ∧ runR = pure (some none, esR.h)) ∨
    ∃ vpL' vpR' i' m',
      runL = pure (some (some (vpL', c.1.1, i', m')), esL.h) ∧
      runR = pure (some (some (vpR', c.1.1, i', m')), esR.h) ∧
      c.1.1 ≤ esR.g.epoch P + 1 ∧
      P.sendsIn c.1.1 = false ∧
      VPBaseRelMain (max (esR.g.epoch P) c.1.1) P vpL' vpR' ∧
      (c.1.1 ≤ esR.g.epoch P →
        vpL'.root = (esL.g.st P).root ∧ vpR'.root = (esR.g.st P).root) ∧
      (c.1.1 = esR.g.epoch P + 1 →
        ∃ Tc rL rR k,
          esL.h.cache c.1.1 = some (Tc, rL, k) ∧
          esR.h.cache c.1.1 = some (Tc, rR, k) ∧
          vpL'.root = resolveCorrRoot esL.h c.1.1 rL ∧
          vpR'.root = resolveCorrRoot esR.h c.1.1 rR) := by
  have hvp := hsync.vp_base P
  dsimp only
  unfold vRecv
  dsimp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
  rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
  by_cases hbad : (P.sendsIn c.1.1 || decide (esR.g.epoch P + 1 < c.1.1)) = true
  · exact Or.inr (Or.inl ⟨by simp [hbad], by simp [hbad]⟩)
  · have hns : P.sendsIn c.1.1 = false := by
      cases hs : P.sendsIn c.1.1
      · rfl
      · simp [hs] at hbad
    have htle : c.1.1 ≤ esR.g.epoch P + 1 := by
      by_contra hgt
      have : decide (esR.g.epoch P + 1 < c.1.1) = true := decide_eq_true (Nat.lt_of_not_le hgt)
      simp [this] at hbad
    simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · simp only [hnew, ↓reduceIte]
      cases hc2 : c.1.2 with
      | none =>
        exact Or.inr (Or.inl ⟨by simp, by simp⟩)
      | some tn0 =>
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        rcases cache_at_succ_main_df hsync P with ⟨hcL, hcR⟩ | ⟨Tc, rL, rR, k, hcL, hcR⟩
        · simp only [hcL, hcR]
          by_cases habort : (!(decide (qep + 1 < esR.g.epoch P + 1)) &&
              inStage2BucketGen (3 + Δcka) tL par (esR.g.epoch P + 1) &&
              (tL.isSome && decide (esR.g.epoch P + 1 = healEpoch tL))) = true
          · exact Or.inl ⟨by simp only [habort, ↓reduceIte, StateT.run_pure, pure_bind],
              by simp only [habort, ↓reduceIte, StateT.run_pure, pure_bind]⟩
          · exact Or.inr (Or.inl ⟨
              by simp only [habort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind],
              by simp only [habort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]⟩)
        · simp only [hcL, hcR]
          by_cases hTc : Tc = tn0
          · subst tn0
            simp only [↓reduceIte, StateT.run_pure, pure_bind, hvp.γ_eq, Function.update_self]
            cases hfs : fs.receive (fs.initReceiver k) c.1 c.2 with
            | none =>
              exact Or.inr (Or.inl ⟨by simp only [StateT.run_pure],
                by simp only [StateT.run_pure]⟩)
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              refine Or.inr (Or.inr ⟨_, _, i', m',
                by simp only [StateT.run_pure]; rfl,
                by simp only [StateT.run_pure]; rfl,
                le_rfl, by rw [← hnew]; exact hns, ?_, ?_, ?_⟩)
              · refine ⟨rfl, by dsimp only; omega, rfl, by dsimp only; omega, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_⟩
                intro t'
                by_cases ht' : t' = esR.g.epoch P + 1
                · subst ht'; simp only [Function.update_self]
                · simp only [Function.update_of_ne ht', hvp.vR_eq t']
              · intro hle; omega
              · intro _
                exact ⟨Tc, rL, rR, k, rfl, rfl, rfl, rfl⟩
          · simp only [hTc, ↓reduceIte]
            by_cases habort : (!(decide (qep + 1 < esR.g.epoch P + 1)) &&
                inStage2BucketGen (3 + Δcka) tL par (esR.g.epoch P + 1) &&
                (tL.isSome && decide (esR.g.epoch P + 1 = healEpoch tL))) = true
            · exact Or.inl ⟨by simp only [habort, ↓reduceIte, StateT.run_pure, pure_bind],
                by simp only [habort, ↓reduceIte, StateT.run_pure, pure_bind]⟩
            · exact Or.inr (Or.inl ⟨
                by simp only [habort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind],
                by simp only [habort, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]⟩)
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      simp only [hnew, ↓reduceIte, pure_bind]
      have hvRL : (esL.g.st P).vR c.1.1 = (esR.g.st P).vR c.1.1 := hvp.vR_eq c.1.1
      cases hvR : (esR.g.st P).vR c.1.1 with
      | none =>
        exact Or.inr (Or.inl ⟨by simp only [hvRL, hvR, StateT.run_pure],
          by simp only [StateT.run_pure]⟩)
      | some v =>
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          exact Or.inr (Or.inl ⟨by simp only [hvRL, hvR, hfs, StateT.run_pure],
            by simp only [hfs, StateT.run_pure]⟩)
        | some vim =>
          rcases vim with ⟨v', i', m'⟩
          refine Or.inr (Or.inr ⟨
            { (esL.g.st P) with vR := Function.update (esL.g.st P).vR c.1.1 (some v') },
            { (esR.g.st P) with vR := Function.update (esR.g.st P).vR c.1.1 (some v') },
            i', m',
            by simp only [hvRL, hvR, hfs, StateT.run_pure],
            by simp only [hfs, StateT.run_pure],
            htle, hns, ?_, fun _ => ⟨rfl, rfl⟩, False.elim⟩)
          rw [Nat.max_eq_left htle_e]
          refine ⟨hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq, ?_⟩
          intro t'
          by_cases ht' : t' = c.1.1
          · subst ht'; simp only [Function.update_self]
          · simp only [Function.update_of_ne ht', hvp.vR_eq t']

private theorem leComp_deliverE_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp
      (fun rL rR =>
        rL.1.2.abort = true ∨
        (rL.1.1 = rR.1.1 ∧
          SyncStepMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2 ∧
          (esR.g.win = false → rR.1.2.g.win = false)))
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          fs.maxSkip (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
    | some r =>
      have hr_mem : r ∈ esR.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esL.g.mustBeCorrect fs.maxSkip P r = esR.g.mustBeCorrect fs.maxSkip P r := by
        simp [SM.GameState.mustBeCorrect, AuthL11.eraseSt_comp hsync.g_eq, AuthL11.eraseSt_maxAcc hsync.g_eq]
      have hr_pos_ep : r.pos.epoch = c.1.1 := by
        rw [← (hsync.trans_epoch r hr_mem.1).2, hr_mem.2.2]
      have hdw_false : (bucketAuthCfg Δcka tL par : SM.Config M).deliverWin = false := rfl
      simp only [hmust_eq, hdw_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, AuthL11.run_liftH]
      rcases run_vRecv_main_df cka prng fs Δcka qep tL par t hsync P c (some r) (some r) with
        ⟨hrunL, hrunR⟩ | ⟨hrunL, hrunR⟩ |
        ⟨vpL', vpR', i', m', hrunL, hrunR, htle, _hns, hvp_base', hroot_le, hnew_cache⟩
      · rw [hrunL, hrunR]
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inl rfl)
      · rw [hrunL, hrunR]
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
      · rw [hrunL, hrunR]
        simp only [pure_bind, StateT.run_bind, run_commitE_main_df,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [AuthL11.eraseSt_chall hsync.g_eq]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
          syncStepMainDF_of_accept hsync hr_pos_ep htle hvp_base' hroot_le hnew_cache,
          fun h => h⟩)

private theorem leComp_injectE_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp
      (fun rL rR =>
        rL.1.2.abort = true ∨
        (rL.1.1 = rR.1.1 ∧
          SyncStepMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2 ∧
          (esR.g.win = false → rR.1.2.g.win = true →
            lastLeakGuessAdmissible (3 + Δcka) tL arg.2.1.1 = true)))
      ((simulateQ (AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (false || esR.g.win || (esR.g.inTransit P.other c).isSome ||
      !esR.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, AuthL11.run_liftH]
    rcases run_vRecv_main_df cka prng fs Δcka qep tL par t hsync P c none none with
      ⟨hrunL, hrunR⟩ | ⟨hrunL, hrunR⟩ |
      ⟨vpL', vpR', i', m', hrunL, hrunR, htle, _hns, hvp_base', hroot_le, hnew_cache⟩
    · rw [hrunL, hrunR]
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inl rfl)
    · rw [hrunL, hrunR]
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
    · rw [hrunL, hrunR]
      simp only [pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
      · simp only [hqep, ↓reduceIte]
        rw [AuthL11.eraseSt_trivial hsync.g_eq]
        by_cases htriv : esR.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_main_df,
            StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncStepMainDF_of_accept hsync rfl htle hvp_base' hroot_le hnew_cache,
            fun h0 h1 => by dsimp [SM.GameState.accept, SM.GameState.delete] at h1; rw [h0] at h1; cases h1⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c.1.1 = true
          · have hadm3 : lastLeakGuessAdmissible (3 + Δcka) tL c.1.1 = true := by
              simp only [bucketAuthCfg, inStage2Bucket, Bool.and_eq_true] at hfull
              exact hfull.1
            simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepMainDF_set_win hsync,
              fun _ _ => hadm3⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)

private theorem leComp_deliverForgeE_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E) × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp
      (fun rL rR =>
        rL.1.2.abort = true ∨
        (rL.1.1 = rR.1.1 ∧
          SyncStepMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2 ∧
          (esR.g.win = false → rR.1.2.g.win = true →
            lastLeakGuessAdmissible (3 + Δcka) tL arg.2.2.1.1 = true)))
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_inTransit hsync.g_eq, AuthL11.eraseSt_comp hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
    | some r =>
      rw [AuthL11.eraseSt_inTransit hsync.g_eq]
      by_cases hrej : ((esR.g.inTransit P.other c').isSome || esR.g.comp.contains r.pos ||
          (c.1 != c'.1)) = true
      · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
      · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, AuthL11.run_liftH]
        rcases run_vRecv_main_df cka prng fs Δcka qep tL par t hsync P c' none none with
          ⟨hrunL, hrunR⟩ | ⟨hrunL, hrunR⟩ |
          ⟨vpL', vpR', i', m', hrunL, hrunR, htle, _hns, hvp_base', hroot_le, hnew_cache⟩
        · rw [hrunL, hrunR]
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inl rfl)
        · rw [hrunL, hrunR]
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
        · rw [hrunL, hrunR]
          simp only [pure_bind]
          by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
          · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)
          · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
            rw [AuthL11.eraseSt_trivial hsync.g_eq]
            by_cases htriv : esR.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_main_df,
                StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl,
                syncStepMainDF_of_accept hsync rfl htle hvp_base' hroot_le hnew_cache,
                fun h0 h1 => by dsimp [SM.GameState.accept, SM.GameState.delete] at h1; rw [h0] at h1; cases h1⟩)
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c'.1.1 = true
              · have hadm3 : lastLeakGuessAdmissible (3 + Δcka) tL c'.1.1 = true := by
                  simp only [bucketAuthCfg, inStage2Bucket, Bool.and_eq_true] at hfull
                  exact hfull.1
                simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepMainDF_set_win hsync,
                  fun _ _ => hadm3⟩)
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, fun h0 h1 => by rw [h0] at h1; cases h1⟩)

private def stepLcSend (tL : Option ℕ) (pl : Bool) (t0 : ℕ)
    (h0 : PRNGBucketState T Sig K I) : PRNGBucketState T Sig K I :=
  if pl && h0.lc.isNone && decide (healEpoch tL < t0) then
    { h0 with lc := some (t0 - 1) }
  else h0

private theorem stepLcSend_false (tL : Option ℕ) (t0 : ℕ) (h0 : PRNGBucketState T Sig K I) :
    stepLcSend tL false t0 h0 = h0 := rfl

private theorem stepLcSend_cache (tL : Option ℕ) (pl : Bool) (t0 : ℕ)
    (h0 : PRNGBucketState T Sig K I) :
    (stepLcSend tL pl t0 h0).cache = h0.cache := by
  unfold stepLcSend; split_ifs <;> rfl

private theorem stepLcSend_corrRoot (tL : Option ℕ) (pl : Bool) (t0 : ℕ)
    (h0 : PRNGBucketState T Sig K I) :
    (stepLcSend tL pl t0 h0).corrRoot = h0.corrRoot := by
  unfold stepLcSend; split_ifs <;> rfl

private theorem stepLcSend_lc_eq (tL : Option ℕ) (pl : Bool) (t0 : ℕ)
    {hL hR : PRNGBucketState T Sig K I} (hlc : hL.lc = hR.lc) :
    (stepLcSend tL pl t0 hL).lc = (stepLcSend tL pl t0 hR).lc := by
  unfold stepLcSend
  have his : hL.lc.isNone = hR.lc.isNone := by rw [hlc]
  rw [his]
  split_ifs
  · rfl
  · exact hlc

private def startSendBodyMain
    [DecidableEq T] [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (pl : Bool) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (coins : CCoins) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) (Option (Γ × T × Option Sig × SS)) := do
  let c := cka.send γ0 coins
  match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par m t0 pl c.2.2 σv0 with
  | none => return none
  | some (σ', kVal) =>
    modify fun s : PRNGBucketState T Sig K I =>
      { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
    return some (c.1, c.2.1, σ', fs.initSender kVal)

private theorem run_startSend_main_some
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (coins : CCoins)
    (h0 : PRNGBucketState T Sig K I) :
    ((hooksPRNGBucketMain cka prng fs Δcka qep tL par m).startSend ctx P t0 γ0 σv0 (some coins)).run h0 =
      (startSendBodyMain cka prng fs Δcka tL par m (postLeak tL ctx) t0 γ0 σv0 coins).run
        (stepLcSend tL (postLeak tL ctx) t0 h0) := by
  unfold stepLcSend startSendBodyMain
  dsimp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond : (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true
  · simp only [hcond, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]; rfl
  · simp only [hcond]; rfl

private theorem run_startSend_main_none
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig)
    (h0 : PRNGBucketState T Sig K I) :
    ((hooksPRNGBucketMain cka prng fs Δcka qep tL par m).startSend ctx P t0 γ0 σv0 none).run h0 =
      (StateT.lift (sampleT CCoins) >>=
        startSendBodyMain cka prng fs Δcka tL par m (postLeak tL ctx) t0 γ0 σv0).run
        (stepLcSend tL (postLeak tL ctx) t0 h0) := by
  unfold stepLcSend startSendBodyMain
  dsimp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond : (postLeak tL ctx && h0.lc.isNone && decide (healEpoch tL < t0)) = true
  · simp only [hcond, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]; rfl
  · simp only [hcond]; rfl

private theorem epMgmt_eq_of_sendsIn_false {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hns : P.sendsIn (s.epoch P + 1) = false)
    (hep : s.epMgmt Δ qep P bad = some s₁) : s₁ = s := by
  unfold SM.GameState.epMgmt at hep
  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split_ifs at hep
  simp only [Option.some.injEq] at hep
  exact hep.symm

private theorem epMgmt_fields_of_sendsIn_true {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hs : P.sendsIn (s.epoch P + 1) = true)
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    s₁.epoch = Function.update s.epoch P (s.epoch P + 1) ∧
    s₁.idx = Function.update s.idx P 0 ∧
    s₁.st = s.st ∧ s₁.trans = s.trans ∧ s₁.comp = s.comp ∧
    s₁.corrs = s.corrs ∧ s₁.win = s.win := by
  unfold SM.GameState.epMgmt at hep
  simp only [hs, ↓reduceIte] at hep
  split_ifs at hep
  all_goals
    simp only [Option.some.injEq] at hep
    subst hep
    simp [SM.GameState.leak]

private theorem leComp_startSend_sends_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (P : Party) (msg : M) (r_coins : Option CCoins)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    {s₁L s₁R : Ctx Γ T (Option Sig) SS RS M E}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR)
    (h2 : esR.g.epMgmt (2 + Δcka) qep P r_coins.isSome = some s₁R)
    (hs₁_er : AuthL11.eraseSt s₁L = AuthL11.eraseSt s₁R)
    (hs₁L_st : s₁L.st = esL.g.st) (hs₁R_st : s₁R.st = esR.g.st)
    (hsends : P.sendsIn (esR.g.epoch P + 1) = true) :
    let eMax := max (esR.g.epoch .A) (esR.g.epoch .B)
    AuthL11.LeComp
      (fun (rL rR : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                      PRFPRNG.GameState Sig I K) =>
        rL.1.1 = none ∨
        ∃ γ' tn rL' rR' kVal,
          rL.1.1 = some (γ', tn, rL', fs.initSender kVal) ∧
          rR.1.1 = some (γ', tn, rR', fs.initSender kVal) ∧
          rL.1.2.lc = rR.1.2.lc ∧
          (∀ e', eMax + 1 < e' → rL.1.2.cache e' = none ∧ rR.1.2.cache e' = none) ∧
          (∀ (vpL' vpR' : VP Γ T (Option Sig) SS RS) (ct : Header T × E),
            vpL'.root = rL' → vpR'.root = rR' →
            ModeMainDF Δcka tL par t
              { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := rL.1.2 } rL.2
              { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := rR.1.2 } rR.2))
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t).startSend
          s₁L P (max (esR.g.epoch .A) (esR.g.epoch .B) + 1)
          (esR.g.st P).γ (esL.g.st P).root r_coins).run esL.h)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1)).startSend
          s₁R P (max (esR.g.epoch .A) (esR.g.epoch .B) + 1)
          (esR.g.st P).γ (esR.g.st P).root r_coins).run esR.h)).run spR) := by
  intro eMax
  obtain ⟨hs₁R_ep, _, _, _, _, _, _⟩ := epMgmt_fields_of_sendsIn_true hsends h2
  have heq_other : esR.g.epoch P = esR.g.epoch P.other :=
    AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends hsends
  have he_eq_max : esR.g.epoch P = eMax := (AuthL11.max_epoch_eq_of_eq heq_other).symm
  have he_other_max : esR.g.epoch P.other = eMax := heq_other.symm.trans he_eq_max
  have hs₁_pl_eq : postLeak tL s₁L = postLeak tL s₁R := eraseSt_postLeak hs₁_er
  have hs₁R_ep_P : s₁R.epoch P = eMax + 1 := by simp [hs₁R_ep, he_eq_max]
  have hs₁R_ep_other : ∀ Q, Q ≠ P → s₁R.epoch Q = eMax := by
    intro Q hQ
    have hQo : Q = P.other := by
      cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
    subst Q; simp [hs₁R_ep, Function.update_of_ne hQ, he_other_max]
  have hs₁R_max : max (s₁R.epoch .A) (s₁R.epoch .B) = eMax + 1 := by
    rw [hs₁R_ep, AuthL11.max_epoch_update_succ heq_other, he_eq_max]
  have hs₁R_min : min (s₁R.epoch .A) (s₁R.epoch .B) = eMax := by
    rw [hs₁R_ep]
    cases P <;> simp [Party.other] at he_eq_max he_other_max ⊢ <;> omega
  have hbody : ∀ c0 : CCoins,
      AuthL11.LeComp
        (fun (rL rR : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                        PRFPRNG.GameState Sig I K) =>
          rL.1.1 = none ∨
          ∃ γ' tn rL' rR' kVal,
            rL.1.1 = some (γ', tn, rL', fs.initSender kVal) ∧
            rR.1.1 = some (γ', tn, rR', fs.initSender kVal) ∧
            rL.1.2.lc = rR.1.2.lc ∧
            (∀ e', eMax + 1 < e' → rL.1.2.cache e' = none ∧ rR.1.2.cache e' = none) ∧
            (∀ (vpL' vpR' : VP Γ T (Option Sig) SS RS) (ct : Header T × E),
              vpL'.root = rL' → vpR'.root = rR' →
              ModeMainDF Δcka tL par t
                { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := rL.1.2 } rL.2
                { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := rR.1.2 } rR.2))
        ((simulateQ (AuthL11.pImpl prng)
          ((startSendBodyMain cka prng fs Δcka tL par t (postLeak tL s₁R) (eMax + 1)
            (esR.g.st P).γ (esL.g.st P).root c0).run
            (stepLcSend tL (postLeak tL s₁R) (eMax + 1) esL.h))).run spL)
        ((simulateQ (AuthL11.pImpl prng)
          ((startSendBodyMain cka prng fs Δcka tL par (t + 1) (postLeak tL s₁R) (eMax + 1)
            (esR.g.st P).γ (esR.g.st P).root c0).run
            (stepLcSend tL (postLeak tL s₁R) (eMax + 1) esR.h))).run spR) := by
    intro c0
    unfold startSendBodyMain
    simp only [StateT.run_bind, simulateQ_bind]
    let ck := cka.send (esR.g.st P).γ c0
    rcases hsync.mode with hm | hm | hm
    · by_cases hpl1 : postLeak tL s₁R = true
      · simp only [hpl1]
        let hL0 := stepLcSend tL true (eMax + 1) esL.h
        let hR0 := stepLcSend tL true (eMax + 1) esR.h
        have hcrL0 : hL0.corrRoot = none := (stepLcSend_corrRoot tL true (eMax + 1) esL.h).trans hm.corrRootL
        have hcrR0 : hR0.corrRoot = none := (stepLcSend_corrRoot tL true (eMax + 1) esR.h).trans hm.corrRootR
        have hcL0 : hL0.cache = esL.h.cache := stepLcSend_cache tL true (eMax + 1) esL.h
        have hcR0 : hR0.cache = esR.h.cache := stepLcSend_cache tL true (eMax + 1) esR.h
        have hlc0 : hL0.lc = hR0.lc := stepLcSend_lc_eq tL true (eMax + 1) hsync.lc_eq
        have hrP : RelStepRoot (healEpoch tL) t
            (spPinStep (3 + Δcka) tL par t eMax spR.σ) eMax (esL.g.st P).root (esR.g.st P).root := by
          simpa [he_eq_max] using hm.vp_root P
        have hrO : RelStepRoot (healEpoch tL) t
            (spPinStep (3 + Δcka) tL par t eMax spR.σ) eMax (esL.g.st P.other).root (esR.g.st P.other).root := by
          simpa [he_other_max] using hm.vp_root P.other
        refine (leComp_rootSend_main_postLeak_from_pre (T := T) (Δbucket := 3 + Δcka) (par := par)
          prng tL t eMax ck.2.2 (esL.g.st P).root (esR.g.st P).root
          (esL.g.st P.other).root (esR.g.st P.other).root
          hL0 hR0 spL spR htLo hcrL0 hcrR0 hrP hrO hm.sp_σ_lt hm.spR_prf_le).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hrel
        rcases hrel with hnone |
          ⟨σNew, kVal, σOther, hresL, hresR, hcL1, hcR1, hlcL1, hlcR1, hresOL, hresOR⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hresL hresR hcL1 hcR1 hlcL1 hlcR1 hresOL hresOR
          subst hresL hresR
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr ⟨ck.1, ck.2.1, some σNew, some σNew, kVal, rfl, rfl,
            by dsimp only; rw [hlcL1, hlcR1]; exact hlc0,
            fun e' hgt => by
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                hcL1, hcR1, hcL0, hcR0]
              exact hsync.cache_gt_max e' (by omega),
            fun vpL' vpR' ct hvpL_r hvpR_r => ?_⟩)
          refine .allResolved ⟨hpl1, ?_, ?_⟩
          · intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁R_ep_P, hvpL_r, hvpR_r]
              exact ⟨σNew, rfl, rfl⟩
            · have hQo : Q = P.other := by
                cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
              subst Q
              simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
              exact ⟨σOther, hresOL, hresOR⟩
          · intro e' he'
            dsimp only [SM.GameState.record] at he' ⊢
            rw [hs₁R_min] at he'
            by_cases heq_e1 : e' = eMax + 1
            · subst e'
              simp only [Function.update_self]
              exact Or.inr ⟨ck.2.1, some σNew, some σNew, kVal, σNew, rfl, rfl, rfl, rfl⟩
            · rw [Function.update_of_ne heq_e1, Function.update_of_ne heq_e1,
                hcL1, hcR1, hcL0, hcR0]
              exact Or.inl (hsync.cache_gt_max e' he')
      · have hpl1_f : postLeak tL s₁R = false := Bool.eq_false_iff.mpr hpl1
        simp only [hpl1_f, stepLcSend_false]
        have hrP : RelStepRoot (healEpoch tL) t
            (spPinStep (3 + Δcka) tL par t eMax spR.σ) eMax (esL.g.st P).root (esR.g.st P).root := by
          simpa [he_eq_max] using hm.vp_root P
        refine (leComp_rootSend_main_pre (T := T) (Δbucket := 3 + Δcka) (par := par)
          prng tL t eMax ck.2.2 (esL.g.st P).root (esR.g.st P).root esL.h esR.h spL spR
          htLo hrP hm.corrRootL hm.corrRootR hm.fTable_ne hm.table_t
          hm.spL_b hm.spR_b hm.sp_σ_lt hm.spR_prf_le hm.spR_prng hm.spR_corr).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hrel
        rcases hrel with hnone |
          ⟨rL', rR', kVal, hresL, hresR, hr_new, hσR_ge, hcL1, hcR1, hcrL1, hcrR1,
            hlcL1, hlcR1, hft1, htab1, hbL1, hbR1, hσ_lt1, hprfR1, hprng1, hcorr1⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hresL hresR hcL1 hcR1 hcrL1 hcrR1 hlcL1 hlcR1
          subst hresL hresR
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr ⟨ck.1, ck.2.1, rL', rR', kVal, rfl, rfl,
            by dsimp only; rw [hlcL1, hlcR1]; exact hsync.lc_eq,
            fun e' hgt => by
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcL1, hcR1]
              exact hsync.cache_gt_max e' (by omega),
            fun vpL' vpR' ct hvpL_r hvpR_r => ?_⟩)
          refine .pre ⟨hpl1_f, hcrL1, hcrR1, by dsimp only; rw [hlcL1]; exact hm.lcL_none,
            ?_, ?_, hft1, htab1, hbL1, hbR1,
            by dsimp only [SM.GameState.record]; rw [hs₁R_max]; exact hσ_lt1,
            by dsimp only [SM.GameState.record]; rw [hs₁R_max]; exact hprfR1,
            hprng1,
            by dsimp only [SM.GameState.record]; rw [hs₁R_max]; exact hcorr1⟩
          · intro Q
            dsimp only [SM.GameState.record]
            rw [hs₁R_max]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁R_ep_P, hvpL_r, hvpR_r]
              exact hr_new
            · have hQo : Q = P.other := by
                cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
              subst Q
              simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
              have hrO : RelStepRoot (healEpoch tL) t
                  (spPinStep (3 + Δcka) tL par t eMax spR.σ) eMax
                  (esL.g.st P.other).root (esR.g.st P.other).root := by
                simpa [he_other_max] using hm.vp_root P.other
              by_cases het : eMax = t
              · rcases hσR_ge (by omega) with heq_pin | hnone_pin
                · rw [heq_pin]; exact hrO
                · exact hrO.change_σ (Or.inr hnone_pin)
              · exact hrO.change_σ (Or.inl het)
          · intro e'
            dsimp only [SM.GameState.record]
            rw [hs₁R_max]
            by_cases heq_e1 : e' = eMax + 1
            · subst e'
              simp only [Function.update_self]
              exact Or.inr ⟨ck.2.1, rL', rR', kVal, rfl, rfl, hr_new⟩
            · simp only [Function.update_of_ne heq_e1, hcL1, hcR1]
              by_cases het : e' = t
              · subst e'
                by_cases hle : t ≤ eMax
                · rcases hσR_ge hle with heq_pin | hnone_pin
                  · rw [heq_pin]; exact hm.cache_rel t
                  · exact (hm.cache_rel t).change_σ (Or.inr (Or.inl hnone_pin))
                · exact (hm.cache_rel t).change_σ (Or.inr (Or.inr (hsync.cache_gt_max t (by omega))))
              · exact (hm.cache_rel e').change_σ (Or.inl het)
    · have hpl1 : postLeak tL s₁R = true := postLeak_epMgmt hm.pl_true h2
      simp only [hpl1]
      let hL0 := stepLcSend tL true (eMax + 1) esL.h
      let hR0 := stepLcSend tL true (eMax + 1) esR.h
      have hcL0 : hL0.cache = esL.h.cache := stepLcSend_cache tL true (eMax + 1) esL.h
      have hcR0 : hR0.cache = esR.h.cache := stepLcSend_cache tL true (eMax + 1) esR.h
      have hcrL0 : hL0.corrRoot = esL.h.corrRoot := stepLcSend_corrRoot tL true (eMax + 1) esL.h
      have hcrR0 : hR0.corrRoot = esR.h.corrRoot := stepLcSend_corrRoot tL true (eMax + 1) esR.h
      have hlc0 : hL0.lc = hR0.lc := stepLcSend_lc_eq tL true (eMax + 1) hsync.lc_eq
      obtain ⟨σ, hresL, hresR⟩ := hm.vp_res P
      rw [he_eq_max] at hresL hresR
      obtain ⟨σO, hresOL, hresOR⟩ := hm.vp_res P.other
      rw [he_other_max] at hresOL hresOR
      have hrunL := run_rootSend_main_post (T := T) prng (3 + Δcka) tL par t (eMax + 1) ck.2.2
        (esL.g.st P).root hL0 σ
        (by simpa only [Nat.add_sub_cancel] using
          (resolveCorrRoot_eq_of_corrRoot_eq hcrL0 _ _).trans hresL)
      have hrunR := run_rootSend_main_post (T := T) prng (3 + Δcka) tL par (t + 1) (eMax + 1) ck.2.2
        (esR.g.st P).root hR0 σ
        (by simpa only [Nat.add_sub_cancel] using
          (resolveCorrRoot_eq_of_corrRoot_eq hcrR0 _ _).trans hresR)
      rw [hrunL, hrunR]
      simp only [StateT.run_bind, pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      let σNew := (prng.up σ ck.2.2).1
      let kVal := (prng.up σ ck.2.2).2
      refine AuthL11.LeComp.pure (Or.inr ⟨ck.1, ck.2.1, some σNew, some σNew, kVal, rfl, rfl,
        hlc0,
        fun e' hgt => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcL0, hcR0]
          exact hsync.cache_gt_max e' (by omega),
        fun vpL' vpR' ct hvpL_r hvpR_r => ?_⟩)
      refine .allResolved ⟨hpl1, ?_, ?_⟩
      · intro Q
        dsimp only [SM.GameState.record]
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, hs₁R_ep_P, hvpL_r, hvpR_r]
          exact ⟨σNew, rfl, rfl⟩
        · have hQo : Q = P.other := by
            cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
          subst Q
          simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
          exact ⟨σO,
            (resolveCorrRoot_eq_of_corrRoot_eq hcrL0 _ _).trans hresOL,
            (resolveCorrRoot_eq_of_corrRoot_eq hcrR0 _ _).trans hresOR⟩
      · intro e' he'
        dsimp only [SM.GameState.record] at he' ⊢
        rw [hs₁R_min] at he'
        by_cases heq_e1 : e' = eMax + 1
        · subst e'
          simp only [Function.update_self]
          exact Or.inr ⟨ck.2.1, some σNew, some σNew, kVal, σNew, rfl, rfl, rfl, rfl⟩
        · rw [Function.update_of_ne heq_e1, Function.update_of_ne heq_e1, hcL0, hcR0]
          have hmin_lt : min (esR.g.epoch .A) (esR.g.epoch .B) < e' := by
            dsimp only [eMax] at he'; omega
          rcases hm.cache_res e' hmin_lt with ⟨hn1, hn2⟩ | ⟨Tc, rL, rR, k, τ, hc1, hc2, hr1, hr2⟩
          · exact Or.inl ⟨hn1, hn2⟩
          · exact Or.inr ⟨Tc, rL, rR, k, τ, hc1, hc2,
              (resolveCorrRoot_eq_of_corrRoot_eq hcrL0 _ _).trans hr1,
              (resolveCorrRoot_eq_of_corrRoot_eq hcrR0 _ _).trans hr2⟩
    · exfalso
      rcases hm with ⟨_, Q_corr, eC, _, _, _, _, _, hep_Qc, _, hep_Qo, _, _, _⟩
      cases Q_corr <;> cases P <;> simp [Party.other] at heq_other hep_Qc hep_Qo <;> omega
  cases r_coins with
  | some c0 =>
    rw [run_startSend_main_some, run_startSend_main_some, hs₁_pl_eq]
    exact hbody c0
  | none =>
    rw [run_startSend_main_none, run_startSend_main_none, hs₁_pl_eq]
    simp only [StateT.run_bind, simulateQ_bind,
      AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
    exact AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun c0 _ => by
      simpa only [pure_bind] using hbody c0

private theorem leComp_transmitEBucket_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (arg : Party × M × Option CCoins)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp
      (fun rL rR =>
        rL.1.2.abort = true ∨
        (rL.1.1 = rR.1.1 ∧
          SyncStepMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2 ∧
          (esR.g.win = false → rR.1.2.g.win = false)))
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep arg).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep arg).run esR)).run spR) := by
  rcases arg with ⟨P, msg, r_coins⟩
  unfold transmitEBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁L, s₁R, h1, h2, hs₁_er, hs₁L_st, hs₁R_st, hs₁_trans, _, _⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
    · have hvp := hsync.vp_base P
      by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
      · obtain ⟨hs₁R_ep, _, _, _, _, _, hs₁R_win⟩ := epMgmt_fields_of_sendsIn_true hsends h2
        have heq_other : esR.g.epoch P = esR.g.epoch P.other :=
          AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends hsends
        let eMax := max (esR.g.epoch .A) (esR.g.epoch .B)
        have he_eq_max : esR.g.epoch P = eMax := (AuthL11.max_epoch_eq_of_eq heq_other).symm
        have he_other_max : esR.g.epoch P.other = eMax := heq_other.symm.trans he_eq_max
        have hs₁R_ep_P : s₁R.epoch P = eMax + 1 := by simp [hs₁R_ep, he_eq_max]
        have hs₁R_ep_other : ∀ Q, Q ≠ P → s₁R.epoch Q = eMax := by
          intro Q hQ
          have hQo : Q = P.other := by
            cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
          subst Q; simp [hs₁R_ep, Function.update_of_ne hQ, he_other_max]
        have hs₁R_max : max (s₁R.epoch .A) (s₁R.epoch .B) = eMax + 1 := by
          rw [hs₁R_ep, AuthL11.max_epoch_update_succ heq_other, he_eq_max]
        have hcommon_sync : ∀ {vpL' vpR' : VP Γ T (Option Sig) SS RS}
            {hL1 hR1 : PRNGBucketState T Sig K I}
            {spL1 spR1 : PRFPRNG.GameState Sig I K} {ct : Header T × E},
            ct.1.1 = eMax + 1 →
            hL1.lc = hR1.lc →
            VPBaseRelMain (eMax + 1) P vpL' vpR' →
            (∀ e', eMax + 1 < e' → hL1.cache e' = none ∧ hR1.cache e' = none) →
            ModeMainDF Δcka tL par t
              { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := hL1 } spL1
              { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := hR1 } spR1 →
            SyncStepMainDF Δcka tL par t
              { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := hL1 } spL1
              { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := hR1 } spR1 := by
          intro vpL' vpR' hL1 hR1 spL1 spR1 ct hct_ep hlc1 hvp' hcache_gt hmode'
          refine ⟨rfl, rfl, ?_, hlc1, ?_, ?_, ?_, ?_, ?_, hmode'⟩
          · rw [AuthL11.eraseSt_epoch hs₁_er, AuthL11.eraseSt_idx hs₁_er]
            exact AuthL11.eraseSt_record hs₁_er (2 + Δcka) P vpL' vpR' _ false
          · intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁R_ep_P]; exact hvp'
            · simp only [Function.update_of_ne hQ, hs₁R_ep_other Q hQ, hs₁L_st, hs₁R_st]
              have hQo : Q = P.other := by
                cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
              subst Q
              simpa [he_other_max] using hsync.vp_base P.other
          · intro e' hgt
            dsimp only [SM.GameState.record] at hgt
            rw [hs₁R_max] at hgt
            exact hcache_gt e' hgt
          · intro Q
            dsimp only [SM.GameState.record]
            rw [hs₁R_ep]
            cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
          · intro Q hlt_Q
            dsimp only [SM.GameState.record] at hlt_Q ⊢
            rw [hs₁R_ep] at hlt_Q ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hsends
            · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          · intro r hr
            dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact ⟨le_rfl, by dsimp only; rw [hct_ep, hs₁R_ep_P]⟩
            · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
              refine ⟨?_, h_eq⟩
              rw [hs₁R_ep]
              by_cases hQ : r.pos.sender = P
              · rw [hQ, Function.update_self]; rw [hQ] at h_le; omega
              · rw [Function.update_of_ne hQ]; exact h_le
        simp only [h1, h2, hs₁L_st, hs₁R_st, StateT.run_bind, AuthL11.run_liftH,
          hsync.abortL, hsync.abortR, simulateQ_bind, bind_assoc]
        unfold vSend
        rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R, hvp.γ_eq]
        simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc]
        rw [he_eq_max]
        refine (leComp_startSend_sends_main_df cka prng fs Δcka qep tL par t htLo
          P msg r_coins hsync h2 hs₁_er hs₁L_st hs₁R_st hsends).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hss
        rcases hss with hnone | ⟨γ', tn, rL', rR', kVal, hresL, hresR, hlc1, hc_gt1, hmode1⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure, pure_bind, abortE,
            StateT.run_bind, StateT.run_modify]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hresL hresR; subst hresL hresR
          simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hcommon_sync rfl hlc1
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq⟩
            hc_gt1 (hmode1 _ _ _ rfl rfl),
            fun h0 => by dsimp [SM.GameState.record]; rw [hs₁R_win, h0]⟩)
      · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
        have hnsL : P.sendsIn (esL.g.epoch P + 1) = false := by
          rw [AuthL11.eraseSt_epoch hsync.g_eq]; exact hns
        have hs₁L_eq := epMgmt_eq_of_sendsIn_false hnsL h1
        have hs₁R_eq := epMgmt_eq_of_sendsIn_false hns h2
        subst hs₁L_eq hs₁R_eq
        simp only [h1, h2, StateT.run_bind, AuthL11.run_liftH,
          hsync.abortL, hsync.abortR, simulateQ_bind, bind_assoc]
        unfold vSend
        rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
        simp only [hns, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, hvp.vS_eq]
        have hrec_sync : ∀ {vpL' vpR' : VP Γ T (Option Sig) SS RS} {ct : Header T × E},
            ct.1.1 = esR.g.epoch P →
            VPBaseRelMain (esR.g.epoch P) P vpL' vpR' →
            vpL'.root = (esL.g.st P).root →
            vpR'.root = (esR.g.st P).root →
            SyncStepMainDF Δcka tL par t
              { g := esL.g.record (2 + Δcka) P vpL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, msg, ct⟩ false, h := esL.h } spL
              { g := esR.g.record (2 + Δcka) P vpR' ⟨⟨P, esR.g.epoch P, esR.g.idx P + 1⟩, msg, ct⟩ false, h := esR.h } spR := by
          intro vpL' vpR' ct hct_ep hvp' hrL' hrR'
          have hroot_same : ∀ Q,
              ((esL.g.record (2 + Δcka) P vpL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, msg, ct⟩ false).st Q).root =
                (esL.g.st Q).root ∧
              ((esR.g.record (2 + Δcka) P vpR' ⟨⟨P, esR.g.epoch P, esR.g.idx P + 1⟩, msg, ct⟩ false).st Q).root =
                (esR.g.st Q).root := by
            intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp [hrL', hrR']
            · simp [Function.update_of_ne hQ]
          refine ⟨rfl, rfl, ?_, hsync.lc_eq, ?_, hsync.cache_gt_max,
            hsync.epoch_le, hsync.epoch_sends, ?_, ?_⟩
          · rw [AuthL11.eraseSt_epoch hsync.g_eq, AuthL11.eraseSt_idx hsync.g_eq]
            exact AuthL11.eraseSt_record hsync.g_eq (2 + Δcka) P vpL' vpR' _ false
          · intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hvp'
            · simp only [Function.update_of_ne hQ]; exact hsync.vp_base Q
          · intro r hr
            dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact ⟨le_rfl, hct_ep⟩
            · exact hsync.trans_epoch r hr'
          · rcases hsync.mode with hm | hm | hm
            · refine .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, hm.lcL_none, ?_, hm.cache_rel,
                hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spR_prf_le,
                hm.spR_prng, hm.spR_corr⟩
              intro Q; dsimp only
              rw [(hroot_same Q).1, (hroot_same Q).2]
              exact hm.vp_root Q
            · refine .allResolved ⟨hm.pl_true, ?_, hm.cache_res⟩
              intro Q; dsimp only
              rw [(hroot_same Q).1, (hroot_same Q).2]
              exact hm.vp_res Q
            · rcases hm with ⟨hpl, Q_corr, eC, σC, htH_eC, hmem_corr, hcrL, hcrR,
                hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩
              refine .postCorr ⟨hpl, Q_corr, eC, σC, htH_eC, hmem_corr, hcrL, hcrR,
                hep_Qc, ?_, hep_Qo, hsends_Qc, ?_, hcache_ge⟩
              · dsimp only
                rw [(hroot_same Q_corr).1, (hroot_same Q_corr).2]
                exact hres_Qc
              · intro hne; dsimp only
                rw [(hroot_same Q_corr.other).1, (hroot_same Q_corr.other).2]
                exact hroot_Qo hne
        cases hvS : (esR.g.st P).vS with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, pure_bind,
            StateT.run_bind, StateT.run_modify]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hrec_sync rfl hvp rfl rfl,
            fun h0 => by dsimp [SM.GameState.record]; rw [h0]⟩)
        | some v =>
          simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
            StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_modify]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hrec_sync rfl
            ⟨hvp.id_L, rfl, hvp.id_R, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq⟩
            rfl rfl, fun h0 => by dsimp [SM.GameState.record]; rw [h0]⟩)

private theorem leComp_corrEPaperBucket_main_df
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (P : Party)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMainDF Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp
      (fun rL rR =>
        DoomedMainDF Δcka tL t (rL.1.2, none) ∨
        (rL.1.1 = rR.1.1 ∧
          SyncStepMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2 ∧
          (esR.g.win = false → rR.1.2.g.win = false)))
      ((simulateQ (AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t) P).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par (t + 1)) P).run esR)).run spR) := by
  unfold corrEPaperBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_corrAllowedPaper hsync.g_eq P]
  by_cases hguard : (false || esR.g.win || !esR.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, id⟩)
  · have hwinR0 : esR.g.win = false := by
      simp only [Bool.false_or, Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
      exact hguard.1
    have hwinL0 : esL.g.win = false := (AuthL11.eraseSt_win hsync.g_eq).trans hwinR0
    have hvp := hsync.vp_base P
    have hac_er := AuthL11.eraseSt_afterCorr hsync.g_eq P
    have hpl_eq : postLeak tL esL.g = postLeak tL esR.g := eraseSt_postLeak hsync.g_eq
    have hep_eq : esL.g.epoch = esR.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
    have hreal_eq : ∀ σ : Sig,
        realParty (esL.g.st P) (esL.g.st P).γ σ (esL.g.st P).vS (esL.g.st P).vR =
        realParty (esR.g.st P) (esR.g.st P).γ σ (esR.g.st P).vS (esR.g.st P).vR := by
      intro σ
      dsimp only [realParty]
      rw [hvp.id_L, hvp.id_R, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_L, hvp.tcur_R,
        hvp.vS_eq, funext hvp.vR_eq]
    simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, AuthL11.run_liftH,
      hsync.abortL, hsync.abortR, simulateQ_bind, bind_assoc]
    dsimp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rw [hvp.tcur_L, hvp.tcur_R, hep_eq, hpl_eq]
    rcases hsync.mode with hm | hm | hm
    · have hlcR_none : esR.h.lc = none := hsync.lc_eq.symm.trans hm.lcL_none
      have hresL0 : resolveCorrRoot esL.h (esR.g.epoch P) (esL.g.st P).root = (esL.g.st P).root :=
        resolveCorrRoot_of_corrRoot_none hm.corrRootL _ _
      have hresR0 : resolveCorrRoot esR.h (esR.g.epoch P) (esR.g.st P).root = (esR.g.st P).root :=
        resolveCorrRoot_of_corrRoot_none hm.corrRootR _ _
      rw [hresL0, hresR0]
      by_cases hle_other : esR.g.epoch P.other ≤ esR.g.epoch P
      · have he_max : esR.g.epoch P = max (esR.g.epoch .A) (esR.g.epoch .B) := by
          cases P <;> simp [Party.other] at hle_other ⊢ <;> omega
        by_cases hlt_tH : esR.g.epoch P < healEpoch tL
        · obtain ⟨l, htL_l, he_lt_l2⟩ : ∃ l, tL = some l ∧ esR.g.epoch P < l + 2 := by
            cases tL with
            | none => simp [healEpoch] at hlt_tH
            | some l => exact ⟨l, rfl, by simpa [healEpoch] using hlt_tH⟩
          subst htL_l
          obtain ⟨σ, hrL, hrR⟩ := RelStepRoot.some_of_lt_tH_df htLo hlt_tH (hm.vp_root P)
          simp only [hrL, hrR, hlt_tH,
            decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify, simulateQ_pure]
          by_cases he_le_l : esR.g.epoch P ≤ l
          · have hpl_ac : postLeak (some l) (esR.g.afterCorr P) = false := by
              have hpl0 := hm.pl_false
              unfold postLeak at hpl0 ⊢
              dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
              rw [← he_max]
              cases hcur : esR.g.tL with
              | none =>
                simp [SM.maxOpt, ltOpt]
                exact decide_eq_false (by omega)
              | some cur =>
                rw [hcur] at hpl0
                simp [SM.maxOpt, ltOpt] at hpl0 ⊢
                exact ⟨hpl0, he_le_l⟩
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
              ⟨rfl, rfl, hac_er, hsync.lc_eq, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
                .pre ⟨hpl_ac, hm.corrRootL, hm.corrRootR, hm.lcL_none, hm.vp_root, hm.cache_rel,
                  hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt,
                  hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩⟩, fun h => h⟩)
          · have he_eq_l1 : esR.g.epoch P = l + 1 := by omega
            refine AuthL11.LeComp.pure (Or.inl (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨hwinL0, rfl⟩,
              l + 1, ?_, by simp [ltOpt], ?_⟩))))
            · dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
              have hpl0 : postLeak (some l) esL.g = false := by rw [hpl_eq]; exact hm.pl_false
              unfold postLeak at hpl0
              have heMaxL : max (esL.g.epoch .A) (esL.g.epoch .B) = l + 1 := by
                rw [hep_eq, ← he_max, he_eq_l1]
              rw [heMaxL]
              cases hcur : esL.g.tL with
              | none => simp [SM.maxOpt]
              | some cur =>
                rw [hcur] at hpl0
                simp [ltOpt] at hpl0
                have hmax_l1 : max cur (l + 1) = l + 1 := by omega
                simp [SM.maxOpt, hmax_l1]
            · intro tWin hadm_win
              simp [lastLeakGuessAdmissible, SM.healedBy] at hadm_win
              omega
        · have hge_tH : healEpoch tL ≤ esR.g.epoch P := Nat.le_of_not_lt hlt_tH
          have hpl_ac : postLeak tL (esR.g.afterCorr P) = true :=
            postLeak_afterCorr_of_ge_healEpoch hge_tH
          have hfinish_ge : ∀ (σC : Sig)
              (spL1 spR1 : PRFPRNG.GameState Sig I K),
              (esR.g.epoch P ≤ t →
                spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ = some σC) →
              SyncStepMainDF Δcka tL par t
                { g := esL.g.afterCorr P,
                  h := { esL.h with corrRoot := some (esR.g.epoch P, σC), lc := some (esR.g.epoch P) } } spL1
                { g := esR.g.afterCorr P,
                  h := { esR.h with corrRoot := some (esR.g.epoch P, σC), lc := some (esR.g.epoch P) } } spR1 := by
            intro σC spL1 spR1 hσC
            refine ⟨rfl, rfl, hac_er, rfl, hsync.vp_base, hsync.cache_gt_max,
              hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, ?_⟩
            obtain ⟨σP, hresPL, hresPR⟩ :=
              (hm.vp_root P).resolve_after_set_corrRoot_df (hL := esL.h) (hR := esR.h) hge_tH hσC
            have hres_P : ∃ σ,
                resolveCorrRoot { esL.h with corrRoot := some (esR.g.epoch P, σC), lc := some (esR.g.epoch P) }
                  (esR.g.epoch P) (esL.g.st P).root = some σ ∧
                resolveCorrRoot { esR.h with corrRoot := some (esR.g.epoch P, σC), lc := some (esR.g.epoch P) }
                  (esR.g.epoch P) (esR.g.st P).root = some σ :=
              ⟨σP,
                (resolveCorrRoot_eq_of_corrRoot_eq
                  (h2 := { esL.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans hresPL,
                (resolveCorrRoot_eq_of_corrRoot_eq
                  (h2 := { esR.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans hresPR⟩
            by_cases heq_o : esR.g.epoch P.other = esR.g.epoch P
            · refine .allResolved ⟨hpl_ac, ?_, ?_⟩
              · intro Q
                dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
                by_cases hQ : Q = P
                · subst Q; exact hres_P
                · have hQo : Q = P.other := by
                    cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
                  subst Q
                  have hrO : RelStepRoot (healEpoch tL) t
                      (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
                      (esR.g.epoch P) (esL.g.st P.other).root (esR.g.st P.other).root := by
                    simpa [heq_o] using hm.vp_root P.other
                  obtain ⟨σO, hOL, hOR⟩ :=
                    hrO.resolve_after_set_corrRoot_df (hL := esL.h) (hR := esR.h) hge_tH hσC
                  refine ⟨σO, ?_, ?_⟩
                  · rw [heq_o]
                    exact (resolveCorrRoot_eq_of_corrRoot_eq
                      (h2 := { esL.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans hOL
                  · rw [heq_o]
                    exact (resolveCorrRoot_eq_of_corrRoot_eq
                      (h2 := { esR.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans hOR
              · intro e' he'
                dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at he' ⊢
                have hmin_e : min (esR.g.epoch .A) (esR.g.epoch .B) = esR.g.epoch P := by
                  cases P <;> simp [Party.other] at heq_o ⊢ <;> omega
                rw [hmin_e, he_max] at he'
                exact Or.inl (hsync.cache_gt_max e' he')
            · have hlt_o : esR.g.epoch P.other < esR.g.epoch P := Nat.lt_of_le_of_ne hle_other heq_o
              have hle_1 := hsync.epoch_le P
              have hep_Qo : esR.g.epoch P.other + 1 = esR.g.epoch P := by omega
              have hsends_P : P.sendsIn (esR.g.epoch P) = true := hsync.epoch_sends P hlt_o
              refine .postCorr ⟨hpl_ac, P, esR.g.epoch P, σC, hge_tH,
                by simp [SM.GameState.afterCorr], rfl, rfl, rfl, hres_P,
                hep_Qo, hsends_P, ?_, ?_⟩
              · intro hne_t
                have hne_o : esR.g.epoch P.other ≠ t := by omega
                exact (hm.vp_root P.other).eq_of_ne_t_df hne_o
              · intro e' he'
                dsimp only
                by_cases heq_e : e' = esR.g.epoch P
                · subst e'
                  rcases hm.cache_rel (esR.g.epoch P) with hnone | ⟨Tc, rL, rR, k, hcL, hcR, hr_c⟩
                  · exact Or.inl hnone
                  · obtain ⟨σOut, h1, h2⟩ := hr_c.resolve_after_set_corrRoot_df
                      (hL := esL.h) (hR := esR.h) hge_tH hσC
                    exact Or.inr ⟨Tc, rL, rR, k, σOut, hcL, hcR,
                      (resolveCorrRoot_eq_of_corrRoot_eq
                        (h2 := { esL.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans h1,
                      (resolveCorrRoot_eq_of_corrRoot_eq
                        (h2 := { esR.h with corrRoot := some (esR.g.epoch P, σC) }) rfl _ _).trans h2⟩
                · have hgt_max : max (esR.g.epoch .A) (esR.g.epoch .B) < e' := by
                    rw [← he_max]
                    omega
                  exact Or.inl (hsync.cache_gt_max e' hgt_max)
          rcases hm.vp_root P with ⟨hlt, _⟩ | ⟨_, hlt_t, hrL, hrR⟩ |
              ⟨heq_t, ⟨σ0, hrL, hpin0⟩, hrR⟩ | ⟨hgt_t, σ, hrL, hrR⟩
          · omega
          · have hprfR := hm.spR_prf_le (by rw [← he_max]; omega)
            have hσ_eq := hm.sp_σ_lt (by rw [← he_max]; exact hlt_t)
            simp only [hrL, hrR, hm.pl_false, hm.corrRootL, hm.corrRootR,
              hm.lcL_none, hlcR_none, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, ← he_max, beq_self_eq_true, Bool.and_self,
              ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind,
              simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_corrQuery,
              AuthL11.run_corrImpl, hprfR, hσ_eq, Bool.false_eq_true]
            cases hprfL : spL.prf
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, pure_bind,
                StateT.run_modify, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq spR.σ),
                hfinish_ge spR.σ _ _ (fun hle => by rw [← he_max]; simp [spPinStep, hle]),
                fun h => h⟩)
            · simp only [↓reduceIte, StateT.run_bind, pure_bind, abortE, StateT.run_modify,
                StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          · have hprfR := hm.spR_prf_le (by rw [← he_max]; omega)
            have hpin_eq : spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ =
                some spR.σ := by rw [← he_max, heq_t]; simp [spPinStep]
            have hσ0_eq : σ0 = spR.σ := by
              rw [hpin_eq] at hpin0
              rcases hpin0 with h1 | h2
              · cases h1; rfl
              · cases h2
            subst hσ0_eq
            simp only [hrL, hrR, hm.pl_false, hm.corrRootL, hm.corrRootR,
              hm.lcL_none, hlcR_none, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, ← he_max, beq_self_eq_true, Bool.and_self,
              ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind,
              simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_corrQuery,
              AuthL11.run_corrImpl, hprfR, Bool.false_eq_true,
              StateT.run_modify, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq spR.σ),
              hfinish_ge spR.σ _ _ (fun _ => hpin_eq), fun h => h⟩)
          · simp only [hrL, hrR, hm.pl_false, hm.corrRootL, hm.corrRootR,
              hm.lcL_none, hlcR_none, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, Bool.and_self,
              ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
              hfinish_ge σ _ _ (fun h => by omega), fun h => h⟩)
      · have hlt_other : esR.g.epoch P < esR.g.epoch P.other := Nat.lt_of_not_le hle_other
        have hle_other1 := hsync.epoch_le P.other
        rw [Party.other_other] at hle_other1
        have heq_other : esR.g.epoch P.other = esR.g.epoch P + 1 := by omega
        have heMax_eq : max (esR.g.epoch .A) (esR.g.epoch .B) = esR.g.epoch P + 1 := by
          cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
        have hne_max : (esR.g.epoch P == max (esR.g.epoch .A) (esR.g.epoch .B)) = false := by
          rw [heMax_eq]; simp only [beq_eq_false_iff_ne, ne_eq]; omega
        by_cases hlt_tH : esR.g.epoch P < healEpoch tL
        · obtain ⟨l, htL_l, he_lt_l2⟩ : ∃ l, tL = some l ∧ esR.g.epoch P < l + 2 := by
            cases tL with
            | none => simp [healEpoch] at hlt_tH
            | some l => exact ⟨l, rfl, by simpa [healEpoch] using hlt_tH⟩
          subst htL_l
          obtain ⟨σ, hrL, hrR⟩ := RelStepRoot.some_of_lt_tH_df htLo hlt_tH (hm.vp_root P)
          simp only [hrL, hrR, hlt_tH,
            decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify, simulateQ_pure]
          by_cases he1_le_l : esR.g.epoch P + 1 ≤ l
          · have hpl_ac : postLeak (some l) (esR.g.afterCorr P) = false := by
              have hpl0 := hm.pl_false
              unfold postLeak at hpl0 ⊢
              dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
              rw [heMax_eq]
              cases hcur : esR.g.tL with
              | none => simp [SM.maxOpt, ltOpt]; omega
              | some cur =>
                rw [hcur] at hpl0
                simp [SM.maxOpt, ltOpt] at hpl0 ⊢; omega
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
              ⟨rfl, rfl, hac_er, hsync.lc_eq, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
                .pre ⟨hpl_ac, hm.corrRootL, hm.corrRootR, hm.lcL_none, hm.vp_root, hm.cache_rel,
                  hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt,
                  hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩⟩, fun h => h⟩)
          · have hl_lt_e1 : l < esR.g.epoch P + 1 := Nat.lt_of_not_le he1_le_l
            refine AuthL11.LeComp.pure (Or.inl (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨hwinL0, rfl⟩,
              esR.g.epoch P + 1, ?_, by simp [ltOpt, hl_lt_e1], ?_⟩))))
            · dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
              have hpl0 : postLeak (some l) esL.g = false := by rw [hpl_eq]; exact hm.pl_false
              unfold postLeak at hpl0
              have heMaxL : max (esL.g.epoch .A) (esL.g.epoch .B) = esR.g.epoch P + 1 := by
                rw [hep_eq]; exact heMax_eq
              rw [heMaxL]
              cases hcur : esL.g.tL with
              | none => simp [SM.maxOpt]
              | some cur =>
                rw [hcur] at hpl0
                simp [ltOpt] at hpl0
                have hmax_e1 : max cur (esR.g.epoch P + 1) = esR.g.epoch P + 1 := by omega
                simp [SM.maxOpt, hmax_e1]
            · intro tWin hadm_win
              simp [lastLeakGuessAdmissible, SM.healedBy] at hadm_win
              omega
        · have hge_tH : healEpoch tL ≤ esR.g.epoch P := Nat.le_of_not_lt hlt_tH
          rcases hm.vp_root P with ⟨hlt, _⟩ | ⟨_, hlt_t, hrL, _⟩ |
              ⟨heq_t, ⟨σ0, hrL, _⟩, _⟩ | ⟨hgt_t, σ, hrL, hrR⟩
          · omega
          · simp only [hrL, hne_max, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, abortE, StateT.run_bind, StateT.run_modify, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          · simp only [hrL, hm.pl_false, hm.corrRootL, hm.lcL_none, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, Bool.and_self,
              ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ =>
              Or.inl (Or.inr (Or.inl ⟨esR.g.epoch P, rfl, by omega⟩))
          · obtain ⟨σO, hrOL, hrOR⟩ : ∃ σO,
                (esL.g.st P.other).root = some σO ∧ (esR.g.st P.other).root = some σO := by
              rcases hm.vp_root P.other with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h1⟩
              · omega
              · omega
              · omega
              · exact h1
            have hpl_ac : postLeak tL (esR.g.afterCorr P) = true :=
              postLeak_afterCorr_of_ge_healEpoch hge_tH
            simp only [hrL, hrR, hm.pl_false, hm.corrRootL, hm.corrRootR,
              hm.lcL_none, hlcR_none, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, Bool.and_self,
              ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
              ⟨rfl, rfl, hac_er, rfl, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
                .allResolved ⟨hpl_ac, ?_, ?_⟩⟩, fun h => h⟩)
            · intro Q
              dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
              by_cases hQ : Q = P
              · subst Q; exact ⟨σ, by simp [hrL], by simp [hrR]⟩
              · have hQo : Q = P.other := by
                  cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
                subst Q; exact ⟨σO, by simp [hrOL], by simp [hrOR]⟩
            · intro e' he'
              dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at he' ⊢
              have hmin_e : min (esR.g.epoch .A) (esR.g.epoch .B) = esR.g.epoch P := by
                cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
              rw [hmin_e] at he'
              rcases hm.cache_rel e' with hnone | ⟨Tc, rLc, rRc, k, hcL, hcR, hrc⟩
              · exact Or.inl hnone
              · rcases hrc with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, σc, h1, h2⟩
                · omega
                · omega
                · omega
                · exact Or.inr ⟨Tc, rLc, rRc, k, σc, hcL, hcR, by simp [h1], by simp [h2]⟩
    · obtain ⟨σ, hresL, hresR⟩ := hm.vp_res P
      have hpl_ac : postLeak tL (esR.g.afterCorr P) = true := postLeak_afterCorr_mono hm.pl_true
      let hL' : PRNGBucketState T Sig K I :=
        if !(decide (esR.g.epoch P < healEpoch tL)) && esL.h.corrRoot.isNone
        then { esL.h with corrRoot := some (esR.g.epoch P, σ) } else esL.h
      let hR' : PRNGBucketState T Sig K I :=
        if !(decide (esR.g.epoch P < healEpoch tL)) && esR.h.corrRoot.isNone
        then { esR.h with corrRoot := some (esR.g.epoch P, σ) } else esR.h
      have hpresL : ∀ {ep : ℕ} {r : Option Sig} {τ : Sig},
          resolveCorrRoot esL.h ep r = some τ → resolveCorrRoot hL' ep r = some τ := by
        intro ep r τ h
        dsimp only [hL']
        split_ifs with hc
        · exact resolveCorrRoot_set_of_isNone (by simp at hc; simp [hc.2]) h _
        · exact h
      have hpresR : ∀ {ep : ℕ} {r : Option Sig} {τ : Sig},
          resolveCorrRoot esR.h ep r = some τ → resolveCorrRoot hR' ep r = some τ := by
        intro ep r τ h
        dsimp only [hR']
        split_ifs with hc
        · exact resolveCorrRoot_set_of_isNone (by simp at hc; simp [hc.2]) h _
        · exact h
      have hcL_eq : hL'.cache = esL.h.cache := by dsimp only [hL']; split_ifs <;> rfl
      have hcR_eq : hR'.cache = esR.h.cache := by dsimp only [hR']; split_ifs <;> rfl
      have hlcL_eq : hL'.lc = esL.h.lc := by dsimp only [hL']; split_ifs <;> rfl
      have hlcR_eq : hR'.lc = esR.h.lc := by dsimp only [hR']; split_ifs <;> rfl
      have hsync_out : SyncStepMainDF Δcka tL par t
          { g := esL.g.afterCorr P, h := hL' } spL
          { g := esR.g.afterCorr P, h := hR' } spR := by
        refine ⟨rfl, rfl, hac_er, by rw [hlcL_eq, hlcR_eq]; exact hsync.lc_eq, hsync.vp_base,
          fun e' hgt => by rw [hcL_eq, hcR_eq]; exact hsync.cache_gt_max e' hgt,
          hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
          .allResolved ⟨hpl_ac, fun Q => ?_, fun e' he' => ?_⟩⟩
        · obtain ⟨τ, h1, h2⟩ := hm.vp_res Q
          exact ⟨τ, hpresL h1, hpresR h2⟩
        · rcases hm.cache_res e' he' with ⟨hn1, hn2⟩ | ⟨Tc, rL, rR, k, τ, hc1, hc2, hr1, hr2⟩
          · exact Or.inl ⟨by rw [hcL_eq]; exact hn1, by rw [hcR_eq]; exact hn2⟩
          · exact Or.inr ⟨Tc, rL, rR, k, τ, by rw [hcL_eq]; exact hc1,
              by rw [hcR_eq]; exact hc2, hpresL hr1, hpresR hr2⟩
      rw [hresL, hresR]
      simp only [hm.pl_true, Bool.not_true, Bool.false_and, Bool.false_eq_true]
      by_cases hmodL : (!(decide (esR.g.epoch P < healEpoch tL)) && esL.h.corrRoot.isNone) = true <;>
        by_cases hmodR : (!(decide (esR.g.epoch P < healEpoch tL)) && esR.h.corrRoot.isNone) = true <;>
        simp only [hmodL, hmodR, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure] <;>
        exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), by
          simpa only [hL', hR', hmodL, hmodR, Bool.false_eq_true, ↓reduceIte] using hsync_out,
          fun h => h⟩)
    · rcases hm with ⟨hpl, Q_corr, eC, σC, htH_eC, hmem_corr, hcrL, hcrR,
        hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩
      have hpl_ac : postLeak tL (esR.g.afterCorr P) = true := postLeak_afterCorr_mono hpl
      have hisNoneL : esL.h.corrRoot.isNone = false := by simp [hcrL]
      have hisNoneR : esR.h.corrRoot.isNone = false := by simp [hcrR]
      by_cases hP_Qc : P = Q_corr
      · subst P
        obtain ⟨σ, hresL, hresR⟩ := hres_Qc
        simp only [hresL, hresR, hpl, Bool.not_true, hisNoneL, hisNoneR,
          Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify, simulateQ_pure]
        refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
          ⟨rfl, rfl, hac_er, hsync.lc_eq, hsync.vp_base, hsync.cache_gt_max,
            hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
            .postCorr ⟨hpl_ac, Q_corr, eC, σC, htH_eC,
              by simp [SM.GameState.afterCorr, hmem_corr],
              hcrL, hcrR, hep_Qc, ⟨σ, hresL, hresR⟩, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩⟩,
          fun h => h⟩)
      · have hP_Qo : P = Q_corr.other := by
          cases P <;> cases Q_corr <;> first | exact False.elim (hP_Qc rfl) | rfl
        subst P
        have hep_eC1 : esR.g.epoch Q_corr.other = eC - 1 := by omega
        by_cases hne_t : eC - 1 ≠ t
        · have hroot_eq := hroot_Qo hne_t
          have hres_eq : resolveCorrRoot esL.h (esR.g.epoch Q_corr.other) (esL.g.st Q_corr.other).root =
              resolveCorrRoot esR.h (esR.g.epoch Q_corr.other) (esR.g.st Q_corr.other).root := by
            simp [resolveCorrRoot, hcrL, hcrR, hroot_eq]
          rw [hres_eq]
          cases hresR_opt : resolveCorrRoot esR.h (esR.g.epoch Q_corr.other) (esR.g.st Q_corr.other).root with
          | none =>
            simp only [hpl, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, abortE, StateT.run_bind, StateT.run_modify, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inl (Or.inl rfl))
          | some σ =>
            simp only [hpl, Bool.not_true, hisNoneL, hisNoneR,
              Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify, simulateQ_pure]
            refine AuthL11.LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ),
              ⟨rfl, rfl, hac_er, hsync.lc_eq, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch,
                .postCorr ⟨hpl_ac, Q_corr, eC, σC, htH_eC,
                  by simp [SM.GameState.afterCorr, hmem_corr],
                  hcrL, hcrR, hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩⟩,
              fun h => h⟩)
        · have heC1_eq_t : eC - 1 = t := Decidable.of_not_not hne_t
          cases hresL_opt : resolveCorrRoot esL.h (esR.g.epoch Q_corr.other) (esL.g.st Q_corr.other).root with
          | none =>
            simp only [hpl, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, abortE, StateT.run_bind, StateT.run_modify, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          | some σL =>
            simp only [hpl, Bool.not_true, hisNoneL,
              Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify, simulateQ_pure]
            refine AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inr (Or.inr (Or.inl ?_)))
            intro P'
            dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
            by_cases hP' : P' = Q_corr.other
            · subst P'
              refine ⟨esL.g.epoch Q_corr.other, List.mem_cons_self, ?_⟩
              rw [hep_eq, hep_eC1, heC1_eq_t]
              exact ltOpt_of_ge_healEpoch htLo
            · have hP'_Qc : P' = Q_corr := by
                cases P' <;> cases Q_corr <;> first | exact False.elim (hP' rfl) | rfl
              subst P'
              have hmemL : (Q_corr, eC) ∈ esL.g.corrs := by
                rw [AuthL11.eraseSt_corrs hsync.g_eq]; exact hmem_corr
              exact ⟨eC, List.mem_cons_of_mem _ hmemL, ltOpt_of_ge_healEpoch htH_eC⟩

/-! ### 5. Full Oracle Dispatcher `stepPMainDF`, `leComp_stepPMainDF`, and Initial `SyncMainDF` -/

/-- Step relation for `stepPMainDF` on `EState × Option ℕ` (`BSt`) and `PRFPRNG.GameState`. -/
private def StepRelMainDF (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {α : Type}
    (rL rR : (α × BSt Γ T Sig SS RS M E I K) × PRFPRNG.GameState Sig I K) : Prop :=
  DoomedMainDF Δcka tL t rL.1.2 ∨
  (rL.1.1 = rR.1.1 ∧ SyncMainDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2)

/-- Per-query `PRFPRNG`-simulated dispatcher for `redMainOut` (`implEDFPaperBucket` + `hooksPRNGBucketMain`). -/
private def stepPMainDF
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (st : BSt Γ T Sig SS RS M E I K)
    (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      BSt Γ T Sig SS RS M E I K) × PRFPRNG.GameState Sig I K) :=
  (simulateQ (AuthL11.pImpl prng)
    ((implEDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par m)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run st)).run sp

/-- Main deliverable (`N3a`): per-query coupling `LeComp` from `(hooksPRNGBucketMain ... t)`
with `spL.b = true` to `(hooksPRNGBucketMain ... (t + 1))` with `spR.b = false`, preserving
`esL.h.lc = esR.h.lc` and `WinEpInv` (or entering absorbing `DoomedMainDF`). -/
private theorem leComp_stepPMainDF
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stL stR : BSt Γ T Sig SS RS M E I K}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsf : SyncMainDF Δcka tL par t stL spL stR spR) :
    AuthL11.LeComp (StepRelMainDF Δcka tL par t)
      (stepPMainDF cka prng fs Δcka qep tL par t q stL spL)
      (stepPMainDF cka prng fs Δcka qep tL par (t + 1) q stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hwinEp_eq, hwin_inv, hsync⟩
  dsimp only at hwinEp_eq hsync
  subst hwinEp_eq
  have hwas_eq : esL.g.win = esR.g.win := AuthL11.eraseSt_win hsync.g_eq
  by_cases hwin0 : esR.g.win = true
  · have hwinL0 : esL.g.win = true := hwas_eq.trans hwin0
    have horL : (esL.abort || esL.g.win) = true := by simp [hwinL0]
    have horR : (esR.abort || esR.g.win) = true := by simp [hwin0]
    have hsf0 : SyncMainDF Δcka tL par t (esL, winEpL) spL (esR, winEpL) spR :=
      ⟨rfl, hwin_inv, hsync⟩
    unfold stepPMainDF implEDFPaperBucket withWinEpDF
    simp only [StateT.run_mk, StateT.run_bind, simulateQ_bind,
      StateT.run_pure, simulateQ_pure, hwinL0, hwin0, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
    · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
      exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, m, r_coins⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
        StateT.run_pure, simulateQ_pure, pure_bind]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, c⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, c⟩
      have hgL : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome ||
          !esL.g.safeInj (2 + Δcka)) = true := by simp [horL]
      have hgR : (esR.abort || esR.g.win || (esR.g.inTransit P.other c).isSome ||
          !esR.g.safeInj (2 + Δcka)) = true := by simp [horR]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
        StateT.run_bind, StateT.run_get, pure_bind, hgL, hgR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · have hgL : (esL.abort || esL.g.win || !esL.g.corrAllowedPaper P) = true := by simp [horL]
      have hgR : (esR.abort || esR.g.win || !esR.g.corrAllowedPaper P) = true := by simp [horR]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
        StateT.run_bind, StateT.run_get, pure_bind, hgL, hgR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases df with ⟨P, c, c'⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
  · have hwinR0 : esR.g.win = false := Bool.eq_false_iff.mpr hwin0
    have hwinL0 : esL.g.win = false := hwas_eq.trans hwinR0
    have hnone0 : winEpL = none := by
      rcases hwin_inv with ⟨_, hnone⟩ | ⟨hw, _⟩
      · exact hnone
      · dsimp only at hw; rw [hwinL0] at hw; cases hw
    subst hnone0
    have hsf_f : SyncMainDF Δcka tL par t (esL, none) spL (esR, none) spR :=
      ⟨rfl, Or.inl ⟨hwinL0, rfl⟩, hsync⟩
    unfold stepPMainDF implEDFPaperBucket withWinEpDF
    simp only [StateT.run_mk, StateT.run_bind, simulateQ_bind,
      StateT.run_pure, simulateQ_pure, hwinL0, hwinR0, Bool.not_false, Bool.true_and]
    rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
    · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc, hwinL0, hwinR0]
      exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf_f⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      refine (leComp_transmitEBucket_main_df cka prng fs Δcka qep tL par t htLo arg hsync).bind ?_
      rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
      rcases hrel with hab | ⟨hres, hsync', hnw⟩
      · exact AuthL11.LeComp.pure (Or.inl (Or.inl hab))
      · have hwR' : esR'.g.win = false := hnw hwinR0
        have hwL' : esL'.g.win = false := (AuthL11.eraseSt_win hsync'.g_eq).trans hwR'
        simp only [hwL', hwR', Bool.false_eq_true, ↓reduceIte]
        exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl, Or.inl ⟨hwL', rfl⟩, hsync'⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
        StateT.run_pure, simulateQ_pure, pure_bind, hwinL0, hwinR0, Bool.false_eq_true, ↓reduceIte]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf_f⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      refine (leComp_deliverE_main_df cka prng fs Δcka qep tL par t arg hsync).bind ?_
      rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
      rcases hrel with hab | ⟨hres, hsync', hnw⟩
      · exact AuthL11.LeComp.pure (Or.inl (Or.inl hab))
      · have hwR' : esR'.g.win = false := hnw hwinR0
        have hwL' : esL'.g.win = false := (AuthL11.eraseSt_win hsync'.g_eq).trans hwR'
        simp only [hwL', hwR', Bool.false_eq_true, ↓reduceIte]
        exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl, Or.inl ⟨hwL', rfl⟩, hsync'⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      refine (leComp_injectE_main_df cka prng fs Δcka qep tL par t arg hsync).bind ?_
      rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
      rcases hrel with hab | ⟨hres, hsync', hwin_adm⟩
      · exact AuthL11.LeComp.pure (Or.inl (Or.inl hab))
      · have hw_eq : esL'.g.win = esR'.g.win := AuthL11.eraseSt_win hsync'.g_eq
        by_cases hwR' : esR'.g.win = true
        · have hwL' : esL'.g.win = true := hw_eq.trans hwR'
          simp only [hwL', hwR', ↓reduceIte, dfQueryTargetEpoch]
          exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl,
            Or.inr ⟨hwL', arg.2.1.1, rfl, hwin_adm hwinR0 hwR'⟩, hsync'⟩)
        · have hwR'_f : esR'.g.win = false := Bool.eq_false_iff.mpr hwR'
          have hwL'_f : esL'.g.win = false := hw_eq.trans hwR'_f
          simp only [hwL'_f, hwR'_f, Bool.false_eq_true, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl, Or.inl ⟨hwL'_f, rfl⟩, hsync'⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      refine (leComp_corrEPaperBucket_main_df cka prng fs Δcka qep tL par t htLo P hsync).bind ?_
      rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
      rcases hrel with hdoom | ⟨hres, hsync', hnw⟩
      · simp only [dfQueryTargetEpoch, ite_self]
        exact AuthL11.LeComp.pure (Or.inl hdoom)
      · have hwR' : esR'.g.win = false := hnw hwinR0
        have hwL' : esL'.g.win = false := (AuthL11.eraseSt_win hsync'.g_eq).trans hwR'
        simp only [hwL', hwR', Bool.false_eq_true, ↓reduceIte]
        exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl, Or.inl ⟨hwL', rfl⟩, hsync'⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      refine (leComp_deliverForgeE_main_df cka prng fs Δcka qep tL par t df hsync).bind ?_
      rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
      rcases hrel with hab | ⟨hres, hsync', hwin_adm⟩
      · exact AuthL11.LeComp.pure (Or.inl (Or.inl hab))
      · have hw_eq : esL'.g.win = esR'.g.win := AuthL11.eraseSt_win hsync'.g_eq
        by_cases hwR' : esR'.g.win = true
        · have hwL' : esL'.g.win = true := hw_eq.trans hwR'
          simp only [hwL', hwR', ↓reduceIte, dfQueryTargetEpoch]
          exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl,
            Or.inr ⟨hwL', df.2.2.1.1, rfl, hwin_adm hwinR0 hwR'⟩, hsync'⟩)
        · have hwR'_f : esR'.g.win = false := Bool.eq_false_iff.mpr hwR'
          have hwL'_f : esL'.g.win = false := hw_eq.trans hwR'_f
          simp only [hwL'_f, hwR'_f, Bool.false_eq_true, ↓reduceIte]
          exact AuthL11.LeComp.pure (Or.inr ⟨hres, rfl, Or.inl ⟨hwL'_f, rfl⟩, hsync'⟩)


private theorem mem_support_liftM_hm_pImpl
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    {α : Type} (prng : PRFPRNG KR Sig I K)
    (m : PRFPRNG.AdversaryComp Sig I K α)
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {r : (α × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((liftPBucket (T := T) m).run h0)).run sp0)) :
    r.1.2 = h0 := by
  simp only [simulateQ_pImpl_liftPBucket, StateT.run_bind, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨⟨_, _⟩, _, rfl⟩
  rfl

private theorem support_lookupPRNGBucketF_lc_n3
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (ep : ℕ) (ik : I)
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {r : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((lookupPRNGBucketF ep ik).run h0)).run sp0)) :
    r.1.2.lc = h0.lc := by
  unfold lookupPRNGBucketF at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases hlk : (h0.fTable ep).lookup ik with
  | some k =>
    rw [hlk] at hr
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | none =>
    rw [hlk] at hr
    simp only [StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      bind_assoc] at hr
    rw [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨k, _, hr2⟩
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr2
    subst hr2; rfl

private theorem support_rootPRNGBucketHybrid_lc_n3
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (m t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig)
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {r : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((rootPRNGBucketHybrid prng Δbucket tL par m t0 pl ik0 σv0).run h0)).run sp0)) :
    r.1.2.lc = h0.lc := by
  unfold rootPRNGBucketHybrid at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hc1 : m < t0
  · simp only [hc1, ↓reduceIte] at hr
    cases hres : resolveCorrRoot h0 (t0 - 1) σv0 with
    | none =>
      rw [hres] at hr
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    | some σ =>
      rw [hres] at hr
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
  · simp only [hc1, ↓reduceIte] at hr
    by_cases hc2 : (pl || h0.corrRoot.isSome) = true
    · simp only [hc2, ↓reduceIte] at hr
      cases hres : resolveCorrRoot h0 (t0 - 1) σv0 with
      | some σ =>
        rw [hres] at hr
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      | none =>
        rw [hres] at hr
        simp only [StateT.run_bind, simulateQ_bind] at hr
        rw [MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨o, hq⟩, sp1⟩, hq_mem, hr2⟩
        have hhq := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq_mem
        dsimp only at hhq hr2; rw [hhq] at hr2
        cases o with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
          subst hr2; rfl
        | some σ =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr2
          subst hr2; rfl
    · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hr
      by_cases hc3 : t0 = m
      · subst hc3
        simp only [↓reduceIte] at hr
        by_cases hc3a : (tL.isSome && decide (t0 = healEpoch tL)) = true
        · simp only [hc3a, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
          rw [MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
          have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
          dsimp only at hhq1 hr2; rw [hhq1] at hr2
          cases o1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2; rfl
          | some kOut =>
            simp only [StateT.run_bind, simulateQ_bind] at hr2
            rw [MonadAttach.mem_support_bind] at hr2
            rcases hr2 with ⟨⟨⟨o2, hq2⟩, sp2⟩, hq2_mem, hr3⟩
            have hhq2 := mem_support_liftM_hm_pImpl prng _ h0 sp1 hq2_mem
            dsimp only at hhq2 hr3; rw [hhq2] at hr3
            cases o2 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr3
              subst hr3; rfl
            | some σOut =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr3
              subst hr3; rfl
        · simp only [hc3a, Bool.false_eq_true, ↓reduceIte] at hr
          by_cases hc3b : inStage2BucketGen Δbucket tL par t0 = true
          · simp only [hc3b, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
            have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
            dsimp only at hhq1 hr2; rw [hhq1] at hr2
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; rfl
            | some sk =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; rfl
          · simp only [hc3b, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
            have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
            dsimp only at hhq1 hr2; rw [hhq1] at hr2
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; rfl
            | some kOut =>
              simp only [StateT.run_bind, simulateQ_bind] at hr2
              rw [MonadAttach.mem_support_bind] at hr2
              rcases hr2 with ⟨⟨⟨o2, hq2⟩, sp2⟩, hq2_mem, hr3⟩
              have hhq2 := mem_support_liftM_hm_pImpl prng _ h0 sp1 hq2_mem
              dsimp only at hhq2 hr3; rw [hhq2] at hr3
              cases o2 with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr3
                subst hr3; rfl
              | some σOut =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr3
                subst hr3; rfl
      · simp only [hc3, ↓reduceIte] at hr
        by_cases hc4 : (!(decide (t0 < healEpoch tL))) = true
        · simp only [hc4, ↓reduceIte] at hr
          by_cases hc4a : (tL.isSome && decide (t0 = healEpoch tL)) = true
          · simp only [hc4a, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
            rw [MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
            have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
            dsimp only at hhq1 hr2; rw [hhq1] at hr2
            cases o1 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; rfl
            | some _ =>
              simp only [StateT.run_bind, simulateQ_bind,
                AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc] at hr2
              rw [MonadAttach.mem_support_bind] at hr2
              rcases hr2 with ⟨kSample, _, hr3⟩
              simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr3
              subst hr3; rfl
          · simp only [hc4a, Bool.false_eq_true, ↓reduceIte] at hr
            by_cases hc4b : inStage2BucketGen Δbucket tL par t0 = true
            · simp only [hc4b, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
              rw [MonadAttach.mem_support_bind] at hr
              rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
              have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
              dsimp only at hhq1 hr2; rw [hhq1] at hr2
              cases o1 with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2; rfl
              | some _ =>
                simp only [StateT.run_bind, simulateQ_bind] at hr2
                rw [MonadAttach.mem_support_bind] at hr2
                rcases hr2 with ⟨rl, hrl1, hr3⟩
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr3
                subst hr3
                exact support_lookupPRNGBucketF_lc_n3 prng t0 ik0 h0 sp1 hrl1
            · simp only [hc4b, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
              rw [MonadAttach.mem_support_bind] at hr
              rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
              have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
              dsimp only at hhq1 hr2; rw [hhq1] at hr2
              cases o1 with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2; rfl
              | some _ =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2; rfl
        · simp only [hc4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
          rw [MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨o1, hq1⟩, sp1⟩, hq1_mem, hr2⟩
          have hhq1 := mem_support_liftM_hm_pImpl prng _ h0 sp0 hq1_mem
          dsimp only at hhq1 hr2; rw [hhq1] at hr2
          cases o1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; rfl
          | some kOut =>
            simp only [StateT.run_bind, simulateQ_bind] at hr2
            rw [MonadAttach.mem_support_bind] at hr2
            rcases hr2 with ⟨⟨⟨o2, hq2⟩, sp2⟩, hq2_mem, hr3⟩
            have hhq2 := mem_support_liftM_hm_pImpl prng _ h0 sp1 hq2_mem
            dsimp only at hhq2 hr3; rw [hhq2] at hr3
            cases o2 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr3
              subst hr3; rfl
            | some σOut =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr3
              subst hr3; rfl

private theorem support_vSend_main_lc_pres [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (msg : M) (r0 : Option CCoins)
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {e0 : ℕ} (hlc : h.lc = some e0)
    {r : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGBucketState T Sig K I) ×
         PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((vSend (hooksPRNGBucketMain cka prng fs Δcka qep tL par m) ctx P vp msg none r0).run h)).run sp)) :
    r.1.2.lc = some e0 := by
  unfold vSend at hr
  dsimp only at hr
  by_cases hs : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
    rw [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨o, h1⟩, sp1⟩, hrs1, hr2⟩
    have hss : h1.lc = some e0 := by
      unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen at hrs1
      dsimp only at hrs1
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hlc, Option.isNone_some,
        Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrs1
      have hbody : ∀ (coins : CCoins)
          (hrs2 : ((o, h1), sp1) ∈ support ((simulateQ (AuthL11.pImpl prng)
            ((do
              let c := cka.send vp.γ coins
              match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par m (vp.tcur + 1)
                  (postLeak tL ctx) c.2.2 vp.root with
              | none => return none
              | some (σ', kVal) =>
                modify fun s : PRNGBucketState T Sig K I =>
                  { s with cache := Function.update s.cache (vp.tcur + 1) (some (c.2.1, σ', kVal)) }
                return some (c.1, c.2.1, σ', fs.initSender kVal)).run h)).run sp)),
          h1.lc = some e0 := by
        intro coins hrs2
        simp only [StateT.run_bind, simulateQ_bind] at hrs2
        rw [MonadAttach.mem_support_bind] at hrs2
        rcases hrs2 with ⟨⟨⟨oroot, hroot⟩, sproot⟩, hrr1, hrb2⟩
        have hrlc : hroot.lc = h.lc :=
          support_rootPRNGBucketHybrid_lc_n3 prng (3 + Δcka) tL par m (vp.tcur + 1)
            (postLeak tL ctx) (cka.send vp.γ coins).2.2 vp.root h sp hrr1
        cases oroot with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hrb2
          have hh1 : h1 = hroot := (Prod.mk.inj (Prod.mk.inj hrb2).1).2
          exact (congrArg PRNGBucketState.lc hh1).trans (hrlc.trans hlc)
        | some sk =>
          rcases sk with ⟨σ', kVal⟩
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hrb2
          have hh1 : h1 =
              { hroot with cache := Function.update hroot.cache (vp.tcur + 1) (some ((cka.send vp.γ coins).2.1, σ', kVal)) } :=
            (Prod.mk.inj (Prod.mk.inj hrb2).1).2
          rw [hh1]
          exact hrlc.trans hlc
      cases r0 with
      | some coins =>
        exact hbody coins hrs1
      | none =>
        rw [StateT.run_bind, simulateQ_bind, StateT.run_bind,
          AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc, MonadAttach.mem_support_bind] at hrs1
        rcases hrs1 with ⟨coins, _, hrs2⟩
        rw [pure_bind] at hrs2
        exact hbody coins hrs2
    cases o with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr2
      subst hr2; exact hss
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss'⟩
      simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
        pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
      subst hr2; exact hss
  · simp only [Bool.eq_false_iff.mpr hs, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr
    cases hvs : vp.vS with
    | none =>
      rw [hvs] at hr
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hlc
    | some ss =>
      rw [hvs] at hr
      simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
        pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hlc

private theorem support_vRecv_main_props [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (g : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (c : Header T × E) (rec : Option (SM.Record M (Header T × E)))
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {r : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGBucketState T Sig K I) ×
         PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par m) g P vp c rec).run h)).run sp)) :
    r.1.2 = h ∧
      ∀ vp' t' i' m', r.1.1 = some (some (vp', t', i', m')) →
        t' = c.1.1 ∧ vp'.id = vp.id ∧ vp'.tcur = max vp.tcur c.1.1 := by
  unfold vRecv at hr
  dsimp only at hr
  by_cases hg : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hn : c.1.1 = vp.tcur + 1
    · simp only [hn, ↓reduceIte] at hr
      cases htn : c.1.2 with
      | none =>
        rw [htn] at hr
        simp only [] at hr
        subst hr; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
      | some tn0 =>
        rw [htn] at hr
        simp only [StateT.run_bind, simulateQ_bind] at hr
        rw [MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨sr, h1⟩, sp1⟩, hsr, hr2⟩
        have hh1 : h1 = h := by
          unfold hooksPRNGBucketMain hooksPRNGBucketMainGen at hsr
          dsimp only at hsr
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at hsr
          cases hc : h.cache (vp.tcur + 1) with
          | none =>
            rw [hc] at hsr; dsimp only at hsr
            split_ifs at hsr <;>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hsr <;>
              exact (Prod.mk.inj (Prod.mk.inj hsr).1).2
          | some entry =>
            rcases entry with ⟨tCached, σc, kVal⟩
            rw [hc] at hsr; dsimp only at hsr
            by_cases hTc : tCached = tn0
            · subst hTc
              simp only [↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hsr
              exact (Prod.mk.inj (Prod.mk.inj hsr).1).2
            · simp only [hTc, ↓reduceIte] at hsr
              split_ifs at hsr <;>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hsr <;>
                exact (Prod.mk.inj (Prod.mk.inj hsr).1).2
        subst hh1
        cases sr with
        | none =>
          simp only [] at hr2
          subst hr2; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
        | some opt_sr =>
          cases opt_sr with
          | none =>
            simp only [] at hr2
            subst hr2; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
          | some gsr =>
            rcases gsr with ⟨γ', σ', rs⟩
            simp only [Function.update_self, hooksPRNGBucketMain, hooksPRNGBucketMainGen,
              hooksPRNGBucketHybridGen, pure_bind] at hr2
            cases hfs : fs.receive rs c.1 c.2 with
            | none =>
              rw [hfs] at hr2
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
            | some out =>
              rcases out with ⟨rs', i', m'⟩
              rw [hfs] at hr2
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2
              refine ⟨rfl, fun vp' t' i1 m1 h0 => ?_⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h0
              rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨hn.symm, rfl, by simp [hn]⟩
    · simp only [hn, ↓reduceIte, pure_bind] at hr
      have hle_tcur : c.1.1 ≤ vp.tcur := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
        omega
      cases hvr : vp.vR c.1.1 with
      | none =>
        rw [hvr] at hr
        simp only [StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
      | some rs =>
        rw [hvr] at hr
        simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
          pure_bind] at hr
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          rw [hfs] at hr
          simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact ⟨rfl, by intro _ _ _ _ h0; cases h0⟩
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          rw [hfs] at hr
          simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨rfl, fun vp' t' i1 m1 h0 => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h0
          rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, (Nat.max_eq_left hle_tcur).symm⟩

private theorem support_reveal_main_lc_pres [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    {e0 : ℕ} (hlc : h.lc = some e0)
    {r : (Option (PartyState Γ T Sig SS RS) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      (((hooksPRNGBucketMain cka prng fs Δcka qep tL par m).reveal ctx P vp).run h)).run sp)) :
    r.1.1 = none ∨ r.1.2.lc = some e0 := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen at hr
  dsimp only at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases hres : resolveCorrRoot h vp.tcur vp.root with
  | some σ =>
    rw [hres] at hr; dsimp only at hr
    by_cases hc1 : (!(decide (vp.tcur < healEpoch tL)) && h.corrRoot.isNone) = true
    · simp only [hc1, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
        hlc, Option.isNone_some, Bool.and_false, Bool.false_and, Bool.false_eq_true,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inr rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte,
        hlc, Option.isNone_some, Bool.and_false, Bool.false_and,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inr hlc
  | none =>
    rw [hres] at hr; dsimp only at hr
    by_cases hc1 : ((!postLeak tL ctx && h.corrRoot.isNone && !(decide (vp.tcur < healEpoch tL))) &&
        (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
    · simp only [hc1, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr
      rw [MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨⟨⟨o, hq⟩, sp1⟩, hq_mem, hr2⟩
      have hhq := mem_support_liftM_hm_pImpl prng _ h sp hq_mem
      dsimp only at hhq hr2; rw [hhq] at hr2
      cases o with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr2
        subst hr2; exact Or.inl rfl
      | some σOut =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind, hlc, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
        subst hr2; exact Or.inr rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl rfl

private theorem epMgmt_corrs_leaks_sub_df {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    s₁.win = s.win ∧ s.corrs ⊆ s₁.corrs ∧ s.leaks ⊆ s₁.leaks := by
  unfold GameState.epMgmt at hep
  split_ifs at hep
  all_goals
    simp only [Option.some.injEq] at hep
    subst hep
  · exact ⟨rfl, List.Subset.refl _, fun _ hx => List.mem_cons_of_mem _ hx⟩
  · exact ⟨rfl, List.Subset.refl _, List.Subset.refl _⟩
  · exact ⟨rfl, List.Subset.refl _, List.Subset.refl _⟩

private theorem run_commitE_mainDF
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketMain cka prng fs Δcka qep tL par m) s P old new pos).run es =
      pure (some (s.accept P new pos), es) :=
  run_commitE_PRNGBucket cka prng fs Δcka qep tL par m s P old new pos es

private theorem stepPMainDF_state_eq_of_abort_or_win
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (haw : es.abort = true ∨ es.g.win = true) :
    ∀ r ∈ support (stepPMainDF cka prng fs Δcka qep tL par m q (es, winEp) sp),
      r.1.2 = (es, winEp) := by
  intro r hr
  have hor : (es.abort || es.g.win) = true := by rcases haw with h | h <;> simp [h]
  have hno_flip : (!es.g.win && es.g.win) = false := by cases es.g.win <;> simp
  unfold stepPMainDF implEDFPaperBucket withWinEpDF at hr
  simp only [StateT.run_mk, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r0, hr0, hr_end⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_end
  subst hr_end
  have hes_eq : r0.1.2 = es := by
    rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
    · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr0
      rcases hr0 with ⟨_, _, rfl⟩; rfl
    · rcases arg with ⟨P, msg, r_coins⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
        StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    · simp [implEDFPaperBucketRaw, challEBucket] at hr0
      subst hr0; rfl
    · rcases arg with ⟨P, c⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    · rcases arg with ⟨P, c⟩
      have hg : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
          !es.g.safeInj (2 + Δcka)) = true := by simp [hor]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
        StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    · have hg : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true := by simp [hor]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
        StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    · rcases df with ⟨P, c, c'⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
  rw [hes_eq]
  simp [hno_flip]

private theorem mem_support_liftH_pImpl
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    {α : Type} (prng : PRFPRNG KR Sig I K)
    (hm : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    {r : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
         PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((liftH hm).run es)).run sp)) :
    r.1.2.g = es.g ∧ r.1.2.abort = es.abort ∧
    ((r.1.1, r.1.2.h), r.2) ∈ support ((simulateQ (AuthL11.pImpl prng) (hm.run es.h)).run sp) := by
  rw [AuthL11.run_liftH] at hr
  simp only [simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨⟨⟨a, h1⟩, sp1⟩, hmem, rfl⟩
  exact ⟨rfl, rfl, hmem⟩

private theorem stepPMainDF_raw_monotone
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hab_f : es.abort = false) (hwin_f : es.g.win = false) :
    ∀ r0 ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par m)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run es)).run sp),
      r0.1.2.abort = true ∨
      ((r0.1.2.g.win = false ∨
        ∃ tWin, dfQueryTargetEpoch (fun c : Header T × E => c.1.1) q = some tWin ∧
          lastLeakGuessAdmissible (3 + Δcka) tL tWin = true) ∧
        es.g.corrs ⊆ r0.1.2.g.corrs ∧
        es.g.leaks ⊆ r0.1.2.g.leaks ∧
        (∀ e0, es.h.lc = some e0 → r0.1.2.h.lc = some e0)) := by
  intro r0 hr0
  have habw_f : (es.abort || es.g.win) = false := by simp [hab_f, hwin_f]
  rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
  · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr0
    rcases hr0 with ⟨_, _, rfl⟩
    exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
  · rcases arg with ⟨P, msg, r_coins⟩
    simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
      StateT.run_bind, StateT.run_get, pure_bind, habw_f, Bool.false_eq_true, ↓reduceIte] at hr0
    cases hep : es.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
    | none =>
      simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr0
      subst hr0
      exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
    | some s₁ =>
      obtain ⟨hs₁_win, hsub_c, hsub_l⟩ := epMgmt_corrs_leaks_sub_df hep
      simp only [hep, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr0
      rcases hr0 with ⟨⟨⟨res_vs, es1⟩, sp2⟩, hvs_lift, hr_rest⟩
      obtain ⟨_, _, hvs⟩ := mem_support_liftH_pImpl prng _ es sp hvs_lift
      cases res_vs with
      | none =>
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
        subst hr_rest
        exact Or.inl rfl
      | some vc =>
        rcases vc with ⟨vp', ct⟩
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
        subst hr_rest
        refine Or.inr ⟨Or.inl ?_, ?_, ?_, fun e0 hlc => ?_⟩
        · simp [SM.GameState.record, hs₁_win, hwin_f]
        · simpa [SM.GameState.record] using hsub_c
        · simpa [SM.GameState.record] using hsub_l
        · exact support_vSend_main_lc_pres cka prng fs Δcka qep tL par m
            s₁ P (s₁.st P) msg r_coins es.h sp hlc hvs
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
    subst hr0
    exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
  · rcases arg with ⟨P, c⟩
    simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
      StateT.run_bind, StateT.run_get, pure_bind, habw_f, Bool.false_eq_true, ↓reduceIte] at hr0
    cases htr : es.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr0
      subst hr0
      exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
    | some rec =>
      simp only [htr, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr0
      rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp2⟩, hvr_lift, hr_d2⟩
      obtain ⟨hes1_g, hes1_ab, hvr⟩ := mem_support_liftH_pImpl prng _ es sp hvr_lift
      obtain ⟨hh1_eq, _⟩ := support_vRecv_main_props cka prng fs Δcka qep tL par m
        es.g P (es.g.st P) c (some rec) es.h sp hvr
      have hes1_eq : es1 = es := by
        cases es1; cases es
        dsimp only at hes1_g hes1_ab hh1_eq
        subst hes1_g hes1_ab hh1_eq; rfl
      rw [hes1_eq] at hr_d2
      cases res_vr with
      | none =>
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_d2
        subst hr_d2; exact Or.inl rfl
      | some opt_vr =>
        cases opt_vr with
        | none =>
          simp only [bucketAuthCfg] at hr_d2
          subst hr_d2
          exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
        | some vtim =>
          rcases vtim with ⟨vp', t', i', m'⟩
          simp only [pure_bind, StateT.run_bind, run_commitE_mainDF,
            StateT.run_modify, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr_d2
          subst hr_d2
          exact Or.inr ⟨Or.inl (by simp [bucketAuthCfg, SM.GameState.accept, SM.GameState.delete, hwin_f]),
            by simp [bucketAuthCfg, SM.GameState.accept, SM.GameState.delete],
            by simp [bucketAuthCfg, SM.GameState.accept, SM.GameState.delete], fun _ h => h⟩
  · rcases arg with ⟨P, c⟩
    simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
      StateT.run_bind, StateT.run_get, pure_bind] at hr0
    by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !es.g.safeInj (2 + Δcka)) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr0
      subst hr0
      exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        simulateQ_bind, MonadAttach.mem_support_bind] at hr0
      rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp2⟩, hvr_lift, hr_i2⟩
      obtain ⟨hes1_g, hes1_ab, hvr⟩ := mem_support_liftH_pImpl prng _ es sp hvr_lift
      obtain ⟨hh1_eq, hvr_some⟩ := support_vRecv_main_props cka prng fs Δcka qep tL par m
        es.g P (es.g.st P) c none es.h sp hvr
      have hes1_eq : es1 = es := by
        cases es1; cases es
        dsimp only at hes1_g hes1_ab hh1_eq
        subst hes1_g hes1_ab hh1_eq; rfl
      rw [hes1_eq] at hr_i2
      cases res_vr with
      | none =>
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_i2
        subst hr_i2; exact Or.inl rfl
      | some opt_vr =>
        cases opt_vr with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr_i2
          subst hr_i2
          exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
        | some vtim =>
          rcases vtim with ⟨vp', t', i', m'⟩
          obtain ⟨ht'_eq, _, _⟩ := hvr_some vp' t' i' m' rfl
          subst ht'_eq
          by_cases hqep : qep + 1 < c.1.1
          · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hr_i2
            subst hr_i2
            exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
          · simp only [hqep, ↓reduceIte] at hr_i2
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_mainDF, pure_bind,
                StateT.run_modify, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr_i2
              subst hr_i2
              exact Or.inr ⟨Or.inl (by simp [SM.GameState.accept, SM.GameState.delete, hwin_f]),
                by simp [SM.GameState.accept, SM.GameState.delete],
                by simp [SM.GameState.accept, SM.GameState.delete], fun _ h => h⟩
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_i2
              by_cases hin : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c.1.1 = true
              · simp only [hin, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_i2
                subst hr_i2
                have hadm3 : lastLeakGuessAdmissible (3 + Δcka) tL c.1.1 = true := by
                  simp only [bucketAuthCfg, inStage2Bucket, Bool.and_eq_true] at hin
                  exact hin.1
                exact Or.inr ⟨Or.inr ⟨c.1.1, rfl, hadm3⟩,
                  List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
              · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                  support_pure, Set.mem_singleton_iff] at hr_i2
                subst hr_i2
                exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
      StateT.run_bind, StateT.run_get, pure_bind] at hr0
    by_cases hguard : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr0
      subst hr0
      exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        simulateQ_bind, MonadAttach.mem_support_bind] at hr0
      rcases hr0 with ⟨⟨⟨res_rv, es1⟩, sp2⟩, hrv_lift, hr_c2⟩
      obtain ⟨_, _, hrv⟩ := mem_support_liftH_pImpl prng _ es sp hrv_lift
      cases res_rv with
      | none =>
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_c2
        subst hr_c2; exact Or.inl rfl
      | some stOut =>
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_c2
        subst hr_c2
        refine Or.inr ⟨Or.inl (by simp [SM.GameState.afterCorr, SM.GameState.leak, hwin_f]),
          by simp [SM.GameState.afterCorr, SM.GameState.leak],
          by simp [SM.GameState.afterCorr, SM.GameState.leak], fun e0 hlc => ?_⟩
        rcases support_reveal_main_lc_pres cka prng fs Δcka qep tL par m
          es.g P (es.g.st P) es.h sp hlc hrv with hnone | hlc'
        · cases hnone
        · exact hlc'
  · rcases df with ⟨P, c, c'⟩
    simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
      StateT.run_bind, StateT.run_get, pure_bind, habw_f, Bool.false_eq_true, ↓reduceIte] at hr0
    cases htr : es.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr0
      subst hr0
      exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
    | some rec =>
      simp only [htr] at hr0
      by_cases hrej : ((es.g.inTransit P.other c').isSome || es.g.comp.contains rec.pos ||
          (c.1 != c'.1)) = true
      · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr0
        subst hr0
        exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
      · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          simulateQ_bind, MonadAttach.mem_support_bind] at hr0
        rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp2⟩, hvr_lift, hr_df2⟩
        obtain ⟨hes1_g, hes1_ab, hvr⟩ := mem_support_liftH_pImpl prng _ es sp hvr_lift
        obtain ⟨hh1_eq, hvr_some⟩ := support_vRecv_main_props cka prng fs Δcka qep tL par m
          es.g P (es.g.st P) c' none es.h sp hvr
        have hes1_eq : es1 = es := by
          cases es1; cases es
          dsimp only at hes1_g hes1_ab hh1_eq
          subst hes1_g hes1_ab hh1_eq; rfl
        rw [hes1_eq] at hr_df2
        cases res_vr with
        | none =>
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_df2
          subst hr_df2; exact Or.inl rfl
        | some opt_vr =>
          cases opt_vr with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr_df2
            subst hr_df2
            exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
          | some vtim =>
            rcases vtim with ⟨vp', t', i', m'⟩
            obtain ⟨ht'_eq, _, _⟩ := hvr_some vp' t' i' m' rfl
            subst ht'_eq
            by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != rec.pos.epoch)) = true
            · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr_df2
              subst hr_df2
              exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
            · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte] at hr_df2
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
              · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_mainDF, pure_bind,
                  StateT.run_modify, StateT.run_pure, simulateQ_pure,
                  support_pure, Set.mem_singleton_iff] at hr_df2
                subst hr_df2
                exact Or.inr ⟨Or.inl (by simp [SM.GameState.accept, SM.GameState.delete, hwin_f]),
                  by simp [SM.GameState.accept, SM.GameState.delete],
                  by simp [SM.GameState.accept, SM.GameState.delete], fun _ h => h⟩
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_df2
                by_cases hin : (bucketAuthCfg (Msg := M) Δcka tL par).injectFull c'.1.1 = true
                · simp only [hin, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                    StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_df2
                  subst hr_df2
                  have hadm3 : lastLeakGuessAdmissible (3 + Δcka) tL c'.1.1 = true := by
                    simp only [bucketAuthCfg, inStage2Bucket, Bool.and_eq_true] at hin
                    exact hin.1
                  exact Or.inr ⟨Or.inr ⟨c'.1.1, rfl, hadm3⟩,
                    List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩
                · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hr_df2
                  subst hr_df2
                  exact Or.inr ⟨Or.inl hwin_f, List.Subset.refl _, List.Subset.refl _, fun _ h => h⟩

private theorem stepPMainDF_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m t : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (st : BSt Γ T Sig SS RS M E I K)
    (sp : PRFPRNG.GameState Sig I K)
    (hd : DoomedMainDF Δcka tL t st) :
    ∀ r ∈ support (stepPMainDF cka prng fs Δcka qep tL par m q st sp),
      DoomedMainDF Δcka tL t r.1.2 := by
  intro r hr
  rcases st with ⟨es, winEp⟩
  by_cases haw : es.abort = true ∨ es.g.win = true
  · rw [stepPMainDF_state_eq_of_abort_or_win cka prng fs Δcka qep tL par m q es winEp sp haw r hr]
    exact hd
  · have hab_f : es.abort = false := by cases h : es.abort <;> simp_all
    have hwin_f : es.g.win = false := by cases h : es.g.win <;> simp_all
    unfold stepPMainDF implEDFPaperBucket withWinEpDF at hr
    simp only [StateT.run_mk, StateT.run_bind, simulateQ_bind, hwin_f, Bool.not_false,
      Bool.true_and, MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨u0, es'⟩, sp1⟩, hr0, hr_end⟩
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_end
    subst hr_end
    rcases stepPMainDF_raw_monotone cka prng fs Δcka qep tL par m q es sp hab_f hwin_f
        ((u0, es'), sp1) hr0 with hab' | ⟨hwin_post, hsub_c, hsub_l, hlc_pres⟩
    · exact Or.inl hab'
    · rcases hd with hab0 | ⟨e0, hlc0, hlt0⟩ | hcorrs0 | ⟨hwinInv0, l, hl_mem, hlt, hlt_win⟩
      · dsimp only at hab0; rw [hab_f] at hab0; cases hab0
      · exact Or.inr (Or.inl ⟨e0, hlc_pres e0 hlc0, hlt0⟩)
      · exact Or.inr (Or.inr (Or.inl fun P =>
          let ⟨e, he_mem, he_lt⟩ := hcorrs0 P
          ⟨e, hsub_c he_mem, he_lt⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨?_, l, hsub_l hl_mem, hlt, hlt_win⟩))
        rcases hwinInv0 with ⟨_, hnone0⟩ | ⟨hw_true, _⟩
        · dsimp only at hnone0; subst hnone0
          by_cases hw' : es'.g.win = true
          · rcases hwin_post with hwf | ⟨tWin, htarget, hadm3⟩
            · rw [hw'] at hwf; cases hwf
            · simp only [hw', ↓reduceIte]
              exact Or.inr ⟨hw', tWin, htarget, hadm3⟩
          · have hwf : es'.g.win = false := Bool.eq_false_iff.mpr hw'
            simp only [hwf, Bool.false_eq_true, ↓reduceIte]
            exact Or.inl ⟨hwf, rfl⟩
        · dsimp only at hw_true; rw [hwin_f] at hw_true; cases hw_true

private def runPMainDF
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m tOut : ℕ)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (st : BSt Γ T Sig SS RS M E I K)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (AuthL11.pImpl prng)
    ((simulateQ (implEDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par m)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) oa).run st)).run sp
  pure (authOutBucketPaperAt (2 + Δcka) tL tOut r.1.2)

private theorem runPMainDF_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m tOut : ℕ) (b : Bool)
    (st : BSt Γ T Sig SS RS M E I K)
    (sp : PRFPRNG.GameState Sig I K) :
    runPMainDF cka prng fs Δcka qep tL par m tOut (pure b) st sp =
      pure (authOutBucketPaperAt (2 + Δcka) tL tOut st) := by
  simp [runPMainDF]

private theorem runPMainDF_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m tOut : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (st : BSt Γ T Sig SS RS M E I K)
    (sp : PRFPRNG.GameState Sig I K) :
    runPMainDF cka prng fs Δcka qep tL par m tOut (liftM (OracleSpec.query q) >>= k) st sp =
      stepPMainDF cka prng fs Δcka qep tL par m q st sp >>= fun r =>
        runPMainDF cka prng fs Δcka qep tL par m tOut (k r.1.1) r.1.2 r.2 := by
  simp [runPMainDF, stepPMainDF, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPMainDF_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (m t : ℕ)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {st : BSt Γ T Sig SS RS M E I K}
    {sp : PRFPRNG.GameState Sig I K}
    (hd : DoomedMainDF Δcka tL t st) :
    𝒟[runPMainDF cka prng fs Δcka qep tL par m (t + 1) oa st sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing st sp with
  | pure b' =>
    rw [runPMainDF_pure, authOutBucketPaperAt_eq_false_of_doomedMainDF hd]
    simp
  | query_bind q k ih =>
    rw [runPMainDF_query_bind]
    exact AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPMainDF_doomed cka prng fs Δcka qep tL par m t q st sp hd r hr)

private theorem runPMainDF_le_succ
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stL stR : BSt Γ T Sig SS RS M E I K}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncMainDF Δcka tL par t stL spL stR spR) :
    𝒟[runPMainDF cka prng fs Δcka qep tL par t (t + 1) oa stL spL] {true} ≤
      𝒟[runPMainDF cka prng fs Δcka qep tL par (t + 1) (t + 1) oa stR spR] {true} := by
  induction oa using OracleComp.inductionOn generalizing stL stR spL spR with
  | pure b' =>
    rw [runPMainDF_pure, runPMainDF_pure]
    rcases stL with ⟨esL, winEpL⟩
    rcases stR with ⟨esR, winEpR⟩
    rcases hsync with ⟨hwinEp, _, hraw⟩
    dsimp only at hwinEp hraw
    subst hwinEp
    have hout : authOutBucketPaperAt (2 + Δcka) tL (t + 1) (esL, winEpL) =
        authOutBucketPaperAt (2 + Δcka) tL (t + 1) (esR, winEpL) := by
      unfold authOutBucketPaperAt
      rw [hraw.lc_eq]
      congr 1
      cases winEpL with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketPaper, authOutBucket, authOut]
        rw [hraw.abortL, hraw.abortR, AuthL11.eraseSt_win hraw.g_eq,
          AuthL11.eraseSt_authOK hraw.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPMainDF_query_bind, runPMainDF_query_bind]
    refine leComp_stepPMainDF cka prng fs Δcka qep tL par t htH q hsync _ _ ?_
    rintro ⟨⟨uL, stL'⟩, spL'⟩ ⟨⟨uR, stR'⟩, spR'⟩ (hd | ⟨hu, hsync'⟩)
    · rw [runPMainDF_doomed cka prng fs Δcka qep tL par t t (k uL) hd]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uL hsync'

private theorem leComp_with_support {α β : Type} {R : α → β → Prop}
    {x : ProbComp α} {y : ProbComp β}
    (h : AuthL11.LeComp R x y) :
    AuthL11.LeComp (fun a b => a ∈ support x ∧ b ∈ support y ∧ R a b) x y := by
  classical
  intro F₁ F₂ hF
  let F₁' : α → ProbComp Bool := fun a => if a ∈ support x then F₁ a else pure false
  let F₂' : β → ProbComp Bool := fun b => if b ∈ support y then F₂ b else pure true
  rw [AuthL11.evalDist_bind_congr_true x F₁ F₁' (fun a ha => by simp only [F₁', ha, ↓reduceIte]),
      AuthL11.evalDist_bind_congr_true y F₂ F₂' (fun b hb => by simp only [F₂', hb, ↓reduceIte])]
  refine h F₁' F₂' fun a b hr => ?_
  dsimp only [F₁', F₂']
  by_cases ha : a ∈ support x
  · by_cases hb : b ∈ support y
    · simp only [ha, hb, ↓reduceIte]
      exact hF a b ⟨ha, hb, hr⟩
    · simp only [ha, hb, ↓reduceIte]
      simp [MeasureTheory.prob_le_one]
  · simp [ha]

/-- T1.4 (L; coupling): ideal-at-`t` vs real-at-`t+1` `Main` with the SAME gate `t + 1`
(port of `BucketPRNGAuthHop2bMain.runPMain_le_succ` / ForgedHdr `runPBucketForgedHdr_le_succ`
to the DF paper engine; the coupling must also preserve `h.lc`). -/
private theorem T1_gatedSucc_le [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) (htH : healEpoch tL ≤ t) (ht : t < qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redMainOut cka prng fs lam Δcka qep tL par t
        (authOutBucketPaperAt (2 + Δcka) tL (t + 1)) A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (t + 1) A)] {true} := by
  let _ := ht
  rw [T1_main_eq_out cka prng fs lam Δcka qep tL par (t + 1) A]
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  unfold PRFPRNG.branch redMainOut engRunDFPaperBucket initPRNGBucketHybrid
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    AuthL11.simulateQ_pImpl_run_lift_sampleT, pure_bind]
  refine AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  refine (leComp_with_support (leComp_rootInit_step (T := T) (Δbucket := 3 + Δcka) (par := par)
    prng tL t lam (prng.init kr) htH)) _ _ ?_
  rintro ⟨⟨resL, hL0⟩, spL0⟩ ⟨⟨resR, hR0⟩, spR0⟩ ⟨hmemL, hmemR, hrel0⟩
  have hlcL0 : hL0.lc = none :=
    support_rootPRNGBucketHybrid_lc_n3 prng (3 + Δcka) tL par t 0 false lam none
      {} { σ := prng.init kr, b := true } hmemL
  have hlcR0 : hR0.lc = none :=
    support_rootPRNGBucketHybrid_lc_n3 prng (3 + Δcka) tL par (t + 1) 0 false lam none
      {} { σ := prng.init kr, b := false } hmemR
  rcases hrel0 with hnone |
    ⟨rL0, rR0, kVal, hresL, hresR, hr0, hcL0, hcR0, hcrL0, hcrR0, hft0, htab0,
      hbL0, hbR0, hσ0, hprfR0, hprng0, hcorr0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hresL hresR
    subst hresL hresR
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc, Function.comp_apply]
    refine runPMainDF_le_succ cka prng fs Δcka qep tL par t htH A
      ⟨rfl, Or.inl ⟨rfl, rfl⟩,
        ⟨rfl, rfl, rfl, hlcL0.trans hlcR0.symm,
          ?_, ?_, ?_, ?_, ?_,
          .pre ⟨rfl, hcrL0, hcrR0, hlcL0, ?_, ?_, hft0, htab0, hbL0, hbR0,
            by simpa using hσ0, fun _ => hprfR0, hprng0,
            fun hle _ => hcorr0 (by simpa using hle)⟩⟩⟩
    · intro P
      cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · intro e' _; rw [hcL0, hcR0]; exact ⟨rfl, rfl⟩
    · intro P; simp
    · intro P hlt; simp at hlt
    · intro r hr; cases hr
    · intro P; cases P <;> exact hr0
    · intro e'; rw [hcL0, hcR0]; exact Or.inl ⟨rfl, rfl⟩

private theorem T1_step [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t) (ht : t < qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A)] {true} ≤
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true} +
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (t + 1) A)] {true} := by
  rw [T1_main_eq_out cka prng fs lam Δcka qep tL par t A]
  refine (T1_branch_out_le_add cka prng fs lam Δcka qep tL par t true _
    (fun st => authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = some t))
    (authOutBucketPaperAt (2 + Δcka) tL (t + 1)) (fun st h => ?_) A).trans
    (add_le_add (T1_lcSlice_le_local cka prng fs lam Δcka qep tL par t htH ht A)
      (T1_gatedSucc_le cka prng fs lam Δcka qep tL par t htH ht A))
  rw [T1_gate_split] at h
  simpa [Bool.or_eq_true] using h

private theorem T1_sum_lcEq_add_none_le [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (a b : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    (∑ t ∈ Finset.Ico a b,
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true}) +
    𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par none A] {true} ≤
      𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} :=
  sum_localAuthDFPaperBucketMainLcEq_add_none_le cka prng fs lam Δcka qep tL par a b A

private theorem T1_telescope [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (B : ℕ → PRFPRNG.Adversary Sig I K) (L : ℕ → ℝ≥0∞) (a k : ℕ)
    (hStep : ∀ t, a ≤ t → t < a + k →
      𝒟[PRFPRNG.branch prng true (B t)] {true} ≤
        L t + 𝒟[PRFPRNG.branch prng false (B (t + 1))] {true}) :
    𝒟[PRFPRNG.branch prng false (B a)] {true} ≤
      (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
      (∑ t ∈ Finset.Ico a (a + k), L t) +
      𝒟[PRFPRNG.branch prng true (B (a + k))] {true} :=
  prng_ico_telescope_with_loss prng B L a k hStep

private theorem T1_top [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (qep + 1) A)] {true} ≤
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some (qep + 1)) A] {true} +
      𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par none A] {true} :=
  prng_branch_true_redPRNGAuthDFPaperBucketHybridMain_top_le_lcEq cka prng fs lam Δcka qep tL par htH A

/-- Unconditional `Main` (`gMain = true`) Hop-2 telescope over `Finset.Ico (healEpoch tL) (qep + 2)`. -/
theorem prng_branch_false_redPRNGAuthDFPaperBucketHybridMain_le_sum_prng_add_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        PRFPRNG.advantage prng
          (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A)) +
      𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} := by
  set a := healEpoch tL
  set k := (qep + 1) - a
  have hak : a + k = qep + 1 := Nat.add_sub_of_le htH
  have hak1 : a + k + 1 = qep + 2 := by omega
  have hTel := T1_telescope prng
    (fun t => redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A)
    (fun t => 𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true})
    a k
    (fun t ht1 ht2 => T1_step cka prng fs lam Δcka qep tL par t ht1 (by omega) A)
  rw [hak1, hak] at hTel
  have hTop := T1_top cka prng fs lam Δcka qep tL par htH A
  have hSumLc :
      (∑ t ∈ Finset.Ico a (qep + 1),
        𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some t) A] {true}) +
      (𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par (some (qep + 1)) A] {true} +
        𝒟[localAuthDFPaperBucketMainLcEq cka prng fs lam Δcka qep tL par none A] {true}) ≤
      𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} := by
    rw [← add_assoc, ← Finset.sum_Ico_succ_top htH]
    exact T1_sum_lcEq_add_none_le cka prng fs lam Δcka qep tL par a (qep + 2) A
  calc _ ≤ _ := hTel.trans (add_le_add le_rfl hTop)
    _ = _ := add_assoc _ _ _
    _ ≤ _ := add_le_add le_rfl hSumLc

/-- Inactive-epoch zero `PRFPRNG.advantage` for `Main` (`gMain = true`). -/
theorem prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hInact : isActiveBucketEpoch (3 + Δcka) tL par t0 = false)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A) = 0 :=
  prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive_impl
    cka prng fs lam Δcka qep tL par t0 hInact A

/-- Top-epoch (`t0 = qep + 1`) zero `PRFPRNG.advantage` for `Main` (`epMgmt` caps `startSend` at
`≤ qep` and `hooksPRNGBucketMain.startRecv` makes `0` `PRFPRNG` queries). -/
theorem prng_advantage_redPRNGAuthDFPaperBucketMain_top_eq_zero
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (qep + 1) A) = 0 :=
  prng_advantage_redPRNGAuthDFPaperBucketMain_top_eq_zero_impl
    cka prng fs lam Δcka qep tL par A

/-- Inactive-epoch zero `PRFPRNG.advantage` for `ForgedHdr` (`gMain = false`). -/
theorem prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hInact : isActiveBucketEpoch (3 + Δcka) tL par t0 = false)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A) = 0 :=
  prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive_impl
    cka prng fs lam Δcka qep tL par t0 hInact A

/-- Hop-2b adjacent-epoch step (`t ↦ t + 1`) for `ForgedHdr` (`gMain = false`). -/
theorem prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_le_succ_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (t + 1) A)] {true} :=
  prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_le_succ_false_impl
    cka prng fs lam Δcka qep tL par t htLo htHi A

/-- Hop-2c top step (`t = qep + 1`) for `ForgedHdr` (`gMain = false`) into
`localAuthDFPaperBucketForgedHdr`. -/
theorem prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_top_le_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (qep + 1) A)] {true} ≤
      𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true} :=
  prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_top_le_local_impl
    cka prng fs lam Δcka qep tL par htH A

/-- Telescoped `ForgedHdr` (`gMain = false`) Hop-2 bound over `Finset.Ico (healEpoch tL) (qep + 2)`. -/
theorem prng_branch_false_redPRNGAuthDFPaperBucketForgedHdr_le_sum_prng_add_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        PRFPRNG.advantage prng
          (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t A)) +
      𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true} := by
  set a := healEpoch tL
  set k := (qep + 1) - a
  have hak : a + k = qep + 1 := Nat.add_sub_of_le htH
  have hak1 : a + k + 1 = qep + 2 := by omega
  have hTel := prng_ico_telescope prng
    (fun t => redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t A)
    a k
    (fun t ht1 ht2 =>
      prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_le_succ_false
        cka prng fs lam Δcka qep tL par t ht1 (by omega) A)
  rw [hak1, hak] at hTel
  exact hTel.trans (add_le_add le_rfl
    (prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_top_le_local
      cka prng fs lam Δcka qep tL par htH A))

/-- Hop-2 parity-packed 3-way `slotDispatchGen` theorem (paper engine): bounds the ideal CKA
world of `redCKAAuthDFPaperBucket` by `1 *` `slotDispatchGen (3 + Δcka)` over
`Finset.Ico (healEpoch tL) (qep + 2)` plus `localAuthDFPaperBucketMode ... true + ... false`. -/
theorem cka_branch_true_redCKAAuthDFPaperBucket_le_sum_slotDispatch_add_local_split
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (hΔ : 1 ≤ Δcka)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        slotDispatchGen (3 + Δcka) tL par
          (fun t0 => PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A))
          (fun t0 => PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A))
          t) +
      (𝒟[localAuthDFPaperBucketMode cka prng fs lam Δcka qep true tL par A] {true} +
        𝒟[localAuthDFPaperBucketMode cka prng fs lam Δcka qep false tL par A] {true}) := by
  have hSplit := cka_branch_true_redCKAAuthDFPaperBucket_le_main_add_forgedHdr
    cka prng fs lam Δcka qep hc tL par A
  have hMain := prng_branch_false_redPRNGAuthDFPaperBucketHybridMain_le_sum_prng_add_local
    cka prng fs lam Δcka qep tL par htH A
  have hMainTop :
      ∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
          PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A) =
        ∑ t ∈ Finset.Ico (healEpoch tL) (qep + 1),
          PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A) := by
    have heq : qep + 2 = (qep + 1) + 1 := by omega
    rw [heq, Finset.sum_Ico_succ_top htH,
      prng_advantage_redPRNGAuthDFPaperBucketMain_top_eq_zero, add_zero]
  rw [hMainTop] at hMain
  have hForged := prng_branch_false_redPRNGAuthDFPaperBucketForgedHdr_le_sum_prng_add_local
    cka prng fs lam Δcka qep tL par htH A
  have hPack := sum_ico_forged_add_main_eq_slotDispatchGen (by omega : 4 ≤ 3 + Δcka) tL par qep
    (fun t0 => PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A))
    (fun t0 => PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A))
    (fun t0 _ hInact =>
      prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A)
    (fun t0 _ hInact =>
      prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A)
  change 𝒟[CKA.branch cka Δcka (healEpoch tL) true
      (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} ≤
    (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), _) +
      (𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} +
        𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true})
  rw [← hPack]
  calc 𝒟[CKA.branch cka Δcka (healEpoch tL) true
          (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true}
      ≤ 𝒟[PRFPRNG.branch prng false
            (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} +
        𝒟[PRFPRNG.branch prng false
            (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} :=
        hSplit
    _ ≤ ((∑ t ∈ Finset.Ico (healEpoch tL) (qep + 1),
            PRFPRNG.advantage prng
              (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t A)) +
          𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true}) +
        ((∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
            PRFPRNG.advantage prng
              (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t A)) +
          𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true}) :=
        add_le_add hMain hForged
    _ = ((∑ t0 ∈ Finset.Ico (healEpoch tL) (qep + 2),
            PRFPRNG.advantage prng
              (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A)) +
          (∑ t0 ∈ Finset.Ico (healEpoch tL) (qep + 1),
            PRFPRNG.advantage prng
              (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A))) +
        (𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} +
          𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true}) := by
        ac_rfl

/-- Hop-2 telescoped parity-packed theorem (paper engine): bounds the ideal CKA world of
`redCKAAuthDFPaperBucket` by the ascending `t ∈ Finset.Ico (healEpoch tL) (qep + 2)` sum of
`PRFPRNG.advantage` on `redPRNGAuthDFPaperBucketPacked` plus
`localAuthDFPaperBucketMain + localAuthDFPaperBucketForgedHdr`. -/
theorem cka_branch_true_redCKAAuthDFPaperBucket_le_sum_prng_add_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (hΔ : 0 < Δcka)
    (tL : Option ℕ) (par : Bool) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        PRFPRNG.advantage prng
          (redPRNGAuthDFPaperBucketPacked cka prng fs lam Δcka qep tL par t A)) +
      (𝒟[localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A] {true} +
        𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true}) := by
  have hBase := cka_branch_true_redCKAAuthDFPaperBucket_le_sum_slotDispatch_add_local_split
    cka prng fs lam Δcka qep hc hΔ tL par htH A
  have hEq :
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        slotDispatchGen (3 + Δcka) tL par
          (fun t0 => PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A))
          (fun t0 => PRFPRNG.advantage prng
            (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A))
          t) =
      ∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        PRFPRNG.advantage prng
          (redPRNGAuthDFPaperBucketPacked cka prng fs lam Δcka qep tL par t A) := by
    rw [← sum_ico_forged_add_main_eq_slotDispatchGen (by omega : 4 ≤ 3 + Δcka) tL par qep _ _
      (fun t0 _ hInact => prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A)
      (fun t0 _ hInact => prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A),
      sum_ico_forged_add_main_eq_bucketSlotPacked (by omega : 4 ≤ 3 + Δcka) tL par qep _ _
      (fun t0 _ hInact => prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A)
      (fun t0 _ hInact => prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive
        cka prng fs lam Δcka qep tL par t0 hInact A)]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold redPRNGAuthDFPaperBucketPacked redPRNGAuthDFPaperBucketSplit
    split_ifs <;> rfl
  rw [← hEq]
  exact hBase

end ShallowBucketPRNG

end CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Construction

open ReductionDsl
open CryptoGames.SM.Engine

section HooksPRNGBucketCDF

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

/-- Combined syntactic + potential PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for
`redPRNGAuthDFBucketHybridProg`. -/
theorem redPRNGAuthDFBucketHybridProg_makesAtMostQueries
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL par t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) :=
  redPRNGAuthDFBucketHybridProg_makesAtMostQueries_impl L B Δcka qep maxSkip tL par t q A hA

/-- Evaluation / `PRFPRNG.advantage` bridge for `redPRNGAuthDFPaperBucketSplitProg` (`gMain : Bool`). -/
theorem redPRNGAuthDFPaperBucketSplitProg_advantage_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t0))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par gMain t0).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng
        (DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par gMain t0 A) :=
  _root_.Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEval.redPRNGAuthDFPaperBucketSplitProg_advantage_vr_impl
    (prngInit := prngInit) (lam := lam) (sampKR := sampKR) (sampI := sampI)
    cka prng fs L B B_q Δcka qep tL par gMain t0
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampK
    hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB

end HooksPRNGBucketCDF

end CryptoGames.SM.Construction
