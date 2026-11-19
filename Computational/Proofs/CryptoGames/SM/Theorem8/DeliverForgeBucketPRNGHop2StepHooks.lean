/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/


module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section StepHooks1

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

private theorem leComp_lookupBucketF_step
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
    exact AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩
    · by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · simp [hne.symm]

private theorem leComp_challPrf_lookupF
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t : ℕ) (ik : I)
    (hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hbL : spL.b = true)
    (hft : ∀ t', t' ≠ t → ∀ hL : PRNGBucketState T Sig K I,
      hL.fTable t' = hR.fTable t' → hL.fTable t' = hR.fTable t')
    (htab : spL.table = hR.fTable t) :
    AuthL11.LeComp
      (fun (r1 : Option (Sig × K) × PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1 = none ∨
        (r1.1 = some ((prng.up spL.σ ik).1, r2.1.1) ∧
          r2.1.2.cache = hR.cache ∧ r2.1.2.corrRoot = hR.corrRoot ∧ r2.2 = spR ∧
          r1.2.σ = spL.σ ∧ r1.2.b = true ∧
          (∀ t', t' ≠ t → r2.1.2.fTable t' = hR.fTable t') ∧
          r1.2.table = r2.1.2.fTable t))
      ((PRFPRNG.challPrfImpl prng ik).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((lookupPRNGBucketF (T := T) (Sig := Sig) t ik).run hR)).run spR) := by
  have _ := hft
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
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩)
    | none =>
      simp only [StateT.run_bind, simulateQ_bind,
        AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
      refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
      simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩)
      · simp [ht']
      · simp


/-! ### Root, Cache, and Virtual-Party Relations for `(true, t)` vs `(false, t + 1)` -/

@[expose]
def spPinStep (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t eMax : ℕ) (σ : Sig) : Option Sig :=
  if decide (eMax ≤ t) || inStage2BucketGen Δbucket tL par (t + 1) then some σ else none

@[expose]
def RelStepRoot (tH t : ℕ) (σR_sp : Option Sig) (e : ℕ) (rL rR : Option Sig) : Prop :=
  (e < tH ∧ ∃ σ, rL = some σ ∧ rR = some σ) ∨
  (tH ≤ e ∧ e < t ∧ rL = none ∧ rR = none) ∨
  (e = t ∧ (∃ σ, rL = some σ ∧ (σR_sp = some σ ∨ σR_sp = none)) ∧ rR = none) ∨
  (t < e ∧ ∃ σ, rL = some σ ∧ rR = some σ)

theorem RelStepRoot.change_σ {tH t : ℕ} {σ₁ σ₂ : Option Sig} {e : ℕ} {rL rR : Option Sig}
    (hcond : e ≠ t ∨ σ₂ = none) (h : RelStepRoot tH t σ₁ e rL rR) : RelStepRoot tH t σ₂ e rL rR := by
  rcases h with h1 | h2 | ⟨heq, ⟨σ, hrL, _⟩, hrR⟩ | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rcases hcond with hne | hnone
    · exact False.elim (hne heq)
    · exact Or.inr (Or.inr (Or.inl ⟨heq, ⟨σ, hrL, Or.inr hnone⟩, hrR⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

@[expose]
def RelCacheStep (tH t : ℕ) (σR_sp : Option Sig) (e : ℕ)
    (cL cR : Option (T × Option Sig × K)) : Prop :=
  (cL = none ∧ cR = none) ∨
  ∃ Tc rL rR k, cL = some (Tc, rL, k) ∧ cR = some (Tc, rR, k) ∧ RelStepRoot tH t σR_sp e rL rR

theorem RelCacheStep.change_σ {tH t : ℕ} {σ₁ σ₂ : Option Sig} {e : ℕ}
    {cL cR : Option (T × Option Sig × K)}
    (hcond : e ≠ t ∨ σ₂ = none ∨ (cL = none ∧ cR = none))
    (h : RelCacheStep tH t σ₁ e cL cR) : RelCacheStep tH t σ₂ e cL cR := by
  rcases hcond with hne | hnone_pin | hnone
  · rcases h with h0 | ⟨Tc, rL, rR, k, hcL, hcR, hr⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR, hr.change_σ (Or.inl hne)⟩
  · rcases h with h0 | ⟨Tc, rL, rR, k, hcL, hcR, hr⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR, hr.change_σ (Or.inr hnone_pin)⟩
  · exact Or.inl hnone

structure RelVPStep (tH t : ℕ) (σR_sp : Option Sig) (e : ℕ) (P : Party)
    (vpL vpR : VP Γ T (Option Sig) SS RS) : Prop where
  id_L : vpL.id = P
  tcur_L : vpL.tcur = e
  id_R : vpR.id = P
  tcur_R : vpR.tcur = e
  γ_eq : vpL.γ = vpR.γ
  Tcur_eq : vpL.curCkaMsg = vpR.curCkaMsg
  vS_eq : vpL.vS = vpR.vS
  vR_eq : ∀ t', vpL.vR t' = vpR.vR t'
  root_rel : RelStepRoot tH t σR_sp e vpL.root vpR.root

theorem RelVPStep.change_σ {tH t : ℕ} {σ₁ σ₂ : Option Sig} {e : ℕ} {P : Party}
    {vpL vpR : VP Γ T (Option Sig) SS RS}
    (hcond : e ≠ t ∨ σ₂ = none) (h : RelVPStep tH t σ₁ e P vpL vpR) :
    RelVPStep tH t σ₂ e P vpL vpR := by
  exact ⟨h.id_L, h.tcur_L, h.id_R, h.tcur_R, h.γ_eq, h.Tcur_eq, h.vS_eq, h.vR_eq,
    h.root_rel.change_σ hcond⟩

/-! ### `DoomedStep`, `WonSyncRaw`, and `SyncStepRaw` -/

@[expose]
def DoomedStep (tL : Option ℕ)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ) :
    Prop :=
  st.1.abort = true ∨
  (st.2 = none ∧ ∃ l ∈ st.1.g.leaks, ltOpt tL l = true ∧ ∃ cur, st.1.g.tL = some cur ∧ l ≤ cur) ∨
  (∃ w, st.2 = some w ∧ ∃ l ∈ st.1.g.leaks, ltOpt tL l = true ∧ l < w)

@[expose]
def DoomedStepRaw (tL : Option ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    Prop :=
  es.abort = true ∨
  ∃ l ∈ es.g.leaks, ltOpt tL l = true ∧ ∃ cur, es.g.tL = some cur ∧ l ≤ cur

structure SyncStepRaw
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop where
  abortL : esL.abort = false
  abortR : esR.abort = false
  g_eq : AuthL11.eraseSt esL.g = AuthL11.eraseSt esR.g
  vp_rel : ∀ P, RelVPStep (healEpoch tL) t
    (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
    (esR.g.epoch P) P (esL.g.st P) (esR.g.st P)
  cache_rel : ∀ e, RelCacheStep (healEpoch tL) t
    (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
    e (esL.h.cache e) (esR.h.cache e)
  cache_gt_max : ∀ e, max (esR.g.epoch .A) (esR.g.epoch .B) < e →
    esL.h.cache e = none ∧ esR.h.cache e = none
  fTable_ne : ∀ t0, t0 ≠ t → esL.h.fTable t0 = esR.h.fTable t0
  table_t : spL.table = esR.h.fTable t
  spL_b : spL.b = true
  spR_b : spR.b = false
  sp_σ_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL.σ = spR.σ
  spR_prf_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t ∨
    (max (esR.g.epoch .A) (esR.g.epoch .B) = t ∧
      inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) → spR.prf = false
  spR_prng : spR.prng = false
  spR_corr : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) →
    (max (esR.g.epoch .A) (esR.g.epoch .B) ≤ t ∨
      inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → spR.corr = false
  comp_inv : ∀ pos ∈ esR.g.comp, SM.healedBy esR.g.tL (2 + Δcka) pos.epoch = false
  trans_epoch : ∀ r ∈ esR.g.trans,
    r.pos.epoch ≤ esR.g.epoch r.pos.sender ∧ r.ct.1.1 = r.pos.epoch
  vp_curCka : ∀ P, P.sendsIn (esR.g.epoch P + 1) = false → 0 < esR.g.epoch P →
    ∀ Tc, (esR.g.st P).curCkaMsg = some Tc →
      ∃ rR k, esR.h.cache (esR.g.epoch P) = some (Tc, rR, k)
  trans_cache : ∀ r ∈ esR.g.trans, 0 < r.pos.epoch →
    ∀ Tc, r.ct.1.2 = some Tc →
      ∃ rR k, esR.h.cache r.pos.epoch = some (Tc, rR, k)
  epoch_le : ∀ P, esR.g.epoch P ≤ esR.g.epoch P.other + 1
  epoch_sends : ∀ P, esR.g.epoch P.other < esR.g.epoch P → P.sendsIn (esR.g.epoch P) = true
  corrRoot_L : esL.h.corrRoot = none
  corrRoot_R : esR.h.corrRoot = none
  pl_false : postLeak tL esR.g = false

/-! ### Initial & Send `rootPRNGBucketHybrid` Coupling -/

private theorem resolveCorrRoot_of_none {h : PRNGBucketState T Sig K I}
    (hcr : h.corrRoot = none) (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h ep σv = σv := by
  cases σv <;> simp [resolveCorrRoot, hcr]


theorem leComp_rootInit_step
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    {Δbucket : ℕ} {par : Bool}
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t : ℕ) (lam : I) (σ0 : Sig)
    (htH : healEpoch tL ≤ t) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ rL rR kVal,
          r1.1.1 = some (rL, kVal) ∧ r2.1.1 = some (rR, kVal) ∧
          RelStepRoot (healEpoch tL) t (spPinStep Δbucket tL par t 0 r2.2.σ) 0 rL rR ∧
          r1.1.2.cache = (fun _ => none) ∧ r2.1.2.cache = (fun _ => none) ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (0 < t → r1.2.σ = r2.2.σ) ∧
          r2.2.prf = false ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ 0 → r2.2.corr = false))
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t 0 false lam none).run ({} : PRNGBucketState T Sig K I))).run
          { σ := σ0, b := true })
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par (t + 1) 0 false lam none).run ({} : PRNGBucketState T Sig K I))).run
          { σ := σ0, b := false }) := by
  have h0_nlt_t : ¬ (t < 0) := by omega
  have h0_nlt_t1 : ¬ (t + 1 < 0) := by omega
  have h0_ne_t1 : ¬ (0 = t + 1) := by omega
  unfold rootPRNGBucketHybrid
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, resolveCorrRoot,
    Option.isSome_none, Bool.or_self, Bool.false_eq_true,
    h0_nlt_t, h0_nlt_t1, h0_ne_t1, ↓reduceIte]
  by_cases hge_tH : (!(0 < healEpoch tL)) = true
  · have htH0 : healEpoch tL = 0 := by simp at hge_tH; omega
    have htL_none : tL = none := by
      cases tL with
      | none => rfl
      | some l => simp [healEpoch] at htH0
    subst htL_none
    by_cases h0_eq_t : 0 = t
    · subst t
      simp only [healEpoch, Nat.lt_irrefl, decide_false, Bool.not_false, ↓reduceIte,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true]
      by_cases hin : inStage2BucketGen Δbucket none par 0 = true
      · simp only [hin, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_challPrfQuery,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          Bool.false_eq_true, pure_bind]
        refine (leComp_challPrf_lookupF (T := T) prng 0 lam ({} : PRNGBucketState T Sig K I)
          { σ := σ0, b := true } { σ := (prng.up σ0 lam).1, b := false }
          rfl (fun _ _ _ h => h) rfl).bind ?_
        rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
        rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
          subst hresL hspR1
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, none, kOut, rfl, rfl,
            Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σ0 lam).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
            rfl, hcR1, rfl, hcrR1,
            fun t0 ht0 => (hft1 t0 ht0).symm, htab1,
            hbL1, rfl, False.elim, rfl, rfl, fun _ => rfl⟩)
      · simp only [hin, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl,
          pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, none, (prng.up σ0 lam).2, rfl, rfl,
          Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σ0 lam).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
          rfl, rfl, rfl, rfl,
          fun _ _ => rfl, rfl, rfl, rfl, False.elim, rfl, rfl, fun _ => rfl⟩)
    · have h0_lt_t : 0 < t := by omega
      simp only [h0_eq_t, healEpoch, Nat.lt_irrefl, decide_false, Bool.not_false, ↓reduceIte,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true]
      by_cases hin : inStage2BucketGen Δbucket none par 0 = true
      · simp only [hin, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          Bool.false_eq_true, pure_bind]
        refine (leComp_lookupBucketF_step (T := T) (Sig := Sig) prng t 0 lam {} {}
          { σ := (prng.up σ0 lam).1, b := true } { σ := (prng.up σ0 lam).1, b := false }
          h0_eq_t (fun _ _ => rfl)).bind ?_
        rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩ ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
        dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
        subst hk_eq hspL1 hspR1
        simp only [StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
          Or.inr (Or.inl ⟨by simp, h0_lt_t, rfl, rfl⟩), hcL1, hcR1, hcrL1, hcrR1, hft1,
          htab1.symm, rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩)
      · simp only [hin, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨none, none, (prng.up σ0 lam).2, rfl, rfl,
          Or.inr (Or.inl ⟨by simp, h0_lt_t, rfl, rfl⟩), rfl, rfl, rfl, rfl,
          fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩)
  · have h0_lt_tH : 0 < healEpoch tL := by
      by_contra hle; exact hge_tH (by simp [hle])
    have h0_ne_t : ¬ (0 = t) := by omega
    simp only [h0_ne_t, hge_tH, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
      AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
      AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl,
      pure_bind, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, some (prng.up σ0 lam).1,
      (prng.up σ0 lam).2, rfl, rfl, Or.inl ⟨h0_lt_tH, (prng.up σ0 lam).1, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl,
      fun _ => rfl, rfl, rfl, fun h => absurd h (not_le.mpr h0_lt_tH)⟩)

theorem leComp_rootSend_step
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
    (hprfR_lt : eMax < t ∨ (eMax = t ∧ inStage2BucketGen Δbucket tL par (t + 1) = false) → spR.prf = false)
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
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
          (eMax + 1 < t ∨ (eMax + 1 = t ∧ inStage2BucketGen Δbucket tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 →
            (eMax + 1 ≤ t ∨ inStage2BucketGen Δbucket tL par (t + 1) = true) → r2.2.corr = false))
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t (eMax + 1) false ik0 rL0).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par (t + 1) (eMax + 1) false ik0 rR0).run hR)).run spR) := by
  rcases spL with ⟨σL, bL, corrL, prngL, prfL, tabL⟩
  rcases spR with ⟨σR, bR, corrR, prngR, prfR, tabR⟩
  dsimp only at hr0 htab hbL hbR hσ_lt hprfR_lt hprngR hcorrR
  subst hbL hbR hprngR htab
  have hresL0 : resolveCorrRoot hL eMax rL0 = rL0 := resolveCorrRoot_of_none hcrL eMax rL0
  have hresR0 : resolveCorrRoot hR eMax rR0 = rR0 := resolveCorrRoot_of_none hcrR eMax rR0
  have hisSomeL : (false || hL.corrRoot.isSome) = false := by simp [hcrL]
  have hisSomeR : (false || hR.corrRoot.isSome) = false := by simp [hcrR]
  by_cases ht_lt : t < eMax + 1
  · by_cases heq_t1 : eMax + 1 = t + 1
    · have heMax_eq : eMax = t := by omega
      subst heMax_eq
      have hcorrR0 : corrR = false := hcorrR htH (Or.inl le_rfl)
      subst hcorrR0
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
          rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
          fun h => by omega, (by rintro (h | ⟨h, _⟩) <;> omega), rfl, fun _ _ => rfl⟩)
      · have hin_f : inStage2BucketGen Δbucket tL par (eMax + 1) = false :=
          Bool.eq_false_iff.mpr hin
        have hprfR0 : prfR = false := hprfR_lt (Or.inr ⟨rfl, hin_f⟩)
        subst hprfR0
        simp only [hin_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
          AuthL11.simulateQ_pImpl_processQuery, AuthL11.run_processImpl_some,
          AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, pure_bind]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σR ik0).1, some (prng.up σR ik0).1,
          (prng.up σR ik0).2, rfl, rfl,
          Or.inr (Or.inr (Or.inr ⟨by omega, (prng.up σR ik0).1, rfl, rfl⟩)),
          (fun _ => Or.inr (by simp [spPinStep, hin_f])),
          rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
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
        rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
        fun h => by omega, (by rintro (h | ⟨h, _⟩) <;> omega), rfl,
        (fun _ h => hcorrR (by omega) (Or.inr (h.resolve_left (by omega))))⟩)
  · have heMax_lt_t : eMax < t := by omega
    have hprfR := hprfR_lt (Or.inl heMax_lt_t)
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
            fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
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
          refine (leComp_challPrf_lookupF prng t ik0 hR
            { σ := σL, b := true, corr := corrL, prng := prngL, prf := prfL, table := hR.fTable t }
            { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false, prf := false,
              table := tabR }
            rfl (fun _ _ _ h => h) rfl).bind ?_
          rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
          rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
          · dsimp only at hnone; subst hnone
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
            subst hresL hspR1
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, none, kOut, rfl, rfl,
              Or.inr (Or.inr (Or.inl ⟨rfl, ⟨(prng.up σL ik0).1, rfl, Or.inl (by simp [spPinStep])⟩, rfl⟩)),
              fun h => by omega, rfl, hcR1, hcrL, hcrR1.trans hcrR,
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
              fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
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
              fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
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
              refine (leComp_lookupBucketF_step prng t (eMax + 1) ik0 hL hR
                { σ := (prng.up σL ik0).1, b := true, corr := corrL, prng := prngL,
                  prf := false, table := hR.fTable t }
                { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false,
                  prf := false, table := tabR }
                heq_t hft).bind ?_
              rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩
                ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
              dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
              subst hk_eq hspL1 hspR1
              simp only [StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
                Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
                fun h => by omega, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR,
                hft1, htab1.symm, rfl, rfl,
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
                fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
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
            fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
            fun _ => rfl, fun _ => rfl, rfl, fun h _ => by omega⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

theorem leComp_vRecv_cached_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {σPin : Option Sig}
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {ep : ℕ} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {c : Header T × E} {rec : Option (SM.Record M (Header T × E))}
    {hL hR : PRNGBucketState T Sig K I} {spL spR : PRFPRNG.GameState Sig I K}
    (hvp : RelVPStep (healEpoch tL) t σPin ep P vpL vpR)
    (hcache : ∀ e, RelCacheStep (healEpoch tL) t σPin e (hL.cache e) (hR.cache e))
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hc_hit : c.1.1 = ep + 1 → ∀ tn0, c.1.2 = some tn0 →
      ∃ rR kc, hR.cache (ep + 1) = some (tn0, rR, kc)) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR) ∨
        ∃ vpL' vpR' i' m',
          r1.1.1 = some (some (vpL', c.1.1, i', m')) ∧
          r2.1.1 = some (some (vpR', c.1.1, i', m')) ∧
          c.1.1 ≤ ep + 1 ∧ P.sendsIn c.1.1 = false ∧
          RelVPStep (healEpoch tL) t σPin (max ep c.1.1) P vpL' vpR' ∧
          r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR ∧
          (c.1.1 ≤ ep → vpR'.curCkaMsg = vpR.curCkaMsg))
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
          ctxL P vpL c rec).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (t + 1))
          ctxR P vpR c rec).run hR)).run spR) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
  by_cases hrej : (P.sendsIn c.1.1 || decide (ep + 1 < c.1.1)) = true
  · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
    have hns : P.sendsIn c.1.1 = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hrej
      exact hrej.1
    have htle : c.1.1 ≤ ep + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrej
      omega
    by_cases hnew : c.1.1 = ep + 1
    · simp only [hnew, ↓reduceIte]
      cases htn0 : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | some tn0 =>
        obtain ⟨rR, kc, hcR_eq⟩ := hc_hit hnew tn0 htn0
        obtain ⟨Tc, rL, rR', kc', hcL_eq, hcR_eq', hr_rel⟩ :
            ∃ Tc rL rR' kc', hL.cache (ep + 1) = some (Tc, rL, kc') ∧
              hR.cache (ep + 1) = some (Tc, rR', kc') ∧
              RelStepRoot (healEpoch tL) t σPin (ep + 1) rL rR' := by
          rcases hcache (ep + 1) with ⟨_, hnone⟩ | hsome
          · rw [hcR_eq] at hnone; cases hnone
          · exact hsome
        rw [hcR_eq] at hcR_eq'
        cases hcR_eq'
        have hns_ep1 : P.sendsIn (ep + 1) = false := hnew ▸ hns
        simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen,
          StateT.run_bind, StateT.run_get, pure_bind, hcL_eq, hcR_eq, ↓reduceIte,
          resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR,
          StateT.run_pure, hvp.γ_eq, Function.update_self]
        cases hfs : fs.receive (fs.initReceiver kc) c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_ep1, ?_,
            rfl, rfl, rfl, rfl, fun h => by omega⟩)
          have hmax : max ep (ep + 1) = ep + 1 := Nat.max_eq_right (Nat.le_succ ep)
          rw [hmax]
          refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, fun t' => ?_, hr_rel⟩
          by_cases ht' : t' = ep + 1
          · subst ht'; simp
          · simp [Function.update_of_ne ht', hvp.vR_eq t']
    · have htle_ep : c.1.1 ≤ ep := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max ep c.1.1 = ep := Nat.max_eq_left htle_ep
      simp only [hnew, ↓reduceIte, pure_bind]
      rw [hvp.vR_eq c.1.1]
      cases hvR : vpR.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | some v =>
        simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, pure_bind]
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, rfl, rfl, fun _ => rfl⟩)
          rw [hmax]
          refine ⟨hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            fun t' => ?_, hvp.root_rel⟩
          by_cases ht' : t' = c.1.1
          · subst ht'; simp
          · simp [Function.update_of_ne ht', hvp.vR_eq t']

private theorem leComp_startRecv_inject_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t ep eMax : ℕ)
    (ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (γ0 : Γ) (rL0 rR0 : Option Sig) (tn0 : T)
    (hL hR : PRNGBucketState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hep_le : ep ≤ eMax)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) ep rL0 rR0)
    (hc0 : RelCacheStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) (ep + 1)
      (hL.cache (ep + 1)) (hR.cache (ep + 1)))
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
      spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax →
      (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → spR.corr = false) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option (Γ × Option Sig × RS)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (Γ × Option Sig × RS)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax →
            (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)) ∨
        (∃ γ' rL' rR' rs,
          r1.1.1 = some (some (γ', rL', rs)) ∧
          r2.1.1 = some (some (γ', rR', rs)) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax →
            (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)))
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startRecv
          ctxL P (ep + 1) γ0 rL0 tn0).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (t + 1)).startRecv
          ctxR P (ep + 1) γ0 rR0 tn0).run hR)).run spR) := by
  unfold hooksPRNGBucketHybrid hooksPRNGBucketHybridGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hplL, hplR,
    resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR, hcrL, hcrR,
    Option.isSome_none, Bool.false_or, decide_eq_true_eq]
  have hoff :
      AuthL11.LeComp
        (fun (r1 : (Option (Option (Γ × Option Sig × RS)) × PRNGBucketState T Sig K I) ×
                    PRFPRNG.GameState Sig I K)
             (r2 : (Option (Option (Γ × Option Sig × RS)) × PRNGBucketState T Sig K I) ×
                    PRFPRNG.GameState Sig I K) =>
          r1.1.1 = none ∨
          (r1.1.1 = some none ∧ r2.1.1 = some none ∧
            r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
            r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
            (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
            r1.2.table = r2.1.2.fTable t ∧
            r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
            (eMax < t → r1.2.σ = r2.2.σ) ∧
            (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
              r2.2.prf = false) ∧
            r2.2.prng = false ∧
            (healEpoch tL ≤ eMax →
              (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)) ∨
          (∃ γ' rL' rR' rs,
            r1.1.1 = some (some (γ', rL', rs)) ∧
            r2.1.1 = some (some (γ', rR', rs)) ∧
            r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
            r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
            (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
            r1.2.table = r2.1.2.fTable t ∧
            r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
            (eMax < t → r1.2.σ = r2.2.σ) ∧
            (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
              r2.2.prf = false) ∧
            r2.2.prng = false ∧
            (healEpoch tL ≤ eMax →
              (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)))
        ((simulateQ (AuthL11.pImpl prng)
          ((if !(qep + 1 < ep + 1) &&
                (lastLeakGuessAdmissible (3 + Δcka) tL (ep + 1) &&
                  (partyPar (Party.senderOf (ep + 1)) == par)) then
              if tL.isSome && (ep + 1 = healEpoch tL) then
                pure none
              else if t < ep + 1 then
                match rL0 with
                | none => pure none
                | some σ =>
                  let kk := cka.receive γ0 tn0
                  let p := prng.up σ kk.2
                  pure (some (some (kk.1, some p.1, fs.initReceiver p.2)))
              else if ep + 1 = t then do
                let kk := cka.receive γ0 tn0
                match ← liftPBucket (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
                | none => pure none
                | some (σOut, kOut) =>
                  pure (some (some (kk.1, some σOut, fs.initReceiver kOut)))
              else if !(ep + 1 < healEpoch tL) then do
                let kk := cka.receive γ0 tn0
                let kOut ← lookupPRNGBucketF (ep + 1) kk.2
                pure (some (some (kk.1, none, fs.initReceiver kOut)))
              else
                pure (some none)
            else
              pure (some none)).run hL)).run spL)
        ((simulateQ (AuthL11.pImpl prng)
          ((if !(qep + 1 < ep + 1) &&
                (lastLeakGuessAdmissible (3 + Δcka) tL (ep + 1) &&
                  (partyPar (Party.senderOf (ep + 1)) == par)) then
              if tL.isSome && (ep + 1 = healEpoch tL) then
                pure none
              else if t + 1 < ep + 1 then
                match rR0 with
                | none => pure none
                | some σ =>
                  let kk := cka.receive γ0 tn0
                  let p := prng.up σ kk.2
                  pure (some (some (kk.1, some p.1, fs.initReceiver p.2)))
              else if ep + 1 = t + 1 then do
                let kk := cka.receive γ0 tn0
                match ← liftPBucket (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
                | none => pure none
                | some (σOut, kOut) =>
                  pure (some (some (kk.1, some σOut, fs.initReceiver kOut)))
              else if !(ep + 1 < healEpoch tL) then do
                let kk := cka.receive γ0 tn0
                let kOut ← lookupPRNGBucketF (ep + 1) kk.2
                pure (some (some (kk.1, none, fs.initReceiver kOut)))
              else
                pure (some none)
            else
              pure (some none)).run hR)).run spR) := by
    by_cases hcond : (!(decide (qep + 1 < ep + 1)) &&
        (lastLeakGuessAdmissible (3 + Δcka) tL (ep + 1) &&
          (partyPar (Party.senderOf (ep + 1)) == par))) = true
    · simp only [hcond, ↓reduceIte]
      have hin : inStage2Bucket Δcka tL par (ep + 1) = true := by
        simp only [Bool.and_eq_true] at hcond
        exact Bool.and_eq_true _ _ |>.mpr hcond.2
      have htH_lt : healEpoch tL < ep + 1 := by
        cases tL with
        | none => simp [healEpoch]
        | some l =>
          simp [inStage2Bucket, lastLeakGuessAdmissible, healEpoch] at hin ⊢
          omega
      have his_tH_false : (tL.isSome && decide (ep + 1 = healEpoch tL)) = false := by
        simp [Nat.ne_of_gt htH_lt]
      have hge_tH : (!(ep + 1 < healEpoch tL)) = true := by simp; omega
      simp only [his_tH_false, Bool.false_eq_true, ↓reduceIte]
      by_cases ht_lt : t < ep + 1
      · by_cases heq_t1 : ep + 1 = t + 1
        · have hnlt_t1 : ¬ (t + 1 < ep + 1) := by omega
          have hin_gen : inStage2BucketGen (3 + Δcka) tL par (t + 1) = true := by
            rw [← heq_t1]; exact hin
          have hpin_eq : spPinStep (3 + Δcka) tL par t eMax spR.σ = some spR.σ := by
            simp [spPinStep, hin_gen]
          have hrL0_eq : rL0 = some spR.σ := by
            rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, ⟨σ, hrL, hpin_s⟩, _⟩ | ⟨h, _⟩
            · omega
            · omega
            · rw [hpin_eq] at hpin_s
              rcases hpin_s with h1 | h2
              · cases h1; exact hrL
              · cases h2
            · omega
          have hcorrR0 : spR.corr = false := hcorrR (by omega) (Or.inr hin_gen)
          simp only [ht_lt, hnlt_t1, ↓reduceIte]
          simp only [heq_t1, ↓reduceIte, hrL0_eq,
            StateT.run_pure, simulateQ_pure,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucket,
            AuthL11.simulateQ_pImpl_challPrfQuery, AuthL11.run_challPrfImpl,
            hcorrR0, hprngR, hbR, Bool.or_self, pure_bind]
          exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
            some (prng.up spR.σ (cka.receive γ0 tn0).2).1,
            some (prng.up spR.σ (cka.receive γ0 tn0).2).1,
            fs.initReceiver (prng.up spR.σ (cka.receive γ0 tn0).2).2,
            rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, rfl, rfl,
            fun h => by omega,
            (fun h => by
              rcases h with h1 | ⟨_, h2⟩
              · omega
              · rw [hin_gen] at h2; cases h2),
            rfl, fun _ _ => rfl⟩))
        · have ht1_lt : t + 1 < ep + 1 := by omega
          obtain ⟨σ0, hrL0_eq, hrR0_eq⟩ : ∃ σ0, rL0 = some σ0 ∧ rR0 = some σ0 := by
            rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
            · omega
            · omega
            · omega
            · exact h
          simp only [ht_lt, ht1_lt, ↓reduceIte, hrL0_eq, hrR0_eq, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
            some (prng.up σ0 (cka.receive γ0 tn0).2).1,
            some (prng.up σ0 (cka.receive γ0 tn0).2).1,
            fs.initReceiver (prng.up σ0 (cka.receive γ0 tn0).2).2,
            rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl,
            fun h => by omega,
            fun h => by rcases h with h1 | ⟨h1, _⟩ <;> omega,
            hprngR, hcorrR⟩))
      · have hnlt_t1 : ¬ (t + 1 < ep + 1) := by omega
        have hne_t1 : ¬ (ep + 1 = t + 1) := by omega
        simp only [ht_lt, hnlt_t1, hne_t1, ↓reduceIte]
        by_cases heq_t : ep + 1 = t
        · simp only [heq_t, ↓reduceIte]
          have hge_t : (!(t < healEpoch tL)) = true := by rw [← heq_t]; exact hge_tH
          simp only [hge_t, ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc,
            simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_challPrfQuery, pure_bind]
          refine (leComp_challPrf_lookupF prng t (cka.receive γ0 tn0).2 hR spL spR
            hbL (fun _ _ _ h => h) htab).bind ?_
          rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
          rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
          · dsimp only at hnone; subst hnone
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
            subst hresL hspR1
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
              some (prng.up spL.σ (cka.receive γ0 tn0).2).1, none, fs.initReceiver kOut,
              rfl, rfl, rfl, hcR1, hcrL, hcrR1.trans hcrR,
              fun t0 ht0 => (hft t0 ht0).trans (hft1 t0 ht0).symm, htab1, hbL1, hbR, rfl,
              fun h => (hσL1.trans (hσ_lt h)), hprfR_lt, hprngR, hcorrR⟩))
        · simp only [heq_t, hge_tH, ↓reduceIte,
            StateT.run_bind, simulateQ_bind]
          refine (leComp_lookupBucketF_step prng t (ep + 1) (cka.receive γ0 tn0).2 hL hR spL spR
            heq_t hft).bind ?_
          rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩ ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
          dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
          subst hk_eq hspL1 hspR1
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
            none, none, fs.initReceiver kL,
            rfl, rfl, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR, hft1, by rw [htab1, ← htab],
            hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
        hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
  rcases hc0 with ⟨hcL, hcR⟩ | ⟨Tc, rL', rR', kVal, hcL, hcR, _⟩
  · simp only [hcL, hcR]
    exact hoff
  · by_cases hTc : Tc = tn0
    · subst hTc
      simp only [hcL, hcR, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 Tc).1,
        rL', rR', fs.initReceiver kVal,
        rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
    · simp only [hcL, hcR, hTc, ↓reduceIte]
      exact hoff

theorem leComp_vRecv_inject_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {ep : ℕ} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {c : Header T × E}
    {hL hR : PRNGBucketState T Sig K I} {spL spR : PRFPRNG.GameState Sig I K}
    (hvp : RelVPStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) ep P vpL vpR)
    (hcache : ∀ e, RelCacheStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) e
      (hL.cache e) (hR.cache e))
    (heMax : ep ≤ eMax)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
      spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax →
      (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → spR.corr = false) :
    AuthL11.LeComp
      (fun (r1 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax →
            (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)) ∨
        ∃ vpL' vpR' i' m',
          r1.1.1 = some (some (vpL', c.1.1, i', m')) ∧
          r2.1.1 = some (some (vpR', c.1.1, i', m')) ∧
          c.1.1 ≤ ep + 1 ∧ P.sendsIn c.1.1 = false ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t ∨ (eMax = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax →
            (eMax ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false) ∧
          (c.1.1 ≤ ep →
            RelVPStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) ep P vpL' vpR' ∧
            vpR'.curCkaMsg = vpR.curCkaMsg ∧
            r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR))
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
          ctxL P vpL c none).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (t + 1))
          ctxR P vpR c none).run hR)).run spR) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
  by_cases hrej : (P.sendsIn c.1.1 || decide (ep + 1 < c.1.1)) = true
  · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
      hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
  · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
    have hns : P.sendsIn c.1.1 = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hrej
      exact hrej.1
    have htle : c.1.1 ≤ ep + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrej
      omega
    by_cases hnew : c.1.1 = ep + 1
    · simp only [hnew, ↓reduceIte]
      cases htn0 : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
          hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
      | some tn0 =>
        simp only [StateT.run_bind, simulateQ_bind]
        rw [hvp.γ_eq]
        refine (leComp_startRecv_inject_step cka prng fs Δcka qep tL par t ep eMax
          ctxL ctxR P vpR.γ vpL.root vpR.root tn0 hL hR spL spR
          heMax hplL hplR hcrL hcrR hvp.root_rel (hcache (ep + 1)) hft htab hbL hbR
          hσ_lt hprfR_lt hprngR hcorrR).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hsr
        rcases hsr with hnone |
          ⟨hL_none, hR_none, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩ |
          ⟨γ', rL', rR', rs, hL_some, hR_some, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
            hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hL_none hR_none; subst hL_none hR_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
            hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩))
        · dsimp only at hL_some hR_some; subst hL_some hR_some
          have hns_ep1 : P.sendsIn (ep + 1) = false := hnew ▸ hns
          simp only [pure_bind, Function.update_self, hooksPRNGBucketHybrid,
            hooksPRNGBucketHybridGen]
          cases hfs : fs.receive rs c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
              hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩))
          | some res =>
            rcases res with ⟨v', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_ep1,
              hcL1, hcR1, hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1,
              fun h => by omega⟩))
    · have htle_ep : c.1.1 ≤ ep := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      simp only [hnew, ↓reduceIte, pure_bind]
      rw [hvp.vR_eq c.1.1]
      cases hvR : vpR.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
          hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
      | some v =>
        simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, pure_bind]
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
            hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns,
            rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR,
            fun _ => ⟨?_, rfl, rfl, rfl, rfl, rfl⟩⟩))
          refine ⟨hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            fun t' => ?_, hvp.root_rel⟩
          by_cases ht' : t' = c.1.1
          · subst ht'; simp
          · simp [Function.update_of_ne ht', hvp.vR_eq t']

end StepHooks1
end CryptoGames.SM.Construction.DeliverForge
