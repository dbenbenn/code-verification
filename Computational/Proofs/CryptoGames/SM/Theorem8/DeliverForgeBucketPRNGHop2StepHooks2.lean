/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/


module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2StepHooks -- proof-setup: allow-public-import
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

section StepHooks2

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}


private theorem leComp_startSend_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {r_coins : Option CCoins}
    {hL hR : PRNGBucketState T Sig K I} {spL spR : PRFPRNG.GameState Sig I K}
    (htH : healEpoch tL ≤ t)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) eMax P vpL vpR)
    (hcache : ∀ e', RelCacheStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) e'
      (hL.cache e') (hR.cache e'))
    (hcache_gt : ∀ e', eMax < e' → hL.cache e' = none ∧ hR.cache e' = none)
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
      (fun (r1 : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                  PRFPRNG.GameState Sig I K)
           (r2 : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                  PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ γ' T' rL' rR' kVal,
          r1.1.1 = some (γ', T', rL', fs.initSender kVal) ∧
          r2.1.1 = some (γ', T', rR', fs.initSender kVal) ∧
          RelStepRoot (healEpoch tL) t (spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ)
            (eMax + 1) rL' rR' ∧
          (t ≤ eMax →
            spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ =
              spPinStep (3 + Δcka) tL par t eMax spR.σ ∨
            spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ = none) ∧
          (∀ e', RelCacheStep (healEpoch tL) t
            (spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ) e'
            (r1.1.2.cache e') (r2.1.2.cache e')) ∧
          (∀ e', eMax + 1 < e' → r1.1.2.cache e' = none ∧ r2.1.2.cache e' = none) ∧
          r2.1.2.cache (eMax + 1) = some (T', rR', kVal) ∧
          (∀ e', e' ≠ eMax + 1 → r2.1.2.cache e' = hR.cache e') ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
          (eMax + 1 < t ∨ (eMax + 1 = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
            r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 →
            (eMax + 1 ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false))
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startSend
          ctxL P (eMax + 1) vpL.γ vpL.root r_coins).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (t + 1)).startSend
          ctxR P (eMax + 1) vpR.γ vpR.root r_coins).run hR)).run spR) := by
  have hbody : ∀ (coins : CCoins),
      AuthL11.LeComp
        (fun (r1 : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                    PRFPRNG.GameState Sig I K)
             (r2 : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
                    PRFPRNG.GameState Sig I K) =>
          r1.1.1 = none ∨
          ∃ γ' T' rL' rR' kVal,
            r1.1.1 = some (γ', T', rL', fs.initSender kVal) ∧
            r2.1.1 = some (γ', T', rR', fs.initSender kVal) ∧
            RelStepRoot (healEpoch tL) t (spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ)
              (eMax + 1) rL' rR' ∧
            (t ≤ eMax →
              spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ =
                spPinStep (3 + Δcka) tL par t eMax spR.σ ∨
              spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ = none) ∧
            (∀ e', RelCacheStep (healEpoch tL) t
              (spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ) e'
              (r1.1.2.cache e') (r2.1.2.cache e')) ∧
            (∀ e', eMax + 1 < e' → r1.1.2.cache e' = none ∧ r2.1.2.cache e' = none) ∧
            r2.1.2.cache (eMax + 1) = some (T', rR', kVal) ∧
            (∀ e', e' ≠ eMax + 1 → r2.1.2.cache e' = hR.cache e') ∧
            r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
            (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
            r1.2.table = r2.1.2.fTable t ∧
            r1.2.b = true ∧ r2.2.b = false ∧
            (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
            (eMax + 1 < t ∨ (eMax + 1 = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
              r2.2.prf = false) ∧
            r2.2.prng = false ∧
            (healEpoch tL ≤ eMax + 1 →
              (eMax + 1 ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false))
        ((simulateQ (AuthL11.pImpl prng)
          ((do
            let c := cka.send vpL.γ coins
            match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par t (eMax + 1) false c.2.2 vpL.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketState T Sig K I =>
                { s with cache := Function.update s.cache (eMax + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hL)).run spL)
        ((simulateQ (AuthL11.pImpl prng)
          ((do
            let c := cka.send vpR.γ coins
            match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par (t + 1) (eMax + 1) false c.2.2 vpR.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketState T Sig K I =>
                { s with cache := Function.update s.cache (eMax + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hR)).run spR) := by
    intro coins
    rw [hvp.γ_eq]
    simp only [StateT.run_bind, simulateQ_bind]
    refine (leComp_rootSend_step (Δbucket := 3 + Δcka) (par := par)
      prng tL t eMax (cka.send vpR.γ coins).2.2 vpL.root vpR.root
      hL hR spL spR htH hvp.root_rel hcrL hcrR hft htab hbL hbR hσ_lt hprfR_lt hprngR hcorrR).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hroot
    rcases hroot with hnone |
      ⟨rL', rR', kVal, hresL, hresR, hr', hσR_ge, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
        hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1⟩
    · dsimp only at hnone; subst hnone
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hresL hresR
      subst hresL hresR
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨(cka.send vpR.γ coins).1, (cka.send vpR.γ coins).2.1,
        rL', rR', kVal, rfl, rfl, hr', hσR_ge, ?_, ?_, ?_, ?_, hcrL1, hcrR1, hft1, htab1,
        hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1⟩)
      · intro e'
        dsimp only
        by_cases he' : e' = eMax + 1
        · subst he'
          simp only [Function.update_self]
          exact Or.inr ⟨_, rL', rR', kVal, rfl, rfl, hr'⟩
        · rw [Function.update_of_ne he', Function.update_of_ne he', hcL1, hcR1]
          by_cases he'_t : e' = t
          · subst he'_t
            by_cases hle : e' ≤ eMax
            · rcases hσR_ge hle with heq | hnone
              · rw [heq]; exact hcache e'
              · exact (hcache e').change_σ (Or.inr (Or.inl hnone))
            · exact (hcache e').change_σ (Or.inr (Or.inr (hcache_gt e' (by omega))))
          · exact (hcache e').change_σ (Or.inl he'_t)
      · intro e' hgt
        have he' : e' ≠ eMax + 1 := by omega
        dsimp only
        rw [Function.update_of_ne he', Function.update_of_ne he', hcL1, hcR1]
        exact hcache_gt e' (by omega)
      · simp
      · intro e' he'
        dsimp only
        rw [Function.update_of_ne he', hcR1]
  cases r_coins with
  | some coins =>
    simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hplL, hplR, pure_bind]
    exact hbody coins
  | none =>
    simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hplL, hplR,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    rw [simulateQ_bind, StateT.run_bind,
      AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc,
      simulateQ_bind, StateT.run_bind,
      AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    simp only [pure_bind]
    exact hbody coins

theorem leComp_vSend_step
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t e eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {m : M} {r_coins : Option CCoins}
    {hL hR : PRNGBucketState T Sig K I} {spL spR : PRFPRNG.GameState Sig I K}
    (htH : healEpoch tL ≤ t)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) e P vpL vpR)
    (hcache : ∀ e', RelCacheStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax spR.σ) e'
      (hL.cache e') (hR.cache e'))
    (hcache_gt : ∀ e', eMax < e' → hL.cache e' = none ∧ hR.cache e' = none)
    (he_eq_max : P.sendsIn (e + 1) = true → e = eMax)
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
      (fun (r1 : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
                  PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        let e' := if P.sendsIn (e + 1) then e + 1 else e
        let eMax' := if P.sendsIn (e + 1) then eMax + 1 else eMax
        r1.1.1 = none ∨
        ∃ vpL' vpR' c,
          r1.1.1 = some (vpL', c) ∧
          r2.1.1 = some (vpR', c) ∧
          c.1 = (e', vpR'.curCkaMsg) ∧
          RelVPStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax' r2.2.σ) e' P vpL' vpR' ∧
          (∀ e'', RelCacheStep (healEpoch tL) t (spPinStep (3 + Δcka) tL par t eMax' r2.2.σ) e''
            (r1.1.2.cache e'') (r2.1.2.cache e'')) ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          r2.2.prng = false ∧
          (P.sendsIn (e + 1) = true →
            (t ≤ eMax →
              spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ =
                spPinStep (3 + Δcka) tL par t eMax spR.σ ∨
              spPinStep (3 + Δcka) tL par t (eMax + 1) r2.2.σ = none) ∧
            (∀ e'', eMax + 1 < e'' → r1.1.2.cache e'' = none ∧ r2.1.2.cache e'' = none) ∧
            (∃ T' rR' k, vpR'.curCkaMsg = some T' ∧ r2.1.2.cache (e + 1) = some (T', rR', k)) ∧
            (∀ e'', e'' ≠ e + 1 → r2.1.2.cache e'' = hR.cache e'') ∧
            (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
            (eMax + 1 < t ∨ (eMax + 1 = t ∧ inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) →
              r2.2.prf = false) ∧
            (healEpoch tL ≤ eMax + 1 →
              (eMax + 1 ≤ t ∨ inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → r2.2.corr = false)) ∧
          (P.sendsIn (e + 1) = false →
            r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR ∧
            vpR'.curCkaMsg = vpR.curCkaMsg))
      ((simulateQ (AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
          ctxL P vpL m none r_coins).run hL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (t + 1))
          ctxR P vpR m none r_coins).run hR)).run spR) := by
  unfold vSend
  rw [hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R]
  by_cases hsends : P.sendsIn (e + 1) = true
  · have he_max := he_eq_max hsends
    subst he_max
    simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind]
    refine (leComp_startSend_step cka prng fs Δcka qep tL par t e htH hplL hplR hcrL hcrR
      hvp hcache hcache_gt hft htab hbL hbR hσ_lt hprfR_lt hprngR hcorrR).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hss
    rcases hss with hnone |
      ⟨γ', T', rL', rR', kVal, hL_eq, hR_eq, hr', hσR_ge, hc_rel, hc_gt, hc_self, hc_other,
        hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hL_eq hR_eq; subst hL_eq hR_eq
      simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, pure_bind,
        StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, hr'⟩, hc_rel, hcrL1, hcrR1,
        hft1, htab1, hbL1, hbR1, hprng1,
        (fun _ => ⟨hσR_ge, hc_gt, ⟨T', rR', kVal, rfl, hc_self⟩, hc_other, hσ1, hprf1, hcorr1⟩),
        (fun hns => by cases hns)⟩)
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rcases hvSR : vpR.vS with _ | ss
    · have hvSL : vpL.vS = none := hvp.vS_eq.trans hvSR
      simp only [hvSL, hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl, hvp, hcache, hcrL, hcrR,
        hft, htab, hbL, hbR, hprngR, False.elim, (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩)
    · have hvSL : vpL.vS = some ss := hvp.vS_eq.trans hvSR
      simp only [hvSL, hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen,
        hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl,
        ⟨hvp.id_L, rfl, hvp.id_R, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_rel⟩, hcache,
        hcrL, hcrR,
        hft, htab, hbL, hbR, hprngR, False.elim, (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩)

theorem syncStepRaw_h_step {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR spL1 spR1 : PRFPRNG.GameState Sig I K}
    {hL1 hR1 : PRNGBucketState T Sig K I}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR)
    (hcL1 : hL1.cache = esL.h.cache) (hcR1 : hR1.cache = esR.h.cache)
    (hcrL1 : hL1.corrRoot = none) (hcrR1 : hR1.corrRoot = none)
    (hft1 : ∀ t0, t0 ≠ t → hL1.fTable t0 = hR1.fTable t0)
    (htab1 : spL1.table = hR1.fTable t)
    (hbL1 : spL1.b = true) (hbR1 : spR1.b = false)
    (hσR1 : spR1.σ = spR.σ)
    (hσ1 : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL1.σ = spR1.σ)
    (hprf1 : max (esR.g.epoch .A) (esR.g.epoch .B) < t ∨
      (max (esR.g.epoch .A) (esR.g.epoch .B) = t ∧
        inStage2BucketGen (3 + Δcka) tL par (t + 1) = false) → spR1.prf = false)
    (hprng1 : spR1.prng = false)
    (hcorr1 : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) →
      (max (esR.g.epoch .A) (esR.g.epoch .B) ≤ t ∨
        inStage2BucketGen (3 + Δcka) tL par (t + 1) = true) → spR1.corr = false) :
    SyncStepRaw Δcka tL par t { esL with h := hL1 } spL1 { esR with h := hR1 } spR1 := by
  refine ⟨hsync.abortL, hsync.abortR, hsync.g_eq, ?_, ?_, ?_,
    hft1, htab1, hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1, hsync.comp_inv, hsync.trans_epoch,
    ?_, ?_, hsync.epoch_le, hsync.epoch_sends, hcrL1, hcrR1, hsync.pl_false⟩
  · intro P; rw [hσR1]; exact hsync.vp_rel P
  · intro e; rw [hσR1, hcL1, hcR1]; exact hsync.cache_rel e
  · intro e hgt; rw [hcL1, hcR1]; exact hsync.cache_gt_max e hgt
  · intro P hns hpos Tc hTc; rw [hcR1]; exact hsync.vp_curCka P hns hpos Tc hTc
  · intro r hr hpos Tc hTc; rw [hcR1]; exact hsync.trans_cache r hr hpos Tc hTc

theorem syncStepRaw_set_win {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    SyncStepRaw Δcka tL par t { esL with g := { esL.g with win := true } } spL
      { esR with g := { esR.g with win := true } } spR := by
  refine ⟨hsync.abortL, hsync.abortR, ?_, hsync.vp_rel, hsync.cache_rel, hsync.cache_gt_max,
    hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b, hsync.sp_σ_lt, hsync.spR_prf_lt,
    hsync.spR_prng, hsync.spR_corr, hsync.comp_inv, hsync.trans_epoch, hsync.vp_curCka,
    hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
    hsync.corrRoot_L, hsync.corrRoot_R, hsync.pl_false⟩
  have hg := hsync.g_eq
  rcases esL with ⟨gL, hL, abL⟩
  rcases esR with ⟨gR, hR, abR⟩
  rcases gL with ⟨stL, epL, idxL, tLL, trL, chL, cpL, maL, bL, wL, lkL, crL⟩
  rcases gR with ⟨stR, epR, idxR, tLR, trR, chR, cpR, maR, bR, wR, lkR, crR⟩
  dsimp only [AuthL11.eraseSt] at hg ⊢
  injection hg with _ hep hidx htL_eq htr hch hcp hma hb _ hlk hcr
  subst hep hidx htL_eq htr hch hcp hma hb hlk hcr
  rfl

theorem syncStepRaw_of_vRecv_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    {P : Party} {c : Header T × E}
    {vpL' vpR' : VP Γ T (Option Sig) SS RS} {pos : SM.Pos}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esR.g.epoch P + 1)
    (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPStep (healEpoch tL) t
      (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR.σ)
      (max (esR.g.epoch P) c.1.1) P vpL' vpR')
    (hcur_le : c.1.1 ≤ esR.g.epoch P → vpR'.curCkaMsg = (esR.g.st P).curCkaMsg)
    (hnew_le_other : c.1.1 = esR.g.epoch P + 1 → c.1.1 ≤ esR.g.epoch P.other) :
    SyncStepRaw Δcka tL par t
      { esL with g := esL.g.accept P vpL' pos } spL
      { esR with g := esR.g.accept P vpR' pos } spR := by
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
  refine ⟨hsync.abortL, hsync.abortR,
    AuthL11.eraseSt_accept hsync.g_eq P vpL' vpR' pos,
    ?_, ?_, ?_, hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b,
    ?_, ?_, hsync.spR_prng, ?_,
    AuthL11.comp_inv_accept esR.g (2 + Δcka) P vpR' pos hsync.comp_inv,
    ?_, ?_, ?_, ?_, ?_,
    hsync.corrRoot_L, hsync.corrRoot_R, hsync.pl_false⟩
  · intro Q
    dsimp only
    rw [hmax_eq, hacc_ep]
    dsimp only [SM.GameState.accept]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact hvp'
    · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
  · intro e; dsimp only; rw [hmax_eq]; exact hsync.cache_rel e
  · intro e hgt; rw [hmax_eq] at hgt; exact hsync.cache_gt_max e hgt
  · rw [hmax_eq]; exact hsync.sp_σ_lt
  · rw [hmax_eq]; exact hsync.spR_prf_lt
  · rw [hmax_eq]; exact hsync.spR_corr
  · intro r' hr'
    dsimp only at hr' ⊢
    rw [hacc_ep]
    simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'
    obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
    refine ⟨?_, h2⟩
    by_cases hQ : r'.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · intro Q hns_Q hpos_Q Tc hTc
    dsimp only at hns_Q hpos_Q hTc ⊢
    rw [hacc_ep] at hns_Q hpos_Q ⊢
    dsimp only [SM.GameState.accept] at hTc
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self] at hns_Q hpos_Q hTc ⊢
      by_cases hnew : c.1.1 = esR.g.epoch P + 1
      · have hns_e1 : P.sendsIn (esR.g.epoch P + 1) = false := hnew ▸ hns
        have hs_e2 : P.sendsIn ((esR.g.epoch P + 1) + 1) = true :=
          sendsIn_succ_true_of_false P (esR.g.epoch P + 1) hns_e1
        have hmax_e1 : max (esR.g.epoch P) c.1.1 = esR.g.epoch P + 1 := by omega
        rw [hmax_e1, hs_e2] at hns_Q
        cases hns_Q
      · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hmax_e : max (esR.g.epoch P) c.1.1 = esR.g.epoch P := Nat.max_eq_left htle_e
        rw [hmax_e] at hns_Q hpos_Q ⊢
        rw [hcur_le htle_e] at hTc
        exact hsync.vp_curCka P hns_Q hpos_Q Tc hTc
    · simp only [Function.update_of_ne hQ] at hns_Q hpos_Q hTc ⊢
      exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
  · intro r' hr' hpos_r Tc hTc
    dsimp only at hr' ⊢
    simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr'
    exact hsync.trans_cache r' hr'.1 hpos_r Tc hTc
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


/-! ### `ForgedHdr` (`gMain = false`) `Doomed` Helpers & `transmitEBucket` Step -/

@[expose] def DoomedForgedHdrRaw (tL : Option ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    Prop :=
  es.abort = true ∨
  (es.g.win = false ∧
    (∀ P, (es.g.st P).id = P ∧ (es.g.st P).tcur = es.g.epoch P) ∧
    (∀ r ∈ es.g.trans, r.ct.1.1 = r.pos.epoch) ∧
    ∃ cur, es.g.tL = some cur ∧ cur ∈ es.g.leaks ∧ ltOpt tL cur = true)

@[expose] def StepRelStepRaw (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {α : Type}
    (rL rR : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
             PRFPRNG.GameState Sig I K) : Prop :=
  DoomedForgedHdrRaw tL rL.1.2 ∨
  (rL.1.1 = rR.1.1 ∧ SyncStepRaw Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2)

@[expose] def DoomedForgedHdrDF (tL : Option ℕ)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ) :
    Prop :=
  st.1.abort = true ∨
  (st.1.g.win = true ∧ st.2 = none) ∨
  (st.1.g.win = true ∧ ∃ tWin cur,
    st.2 = some tWin ∧ cur ∈ st.1.g.leaks ∧ ltOpt tL cur = true ∧ cur < tWin) ∨
  (st.1.g.win = false ∧ st.2 = none ∧
    (∀ P, (st.1.g.st P).id = P ∧ (st.1.g.st P).tcur = st.1.g.epoch P) ∧
    (∀ r ∈ st.1.g.trans, r.ct.1.1 = r.pos.epoch) ∧
    ∃ cur, st.1.g.tL = some cur ∧ cur ∈ st.1.g.leaks ∧ ltOpt tL cur = true)

theorem authOutBucketPaper_eq_false_of_doomedForgedHdrDF
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δ : ℕ} {tL : Option ℕ}
    {st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    (hd : DoomedForgedHdrDF tL st) :
    authOutBucketPaper Δ tL st = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨_, hnone⟩ | ⟨_, tWin, cur, hsome, hmem, hlt, hcur_lt⟩ | ⟨_, hnone, _⟩
  · dsimp only at hab; cases winEp <;> simp [authOutBucketPaper, authOutBucket, authOut, hab]
  · dsimp only at hnone; subst hnone; rfl
  · dsimp only at hsome hmem; subst hsome
    have hall : es.g.leaks.all (fun l' => !(ltOpt tL l' && decide (l' < tWin))) = false :=
      List.all_eq_false.mpr ⟨cur, hmem, by simp [hlt, hcur_lt]⟩
    simp only [authOutBucketPaper, authOutBucket, authOut, SM.authLosingConditionsAvoided,
      hall, Bool.and_false, Bool.false_and]
  · dsimp only at hnone; subst hnone; rfl

theorem ltOpt_mono {tL : Option ℕ} {c1 c2 : ℕ} (h : ltOpt tL c1 = true) (hle : c1 ≤ c2) :
    ltOpt tL c2 = true := by
  cases tL with
  | none => rfl
  | some l => simp only [ltOpt, decide_eq_true_eq] at h ⊢; omega

theorem healedBy_some_le {cur Δ ep : ℕ}
    (h : SM.healedBy (some cur) Δ ep = true) : cur + Δ ≤ ep := by
  simp only [SM.healedBy, decide_eq_true_eq] at h
  exact h

theorem leComp_of_support_left {α β : Type} {R : α → β → Prop}
    (x : ProbComp α) (y : ProbComp β) (hx : ∀ a ∈ support x, ∀ b ∈ support y, R a b) :
    AuthL11.LeComp R x y := by
  induction x using OracleComp.inductionOn with
  | pure a => exact AuthL11.LeComp.pure_left a y (hx a (by simp))
  | query_bind t r ih =>
    intro F₁ F₂ hF
    rw [bind_assoc, ← OracleComp.evalDist_bind_const (query t) (y >>= F₂)]
    refine AuthL11.evalDist_bind_mono (query t) _ _ fun u _ =>
      ih u (fun a ha => hx a ?_) F₁ F₂ hF
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

theorem support_liftH_g_eq [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (x : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    {r : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
         PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng) ((liftH x).run es)).run sp)) :
    r.1.2.g = es.g ∧ r.1.2.abort = es.abort := by
  rw [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind] at hr
  rw [MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨a, h'⟩, sp'⟩, _, hr2⟩
  simp at hr2
  rcases hr2 with rfl
  exact ⟨rfl, rfl⟩

theorem isHonestHdrPRNGBucket_eq_of_relCacheStep [DecidableEq T]
    {tH t : ℕ} {σ : Sig} {hL hR : PRNGBucketState T Sig K I}
    (hc : ∀ e, RelCacheStep tH t σ e (hL.cache e) (hR.cache e)) (hdr : Header T) :
    isHonestHdrPRNGBucket hL hdr = isHonestHdrPRNGBucket hR hdr := by
  unfold isHonestHdrPRNGBucket
  rcases hc hdr.1 with ⟨hL0, hR0⟩ | ⟨Tc, rL, rR, k, hL1, hR1, _⟩
  · rw [hL0, hR0]
  · rw [hL1, hR1]; cases hdr.2 <;> rfl

private theorem support_vSend_props [DecidableEq I] [Inhabited E] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (ep : ℕ) (m : M) (r_coins : Option CCoins)
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {r : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
          PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {ct : Header T × E}
    (hid : vp.id = P) (htcur : vp.tcur = ep)
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((vSend hk ctx P vp m none r_coins).run h0)).run sp0))
    (hsome : r.1.1 = some (vp', ct)) :
    vp'.id = P ∧ vp'.tcur = (if P.sendsIn (ep + 1) then ep + 1 else ep) ∧ ct.1.1 = vp'.tcur := by
  unfold vSend at hr
  rw [hid, htcur] at hr
  by_cases hs : P.sendsIn (ep + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind, simulateQ_bind,
      MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨res_ss, h1⟩, sp1⟩, _, hr2⟩
    cases res_ss with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr2
      subst hr2; simp at hsome
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss⟩
      simp only [pure_bind, StateT.run_bind, simulateQ_bind,
        MonadAttach.mem_support_bind] at hr2
      rcases hr2 with ⟨⟨⟨res_fs, h2⟩, sp2⟩, _, hr3⟩
      cases res_fs with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
        subst hr3; simp at hsome
      | some ve =>
        rcases ve with ⟨v', e⟩
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
        subst hr3
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr
    cases hvS : vp.vS with
    | none =>
      simp only [hvS, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨rfl, rfl⟩
      simp [hid, htcur, hs]
    | some v =>
      simp only [hvS, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨⟨⟨res_fs, h2⟩, sp2⟩, _, hr3⟩
      cases res_fs with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
        subst hr3; simp at hsome
      | some ve =>
        rcases ve with ⟨v', e⟩
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
        subst hr3
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        simp [hid, htcur, hs]

theorem support_liftH_vSend_props [DecidableEq I] [Inhabited E]
    [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (ep : ℕ) (m : M) (r_coins : Option CCoins) (sp0 : PRFPRNG.GameState Sig I K)
    {es1 : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp1 : PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {ct : Header T × E}
    (hid : (es.g.st P).id = P) (htcur : (es.g.st P).tcur = ep)
    (hr : ((some (vp', ct), es1), sp1) ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((liftH (vSend hk ctx P (es.g.st P) m none r_coins)).run es)).run sp0)) :
    es1.g = es.g ∧ es1.abort = es.abort ∧
      vp'.id = P ∧ vp'.tcur = (if P.sendsIn (ep + 1) then ep + 1 else ep) ∧ ct.1.1 = vp'.tcur := by
  rw [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨res_vs, h1⟩, sp1'⟩, hr_vs, hr2⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
  rcases Prod.mk.inj hr2 with ⟨hpair, rfl⟩
  rcases Prod.mk.inj hpair with ⟨hres, rfl⟩
  exact ⟨rfl, rfl, support_vSend_props prng hk ctx P (es.g.st P) ep m r_coins es.h sp0
    hid htcur hr_vs hres.symm⟩

private theorem support_vRecv_props [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (ep : ℕ) (c : Header T × E) (rec : Option (SM.Record M (Header T × E)))
    (h0 : PRNGBucketState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {r : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
          PRNGBucketState T Sig K I) × PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {t' i' : ℕ} {m' : M}
    (hid : vp.id = P) (htcur : vp.tcur = ep)
    (hr : r ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((vRecv hk ctx P vp c rec).run h0)).run sp0))
    (hsome : r.1.1 = some (some (vp', t', i', m'))) :
    t' = c.1.1 ∧ c.1.1 ≤ ep + 1 ∧ vp'.id = P ∧ vp'.tcur = max ep c.1.1 := by
  unfold vRecv at hr
  dsimp only at hr
  rw [hid, htcur] at hr
  by_cases hrej : (P.sendsIn c.1.1 || decide (ep + 1 < c.1.1)) = true
  · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; simp at hsome
  · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hr
    have htle : c.1.1 ≤ ep + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrej; omega
    by_cases hnew : c.1.1 = ep + 1
    · simp only [hnew, ↓reduceIte] at hr
      cases htn : c.1.2 with
      | none =>
        simp only [htn, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr
        subst hr; simp at hsome
      | some Tn =>
        simp only [htn, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨res_sr, h1⟩, sp1⟩, _, hr2⟩
        rcases res_sr with _ | _ | ⟨γ', σ', rs⟩
        · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr2
          subst hr2; simp at hsome
        · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr2
          subst hr2; simp at hsome
        · simp only [pure_bind, Function.update_self, StateT.run_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr2
          rcases hr2 with ⟨⟨⟨res_fs, h2⟩, sp2⟩, _, hr3⟩
          rcases res_fs with _ | _ | ⟨v', i, m⟩
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
            subst hr3; simp at hsome
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
            subst hr3; simp at hsome
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
            subst hr3
            simp only [Option.some.injEq, Prod.mk.injEq] at hsome
            rcases hsome with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨hnew.symm, htle, rfl, by dsimp only; omega⟩
    · have htle_ep : c.1.1 ≤ ep := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      simp only [hnew, ↓reduceIte, pure_bind] at hr
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; simp at hsome
      | some v =>
        simp only [hvR, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨res_fs, h2⟩, sp2⟩, _, hr3⟩
        rcases res_fs with _ | _ | ⟨v', i, m⟩
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
          subst hr3; simp at hsome
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
          subst hr3; simp at hsome
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr3
          subst hr3
          simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          rcases hsome with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, htle, hid, htcur.trans (Nat.max_eq_left htle_ep).symm⟩

theorem support_liftH_vRecv_props [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (ep : ℕ) (c : Header T × E) (rec : Option (SM.Record M (Header T × E)))
    (sp0 : PRFPRNG.GameState Sig I K)
    {es1 : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp1 : PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {t' i' : ℕ} {m' : M}
    (hid : (es.g.st P).id = P) (htcur : (es.g.st P).tcur = ep)
    (hr : ((some (some (vp', t', i', m')), es1), sp1) ∈ support ((simulateQ (AuthL11.pImpl prng)
      ((liftH (vRecv hk ctx P (es.g.st P) c rec)).run es)).run sp0)) :
    es1.g = es.g ∧ es1.abort = es.abort ∧
      t' = c.1.1 ∧ c.1.1 ≤ ep + 1 ∧ vp'.id = P ∧ vp'.tcur = max ep c.1.1 := by
  rw [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨res_vr, h1⟩, sp1'⟩, hr_vr, hr2⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
  rcases Prod.mk.inj hr2 with ⟨hpair, rfl⟩
  rcases Prod.mk.inj hpair with ⟨hres, rfl⟩
  exact ⟨rfl, rfl, support_vRecv_props prng hk ctx P (es.g.st P) ep c rec es.h sp0
    hid htcur hr_vr hres.symm⟩

theorem epMgmt_preserving_props {St Msg C : Type}
    {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁.win = g.win ∧ s₁.st = g.st ∧ s₁.trans = g.trans ∧
    s₁.epoch P = (if P.sendsIn (g.epoch P + 1) then g.epoch P + 1 else g.epoch P) ∧
    (∀ Q, Q ≠ P → s₁.epoch Q = g.epoch Q) := by
  unfold SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep ⊢
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hc : (bad && !g.safeCh Δ P) = true
      · refine ⟨?_, ?_, ?_, ?_, fun Q hQ => ?_⟩ <;>
          simp [SM.GameState.leak, Function.update_of_ne, *]
      · refine ⟨?_, ?_, ?_, ?_, fun Q hQ => ?_⟩ <;>
          simp [Function.update_of_ne, *]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep ⊢
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem epMgmt_doomed_mem {St Msg C : Type}
    {g s₁ : SM.GameState St Msg C}
    {tL : Option ℕ} {cur Δ qep : ℕ} {P : Party} {bad : Bool}
    (hcur : g.tL = some cur) (hmem : cur ∈ g.leaks) (hlt : ltOpt tL cur = true)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    ∃ cur', s₁.tL = some cur' ∧ cur' ∈ s₁.leaks ∧ ltOpt tL cur' = true := by
  unfold SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hc : (bad && !g.safeCh Δ P) = true
      · simp only [hc, ↓reduceIte, SM.GameState.leak, hcur, SM.maxOpt]
        exact ⟨_, rfl, List.mem_cons_self, ltOpt_mono hlt (Nat.le_max_left _ _)⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨cur, hcur, hmem, hlt⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨cur, hcur, hmem, hlt⟩

theorem doomed_branch4_of_record
    {Δcka : ℕ} {tL : Option ℕ}
    {abort0 : Bool}
    {s₁ : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {st' : VP Γ T (Option Sig) SS RS} {m : M} {ct : Header T × E}
    {h' : PRNGBucketState T Sig K I} {ep0 cur : ℕ}
    (hwin1 : s₁.win = false)
    (hvp_s1 : ∀ Q, Q ≠ P → (s₁.st Q).id = Q ∧ (s₁.st Q).tcur = s₁.epoch Q)
    (htr_s1 : ∀ r ∈ s₁.trans, r.ct.1.1 = r.pos.epoch)
    (hep_P : s₁.epoch P = if P.sendsIn (ep0 + 1) then ep0 + 1 else ep0)
    (hst'_id : st'.id = P)
    (hst'_tcur : st'.tcur = if P.sendsIn (ep0 + 1) then ep0 + 1 else ep0)
    (hct_ep : ct.1.1 = st'.tcur)
    (hcur : s₁.tL = some cur) (hmem : cur ∈ s₁.leaks) (hlt : ltOpt tL cur = true) :
    DoomedForgedHdrDF tL
      ({ g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false
         h := h'
         abort := abort0 }, none) := by
  refine Or.inr (Or.inr (Or.inr ⟨hwin1, rfl, ?_, ?_, ⟨cur, hcur, hmem, hlt⟩⟩))
  · intro Q
    dsimp only [SM.GameState.record]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact ⟨hst'_id, hst'_tcur.trans hep_P.symm⟩
    · simp only [Function.update_of_ne hQ]; exact hvp_s1 Q hQ
  · intro r hr
    dsimp only [SM.GameState.record] at hr ⊢
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hct_ep.trans (hst'_tcur.trans hep_P.symm)
    · exact htr_s1 r hr'

theorem doomed_branch4_of_accept [DecidableEq T] [DecidableEq E]
    {tL : Option ℕ} {abort0 : Bool}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {P : Party} {vp' : VP Γ T (Option Sig) SS RS} {pos : SM.Pos}
    {h' : PRNGBucketState T Sig K I} {cur : ℕ}
    (hwin : es.g.win = false)
    (hvp_inv : ∀ Q, (es.g.st Q).id = Q ∧ (es.g.st Q).tcur = es.g.epoch Q)
    (htr_inv : ∀ r ∈ es.g.trans, r.ct.1.1 = r.pos.epoch)
    (hvp'_id : vp'.id = P)
    (hvp'_tcur : vp'.tcur = max (es.g.epoch P) pos.epoch)
    (hcur : es.g.tL = some cur) (hmem : cur ∈ es.g.leaks) (hlt : ltOpt tL cur = true) :
    DoomedForgedHdrDF tL ({ g := es.g.accept P vp' pos, h := h', abort := abort0 }, none) := by
  refine Or.inr (Or.inr (Or.inr ⟨hwin, rfl, ?_, ?_, ⟨cur, hcur, hmem, hlt⟩⟩))
  · intro Q
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact ⟨hvp'_id, hvp'_tcur⟩
    · simp only [Function.update_of_ne hQ]; exact hvp_inv Q
  · intro r hr
    dsimp only [SM.GameState.accept, SM.GameState.delete] at hr ⊢
    rw [List.mem_filter] at hr
    exact htr_inv r hr.1

theorem vSend_hooksPRNGBucketForgedHdr_eq
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    vSend (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) :=
  rfl

theorem vRecv_hooksPRNGBucketForgedHdr_eq
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    vRecv (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) :=
  rfl

theorem commitE_hooksPRNGBucketForgedHdr_eq
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    commitE (M := M) (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      commitE (M := M) (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) :=
  rfl

theorem leComp_transmitEBucket_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (arg : Party × M × Option CCoins)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep arg).run esL)).run spL)
      ((simulateQ (AuthL11.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep arg).run esR)).run spR) := by
  rcases arg with ⟨P, m, r_coins⟩
  unfold transmitEBucket
  rw [vSend_hooksPRNGBucketForgedHdr_eq, vSend_hooksPRNGBucketForgedHdr_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, AuthL11.eraseSt_win hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁L, s₁R, h1, h2, hs₁_er, hs₁L_st, hs₁R_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · if hpl1 : postLeak tL s₁R = true then
        have hplL1 : postLeak tL s₁L = true := (eraseSt_postLeak hs₁_er).trans hpl1
        have hplL0 : postLeak tL esL.g = false :=
          (eraseSt_postLeak hsync.g_eq).trans hsync.pl_false
        have hwinR : esR.g.win = false := by simpa using habw
        have hwinL : esL.g.win = false := (AuthL11.eraseSt_win hsync.g_eq).trans hwinR
        obtain ⟨hs₁_win, hs₁_st, hs₁_tr, hs₁_epP, hs₁_epQ⟩ := epMgmt_preserving_props h1
        have hep_eq : esL.g.epoch = esR.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
        have htr_eq : esL.g.trans = esR.g.trans := congrArg (fun g => g.trans) hsync.g_eq
        have hvpL_inv : ∀ Q, (esL.g.st Q).id = Q ∧ (esL.g.st Q).tcur = esL.g.epoch Q :=
          fun Q => ⟨(hsync.vp_rel Q).id_L, (hsync.vp_rel Q).tcur_L.trans (congrFun hep_eq Q).symm⟩
        have htrL_inv : ∀ r ∈ esL.g.trans, r.ct.1.1 = r.pos.epoch := fun r hr =>
          (hsync.trans_epoch r (by rwa [← htr_eq])).2
        obtain ⟨cur, hcur, hmem, hlt_cur⟩ :
            ∃ cur, s₁L.tL = some cur ∧ cur ∈ s₁L.leaks ∧ ltOpt tL cur = true := by
          have h1' := h1
          unfold SM.GameState.epMgmt at h1'
          by_cases hs : P.sendsIn (esL.g.epoch P + 1) = true
          · simp only [hs, ↓reduceIte] at h1'
            by_cases hq : qep < esL.g.epoch P + 1
            · simp [hq] at h1'
            · simp only [hq, ↓reduceIte, Option.some.injEq] at h1'
              by_cases hc : (r_coins.isSome && !esL.g.safeCh (2 + Δcka) P) = true
              · simp only [hc, ↓reduceIte] at h1'
                subst h1'
                exact ⟨SM.maxOpt esL.g.tL (esL.g.epoch P + 1), rfl,
                  by simp [SM.GameState.leak],
                  by simpa [postLeak, SM.GameState.leak] using hplL1⟩
              · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h1'
                subst h1'
                simp only [postLeak] at hplL0 hplL1
                rw [hplL0] at hplL1
                cases hplL1
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h1'
            by_cases hq : qep < esL.g.epoch P
            · simp [hq] at h1'
            · simp only [hq, ↓reduceIte, Option.some.injEq] at h1'
              subst h1'
              rw [hplL0] at hplL1
              cases hplL1
        simp only [h1, h2]
        refine leComp_of_support_left _ _ fun a ha _ _ => Or.inl ?_
        simp only [hs₁_st, StateT.run_bind, simulateQ_bind] at ha
        rw [MonadAttach.mem_support_bind] at ha
        rcases ha with ⟨⟨⟨res_vs, es1⟩, sp1⟩, hr_vs, hr_rest⟩
        cases res_vs with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          subst hr_rest; exact Or.inl rfl
        | some vc =>
          rcases vc with ⟨st', ct⟩
          simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          subst hr_rest
          obtain ⟨_, _, hst'_id, hst'_tcur, hct_ep⟩ := support_liftH_vSend_props prng
            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) s₁L P esL
            (esL.g.epoch P) m r_coins spL
            (hvpL_inv P).1 (hvpL_inv P).2 hr_vs
          refine Or.inr ⟨hs₁_win.trans hwinL, ?_, ?_,
            ⟨cur, by simpa [SM.GameState.record] using hcur,
              by simpa [SM.GameState.record] using hmem, hlt_cur⟩⟩
          · intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact ⟨hst'_id, hst'_tcur.trans hs₁_epP.symm⟩
            · simp only [Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ]; exact hvpL_inv Q
          · intro rec hrec
            dsimp only [SM.GameState.record] at hrec ⊢
            rcases List.mem_cons.mp hrec with rfl | hr'
            · exact hct_ep.trans (hst'_tcur.trans hs₁_epP.symm)
            · rw [hs₁_tr] at hr'; exact htrL_inv rec hr'
      else
      have hplR1 : postLeak tL s₁R = false := Bool.eq_false_iff.mpr hpl1
      have hplL1 : postLeak tL s₁L = false := (eraseSt_postLeak hs₁_er).trans hplR1
      simp only [h1, h2, hs₁L_st, hs₁R_st, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind,
        bind_assoc]
      have hheq : P.sendsIn (esR.g.epoch P + 1) = true →
          esR.g.epoch P = esR.g.epoch P.other :=
        AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
      have he_eq_max : P.sendsIn (esR.g.epoch P + 1) = true →
          esR.g.epoch P = max (esR.g.epoch .A) (esR.g.epoch .B) :=
        fun hsends => (AuthL11.max_epoch_eq_of_eq (hheq hsends)).symm
      refine (leComp_vSend_step cka prng fs Δcka qep tL par t (esR.g.epoch P)
        (max (esR.g.epoch .A) (esR.g.epoch .B)) htH hplL1 hplR1
        hsync.corrRoot_L hsync.corrRoot_R (hsync.vp_rel P) hsync.cache_rel
        hsync.cache_gt_max he_eq_max hsync.fTable_ne hsync.table_t hsync.spL_b hsync.spR_b
        hsync.sp_σ_lt hsync.spR_prf_lt hsync.spR_prng hsync.spR_corr).bind ?_
      rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvs
      rcases hvs with hnone |
        ⟨vpL', vpR', c, hL_eq, hR_eq, hc_hdr, hvp', hc_rel, hcrL1, hcrR1, hft1, htab1,
          hbL1, hbR1, hprng1, hsends_props, hns_props⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
      · dsimp only at hL_eq hR_eq; subst hL_eq hR_eq
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine AuthL11.LeComp.pure ?_
        have hs₁_ep : s₁R.epoch P = if P.sendsIn (esR.g.epoch P + 1) then esR.g.epoch P + 1
            else esR.g.epoch P := by
          rw [hs₁_ep_fn]; split <;> simp
        have hs₁_ep_other : ∀ Q, Q ≠ P → s₁R.epoch Q = esR.g.epoch Q := by
          intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
        have hs₁_comp := hs₁_comp_imp hsync.comp_inv
        have hs₁_max : max (s₁R.epoch .A) (s₁R.epoch .B) =
            if P.sendsIn (esR.g.epoch P + 1) then max (esR.g.epoch .A) (esR.g.epoch .B) + 1
            else max (esR.g.epoch .A) (esR.g.epoch .B) := by
          rw [hs₁_ep_fn]
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · simp only [hsends, ↓reduceIte]
            rw [AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
          · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
        refine Or.inr ⟨rfl, ⟨hsync.abortL, hsync.abortR, ?_, ?_, ?_, ?_, hft1, htab1,
          hbL1, hbR1, ?_, ?_, hprng1, ?_,
          AuthL11.comp_inv_record s₁R (2 + Δcka) P vpR' _ false rfl hs₁_comp,
          ?_, ?_, ?_, ?_, ?_, hcrL1, hcrR1, hplR1⟩⟩
        · rw [AuthL11.eraseSt_epoch hs₁_er, AuthL11.eraseSt_idx hs₁_er]
          exact AuthL11.eraseSt_record hs₁_er (2 + Δcka) P vpL' vpR' _ false
        · intro Q
          dsimp only [SM.GameState.record]
          rw [hs₁_max]
          by_cases hQ : Q = P
          · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
          · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st, hs₁R_st]
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · simp only [hsends, ↓reduceIte]
              obtain ⟨hσR_ge, _⟩ := hsends_props hsends
              by_cases hQt : esR.g.epoch Q = t
              · have hle_max : t ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
                  rw [← hQt]; cases Q <;> simp
                rcases hσR_ge hle_max with heq | hnone
                · rw [heq]; exact hsync.vp_rel Q
                · exact (hsync.vp_rel Q).change_σ (Or.inr hnone)
              · exact (hsync.vp_rel Q).change_σ (Or.inl hQt)
            · simp only [hsends]
              obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props (Bool.eq_false_iff.mpr hsends)
              dsimp only at hspR_eq; rw [hspR_eq]; exact hsync.vp_rel Q
        · intro e'; dsimp only [SM.GameState.record]; rw [hs₁_max]; exact hc_rel e'
        · intro e' hgt
          dsimp only [SM.GameState.record] at hgt ⊢
          rw [hs₁_ep_fn] at hgt
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · simp only [hsends, ↓reduceIte] at hgt
            rw [AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends] at hgt
            exact (hsends_props hsends).2.1 e' hgt
          · have hns := Bool.eq_false_iff.mpr hsends
            simp only [hns, Bool.false_eq_true, ↓reduceIte] at hgt
            obtain ⟨hhL1, hhR1, _⟩ := hns_props hns
            dsimp only at hhL1 hhR1; rw [hhL1, hhR1]
            exact hsync.cache_gt_max e' hgt
        · dsimp only [SM.GameState.record]
          rw [hs₁_ep_fn]
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · simp only [hsends, ↓reduceIte]
            rw [AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
            exact (hsends_props hsends).2.2.2.2.1
          · have hns := Bool.eq_false_iff.mpr hsends
            simp only [hns, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨_, _, hspL_eq, hspR_eq, _⟩ := hns_props hns
            dsimp only at hspL_eq hspR_eq; rw [hspL_eq, hspR_eq]
            exact hsync.sp_σ_lt
        · dsimp only [SM.GameState.record]
          rw [hs₁_ep_fn]
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · simp only [hsends, ↓reduceIte]
            rw [AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
            exact (hsends_props hsends).2.2.2.2.2.1
          · have hns := Bool.eq_false_iff.mpr hsends
            simp only [hns, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props hns
            dsimp only at hspR_eq; rw [hspR_eq]
            exact hsync.spR_prf_lt
        · dsimp only [SM.GameState.record]
          rw [hs₁_ep_fn]
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · simp only [hsends, ↓reduceIte]
            rw [AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
            exact (hsends_props hsends).2.2.2.2.2.2
          · have hns := Bool.eq_false_iff.mpr hsends
            simp only [hns, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props hns
            dsimp only at hspR_eq; rw [hspR_eq]
            exact hsync.spR_corr
        · intro r hr
          dsimp only [SM.GameState.record] at hr ⊢
          rcases List.mem_cons.mp hr with rfl | hr'
          · refine ⟨le_rfl, ?_⟩
            dsimp only
            rw [hc_hdr, hs₁_ep]
          · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
            refine ⟨?_, h_eq⟩
            by_cases hQ : r.pos.sender = P
            · rw [hQ, hs₁_ep]; rw [hQ] at h_le; split <;> omega
            · rw [hs₁_ep_other _ hQ]; exact h_le
        · intro Q hns_Q hpos_Q Tc hTc
          dsimp only [SM.GameState.record] at hns_Q hpos_Q hTc ⊢
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · obtain ⟨_, _, ⟨T', rR', k, hT', hc_self⟩, hc_other, _⟩ := hsends_props hsends
            have heq_other := hheq hsends
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte] at hTc ⊢
              rw [hT'] at hTc; cases hTc
              exact ⟨rR', k, hc_self⟩
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁R_st] at hns_Q hpos_Q hTc ⊢
              have hne : esR.g.epoch Q ≠ esR.g.epoch P + 1 := by
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other ⊢ <;> omega
              rw [hc_other _ hne]
              exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
            obtain ⟨_, hhR1, _, _, hcur_eq⟩ := hns_props hns
            dsimp only at hhR1
            rw [hhR1]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁_ep, hns, Bool.false_eq_true, ↓reduceIte] at hpos_Q hTc ⊢
              rw [hcur_eq] at hTc
              exact hsync.vp_curCka P hns hpos_Q Tc hTc
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁R_st] at hns_Q hpos_Q hTc ⊢
              exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
        · intro r hr hpos_r Tc hTc
          dsimp only [SM.GameState.record] at hr ⊢
          rcases List.mem_cons.mp hr with rfl | hr'
          · dsimp only at hpos_r hTc ⊢
            rw [hc_hdr] at hTc
            dsimp only at hTc
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · obtain ⟨_, _, ⟨T', rR', k, hT', hc_self⟩, _⟩ := hsends_props hsends
              rw [hs₁_ep, hsends]
              simp only [↓reduceIte]
              rw [hT'] at hTc; cases hTc
              exact ⟨rR', k, hc_self⟩
            · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, hhR1, _, _, hcur_eq⟩ := hns_props hns
              dsimp only at hhR1
              rw [hhR1]
              rw [hs₁_ep] at hpos_r ⊢
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hpos_r ⊢
              rw [hcur_eq] at hTc
              exact hsync.vp_curCka P hns hpos_r Tc hTc
          · have hr_mem : r ∈ esR.g.trans := hs₁_trans ▸ hr'
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · obtain ⟨_, _, _, hc_other, _⟩ := hsends_props hsends
              have heq_other := hheq hsends
              have hr_le := (hsync.trans_epoch r hr_mem).1
              have hne : r.pos.epoch ≠ esR.g.epoch P + 1 := by
                cases hS : r.pos.sender <;> cases P <;>
                  simp [Party.other, hS] at heq_other hr_le ⊢ <;> omega
              rw [hc_other _ hne]
              exact hsync.trans_cache r hr_mem hpos_r Tc hTc
            · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, hhR1, _⟩ := hns_props hns
              dsimp only at hhR1
              rw [hhR1]
              exact hsync.trans_cache r hr_mem hpos_r Tc hTc
        · intro Q
          dsimp only [SM.GameState.record]
          rw [hs₁_ep_fn]
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · have heq_other := hheq hsends
            simp only [hsends, ↓reduceIte]
            cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
          · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
            exact hsync.epoch_le Q
        · intro Q hlt_Q
          dsimp only [SM.GameState.record] at hlt_Q ⊢
          rw [hs₁_ep_fn] at hlt_Q ⊢
          by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
          · have heq_other := hheq hsends
            simp only [hsends, ↓reduceIte] at hlt_Q ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hsends
            · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hlt_Q ⊢
            exact hsync.epoch_sends Q hlt_Q

end StepHooks2

end CryptoGames.SM.Construction.DeliverForge
