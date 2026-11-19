/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2StepHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2StepHooks2
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal MeasureTheory
open OracleComp OracleSpec
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.SM (GameState Pos Record healedBy ltOpt maxOpt)
open CryptoGames.SM.Construction (Header healEpoch mkParties realParty)
open CryptoGames.SM.Engine
  (Ctx EState HM Hooks VP abortE authOut coinsE commitE deliverE injectE liftH vRecv vSend)

namespace CryptoGames.SM.Construction.DeliverForge

section StepCoupling

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

private theorem leComp_deliverE_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((deliverE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          fs.maxSkip (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((deliverE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  rw [vRecv_hooksPRNGBucketForgedHdr_eq, vRecv_hooksPRNGBucketForgedHdr_eq,
    commitE_hooksPRNGBucketForgedHdr_eq, commitE_hooksPRNGBucketForgedHdr_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esR.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold CryptoGames.SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esL.g.mustBeCorrect fs.maxSkip P r = esR.g.mustBeCorrect fs.maxSkip P r := by
        simp [CryptoGames.SM.GameState.mustBeCorrect, CryptoGames.SM.Construction.AuthL11.eraseSt_comp hsync.g_eq,
          CryptoGames.SM.Construction.AuthL11.eraseSt_maxAcc hsync.g_eq]
      have hr_ep := hsync.trans_epoch r hr_mem.1
      have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
      have hc_hit : c.1.1 = esR.g.epoch P + 1 → ∀ tn0, c.1.2 = some tn0 →
          ∃ rR kc, esR.h.cache (esR.g.epoch P + 1) = some (tn0, rR, kc) := by
        intro hnew tn0 htn0
        have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2]; exact htn0
        rw [← hnew, ← hr_pos_ep]
        exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2
      simp only [hmust_eq, StateT.run_bind, CryptoGames.SM.Construction.AuthL11.run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecv_cached_step cka prng fs Δcka qep tL par t
        (hsync.vp_rel P) hsync.cache_rel hsync.corrRoot_L hsync.corrRoot_R hc_hit).bind ?_
      rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvr
      rcases hvr with ⟨hL_none, hR_none, hhL1, hhR1, hspL1, hspR1⟩ |
        ⟨vpL', vpR', i', m', hL_some, hR_some, htle, hns, hvp', hhL1, hhR1, hspL1, hspR1, hcur_le⟩
      · dsimp only at hL_none hR_none hhL1 hhR1 hspL1 hspR1
        subst hL_none hR_none hhL1 hhR1 hspL1 hspR1
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        by_cases hmust : ((bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).deliverWin &&
            esR.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepRaw_set_win hsync⟩)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · dsimp only at hL_some hR_some hhL1 hhR1 hspL1 hspR1
        subst hL_some hR_some hhL1 hhR1 hspL1 hspR1
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucket,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [CryptoGames.SM.Construction.AuthL11.eraseSt_chall hsync.g_eq]
        have hs_acc := syncStepRaw_of_vRecv_accept hsync hr_pos_ep htle hns hvp' hcur_le
          (fun _ => by rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1)
        by_cases hwin_cond : (((bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).deliverWin &&
            esR.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg))) = true
        · simp only [hwin_cond, ↓reduceIte]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepRaw_set_win hs_acc⟩)
        · simp only [hwin_cond, Bool.false_eq_true, ↓reduceIte]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs_acc⟩)

private theorem leComp_injectE_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  rw [vRecv_hooksPRNGBucketForgedHdr_eq, vRecv_hooksPRNGBucketForgedHdr_eq,
    commitE_hooksPRNGBucketForgedHdr_eq, commitE_hooksPRNGBucketForgedHdr_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq, CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (false || esR.g.win || (esR.g.inTransit P.other c).isSome ||
      !esR.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, CryptoGames.SM.Construction.AuthL11.run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esR.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have heMax : esR.g.epoch P ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
      cases P <;> simp
    refine (leComp_vRecv_inject_step cka prng fs Δcka qep tL par t
      (max (esR.g.epoch .A) (esR.g.epoch .B)) (hsync.vp_rel P) hsync.cache_rel heMax
      ((eraseSt_postLeak hsync.g_eq).trans hsync.pl_false) hsync.pl_false
      hsync.corrRoot_L hsync.corrRoot_R
      hsync.fTable_ne hsync.table_t hsync.spL_b hsync.spR_b
      hsync.sp_σ_lt hsync.spR_prf_lt hsync.spR_prng hsync.spR_corr).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvr
    rcases hvr with hnone |
      ⟨hL_none, hR_none, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩ |
      ⟨vpL', vpR', i', m', hL_some, hR_some, htle, hns, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
        hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1, hle_props⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
    · dsimp only at hL_none hR_none; subst hL_none hR_none
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
        syncStepRaw_h_step hsync hcL1 hcR1 hcrL1 hcrR1 hft1 htab1 hbL1 hbR1 hσR1 hσ1 hprf1 hprng1 hcorr1⟩)
    · dsimp only at hL_some hR_some; subst hL_some hR_some
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      have hs1 := syncStepRaw_h_step hsync hcL1 hcR1 hcrL1 hcrR1 hft1 htab1 hbL1 hbR1 hσR1 hσ1 hprf1 hprng1 hcorr1
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)
      · simp only [hqep, ↓reduceIte]
        rw [CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.g_eq]
        by_cases htriv : esR.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esR.g.epoch P + 1 := by
            intro heq
            rw [heq] at htriv
            have htf := CryptoGames.SM.Construction.AuthL11.trivial_false_of_safeInj esR.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv
            cases htriv
          have htle_ep : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hne_e1)
          obtain ⟨hvp_ep, hcur_eq, hhL1, hhR1, hspL1, hspR1⟩ := hle_props htle_ep
          dsimp only at hhL1 hhR1 hspL1 hspR1
          subst hhL1 hhR1 hspL1 hspR1
          have hvp_max : RelVPStep (healEpoch tL) t
              (spPinStep (3 + Δcka) tL par t (max (esR.g.epoch .A) (esR.g.epoch .B)) spR1.σ)
              (max (esR.g.epoch P) c.1.1) P vpL' vpR' := by
            rw [Nat.max_eq_left htle_ep]; exact hvp_ep
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucket,
            StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncStepRaw_of_vRecv_accept hsync rfl htle hns hvp_max
              (fun _ => hcur_eq) (fun heq => False.elim (hne_e1 heq))⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepRaw_set_win hs1⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1⟩)

private theorem leComp_deliverForgeE_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E) × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  rw [vRecv_hooksPRNGBucketForgedHdr_eq, vRecv_hooksPRNGBucketForgedHdr_eq,
    commitE_hooksPRNGBucketForgedHdr_eq, commitE_hooksPRNGBucketForgedHdr_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq, CryptoGames.SM.Construction.AuthL11.eraseSt_comp hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      rw [CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq]
      by_cases hrej : ((esR.g.inTransit P.other c').isSome || esR.g.comp.contains r.pos ||
          (c.1 != c'.1)) = true
      · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hrej, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, CryptoGames.SM.Construction.AuthL11.run_liftH, simulateQ_bind, bind_assoc]
        have hhdr_eq : c.1 = c'.1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hrej
          exact hrej.2
        have hr_mem : r ∈ esR.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
          unfold CryptoGames.SM.GameState.inTransit at htr
          have hfind := List.find?_some htr
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
          exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hc'_ep_eq : c'.1.1 = r.pos.epoch := by
          rw [← hhdr_eq, ← hr_mem.2.2, hr_ep.2]
        have hc_hit : c'.1.1 = esR.g.epoch P + 1 → ∀ tn0, c'.1.2 = some tn0 →
            ∃ rR kc, esR.h.cache (esR.g.epoch P + 1) = some (tn0, rR, kc) := by
          intro hnew tn0 htn0
          have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2, hhdr_eq]; exact htn0
          rw [← hnew, hc'_ep_eq]
          exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2
        refine (leComp_vRecv_cached_step cka prng fs Δcka qep tL par t
          (hsync.vp_rel P) hsync.cache_rel hsync.corrRoot_L hsync.corrRoot_R hc_hit).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvr
        rcases hvr with ⟨hL_none, hR_none, hhL1, hhR1, hspL1, hspR1⟩ |
          ⟨vpL', vpR', i', m', hL_some, hR_some, htle, hns, hvp', hhL1, hhR1, hspL1, hspR1, hcur_le⟩
        · dsimp only at hL_none hR_none hhL1 hhR1 hspL1 hspR1
          subst hL_none hR_none hhL1 hhR1 hspL1 hspR1
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
        · dsimp only at hL_some hR_some hhL1 hhR1 hspL1 hspR1
          subst hL_some hR_some hhL1 hhR1 hspL1 hspR1
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
          by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
          · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
          · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
            rw [CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.g_eq]
            by_cases htriv : esR.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucket,
                StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
              exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
                syncStepRaw_of_vRecv_accept hsync rfl htle hns hvp' hcur_le
                  (fun _ => by rw [hc'_ep_eq, ← hr_mem.2.1]; exact hr_ep.1)⟩)
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : (bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).injectFull c'.1.1 = true
              · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepRaw_set_win hsync⟩)
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)

private theorem leComp_corrEPaperBucket_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (_htH : healEpoch tL ≤ t)
    (P : Party)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          P).run esL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((corrEPaperBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          P).run esR)).run spR) := by
  unfold corrEPaperBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_corrAllowedPaper hsync.g_eq P]
  by_cases hguard : (false || esR.g.win || !esR.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hac_er := CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hsync.g_eq P
    have hvp := hsync.vp_rel P
    have hep_eq : esL.g.epoch = esR.g.epoch := CryptoGames.SM.Construction.AuthL11.eraseSt_epoch hsync.g_eq
    by_cases hcond : (!(esR.g.epoch P < healEpoch tL) ||
        !(max (esR.g.epoch .A) (esR.g.epoch .B) < healEpoch tL)) = true
    · have hcondL : (!((esL.g.st P).tcur < healEpoch tL) ||
          !(max (esL.g.epoch .A) (esL.g.epoch .B) < healEpoch tL)) = true := by
        simpa only [hvp.tcur_L, hep_eq] using hcond
      simp only [StateT.run_bind, CryptoGames.SM.Construction.AuthL11.run_liftH,
        hooksPRNGBucketForgedHdr, hooksPRNGBucketForgedHdrGen,
        hcondL, ↓reduceIte, StateT.run_pure, pure_bind, abortE,
        StateT.run_modify, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
    · have hcondL : (!((esL.g.st P).tcur < healEpoch tL) ||
          !(max (esL.g.epoch .A) (esL.g.epoch .B) < healEpoch tL)) = false := by
        simpa only [hvp.tcur_L, hep_eq] using Bool.eq_false_iff.mpr hcond
      have hcondR : (!((esR.g.st P).tcur < healEpoch tL) ||
          !(max (esR.g.epoch .A) (esR.g.epoch .B) < healEpoch tL)) = false := by
        simpa only [hvp.tcur_R] using Bool.eq_false_iff.mpr hcond
      have he_lt : esR.g.epoch P < healEpoch tL := by
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hcond
        exact of_decide_eq_true hcond.1
      obtain ⟨σ, hrL, hrR⟩ : ∃ σ, (esL.g.st P).root = some σ ∧ (esR.g.st P).root = some σ := by
        rcases hvp.root_rel with ⟨_, h⟩ | ⟨hle, _⟩ | ⟨heq, _⟩ | ⟨hgt, _⟩
        · exact h
        · omega
        · omega
        · omega
      simp only [StateT.run_bind, CryptoGames.SM.Construction.AuthL11.run_liftH,
        hooksPRNGBucketForgedHdr, hooksPRNGBucketForgedHdrGen,
        hcondL, hcondR, Bool.false_eq_true, ↓reduceIte,
        hrL, hrR, StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure]
      by_cases hlt_max : ltOpt tL (max (esR.g.epoch .A) (esR.g.epoch .B)) = true
      · have hwinR : esR.g.win = false := by
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
          exact hguard.1.2
        have hwinL : esL.g.win = false := (CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq).trans hwinR
        have htr_eq : esL.g.trans = esR.g.trans := congrArg (fun g => g.trans) hsync.g_eq
        have hvpL_inv : ∀ Q, (esL.g.st Q).id = Q ∧ (esL.g.st Q).tcur = esL.g.epoch Q :=
          fun Q => ⟨(hsync.vp_rel Q).id_L, (hsync.vp_rel Q).tcur_L.trans (congrFun hep_eq Q).symm⟩
        have htrL_inv : ∀ r ∈ esL.g.trans, r.ct.1.1 = r.pos.epoch := fun r hr =>
          (hsync.trans_epoch r (by rwa [← htr_eq])).2
        refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inr ⟨hwinL, hvpL_inv, htrL_inv,
          CryptoGames.SM.maxOpt esL.g.tL (max (esL.g.epoch .A) (esL.g.epoch .B)),
          by simp [CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak],
          by simp [CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak],
          by rw [hep_eq]; exact ltOpt_mono hlt_max (by cases esL.g.tL <;> simp [CryptoGames.SM.maxOpt])⟩))
      · have hlt_max_false : ltOpt tL (max (esR.g.epoch .A) (esR.g.epoch .B)) = false :=
          Bool.eq_false_iff.mpr hlt_max
        have hpl_ac : postLeak tL (esR.g.afterCorr P) = false := by
          have hpl0 := hsync.pl_false
          simp only [postLeak, CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak] at hpl0 ⊢
          cases htLR : esR.g.tL with
          | none => simp [CryptoGames.SM.maxOpt, hlt_max_false]
          | some prev =>
            rw [htLR] at hpl0
            simp only [CryptoGames.SM.maxOpt]
            cases tL with
            | none => simp [ltOpt] at hpl0
            | some l =>
              simp only [ltOpt, decide_eq_false_iff_not] at hpl0 hlt_max_false ⊢
              omega
        refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨?_, ?_⟩)
        · dsimp only [realParty]
          rw [hvp.id_L, hvp.id_R, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_L, hvp.tcur_R, hvp.vS_eq,
            funext hvp.vR_eq]
        · exact ⟨hsync.abortL, hsync.abortR, hac_er, hsync.vp_rel, hsync.cache_rel,
            hsync.cache_gt_max, hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b,
            hsync.sp_σ_lt, hsync.spR_prf_lt, hsync.spR_prng, hsync.spR_corr,
            CryptoGames.SM.Construction.AuthL11.comp_inv_afterCorr esR.g (2 + Δcka) (by omega) P
              (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv,
            hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
            hsync.epoch_le, hsync.epoch_sends, hsync.corrRoot_L, hsync.corrRoot_R, hpl_ac⟩


private theorem run_commitE_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : CryptoGames.SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  rw [commitE_hooksPRNGBucketForgedHdr_eq]
  exact run_commitE_PRNGBucket cka prng fs Δcka qep tL par t s P old new pos es

private theorem leComp_implEDFPaperBucketRaw_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepRaw Δcka tL par t esL spL esR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelStepRaw Δcka tL par t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((implEDFPaperBucketRaw (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((implEDFPaperBucketRaw (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (t + 1))
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esR)).run spR) := by
  rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
  · simp [implEDFPaperBucketRaw, coinsE, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind _ fun u _ => CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · exact leComp_transmitEBucket_step cka prng fs Δcka qep tL par t htH arg hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
      StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · exact leComp_deliverE_step cka prng fs Δcka qep tL par t arg hsync
  · exact leComp_injectE_step cka prng fs Δcka qep tL par t arg hsync
  · exact leComp_corrEPaperBucket_step cka prng fs Δcka qep tL par t htH P hsync
  · exact leComp_deliverForgeE_step cka prng fs Δcka qep tL par t df hsync

private def SyncForgedHdrDF
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (stL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (spL : CryptoGames.PRFPRNG.GameState Sig I K)
    (stR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (spR : CryptoGames.PRFPRNG.GameState Sig I K) : Prop :=
  SyncStepRaw Δcka tL par t stL.1 spL stR.1 spR ∧
  stL.2 = stR.2 ∧
  (stR.1.g.win = false → stR.2 = none)

private def StepRelForgedHdrDF (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {α : Type}
    (rL rR : (α × (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
             CryptoGames.PRFPRNG.GameState Sig I K) : Prop :=
  DoomedForgedHdrDF tL rL.1.2 ∨
  (rL.1.1 = rR.1.1 ∧ SyncForgedHdrDF Δcka tL par t rL.1.2 rL.2 rR.1.2 rR.2)

private def stepPBucketForgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    ProbComp (((CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      CryptoGames.PRFPRNG.GameState Sig I K) :=
  (simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
    ((implEDFPaperBucketMode
      (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket q).run st)).run sp

private theorem stepPBucketForgedHdr_state_eq_of_abort_or_win
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (winEp : Option ℕ) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (haw : es.abort = true ∨ es.g.win = true) :
    ∀ r ∈ support (stepPBucketForgedHdr cka prng fs Δcka qep tL par t q (es, winEp) sp),
      r.1.2 = (es, winEp) := by
  intro r hr
  have hor : (es.abort || es.g.win) = true := by
    rcases haw with h | h <;> simp [h]
  have hno_flip : (!es.g.win && es.g.win) = false := by cases es.g.win <;> simp
  unfold stepPBucketForgedHdr implEDFPaperBucketMode withWinEpDFMode at hr
  simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, simulateQ_bind,
    MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r0, hr0, hr_end⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_end
  subst hr_end
  have hes_eq : r0.1.2 = es := by
    rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
    · simp [implEDFPaperBucketRaw, coinsE, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr0
      rcases hr0 with ⟨_, _, rfl⟩; rfl
    · rcases arg with ⟨P, m, r_coins⟩
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

private theorem leComp_stepPBucketForgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stL stR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdrDF Δcka tL par t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdrDF Δcka tL par t)
      (stepPBucketForgedHdr cka prng fs Δcka qep tL par t q stL spL)
      (stepPBucketForgedHdr cka prng fs Δcka qep tL par (t + 1) q stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hsync, hwinEp_eq, hwin_imp⟩
  dsimp only at hsync hwinEp_eq hwin_imp
  subst hwinEp_eq
  have hwas_eq : esL.g.win = esR.g.win := CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq
  by_cases hwin0 : esR.g.win = true
  · have hwinL0 : esL.g.win = true := hwas_eq.trans hwin0
    have horL : (esL.abort || esL.g.win) = true := by simp [hwinL0]
    have horR : (esR.abort || esR.g.win) = true := by simp [hwin0]
    have hsf0 : SyncForgedHdrDF Δcka tL par t (esL, winEpL) spL (esR, winEpL) spR :=
      ⟨hsync, rfl, fun hf => by dsimp only at hf; rw [hf] at hwin0; cases hwin0⟩
    unfold stepPBucketForgedHdr implEDFPaperBucketMode withWinEpDFMode
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, simulateQ_bind,
      StateT.run_pure, simulateQ_pure, hwinL0, hwin0, Bool.not_true, Bool.false_and]
    rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
    · simp [implEDFPaperBucketRaw, coinsE, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind _ fun u _ => CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, m, r_coins⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
        StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, c⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases arg with ⟨P, c⟩
      have hgL : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome ||
          !esL.g.safeInj (2 + Δcka)) = true := by simp [horL]
      have hgR : (esR.abort || esR.g.win || (esR.g.inTransit P.other c).isSome ||
          !esR.g.safeInj (2 + Δcka)) = true := by simp [horR]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
        StateT.run_bind, StateT.run_get, pure_bind, hgL, hgR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · have hgL : (esL.abort || esL.g.win || !esL.g.corrAllowedPaper P) = true := by simp [horL]
      have hgR : (esR.abort || esR.g.win || !esR.g.corrAllowedPaper P) = true := by simp [horR]
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
        StateT.run_bind, StateT.run_get, pure_bind, hgL, hgR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
    · rcases df with ⟨P, c, c'⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, horL, horR, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf0⟩)
  · have hwinR0 : esR.g.win = false := Bool.eq_false_iff.mpr hwin0
    have hwinL0 : esL.g.win = false := hwas_eq.trans hwinR0
    have hnone0 : winEpL = none := hwin_imp hwinR0
    subst hnone0
    unfold stepPBucketForgedHdr implEDFPaperBucketMode withWinEpDFMode
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, simulateQ_bind,
      StateT.run_pure, simulateQ_pure, hwinL0, hwinR0, Bool.not_false, Bool.true_and]
    refine (leComp_implEDFPaperBucketRaw_step cka prng fs Δcka qep tL par t htH q hsync).bind ?_
    rintro ⟨⟨resL, esL'⟩, spL'⟩ ⟨⟨resR, esR'⟩, spR'⟩ hrel
    rcases hrel with (hab | ⟨hwin'_f, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩) | ⟨hres, hsync'⟩
    · exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inl hab))
    · dsimp only at hwin'_f hvp_inv htr_inv hcur hmem
      simp only [hwin'_f, Bool.false_eq_true, ↓reduceIte]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inr (Or.inr (Or.inr
        ⟨hwin'_f, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))))
    · dsimp only at hres hsync'
      have hwin'_eq : esL'.g.win = esR'.g.win := CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync'.g_eq
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨hres, hsync', ?_, ?_⟩)
      · dsimp only
        rw [hwin'_eq]
        by_cases hw' : esR'.g.win = true
        · simp only [hw', ↓reduceIte]
          rcases q with s | (((((arg | arg) | arg) | ⟨P, c⟩) | P) | df) <;> try rfl
          dsimp only
          have htcur_eq : (esL.g.st P).tcur = (esR.g.st P).tcur :=
            (hsync.vp_rel P).tcur_L.trans (hsync.vp_rel P).tcur_R.symm
          have hhon_eq : isHonestHdrPRNGBucket esL.h c.1 = isHonestHdrPRNGBucket esR.h c.1 := by
            unfold isHonestHdrPRNGBucket
            rcases hsync.cache_rel c.1.1 with ⟨hL0, hR0⟩ | ⟨Tc, rL, rR, k, hL1, hR1, _⟩
            · rw [hL0, hR0]
            · rw [hL1, hR1]; cases c.1.2 <;> rfl
          simp only [htcur_eq, hhon_eq]
        · simp [hw']
      · intro hf
        dsimp only at hf ⊢
        simp [hf]

private theorem stepPBucketForgedHdr_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hd : DoomedForgedHdrDF tL st) :
    ∀ r ∈ support (stepPBucketForgedHdr cka prng fs Δcka qep tL par t q st sp),
      DoomedForgedHdrDF tL r.1.2 := by
  intro r hr
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨hwin, hnone⟩ | ⟨hwin, tWin, cur, hsome, hmem, hlt, hcur_lt⟩ |
    ⟨hwin, hnone, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩
  · rw [stepPBucketForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL par t q es winEp sp (Or.inl hab) r hr]
    exact Or.inl hab
  · rw [stepPBucketForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL par t q es winEp sp (Or.inr hwin) r hr]
    exact Or.inr (Or.inl ⟨hwin, hnone⟩)
  · rw [stepPBucketForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL par t q es winEp sp (Or.inr hwin) r hr]
    exact Or.inr (Or.inr (Or.inl ⟨hwin, tWin, cur, hsome, hmem, hlt, hcur_lt⟩))
  · dsimp only at hwin hnone hvp_inv htr_inv hcur hmem
    subst hnone
    by_cases hab : es.abort = true
    · rw [stepPBucketForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL par t q es none sp (Or.inl hab) r hr]
      exact Or.inl hab
    · have hor_f : (es.abort || es.g.win) = false := by
        simp [Bool.eq_false_iff.mpr hab, hwin]
      unfold stepPBucketForgedHdr implEDFPaperBucketMode withWinEpDFMode at hr
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, simulateQ_bind,
        hwin, Bool.not_false, Bool.true_and, MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨r0, hr0, hr_end⟩
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_end
      subst hr_end
      rcases q with s | (((((arg | arg) | arg) | arg) | P) | df)
      · simp [implEDFPaperBucketRaw, coinsE, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
          simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr0
        rcases hr0 with ⟨_, _, rfl⟩
        dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
      · rcases arg with ⟨P, m, r_coins⟩
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, transmitEBucket,
          vSend_hooksPRNGBucketForgedHdr_eq,
          StateT.run_bind, StateT.run_get, pure_bind, hor_f, Bool.false_eq_true, ↓reduceIte] at hr0
        cases hep : es.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
          subst hr0
          dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        | some s₁ =>
          obtain ⟨hs₁_win, hs₁_st, hs₁_tr, hs₁_epP, hs₁_epQ⟩ := epMgmt_preserving_props hep
          obtain ⟨cur', hcur', hmem', hlt'⟩ := epMgmt_doomed_mem hcur hmem hlt hep
          simp only [hep, hs₁_st, StateT.run_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr0
          rcases hr0 with ⟨⟨⟨res_vs, es1⟩, sp1⟩, hr_vs, hr_rest⟩
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
            have hrec_win : (s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false).win = false :=
              hs₁_win.trans hwin
            dsimp only; simp only [hrec_win, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨_, _, hst'_id, hst'_tcur, hct_ep⟩ := support_liftH_vSend_props prng
              (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) s₁ P es
              (es.g.epoch P) m r_coins sp
              (hvp_inv P).1 (hvp_inv P).2 hr_vs
            refine doomed_branch4_of_record hrec_win ?_ ?_ hs₁_epP
              hst'_id hst'_tcur hct_ep hcur' hmem' hlt'
            · intro Q hQ; rw [hs₁_st, hs₁_epQ Q hQ]; exact hvp_inv Q
            · intro rec hrec; rw [hs₁_tr] at hrec; exact htr_inv rec hrec
      · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
        subst hr0
        dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
      · rcases arg with ⟨P, c⟩
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverE,
          vRecv_hooksPRNGBucketForgedHdr_eq,
          StateT.run_bind, StateT.run_get, pure_bind, hor_f, Bool.false_eq_true, ↓reduceIte] at hr0
        cases htr : es.g.inTransit P.other c with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
          subst hr0
          dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        | some rec =>
          have hrec_mem : rec ∈ es.g.trans ∧ rec.ct = c := by
            unfold CryptoGames.SM.GameState.inTransit at htr
            have hfind := List.find?_some htr
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
            exact ⟨List.mem_of_find?_eq_some htr, hfind.2⟩
          have hc_ep : c.1.1 = rec.pos.epoch := by
            rw [← hrec_mem.2]; exact htr_inv rec hrec_mem.1
          simp only [htr, StateT.run_bind, simulateQ_bind,
            bucketAuthCfg, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            MonadAttach.mem_support_bind] at hr0
          rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp1⟩, hr_vr, hr_rest⟩
          have hg1 := support_liftH_g_eq prng _ es sp hr_vr
          cases res_vr with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some opt_vr =>
            cases opt_vr with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr_rest
              subst hr_rest
              dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
              exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
            | some vtim =>
              rcases vtim with ⟨vp', t', i', m'⟩
              simp only [StateT.run_bind, run_commitE_forgedHdr, pure_bind,
                StateT.run_modify, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr_rest
              subst hr_rest
              obtain ⟨_, _, _, _, hvp'_id, hvp'_tcur⟩ := support_liftH_vRecv_props prng
                (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) es.g P es
                (es.g.epoch P) c (some rec) sp
                (hvp_inv P).1 (hvp_inv P).2 hr_vr
              rw [hc_ep] at hvp'_tcur
              have hacc_win : (es.g.accept P vp' rec.pos).win = false := hwin
              dsimp only; simp only [hacc_win, Bool.false_eq_true, ↓reduceIte]
              exact doomed_branch4_of_accept (pos := rec.pos)
                hwin hvp_inv htr_inv hvp'_id hvp'_tcur hcur hmem hlt
      · rcases arg with ⟨P, c⟩
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, injectE,
          vRecv_hooksPRNGBucketForgedHdr_eq,
          StateT.run_bind, StateT.run_get, pure_bind, hor_f, Bool.false_or] at hr0
        by_cases hguard : ((es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr0
          subst hr0
          dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        · have hsafe : es.g.safeInj (2 + Δcka) = true := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
            exact Bool.eq_true_of_not_eq_false hguard.2
          have hcur_le_epP : cur + (2 + Δcka) ≤ es.g.epoch P := by
            unfold CryptoGames.SM.GameState.safeInj at hsafe
            rw [hcur] at hsafe
            have hmin := healedBy_some_le hsafe
            have hleP : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
              cases P <;> simp
            omega
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            simulateQ_bind, MonadAttach.mem_support_bind] at hr0
          rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp1⟩, hr_vr, hr_rest⟩
          have hg1 := support_liftH_g_eq prng _ es sp hr_vr
          cases res_vr with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some opt_vr =>
            cases opt_vr with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr_rest
              subst hr_rest
              dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
              exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
            | some vtim =>
              rcases vtim with ⟨vp', t', i', m'⟩
              obtain ⟨_, _, ht'_eq, _, hvp'_id, hvp'_tcur⟩ := support_liftH_vRecv_props prng
                (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) es.g P es
                (es.g.epoch P) c none sp
                (hvp_inv P).1 (hvp_inv P).2 hr_vr
              subst ht'_eq
              dsimp only at hr_rest
              by_cases hqep : qep + 1 < c.1.1
              · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                  support_pure, Set.mem_singleton_iff] at hr_rest
                subst hr_rest
                dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
                exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                  by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
              · simp only [hqep, ↓reduceIte] at hr_rest
                by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_forgedHdr,
                    pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hr_rest
                  subst hr_rest
                  have hacc_win : (es.g.accept P vp' ⟨P.other, c.1.1, i'⟩).win = false := hwin
                  dsimp only; simp only [hacc_win, Bool.false_eq_true, ↓reduceIte]
                  exact doomed_branch4_of_accept (pos := ⟨P.other, c.1.1, i'⟩)
                    hwin hvp_inv htr_inv hvp'_id hvp'_tcur hcur hmem hlt
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_rest
                  by_cases hfull : (bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).injectFull c.1.1 = true
                  · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
                    subst hr_rest
                    dsimp only
                    simp only [↓reduceIte]
                    by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) &&
                        !isHonestHdrPRNGBucket es.h c.1) = true
                    · simp only [hnf, ↓reduceIte]
                      have hc_eq : c.1.1 = es.g.epoch P + 1 := by
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hnf
                        rw [(hvp_inv P).2] at hnf
                        exact hnf.1
                      exact Or.inr (Or.inr (Or.inl ⟨rfl, c.1.1, cur, rfl,
                        (show cur ∈ es1.g.leaks by rwa [hg1.1]), hlt, by omega⟩))
                    · simp only [hnf, Bool.false_eq_true, ↓reduceIte]
                      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · simp only [hfull, Bool.false_eq_true, ↓reduceIte,
                      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
                    subst hr_rest
                    dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
                    exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                      by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
      · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, corrEPaperBucket,
          StateT.run_bind, StateT.run_get, pure_bind] at hr0
        by_cases hguard : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr0
          subst hr0
          dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            simulateQ_bind, MonadAttach.mem_support_bind] at hr0
          rcases hr0 with ⟨⟨⟨res_rv, es1⟩, sp1⟩, hr_rv, hr_rest⟩
          have hg1 := support_liftH_g_eq prng _ es sp hr_rv
          cases res_rv with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some rp =>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest
            have hac_win : (es.g.afterCorr P).win = false := hwin
            dsimp only; simp only [hac_win, Bool.false_eq_true, ↓reduceIte]
            refine Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv,
              CryptoGames.SM.maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)),
              by simp [CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak],
              by simp [CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak], ?_⟩))
            rw [hcur]
            exact ltOpt_mono hlt (Nat.le_max_left _ _)
      · rcases df with ⟨P, c, c'⟩
        simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, deliverForgeE,
          vRecv_hooksPRNGBucketForgedHdr_eq,
          StateT.run_bind, StateT.run_get, pure_bind, hor_f, Bool.false_eq_true, ↓reduceIte] at hr0
        cases htr : es.g.inTransit P.other c with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr0
          subst hr0
          dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        | some rec =>
          simp only [htr] at hr0
          by_cases hrej : ((es.g.inTransit P.other c').isSome || es.g.comp.contains rec.pos ||
              (c.1 != c'.1)) = true
          · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hr0
            subst hr0
            dsimp only; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
          · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              simulateQ_bind, MonadAttach.mem_support_bind] at hr0
            rcases hr0 with ⟨⟨⟨res_vr, es1⟩, sp1⟩, hr_vr, hr_rest⟩
            have hg1 := support_liftH_g_eq prng _ es sp hr_vr
            cases res_vr with
            | none =>
              simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
                StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
              subst hr_rest; exact Or.inl rfl
            | some opt_vr =>
              cases opt_vr with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr_rest
                subst hr_rest
                dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
                exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                  by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
              | some vtim =>
                rcases vtim with ⟨vp', t', i', m'⟩
                obtain ⟨_, _, ht'_eq, _, hvp'_id, hvp'_tcur⟩ := support_liftH_vRecv_props prng
                  (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) es.g P es
                  (es.g.epoch P) c' none sp
                  (hvp_inv P).1 (hvp_inv P).2 hr_vr
                dsimp only at hr_rest
                by_cases hbad_ep : (decide (qep + 1 < t') || (t' != rec.pos.epoch)) = true
                · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hr_rest
                  subst hr_rest
                  dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
                  exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                    by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))
                · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte] at hr_rest
                  by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
                  · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_forgedHdr,
                      pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                      support_pure, Set.mem_singleton_iff] at hr_rest
                    subst hr_rest
                    have hacc_win : (es.g.accept P vp' ⟨P.other, t', i'⟩).win = false := hwin
                    dsimp only; simp only [hacc_win, Bool.false_eq_true, ↓reduceIte]
                    rw [← ht'_eq] at hvp'_tcur
                    exact doomed_branch4_of_accept (pos := ⟨P.other, t', i'⟩)
                      hwin hvp_inv htr_inv hvp'_id hvp'_tcur hcur hmem hlt
                  · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_rest
                    by_cases hfull : (bucketAuthCfg Δcka tL par : CryptoGames.SM.Config M).injectFull t' = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
                      subst hr_rest
                      exact Or.inr (Or.inl ⟨rfl, by simp⟩)
                    · simp only [hfull, Bool.false_eq_true, ↓reduceIte,
                        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
                      subst hr_rest
                      dsimp only; rw [hg1.1]; simp only [hwin, Bool.false_eq_true, ↓reduceIte]
                      exact Or.inr (Or.inr (Or.inr ⟨by rwa [hg1.1], rfl,
                        by rwa [hg1.1], by rwa [hg1.1], cur, by rwa [hg1.1], by rwa [hg1.1], hlt⟩))

private def runPBucketForgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (oa : CryptoGames.SM.Construction.AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
    ((simulateQ (implEDFPaperBucketMode
      (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket) oa).run st)).run sp
  pure (authOutBucketPaper (2 + Δcka) tL r.1.2)

private theorem runPBucketForgedHdr_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (b : Bool)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runPBucketForgedHdr cka prng fs Δcka qep tL par t (pure b) st sp =
      pure (authOutBucketPaper (2 + Δcka) tL st) := by
  simp [runPBucketForgedHdr]

private theorem runPBucketForgedHdr_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (q : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (CryptoGames.SM.Construction.AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      CryptoGames.SM.Construction.AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runPBucketForgedHdr cka prng fs Δcka qep tL par t (liftM (OracleSpec.query q) >>= k) st sp =
      stepPBucketForgedHdr cka prng fs Δcka qep tL par t q st sp >>= fun r =>
        runPBucketForgedHdr cka prng fs Δcka qep tL par t (k r.1.1) r.1.2 r.2 := by
  simp [runPBucketForgedHdr, stepPBucketForgedHdr, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPBucketForgedHdr_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (oa : CryptoGames.SM.Construction.AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    (hd : DoomedForgedHdrDF tL st) :
    𝒟[runPBucketForgedHdr cka prng fs Δcka qep tL par t oa st sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing st sp with
  | pure b' =>
    rw [runPBucketForgedHdr_pure, authOutBucketPaper_eq_false_of_doomedForgedHdrDF hd]
    simp
  | query_bind q k ih =>
    rw [runPBucketForgedHdr_query_bind]
    exact CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPBucketForgedHdr_doomed cka prng fs Δcka qep tL par t q st sp hd r hr)

private theorem runPBucketForgedHdr_le_succ
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (oa : CryptoGames.SM.Construction.AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stL stR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdrDF Δcka tL par t stL spL stR spR) :
    𝒟[runPBucketForgedHdr cka prng fs Δcka qep tL par t oa stL spL] {true} ≤
      𝒟[runPBucketForgedHdr cka prng fs Δcka qep tL par (t + 1) oa stR spR] {true} := by
  induction oa using OracleComp.inductionOn generalizing stL stR spL spR with
  | pure b' =>
    rw [runPBucketForgedHdr_pure, runPBucketForgedHdr_pure]
    rcases stL with ⟨esL, winEpL⟩
    rcases stR with ⟨esR, winEpR⟩
    rcases hsf with ⟨hsync, hwinEp, _⟩
    dsimp only at hsync hwinEp
    subst hwinEp
    have hout : authOutBucketPaper (2 + Δcka) tL (esL, winEpL) =
        authOutBucketPaper (2 + Δcka) tL (esR, winEpL) := by
      cases winEpL with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketPaper, authOutBucket, authOut]
        rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
          CryptoGames.SM.Construction.AuthL11.eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPBucketForgedHdr_query_bind, runPBucketForgedHdr_query_bind]
    refine leComp_stepPBucketForgedHdr cka prng fs Δcka qep tL par t htH q hsf _ _ ?_
    rintro ⟨⟨uL, stL'⟩, spL'⟩ ⟨⟨uR, stR'⟩, spR'⟩ (hd | ⟨hu, hsf'⟩)
    · rw [runPBucketForgedHdr_doomed cka prng fs Δcka qep tL par t (k uL) hd]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uL hsf'

theorem prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_le_succ_false_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (htH : healEpoch tL ≤ t) (_ht : t < qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CryptoGames.PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t A)] {true} ≤
      𝒟[CryptoGames.PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (t + 1) A)] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (CryptoGames.PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = CryptoGames.SM.Construction.AuthL11.pImpl prng := rfl
  unfold CryptoGames.PRFPRNG.branch redPRNGAuthDFPaperBucketForgedHdr engRunDFPaperBucketMode initPRNGBucketHybrid
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT, pure_bind]
  refine CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  refine (leComp_rootInit_step (T := T) (Δbucket := 3 + Δcka) (par := par)
    prng tL t lam (prng.init kr) htH) _ _ ?_
  rintro ⟨⟨resL, hL0⟩, spL0⟩ ⟨⟨resR, hR0⟩, spR0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨rL0, rR0, kVal, hresL, hresR, hr0, hcL0, hcR0, hcrL0, hcrR0, hft0, htab0,
      hbL0, hbR0, hσ0, hprf0, hprng0, hcorr0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hresL hresR
    subst hresL hresR
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc, Function.comp_apply]
    refine runPBucketForgedHdr_le_succ cka prng fs Δcka qep tL par t htH A ⟨?_, rfl, fun _ => rfl⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, hft0, htab0, hbL0, hbR0,
      ?_, ?_, hprng0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcrL0, hcrR0, rfl⟩
    · intro P
      cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hr0⟩
    · intro e'; rw [hcL0, hcR0]; exact Or.inl ⟨rfl, rfl⟩
    · intro e' _; rw [hcL0, hcR0]; exact ⟨rfl, rfl⟩
    · simpa using hσ0
    · exact fun _ => hprf0
    · exact fun hle _ => hcorr0 (by simpa using hle)
    · intro pos hpos; cases hpos
    · intro r hr; cases hr
    · intro P _ hpos; simp at hpos
    · intro r hr; cases hr
    · intro P; simp
    · intro P hlt; simp at hlt


end StepCoupling

end CryptoGames.SM.Construction.DeliverForge
