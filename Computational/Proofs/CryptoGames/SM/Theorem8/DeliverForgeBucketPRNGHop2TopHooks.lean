/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

-- postLeak + corrRoot Hop-2 top hooks

section TopHooks

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

@[simp]
theorem simulateQ_pImpl_liftPBucket
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (q : PRFPRNG.AdversaryComp Sig I K α)
    (s : PRNGBucketState T Sig K I) :
    simulateQ (AuthL11.pImpl prng) ((liftPBucket q).run s) =
      (simulateQ (AuthL11.pImpl prng) q >>= fun a => pure (a, s)) := by
  simp [liftPBucket, StateT.run_lift, simulateQ_bind, map_eq_bind_pure_comp]

@[expose] def RelCacheBucket
    (cp : Option (T × Option Sig × K)) (cl : Option (T × Sig × K)) : Prop :=
  (cp = none ∧ cl = none) ∨
  ∃ Tc σp σl k, cp = some (Tc, σp, k) ∧ cl = some (Tc, σl, k) ∧ (∀ s, σp = some s → s = σl)

structure RelVPBucket (ep : ℕ) (P : Party)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS) : Prop where
  id_P : vpP.id = P
  tcur_P : vpP.tcur = ep
  id_L : vpL.id = P
  tcur_L : vpL.tcur = ep
  γ_eq : vpP.γ = vpL.γ
  Tcur_eq : vpP.curCkaMsg = vpL.curCkaMsg
  vS_eq : vpP.vS = vpL.vS
  vR_eq : ∀ t', vpP.vR t' = vpL.vR t'
  root_eq : ∀ s, vpP.root = some s → s = vpL.root

private theorem leComp_lookupBucketF [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (qep t0 : ℕ) (ik : I)
    (hP : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K)
    (hL : LocalBucketState T Sig K I)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t') (ht0 : t0 < qep + 1) :
    AuthL11.LeComp (fun rP rL =>
        rP.1.1 = rL.1 ∧ rP.2 = sp ∧ rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧
        rP.1.2.lc = hP.lc ∧ rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
        (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
        rL.2.fTable (qep + 1) = hL.fTable (qep + 1))
      ((simulateQ (AuthL11.pImpl prng) ((lookupPRNGBucketF (T := T) (Sig := Sig) t0 ik).run hP)).run sp)
      (simulateQ AuthL11.lImpl ((lookupLocalBucketF (T := T) (Sig := Sig) t0 ik).run hL)) := by
  unfold lookupPRNGBucketF lookupLocalBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]; rw [hft t0 ht0]
  cases hlk : (hL.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_pImpl_run_lift_sampleT,
      AuthL11.simulateQ_lImpl_run_lift_sampleT, bind_assoc]
    refine AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro t' ht'; by_cases heq : t' = t0 <;> [subst heq; skip] <;> simp [*, hft t' ht']
    · have hne : qep + 1 ≠ t0 := by omega
      simp [hne]

theorem eraseSt_postLeak {St1 St2 Msg C : Type} {tL : Option ℕ}
    {g1 : SM.GameState St1 Msg C} {g2 : SM.GameState St2 Msg C}
    (hg : AuthL11.eraseSt g1 = AuthL11.eraseSt g2) :
    postLeak tL g1 = postLeak tL g2 := by
  have htl : g1.tL = g2.tL := congrArg SM.GameState.tL hg
  simp only [postLeak, htl]

theorem postLeak_epMgmt {St Msg C : Type} {tL : Option ℕ} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {g s₁ : SM.GameState St Msg C} (hpl : postLeak tL g = true)
    (hep : g.epMgmt Δ qep P bad = some s₁) : postLeak tL s₁ = true := by
  cases htl : g.tL with
  | none => simp [postLeak, htl] at hpl
  | some cur =>
    simp only [postLeak, htl] at hpl
    unfold SM.GameState.epMgmt at hep
    by_cases hs : P.sendsIn (g.epoch P + 1) = true
    · simp only [hs, ↓reduceIte] at hep
      by_cases hq : qep < g.epoch P + 1
      · simp [hq] at hep
      · simp only [hq, ↓reduceIte, Option.some.injEq] at hep; subst hep
        split
        · simp only [postLeak, SM.GameState.leak, htl, SM.maxOpt]
          cases tL with
          | none => rfl
          | some l => simp only [ltOpt, decide_eq_true_eq] at hpl ⊢; omega
        · simp [postLeak, htl, hpl]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
      by_cases hq : qep < g.epoch P
      · simp [hq] at hep
      · simp only [hq, ↓reduceIte, Option.some.injEq] at hep; subst hep; simp [postLeak, htl, hpl]

theorem postLeak_afterCorr_of_ge_healEpoch {St Msg C : Type} {tL : Option ℕ}
    {g : SM.GameState St Msg C} {P : Party} (hge : healEpoch tL ≤ g.epoch P) :
    postLeak tL (g.afterCorr P) = true := by
  have hle_max : g.epoch P ≤ max (g.epoch .A) (g.epoch .B) := by cases P <;> simp
  have hlt_max : ltOpt tL (max (g.epoch .A) (g.epoch .B)) = true := by
    cases tL with | none => rfl | some l => simp only [healEpoch, ltOpt, decide_eq_true_eq] at hge ⊢; omega
  cases htl : g.tL with
  | none => simp [SM.GameState.afterCorr, SM.GameState.leak, postLeak, htl, SM.maxOpt, hlt_max]
  | some cur =>
    simp only [SM.GameState.afterCorr, SM.GameState.leak, postLeak, htl, SM.maxOpt]
    cases tL with | none => rfl | some l => simp only [ltOpt, decide_eq_true_eq] at hlt_max ⊢; omega

theorem postLeak_afterCorr_mono {St Msg C : Type} {tL : Option ℕ}
    {g : SM.GameState St Msg C} {P : Party} (hpl : postLeak tL g = true) :
    postLeak tL (g.afterCorr P) = true := by
  cases htl : g.tL with
  | none => simp [postLeak, htl] at hpl
  | some cur =>
    simp only [postLeak, htl] at hpl
    simp only [SM.GameState.afterCorr, SM.GameState.leak, postLeak, htl, SM.maxOpt]
    cases tL with | none => rfl | some l => simp only [ltOpt, decide_eq_true_eq] at hpl ⊢; omega

theorem leComp_rootBucketTop [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig) (σ0 : Sig) (hP : PRNGBucketState T Sig K I)
    (sp : PRFPRNG.GameState Sig I K) (hL : LocalBucketState T Sig K I)
    (hΔ : 2 ≤ Δbucket) (ht0 : t0 < qep + 1) (hb : sp.b = true)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t') (htop : sp.table = hL.fTable (qep + 1))
    (hpl_cr : hP.corrRoot.isSome = true → pl = true)
    (hσ_res : ∀ s, resolveCorrRoot hP (t0 - 1) σv0 = some s → s = σ0)
    (hσ_sp : (pl = false ∨ resolveCorrRoot hP (t0 - 1) σv0 = none) → hP.corrRoot = none ∧ sp.σ = σ0) :
    AuthL11.LeComp (fun rP rL =>
        rP.1.1 = none ∨
        ∃ σP σL k, rP.1.1 = some (σP, k) ∧ rL.1 = (σL, k) ∧ (∀ s, σP = some s → s = σL) ∧
          (pl = false → σP = (if t0 < healEpoch tL then some σL else none) ∧
            rP.2.σ = σL ∧ rP.1.2.corrRoot = none) ∧
          (pl = true → σP = some σL ∧ (rP.1.2.corrRoot = hP.corrRoot ∨
            (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (t0 - 1, σ0)))) ∧
          rP.2.b = true ∧ rP.1.2.cache = hP.cache ∧ rP.1.2.lc = hP.lc ∧
          rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧
          (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
          rP.2.table = rL.2.fTable (qep + 1))
      ((simulateQ (AuthL11.pImpl prng)
        ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par (qep + 1) t0 pl ik0 σv0).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((rootLocalBucket (T := T) prng Δbucket qep tL par t0 pl ik0 σ0).run hL)) := by
  unfold rootPRNGBucketHybrid rootLocalBucket
  rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
  dsimp only at hb htop hσ_sp; subst hb
  have hnot_gt : ¬ (qep + 1 < t0) := by omega
  have hnot_eq : ¬ (t0 = qep + 1) := by omega
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hnot_gt, hnot_eq, ↓reduceIte]
  cases pl
  · obtain ⟨hcr_none, hσ0⟩ := hσ_sp (Or.inl rfl); subst hσ0
    simp only [hcr_none, Option.isSome_none, Bool.or_self, Bool.false_or, Bool.false_eq_true,
      decide_eq_true_eq, ↓reduceIte]
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
            (fun _ h => by cases h), (fun _ => ⟨by simp [hnot_lt_tH], rfl, hcr_none⟩),
            (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, hft, htop⟩)
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
            refine (leComp_lookupBucketF prng qep t0 ik0 hP
              { σ := (prng.up σ_sp ik0).1, b := true, corr := corr_sp, prng := prng_sp,
                prf := false, table := table_sp } hL hft ht0).bind ?_
            rintro ⟨⟨kP, hP1⟩, sp1⟩ ⟨kL, hL1⟩ ⟨hk, hsp1, hcP1, hcr1, hlcP1, hcL1, hlcL1, hft1, htop1⟩
            subst hk hsp1; simp only [StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ_sp ik0).1, kP, rfl, rfl,
              (fun _ h => by cases h), (fun _ => ⟨by simp [hnot_lt_tH], rfl, hcr1.trans hcr_none⟩),
              (by intro h; cases h), rfl, hcP1, hlcP1, hcL1, hlcL1, hft1, by rw [htop1, ← htop]⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_processQuery,
            AuthL11.run_processImpl_some, bind_assoc]
          cases prf_sp
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure]
            exact AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).2,
              rfl, rfl, (fun _ h => by cases h), (fun _ => ⟨by simp [hnot_lt_tH], rfl, hcr_none⟩),
              (by intro h; cases h), rfl, rfl, rfl, rfl, rfl, hft, htop⟩)
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
          (prng.up σ_sp ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (fun _ => ⟨by simp [hlt_tH], rfl, hcr_none⟩), (by intro h; cases h),
          rfl, rfl, rfl, rfl, rfl, hft, htop⟩)
      · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · simp only [Bool.true_or, ↓reduceIte]
    cases hres : resolveCorrRoot hP (t0 - 1) σv0 with
    | some σ =>
      have hσ_eq : σ = σ0 := hσ_res σ hres; subst hσ_eq
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ ik0).1, (prng.up σ ik0).1,
        (prng.up σ ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
        (by intro h; cases h), (fun _ => ⟨rfl, Or.inl rfl⟩), rfl, rfl, rfl, rfl, rfl, hft, htop⟩)
    | none =>
      obtain ⟨hcr_none, hσ0⟩ := hσ_sp (Or.inr hres); subst hσ0
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucket,
        AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, bind_assoc]
      cases prf_sp
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind,
          StateT.run_modify, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ_sp ik0).1, (prng.up σ_sp ik0).1,
          (prng.up σ_sp ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (by intro h; cases h), (fun _ => ⟨rfl, Or.inr ⟨hcr_none, rfl⟩⟩),
          rfl, rfl, rfl, rfl, rfl, hft, htop⟩)
      · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private def StartSendPostBucketTop
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep : ℕ) (tL : Option ℕ) (pl : Bool) (e : ℕ)
    (σ0 : Sig) (hP : PRNGBucketState T Sig K I) (hL : LocalBucketState T Sig K I)
    (rP : (Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Γ × T × Sig × SS) × LocalBucketState T Sig K I) : Prop :=
  rP.1.1 = none ∨
  ∃ γ' T' σP σL k,
    rP.1.1 = some (γ', T', σP, fs.initSender k) ∧ rL.1 = some (γ', T', σL, fs.initSender k) ∧
    (∀ s, σP = some s → s = σL) ∧
    (pl = false → σP = (if e + 1 < healEpoch tL then some σL else none) ∧
      rP.2.σ = σL ∧ rP.1.2.corrRoot = none) ∧
    (pl = true → σP = some σL ∧ (rP.1.2.corrRoot = hP.corrRoot ∨
      (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, σ0)))) ∧
    rP.2.b = true ∧ (∀ t', RelCacheBucket (rP.1.2.cache t') (rL.2.cache t')) ∧
    rP.1.2.cache (e + 1) = some (T', σP, k) ∧ (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t') ∧
    rL.2.cache (e + 1) = some (T', σL, k) ∧ (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
    rP.1.2.lc = (if pl && hP.lc.isNone && decide (healEpoch tL < e + 1) then some e else hP.lc) ∧
    rL.2.lc = (if pl && hL.lc.isNone && decide (healEpoch tL < e + 1) then some e else hL.lc) ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧ rP.2.table = rL.2.fTable (qep + 1)

private theorem leComp_startSendBucketTop
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS} {r_coins : Option CCoins}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true) (he_lt : e + 1 < qep + 1)
    (hpl_cr : hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_res : ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hσ_sp : (postLeak tL gL = false ∨ resolveCorrRoot hP e vpP.root = none) →
      hP.corrRoot = none ∧ sp.σ = vpL.root) :
    AuthL11.LeComp (StartSendPostBucketTop fs qep tL (postLeak tL gL) e vpL.root hP hL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1)).startSend
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
  have hft0 : ∀ t', t' < qep + 1 → hP0.fTable t' = hL0.fTable t' := by
    intro t' ht'; dsimp only [hP0, hL0]; split_ifs <;> exact hft t' ht'
  have htop0 : sp.table = hL0.fTable (qep + 1) := by dsimp only [hL0]; split_ifs <;> exact htop
  have hcL0 : hL0.cache = hL.cache := by dsimp only [hL0]; split_ifs <;> rfl
  have hres0 : resolveCorrRoot hP0 = resolveCorrRoot hP := by
    funext ep sv; simp [resolveCorrRoot, hcr0]
  have hlcP0 : hP0.lc = (if postLeak tL gL && hP.lc.isNone && decide (healEpoch tL < e + 1) then
      some e else hP.lc) := by dsimp only [hP0]; split_ifs <;> rfl
  have hlcL0 : hL0.lc = (if postLeak tL gL && hL.lc.isNone && decide (healEpoch tL < e + 1) then
      some e else hL.lc) := by dsimp only [hL0]; split_ifs <;> rfl
  have hbody : ∀ (coins : CCoins),
      AuthL11.LeComp (StartSendPostBucketTop fs qep tL (postLeak tL gL) e vpL.root hP hL)
        ((simulateQ (AuthL11.pImpl prng)
          ((do
            let c := cka.send vpP.γ coins
            match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par (qep + 1) (e + 1)
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
    refine (leComp_rootBucketTop prng (3 + Δcka) qep tL par (e + 1) (postLeak tL gL)
      (cka.send vpL.γ coins).2.2 vpP.root vpL.root hP0 sp hL0 (by omega) he_lt hb hft0 htop0
      (fun h => hpl_cr (hcr0 ▸ h)) (fun s hs => hσ_res s (hres0 ▸ hs))
      (fun h => by obtain ⟨h1, h2⟩ := hσ_sp (hres0 ▸ h); exact ⟨hcr0.trans h1, h2⟩)).bind ?_
    rintro ⟨⟨res_root, hP1⟩, sp1⟩ ⟨⟨σL, kL⟩, hL1⟩ hroot
    rcases hroot with hnone | ⟨σP, σL', k, hres_P, hres_L, hσ_rel, hpl_f, hpl_t,
      hb1, hcP1, hlcP1, hcL1, hlcL1, hft1, htop1⟩
    · dsimp only at hnone; subst hnone
      simp only [StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hres_P hres_L; cases hres_L; subst hres_P
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨(cka.send vpL.γ coins).1, (cka.send vpL.γ coins).2.1,
        σP, σL, kL, rfl, rfl, hσ_rel, hpl_f,
        (fun hpl => ⟨(hpl_t hpl).1, by rw [hcr0] at hpl_t; exact (hpl_t hpl).2⟩),
        hb1, ?_, by simp, ?_, by simp, ?_, hlcP1.trans hlcP0, hlcL1.trans hlcL0, hft1, htop1⟩)
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

@[expose] def VSendRelBucketTop (qep : ℕ) (tL : Option ℕ) (pl : Bool) (e : ℕ) (P : Party)
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
    rP.2.b = true ∧ (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1) ∧
    (P.sendsIn (e + 1) = true →
      (pl = false → vpP'.root = (if e + 1 < healEpoch tL then some vpL'.root else none) ∧
        rP.2.σ = vpL'.root ∧ rP.1.2.corrRoot = none) ∧
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

theorem leComp_vSendBucketTop
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS} {m : M} {r_coins : Option CCoins}
    {hP : PRNGBucketState T Sig K I} {sp : PRFPRNG.GameState Sig I K}
    {hL : LocalBucketState T Sig K I}
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true)
    (he_lt : P.sendsIn (e + 1) = true → e + 1 < qep + 1)
    (hpl_cr : P.sendsIn (e + 1) = true → hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_res : P.sendsIn (e + 1) = true →
      ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hσ_sp : P.sendsIn (e + 1) = true →
      (postLeak tL gL = false ∨ resolveCorrRoot hP e vpP.root = none) →
      hP.corrRoot = none ∧ sp.σ = vpL.root) :
    AuthL11.LeComp (VSendRelBucketTop qep tL (postLeak tL gL) e P vpP vpL hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1))
          gP P vpP m none r_coins).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((vSend (hooksLocalBucket cka prng fs Δcka qep tL par)
          gL P vpL m none r_coins).run hL)) := by
  unfold vSend
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hsends : P.sendsIn (e + 1) = true
  · simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind]
    refine (leComp_startSendBucketTop cka prng fs Δcka qep tL par hg_pl hvp hcache hft htop hb
      (he_lt hsends) (hpl_cr hsends) (hσ_res hsends) (hσ_sp hsends)).bind ?_
    rintro ⟨⟨res_ssP, hP1⟩, sp1⟩ ⟨res_ssL, hL1⟩ hss
    rcases hss with hnone | ⟨γ', T', σP, σL, k, hP_eq, hL_eq, hσ_rel, hpl_f, hpl_t, hb1,
      hc_rel, hcP_self, hcP_other, hcL_self, hcL_other, hlcP1, hlcL1, hft1, htop1⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
      simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
        pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hsends]), ?_, hc_rel,
        hb1, hft1, htop1, ?_, (fun hns => by rw [hsends] at hns; cases hns)⟩)
      · simp only [hsends, ↓reduceIte]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, hσ_rel⟩
      · intro _
        exact ⟨hpl_f, hpl_t, ⟨T', k, rfl, hcP_self, hcL_self⟩, hcP_other, hcL_other, hlcP1, hlcL1⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have hns : P.sendsIn (e + 1) = false := Bool.eq_false_iff.mpr hsends
    rcases hvSL : vpL.vS with _ | ss
    · have hvSP : vpP.vS = none := hvp.vS_eq.trans hvSL
      simp only [hvSP, hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb,
        hft, htop, (fun hs => absurd hs hsends), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]; exact hvp
    · have hvSP : vpP.vS = some ss := hvp.vS_eq.trans hvSL
      simp only [hvSP, hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket,
        hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, pure_bind, StateT.run_pure, simulateQ_pure]
      refine AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb,
        hft, htop, (fun hs => absurd hs hsends), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hvp.id_P, rfl, hvp.id_L, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_eq⟩

private theorem inStage2Bucket_gt_healEpoch (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (e : ℕ)
    (hin : inStage2Bucket Δcka tL par (e + 1) = true) : healEpoch tL < e + 1 := by
  cases tL with
  | none => simp [healEpoch]
  | some l => simp [inStage2Bucket, lastLeakGuessAdmissible, healEpoch] at hin ⊢; omega

private def StartRecvPostBucketTop
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

private theorem leComp_startRecvBucketTop
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
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true) (he_le : e ≤ qep)
    (hpl_cr : hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl)
    (hσ_res : postLeak tL gL = true →
      ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hσ_qep : postLeak tL gL = false → e = qep → sp.σ = vpL.root) :
    AuthL11.LeComp (StartRecvPostBucketTop fs qep e tn0 hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1)).startRecv
          gP P (e + 1) vpP.γ vpP.root tn0).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        (((hooksLocalBucket cka prng fs Δcka qep tL par).startRecv
          gL P (e + 1) vpL.γ vpL.root tn0).run hL)) := by
  unfold hooksPRNGBucketHybrid hooksPRNGBucketHybridGen hooksLocalBucket; dsimp only
  rw [hvp.γ_eq, hg_pl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hnot_gt : (!(qep + 1 < e + 1)) = true := by simp; omega
  have hoff : (∀ σc kc, hL.cache (e + 1) ≠ some (tn0, σc, kc)) →
      AuthL11.LeComp (StartRecvPostBucketTop fs qep e tn0 hP sp hL)
        ((simulateQ (AuthL11.pImpl prng)
          ((if !(qep + 1 < e + 1) &&
                (lastLeakGuessAdmissible (3 + Δcka) tL (e + 1) &&
                  (partyPar (Party.senderOf (e + 1)) == par)) then
              if tL.isSome && decide (e + 1 = healEpoch tL) then pure none
              else if (postLeak tL gL || hP.corrRoot.isSome || decide (qep + 1 < e + 1)) then
                match resolveCorrRoot hP ((e + 1) - 1) vpP.root with
                | none => pure none
                | some σ =>
                  let kk := cka.receive vpL.γ tn0
                  let p := prng.up σ kk.2
                  pure (some (some (kk.1, some p.1, fs.initReceiver p.2)))
              else if e + 1 = qep + 1 then do
                let kk := cka.receive vpL.γ tn0
                match ← liftPBucket
                    (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
                | none => pure none
                | some (σOut, kOut) => pure (some (some (kk.1, some σOut, fs.initReceiver kOut)))
              else if !(e + 1 < healEpoch tL) then do
                let kk := cka.receive vpL.γ tn0
                let kOut ← lookupPRNGBucketF (e + 1) kk.2
                pure (some (some (kk.1, none, fs.initReceiver kOut)))
              else pure (some none)
            else pure (some none)).run hP)).run sp)
        (simulateQ AuthL11.lImpl
          ((if !(qep + 1 < e + 1) && inStage2Bucket Δcka tL par (e + 1) then
              if tL.isSome && decide (e + 1 = healEpoch tL) then pure none
              else if postLeak tL gL then
                let kk := cka.receive vpL.γ tn0
                let p := prng.up vpL.root kk.2
                pure (some (some (kk.1, p.1, fs.initReceiver p.2)))
              else do
                let kk := cka.receive vpL.γ tn0
                let k' ← lookupLocalBucketF (e + 1) kk.2
                pure (some (some (kk.1, (prng.up vpL.root kk.2).1, fs.initReceiver k')))
            else pure (some none)).run hL)) := by
    intro hno_cache
    have hin_eq : (lastLeakGuessAdmissible (3 + Δcka) tL (e + 1) &&
        (partyPar (Party.senderOf (e + 1)) == par)) = inStage2Bucket Δcka tL par (e + 1) := rfl
    rw [hin_eq, hnot_gt, Bool.true_and]
    by_cases hin : inStage2Bucket Δcka tL par (e + 1) = true
    · simp only [hin, ↓reduceIte]
      have hgt_tH : healEpoch tL < e + 1 := inStage2Bucket_gt_healEpoch Δcka tL par e hin
      have his_tH : (tL.isSome && decide (e + 1 = healEpoch tL)) = false := by simp [Nat.ne_of_gt hgt_tH]
      have hge_tH : (!(e + 1 < healEpoch tL)) = true := by simp; omega
      have hnot_gt_dec : decide (qep + 1 < e + 1) = false := by simp; omega
      simp only [his_tH, hnot_gt_dec, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
      cases hpl : postLeak tL gL
      · have hcr_false : hP.corrRoot.isSome = false := by
          cases hcr_b : hP.corrRoot.isSome
          · rfl
          · exact (hpl_cr hcr_b).symm.trans hpl
        simp only [hcr_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        by_cases htop_ep : e + 1 = qep + 1
        · have hσ_eq : sp.σ = vpL.root := hσ_qep hpl (by omega)
          simp only [htop_ep, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucket, AuthL11.simulateQ_pImpl_challPrfQuery,
            AuthL11.run_challPrfImpl, bind_assoc]
          by_cases hcp : (sp.corr || sp.prng) = true
          · simp only [hcp, ↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [hcp, Bool.false_eq_true, hb, ↓reduceIte]
            unfold lookupLocalBucketF; simp only [StateT.run_bind, StateT.run_get, pure_bind]; rw [htop]
            cases hlk : (hL.fTable (qep + 1)).lookup (cka.receive vpL.γ tn0).2 with
            | some R' =>
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
                some (prng.up sp.σ (cka.receive vpL.γ tn0).2).1,
                (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, R', rfl, rfl,
                (fun _ hs => by cases hs; rw [hσ_eq]), rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl,
                fun _ σl kc _ hc => False.elim (hno_cache σl kc (htop_ep ▸ hc))⟩))
            | none =>
              simp only [bind_assoc, pure_bind, StateT.run_bind, simulateQ_bind, AuthL11.simulateQ_lImpl_run_lift_sampleT]
              refine AuthL11.LeComp.sample_bind ($ᵗ K) fun R' _ => ?_
              simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              refine AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
                some (prng.up sp.σ (cka.receive vpL.γ tn0).2).1,
                (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, R', rfl, rfl,
                (fun _ hs => by cases hs; rw [hσ_eq]), rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, by simp,
                fun _ σl kc _ hc => False.elim (hno_cache σl kc (htop_ep ▸ hc))⟩))
              intro t' ht'; have hne : t' ≠ qep + 1 := by omega
              simp [hne, hft t' ht']
        · simp only [htop_ep, hge_tH, ↓reduceIte, StateT.run_bind, simulateQ_bind]
          refine (leComp_lookupBucketF prng qep (e + 1) (cka.receive vpL.γ tn0).2 hP sp hL hft (by omega)).bind ?_
          rintro ⟨⟨kOut, hP1⟩, sp1⟩ ⟨k', hL1⟩ ⟨hk, hsp1, hcP1, hcr1, hlcP1, hcL1, hlcL1, hft1, htop1⟩
          subst hk hsp1; simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
            none, (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, kOut, rfl, rfl,
            (fun _ hs => by cases hs), rfl, hb, hcP1, hcr1, hlcP1, hcL1, hlcL1, hft1,
            by rw [htop1, ← htop], fun _ σl kc _ hc => False.elim (hno_cache σl kc hc)⟩))
      · simp only [Bool.true_or, ↓reduceIte]
        cases hres : resolveCorrRoot hP e vpP.root with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]; exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        | some σ =>
          have hσ_eq := hσ_res hpl σ hres; subst hσ_eq; simp only [StateT.run_pure, simulateQ_pure]
          exact AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
            some (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, (prng.up vpL.root (cka.receive vpL.γ tn0).2).1,
            (prng.up vpL.root (cka.receive vpL.γ tn0).2).2, rfl, rfl,
            (fun _ hs => Option.some.inj hs ▸ rfl), rfl, hb, rfl, rfl, rfl, rfl, rfl, hft, htop,
            fun _ σl kc _ hc => False.elim (hno_cache σl kc hc)⟩))
    · simp only [hin, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  rcases hcache (e + 1) with ⟨hcP, hcL⟩ | ⟨Tc, σp, σl, k, hcP, hcL, hσ_rel⟩
  · conv => arg 2; rw [hcP]
    conv => arg 3; rw [hcL]
    exact hoff (fun σc kc hc => by rw [hcL] at hc; cases hc)
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
      exact hoff (fun σc kc hc => by rw [hcL] at hc; cases hc; exact hTc rfl)

@[expose] def VRecvRelBucketTop (qep e : ℕ) (P : Party) (c : Header T × E)
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
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1)) ∨
  ∃ vpP' vpL' i' m',
    rP.1.1 = some (some (vpP', t0, i', m')) ∧ rL.1 = some (some (vpL', t0, i', m')) ∧
    t0 ≤ e + 1 ∧ P.sendsIn t0 = false ∧ RelVPBucket (max e t0) P vpP' vpL' ∧
    rP.1.2.cache = hP.cache ∧ rP.1.2.corrRoot = hP.corrRoot ∧ rP.1.2.lc = hP.lc ∧
    rL.2.cache = hL.cache ∧ rL.2.lc = hL.lc ∧ rP.2.b = true ∧ rP.2.σ = sp.σ ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1) ∧
    (t0 ≤ e → vpP'.root = vpP.root ∧ vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg) ∧
    (t0 = e + 1 → (∃ tn0, c.1.2 = some tn0) ∧
      ∀ tn0 σp σl kc, c.1.2 = some tn0 → hP.cache (e + 1) = some (tn0, σp, kc) →
        hL.cache (e + 1) = some (tn0, σl, kc) →
        vpP'.root = resolveCorrRoot hP (e + 1) σp ∧ vpL'.root = σl)

theorem leComp_vRecvBucketTop
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
    (hg_pl : postLeak tL gP = postLeak tL gL) (hvp : RelVPBucket e P vpP vpL)
    (hcache : ∀ t', RelCacheBucket (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1)) (hb : sp.b = true) (he_le : e ≤ qep)
    (hpl_cr : hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hcr_cache : ∀ eC σC, hP.corrRoot = some (eC, σC) →
      ∀ Tc σl k, hL.cache eC = some (Tc, σl, k) → σC = σl)
    (hσ_res : postLeak tL gL = true →
      ∀ s, resolveCorrRoot hP e vpP.root = some s → s = vpL.root)
    (hσ_qep : postLeak tL gL = false → e = qep → sp.σ = vpL.root) :
    AuthL11.LeComp (VRecvRelBucketTop qep e P c vpP vpL hP sp hL)
      ((simulateQ (AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (qep + 1))
          gP P vpP c rec).run hP)).run sp)
      (simulateQ AuthL11.lImpl
        ((vRecv (hooksLocalBucket cka prng fs Δcka qep tL par)
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
        refine (leComp_startRecvBucketTop cka prng fs Δcka qep tL par hg_pl hvp hcache hft htop
          hb he_le hpl_cr hcr_cache hσ_res hσ_qep).bind ?_
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
          simp only [pure_bind, Function.update_self, hooksPRNGBucketHybrid,
            hooksPRNGBucketHybridGen, hooksLocalBucket]
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
        simp only [hvRP, hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hooksLocalBucket, pure_bind]
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

theorem sendsIn_succ_true_of_false (P : Party) (t : ℕ) (h : P.sendsIn t = false) :
    P.sendsIn (t + 1) = true := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem epMgmt_le_qep {St Msg C : Type} {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hle : ∀ Q, g.epoch Q ≤ qep) (hep : g.epMgmt Δ qep P bad = some s₁) :
    (∀ Q, s₁.epoch Q ≤ qep) ∧ (P.sendsIn (g.epoch P + 1) = true → g.epoch P + 1 ≤ qep) := by
  unfold SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep; subst hep
      have he1 : g.epoch P + 1 ≤ qep := by omega
      refine ⟨fun Q => ?_, fun _ => he1⟩
      by_cases hQ : Q = P
      · subst hQ; split <;> simp [SM.GameState.leak, he1]
      · split <;> simp [SM.GameState.leak, Function.update_of_ne hQ, hle Q]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep; subst hep
      exact ⟨hle, fun h => absurd h hs⟩

structure SyncTopRaw
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) : Prop where
  abortP : esP.abort = false
  abortL : esL.abort = false
  g_eq : AuthL11.eraseSt esP.g = AuthL11.eraseSt esL.g
  vp_rel : ∀ P, RelVPBucket (esL.g.epoch P) P (esP.g.st P) (esL.g.st P)
  cache_rel : ∀ t', RelCacheBucket (esP.h.cache t') (esL.h.cache t')
  fTable_lt : ∀ t0, t0 < qep + 1 → esP.h.fTable t0 = esL.h.fTable t0
  table_top : sp.table = esL.h.fTable (qep + 1)
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
  root_ge_tH_pl : ∀ P, healEpoch tL ≤ esL.g.epoch P → ((esP.g.st P).root).isSome = true →
    postLeak tL esL.g = true
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
  pl_false_max : postLeak tL esL.g = false →
    (∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) → (esL.g.st P).root = sp.σ) ∧
    (∀ Tc σc k, esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σc, k) → σc = sp.σ)
  lc_inv : esP.h.lc = esL.h.lc ∧ ∀ e, esL.h.lc = some e → e ≤ qep

@[expose] def StepRelTopRaw {α : Type}
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (rP : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
      PRFPRNG.GameState Sig I K)
    (rL : α × EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) : Prop :=
  rP.1.2.abort = true ∨ (rP.1.1 = rL.1 ∧ SyncTopRaw prng Δcka qep tL rP.1.2 rP.2 rL.2)

theorem syncTopRaw_h_step
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp sp1 : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    {hP1 : PRNGBucketState T Sig K I} {hL1 : LocalBucketState T Sig K I}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL)
    (hcP1 : hP1.cache = esP.h.cache) (hcr1 : hP1.corrRoot = esP.h.corrRoot)
    (hlcP1 : hP1.lc = esP.h.lc) (hcL1 : hL1.cache = esL.h.cache) (hlcL1 : hL1.lc = esL.h.lc)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' < qep + 1 → hP1.fTable t' = hL1.fTable t')
    (htop1 : sp1.table = hL1.fTable (qep + 1)) :
    SyncTopRaw prng Δcka qep tL { esP with h := hP1 } sp1 { esL with h := hL1 } :=
  ⟨hsync.abortP, hsync.abortL, hsync.g_eq, hsync.vp_rel,
    fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t',
    hft1, htop1, hb1, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    fun P h1 h2 Tc h3 => by rw [hcL1]; exact hsync.vp_curCka P h1 h2 Tc h3,
    fun r hr h1 Tc h2 => by rw [hcL1]; exact hsync.trans_cache r hr h1 Tc h2,
    hsync.epoch_le, hsync.epoch_sends, hsync.same_epoch_rootL,
    fun P Tc σc k hc => hsync.cache_rootL P Tc σc k (hcL1 ▸ hc),
    fun hcr P Tc σp k hc => hsync.cache_rootP_none (hcr1 ▸ hcr) P Tc σp k (hcP1 ▸ hc),
    fun hcr => hsync.corrRoot_pl (hcr1 ▸ hcr),
    fun eC σC hcr => by
      obtain ⟨h1, h2, h3⟩ := hsync.corrRoot_rel eC σC (hcr1 ▸ hcr)
      exact ⟨h1, h2, fun Tc σl k hc => h3 Tc σl k (hcL1 ▸ hc)⟩,
    hsync.root_ge_tH_pl,
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
    fun hpl => ⟨fun P hmax => ((hsync.pl_false_max hpl).1 P hmax).trans hσ1.symm,
      fun Tc σc k hc => ((hsync.pl_false_max hpl).2 Tc σc k (hcL1 ▸ hc)).trans hσ1.symm⟩,
    ⟨by rw [hlcP1, hlcL1]; exact hsync.lc_inv.1, fun e he => hsync.lc_inv.2 e (hlcL1 ▸ he)⟩⟩

theorem syncTopRaw_set_win [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    SyncTopRaw prng Δcka qep tL
      { esP with g := { esP.g with win := true } } sp
      { esL with g := { esL.g with win := true } } := by
  have hg := hsync.g_eq
  refine ⟨hsync.abortP, hsync.abortL, ?_, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
    hsync.table_top, hsync.sp_b, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
    hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
    hsync.corrRoot_pl, hsync.corrRoot_rel, hsync.root_ge_tH_pl, hsync.some_mono_max,
    hsync.root_max, hsync.cache_max, hsync.pl_false_max, hsync.lc_inv⟩
  simp [AuthL11.eraseSt, AuthL11.eraseSt_epoch hg, AuthL11.eraseSt_idx hg,
    AuthL11.eraseSt_tL hg, AuthL11.eraseSt_trans hg, AuthL11.eraseSt_chall hg,
    AuthL11.eraseSt_comp hg, AuthL11.eraseSt_maxAcc hg, AuthL11.eraseSt_b hg,
    AuthL11.eraseSt_leaks hg, AuthL11.eraseSt_corrs hg]

@[simp]
theorem run_commitE_PRNGBucket
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    (commitE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen]

@[simp]
theorem run_commitE_LocalBucket
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (s : Ctx Γ T Sig SS RS M E) (P : Party)
    (old new : VP Γ T Sig SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)) :
    (commitE (hooksLocalBucket cka prng fs Δcka qep tL par) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksLocalBucket]

theorem syncTopRaw_of_vRecv_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp sp1 : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    {hP1 : PRNGBucketState T Sig K I} {hL1 : LocalBucketState T Sig K I}
    {P : Party} {c : Header T × E}
    {vpP' : VP Γ T (Option Sig) SS RS} {vpL' : VP Γ T Sig SS RS} {pos : SM.Pos}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL)
    (hpos_ep : pos.epoch = c.1.1) (htle : c.1.1 ≤ esL.g.epoch P + 1) (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPBucket (max (esL.g.epoch P) c.1.1) P vpP' vpL')
    (hcP1 : hP1.cache = esP.h.cache) (hcr1 : hP1.corrRoot = esP.h.corrRoot)
    (hlcP1 : hP1.lc = esP.h.lc) (hcL1 : hL1.cache = esL.h.cache) (hlcL1 : hL1.lc = esL.h.lc)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' < qep + 1 → hP1.fTable t' = hL1.fTable t')
    (htop1 : sp1.table = hL1.fTable (qep + 1))
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
    SyncTopRaw prng Δcka qep tL
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
      ?_, fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t', hft1, htop1, hb1,
      fun Q => by dsimp only; rw [hep_new Q, ← heq_other]; exact hsync.epoch_le_qep P.other,
      AuthL11.comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv, ?_, ?_, ?_,
      fun Q => by dsimp only; rw [hep_new Q, hep_new Q.other]; omega,
      fun Q hlt => by dsimp only at hlt ⊢; rw [hep_new Q, hep_new Q.other] at hlt; omega,
      fun Q1 Q2 _ => by dsimp only; rw [hrL_new Q1, hrL_new Q2], ?_, ?_,
      fun hcr => by dsimp only [SM.GameState.accept, postLeak] at hcr ⊢; rw [hcr1] at hcr; exact hsync.corrRoot_pl hcr,
      ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨by rw [hlcP1, hlcL1]; exact hsync.lc_inv.1, fun e he => hsync.lc_inv.2 e (hlcL1 ▸ he)⟩⟩
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
    · intro Q hge his; dsimp only at hge his ⊢; dsimp only [SM.GameState.accept, postLeak]
      by_cases hcr_some : esP.h.corrRoot.isSome = true
      · exact hsync.corrRoot_pl hcr_some
      · have hcr_none := Option.not_isSome_iff_eq_none.mp hcr_some
        rw [hep_new Q] at hge; rw [hrP_new_none hcr_none Q] at his
        exact hsync.root_ge_tH_pl P.other (heq_other.symm ▸ hge) his
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
    · intro hpl; dsimp only [SM.GameState.accept, postLeak] at hpl; obtain ⟨hp1, hp2⟩ := hsync.pl_false_max hpl
      exact ⟨fun Q _ => by dsimp only; rw [hrL_new Q]; exact (hp1 P.other (heq_other.trans hmax_old.symm)).trans hσ1.symm,
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
      ?_, fun t' => by rw [hcP1, hcL1]; exact hsync.cache_rel t', hft1, htop1, hb1,
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
      ?_, fun Q hge his => by dsimp only at hge his ⊢; rw [hep_old] at hge; rw [hrP_old Q] at his; exact hsync.root_ge_tH_pl Q hge his,
      ?_, ?_, ?_, ?_, ⟨by rw [hlcP1, hlcL1]; exact hsync.lc_inv.1, fun e he => hsync.lc_inv.2 e (hlcL1 ▸ he)⟩⟩
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
    · intro hpl; dsimp only [SM.GameState.accept, postLeak] at hpl; obtain ⟨hp1, hp2⟩ := hsync.pl_false_max hpl
      exact ⟨fun Q hQ => by dsimp only at hQ ⊢; rw [hep_old] at hQ; rw [hrL_old Q]; exact (hp1 Q hQ).trans hσ1.symm,
        fun Tc σc k hc => by dsimp only at hc; rw [hep_old, hcL1] at hc; exact (hp2 Tc σc k hc).trans hσ1.symm⟩
end TopHooks
end CryptoGames.SM.Construction.DeliverForge
