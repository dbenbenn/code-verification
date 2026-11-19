/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import VCVio.OracleComp.EvalDist.Measure

open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.SM (GameState Pos Record authLosingConditionsAvoided healedBy lastLeakGuessAdmissible ltOpt maxOpt spec)
open CryptoGames.SM.Construction (Header PartyState SchemeAdversary healEpoch mkParties realParty)
open CryptoGames.SM.Construction.AuthL11 (LeComp comp_inv_accept comp_inv_afterCorr comp_inv_record epMgmt_sync epoch_eq_other_of_sendsIn_succ eraseSt eraseSt_accept eraseSt_afterCorr eraseSt_authOK eraseSt_b eraseSt_chall eraseSt_comp eraseSt_corrAllowed eraseSt_corrs eraseSt_epoch eraseSt_idx eraseSt_inTransit eraseSt_leaks eraseSt_maxAcc eraseSt_record eraseSt_safeInj eraseSt_tL eraseSt_trans eraseSt_trivial eraseSt_win evalDist_bind_eq_zero evalDist_bind_mono lImpl max_epoch_accept_succ max_epoch_eq_of_eq max_epoch_update_succ nilSpec pImpl run_challPrfImpl run_corrImpl run_liftH run_processImpl_none run_processImpl_some simulateQ_lImpl_run_lift_sampleT simulateQ_pImpl_challPrfQuery simulateQ_pImpl_corrQuery simulateQ_pImpl_processQuery simulateQ_pImpl_run_lift_sampleT trivial_false_of_safeInj)
open CryptoGames.SM.Engine (Ctx EState Hooks VP abortE commitE deliverE injectE vRecv vSend)

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2c

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme SMScheme)
open _root_.CryptoGames.SM
  (Config GameState Pos Record RecvResult
   authLosingConditionsAvoided healedBy lastLeakGuessAdmissible ltOpt maxOpt spec)
open _root_.CryptoGames.SM.Engine
  (VP Ctx HM EState EM Hooks vSend vRecv commitE abortE deliverE injectE)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch realParty mkParties sampleT SchemeAdversary)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
  (postLeak bucketAuthCfg PRNGBucketAuthState resolveCorrRoot liftPBucketAuth
   lookupPRNGBucketAuthF rootPRNGBucketAuthHybrid hooksPRNGBucketAuthHybrid
   initPRNGBucketAuthHybrid PRNGBucketAuthEState isHonestHdrPRNGBucket
   hooksPRNGBucketAuthMain hooksPRNGBucketAuthForgedHdr implPRNGBucketAuthGen
   runPRNGAuthBucketHybridGen redPRNGAuthBucketHybridMain redPRNGAuthBucketHybridForgedHdr
   LocalBucketAuthState lookupLocalBucketAuthF rootLocalBucketAuth hooksLocalBucketAuth
   hooksLocalBucketAuthMain hooksLocalBucketAuthForgedHdr initLocalBucketAuth
   LocalBucketAuthEState isHonestHdrLocalBucket implLocalBucketAuthGen localAuthBucketMain
   localAuthBucketForgedHdr)

section Hop2cProofs

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}

@[local simp]
private theorem simulateQ_pImpl_liftPBucketAuth [DecidableEq I]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type} (q : CryptoGames.PRFPRNG.AdversaryComp Sig I K α)
    (s : PRNGBucketAuthState T Sig K I) :
    simulateQ (pImpl prng) ((liftPBucketAuth (T := T) q).run s) =
      (simulateQ (pImpl prng) q >>= fun a => pure (a, s)) := by
  change simulateQ (pImpl prng) (q >>= fun a => pure (a, s)) = _
  simp

/-- Cache coupling between `PRNGBucketAuthState` (at `t = qep + 1`, `b = true`) and
`LocalBucketAuthState`: matching CKA message `Tc` and FS-AEAD key `k`, and whenever `σP` resolves
at `ep` (either `some s` or via `hP.corrRoot`), `s = σL`. -/
private def RelCacheBucketAuth (hP : PRNGBucketAuthState T Sig K I) (ep : ℕ)
    (cP : Option (T × Option Sig × K)) (cL : Option (T × Sig × K)) : Prop :=
  (cP = none ∧ cL = none) ∨
  ∃ Tc σP σL k,
    cP = some (Tc, σP, k) ∧ cL = some (Tc, σL, k) ∧
      (∀ s, resolveCorrRoot hP ep σP = some s → s = σL)

/-- Virtual party coupling between `hooksPRNGBucketAuthHybrid` and `hooksLocalBucketAuth`. -/
private structure RelVPBucketAuth (hP : PRNGBucketAuthState T Sig K I) (ep : ℕ) (P : Party)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS) : Prop where
  id_P : vpP.id = P
  tcur_P : vpP.tcur = ep
  id_L : vpL.id = P
  tcur_L : vpL.tcur = ep
  γ_eq : vpP.γ = vpL.γ
  Tcur_eq : vpP.curCkaMsg = vpL.curCkaMsg
  vS_eq : vpP.vS = vpL.vS
  vR_eq : ∀ t', vpP.vR t' = vpL.vR t'
  root_eq : ∀ s, resolveCorrRoot hP ep vpP.root = some s → s = vpL.root

private theorem resolveCorrRoot_eq_of_corrRoot_eq
    {h1 h2 : PRNGBucketAuthState T Sig K I} (hcr : h1.corrRoot = h2.corrRoot)
    (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h1 ep σv = resolveCorrRoot h2 ep σv := by
  simp [resolveCorrRoot, hcr]

private theorem relCacheBucketAuth_of_corrRoot_eq
    {h1 h2 : PRNGBucketAuthState T Sig K I} (hcr : h1.corrRoot = h2.corrRoot)
    {ep : ℕ} {cP : Option (T × Option Sig × K)} {cL : Option (T × Sig × K)}
    (h : RelCacheBucketAuth h1 ep cP cL) :
    RelCacheBucketAuth h2 ep cP cL := by
  rcases h with ⟨hP0, hL0⟩ | ⟨Tc, σP, σL, k, hP0, hL0, hres⟩
  · exact Or.inl ⟨hP0, hL0⟩
  · refine Or.inr ⟨Tc, σP, σL, k, hP0, hL0, fun s hs => hres s ?_⟩
    rwa [resolveCorrRoot_eq_of_corrRoot_eq hcr]

private theorem relVPBucketAuth_of_corrRoot_eq
    {h1 h2 : PRNGBucketAuthState T Sig K I} (hcr : h1.corrRoot = h2.corrRoot)
    {ep : ℕ} {P : Party}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    (h : RelVPBucketAuth h1 ep P vpP vpL) :
    RelVPBucketAuth h2 ep P vpP vpL :=
  ⟨h.id_P, h.tcur_P, h.id_L, h.tcur_L, h.γ_eq, h.Tcur_eq, h.vS_eq, h.vR_eq,
    fun s hs => h.root_eq s (by rwa [resolveCorrRoot_eq_of_corrRoot_eq hcr])⟩

private theorem isHonestHdr_eq_of_relCache [DecidableEq T]
    {hP : PRNGBucketAuthState T Sig K I} {hL : LocalBucketAuthState T Sig K I}
    (hdr : Header T)
    (hcache : RelCacheBucketAuth hP hdr.1 (hP.cache hdr.1) (hL.cache hdr.1)) :
    isHonestHdrPRNGBucket hP hdr = isHonestHdrLocalBucket hL hdr := by
  unfold isHonestHdrPRNGBucket isHonestHdrLocalBucket
  rcases hcache with ⟨hP0, hL0⟩ | ⟨Tc, σP, σL, k, hP0, hL0, _⟩ <;> cases hdr.2 <;> simp [hP0, hL0]

private theorem postLeak_eraseSt {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (tL : Option ℕ) :
    postLeak tL g₁ = postLeak tL g₂ := by
  have htL : g₁.tL = g₂.tL := congrArg CryptoGames.SM.GameState.tL h
  simp [postLeak, htL]

private theorem admissible_ge_healEpoch (Δcka : ℕ) (tL : Option ℕ) (t0 : ℕ)
    (hadm : lastLeakGuessAdmissible (2 + Δcka) tL t0 = true) :
    healEpoch tL ≤ t0 := by
  cases tL with
  | none => simp [healEpoch]
  | some l =>
    simp [lastLeakGuessAdmissible, healedBy, healEpoch] at hadm ⊢
    omega

private theorem epMgmt_le_qep_auth {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hle : ∀ Q, g.epoch Q ≤ qep)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    (∀ Q, s₁.epoch Q ≤ qep) ∧ (P.sendsIn (g.epoch P + 1) = true → g.epoch P + 1 ≤ qep) := by
  unfold CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      have he1 : g.epoch P + 1 ≤ qep := by omega
      refine ⟨fun Q => ?_, fun _ => he1⟩
      by_cases hQ : Q = P
      · subst hQ; split <;> simp [CryptoGames.SM.GameState.leak, he1]
      · split <;> simp [CryptoGames.SM.GameState.leak, Function.update_of_ne hQ, hle Q]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨hle, fun h => absurd h hs⟩

private theorem sendsIn_succ_true_of_false_auth (P : Party) (t : ℕ) (h : P.sendsIn t = false) :
    P.sendsIn (t + 1) = true := by
  cases P <;> simp [CryptoGames.Party.sendsIn] at h ⊢ <;> omega

private theorem leComp_lookupBucketAuthF [DecidableEq I] [SampleableType KR] [SampleableType I]
    [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (qep t0 : ℕ) (ik : I)
    (hP : PRNGBucketAuthState T Sig K I) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hL : LocalBucketAuthState T Sig K I)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (ht0 : t0 < qep + 1) :
    LeComp (fun rP rL =>
        rP.1.1 = rL.1 ∧
        rP.2 = sp ∧
        rP.1.2.cache = hP.cache ∧
        rP.1.2.corrRoot = hP.corrRoot ∧
        rL.2.cache = hL.cache ∧
        (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
        rL.2.fTable (qep + 1) = hL.fTable (qep + 1))
      ((simulateQ (pImpl prng) ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t0 ik).run hP)).run sp)
      (simulateQ lImpl ((lookupLocalBucketAuthF (T := T) (Sig := Sig) t0 ik).run hL)) := by
  unfold lookupPRNGBucketAuthF lookupLocalBucketAuthF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft t0 ht0]
  cases hlk : (hL.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_pImpl_run_lift_sampleT,
      simulateQ_lImpl_run_lift_sampleT, bind_assoc]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro t' ht'
      by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · have hne : qep + 1 ≠ t0 := by omega
      simp [hne]

private theorem leComp_rootBucketAuthTop [DecidableEq I] [SampleableType KR] [SampleableType I]
    [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (qep : ℕ) (tL : Option ℕ) (t0 : ℕ) (pl : Bool) (ik0 : I)
    (σv0 : Option Sig) (σ0 : Sig)
    (hP : PRNGBucketAuthState T Sig K I) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hL : LocalBucketAuthState T Sig K I)
    (ht0 : t0 < qep + 1)
    (hb : sp.b = true)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1))
    (hcr_pl : hP.corrRoot.isSome = true → pl = true)
    (hσ_res : ∀ s, resolveCorrRoot hP (t0 - 1) σv0 = some s → s = σ0)
    (hσ_pl_false : pl = false → sp.σ = σ0)
    (hσ_unres : pl = true → resolveCorrRoot hP (t0 - 1) σv0 = none →
      hP.corrRoot = none ∧ σv0 = none ∧ sp.σ = σ0) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        ∃ σP σL k,
          rP.1.1 = some (σP, k) ∧
          rL.1 = (σL, k) ∧
          (∀ s, σP = some s → s = σL) ∧
          (pl = false → rP.2.σ = σL ∧ rP.1.2.corrRoot = none ∧
            (t0 < healEpoch tL → σP = some σL) ∧ (healEpoch tL ≤ t0 → σP = none)) ∧
          (pl = true → σP = some σL ∧
            (rP.1.2.corrRoot = hP.corrRoot ∨
              (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (t0 - 1, σ0)))) ∧
          rP.2.b = true ∧
          rP.1.2.cache = hP.cache ∧
          rL.2.cache = hL.cache ∧
          (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
          rP.2.table = rL.2.fTable (qep + 1))
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (qep + 1) t0 pl ik0 σv0).run hP)).run sp)
      (simulateQ lImpl
        ((rootLocalBucketAuth (T := T) prng qep tL t0 pl ik0 σ0).run hL)) := by
  unfold rootPRNGBucketAuthHybrid rootLocalBucketAuth
  rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
  dsimp only at hb htop hσ_pl_false hσ_unres
  subst hb
  have hnot_gt : ¬ (qep + 1 < t0) := by omega
  have hnot_eq : ¬ (t0 = qep + 1) := by omega
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hnot_gt, ↓reduceIte]
  cases pl
  · have hcr_none : hP.corrRoot = none := by
      cases hcr : hP.corrRoot with
      | none => rfl
      | some p => exact False.elim (Bool.noConfusion (hcr_pl (by simp [hcr])))
    have hcr_false : hP.corrRoot.isSome = false := by simp [hcr_none]
    have hσ_eq : σ_sp = σ0 := hσ_pl_false rfl
    subst σ_sp
    have hfl_rhs : (false || decide False) = false := rfl
    simp only [Bool.false_or, hcr_false, hfl_rhs, Bool.false_eq_true, hnot_eq, ↓reduceIte]
    by_cases hge_tH : (!(t0 < healEpoch tL)) = true
    · simp only [hge_tH, ↓reduceIte]
      have hlt_false : t0 < healEpoch tL → False := by
        intro hlt; simp [hlt] at hge_tH
      by_cases his_tH : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · simp only [his_tH, ↓reduceIte, StateT.run_bind, simulateQ_bind,
          simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_processQuery,
          run_processImpl_none, bind_assoc]
        cases prf_sp
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
            simulateQ_lImpl_run_lift_sampleT, bind_assoc]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ I) fun ir _ => ?_
          simp only [pure_bind, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_run_lift_sampleT, bind_assoc]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ0 ir).1, kRand, rfl, rfl,
            (fun _ h => by cases h),
            (fun _ => ⟨rfl, hcr_none, fun hlt => False.elim (hlt_false hlt), fun _ => rfl⟩),
            (fun h => by cases h), rfl, rfl, rfl, hft, htop⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · simp only [his_tH, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
          simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_processQuery,
          run_processImpl_some, bind_assoc]
        cases prf_sp
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
            StateT.run_bind, simulateQ_bind]
          refine (leComp_lookupBucketAuthF prng qep t0 ik0 hP
            { σ := (prng.up σ0 ik0).1, b := true, corr := corr_sp, prng := prng_sp,
              prf := false, table := table_sp } hL hft ht0).bind ?_
          rintro ⟨⟨kP, hP1⟩, sp1⟩ ⟨kL, hL1⟩ ⟨hk, hsp1, hcP1, hcr1, hcL1, hft1, htop1⟩
          subst hk hsp1
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨none, (prng.up σ0 ik0).1, kP, rfl, rfl,
            (fun _ h => by cases h),
            (fun _ => ⟨rfl, hcr1.trans hcr_none, fun hlt => False.elim (hlt_false hlt), fun _ => rfl⟩),
            (fun h => by cases h), rfl, hcP1, hcL1, hft1, by rw [htop1, ← htop]⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · have hlt_tH : t0 < healEpoch tL := by simp at hge_tH; exact hge_tH
      have his_tH : (tL.isSome && decide (t0 = healEpoch tL)) = false := by
        simp [Nat.ne_of_lt hlt_tH]
      simp only [hge_tH, his_tH, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
        simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_processQuery,
        run_processImpl_some, bind_assoc]
      cases prf_sp
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind,
          simulateQ_bind, simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_corrQuery,
          run_corrImpl, bind_assoc, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
          (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (fun _ => ⟨rfl, hcr_none, fun _ => rfl, fun hge => by omega⟩),
          (fun h => by cases h), rfl, rfl, rfl, hft, htop⟩)
      · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · have htr_rhs : (true || decide False) = true := rfl
    simp only [Bool.true_or, htr_rhs, ↓reduceIte]
    cases hres : resolveCorrRoot hP (t0 - 1) σv0 with
    | some σ =>
      have hσ_eq : σ = σ0 := hσ_res σ hres
      subst σ
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
        (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
        (fun h => by cases h), (fun _ => ⟨rfl, Or.inl rfl⟩), rfl, rfl, rfl, hft, htop⟩)
    | none =>
      obtain ⟨hcr_none, _, hσ_eq⟩ := hσ_unres rfl hres
      subst σ_sp
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucketAuth,
        simulateQ_pImpl_corrQuery, run_corrImpl, bind_assoc]
      cases prf_sp
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, (prng.up σ0 ik0).1,
          (prng.up σ0 ik0).2, rfl, rfl, (fun _ h => Option.some.inj h ▸ rfl),
          (fun h => by cases h), (fun _ => ⟨rfl, Or.inr ⟨hcr_none, rfl⟩⟩),
          rfl, rfl, rfl, hft, htop⟩)
      · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private def hkPRNGBucketChoice [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (forgedMode : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Hooks (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS :=
  if forgedMode then hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t
  else hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t

private def hkLocalBucketChoice [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (forgedMode : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) :
    Hooks nilSpec (LocalBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS :=
  if forgedMode then hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL
  else hooksLocalBucketAuthMain cka prng fs Δcka qep tL

private theorem leComp_startSendBucketAuthTop (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {e : ℕ} {P : Party}
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {r_coins : Option CCoins}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hpl_eq : postLeak tL gP = postLeak tL gL)
    (hvp : RelVPBucketAuth hP e P vpP vpL)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1))
    (hb : sp.b = true)
    (he_lt : e + 1 < qep + 1)
    (hcr_pl : hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_pl_false : postLeak tL gL = false → sp.σ = vpL.root)
    (hσ_unres : postLeak tL gL = true → resolveCorrRoot hP e vpP.root = none →
      hP.corrRoot = none ∧ vpP.root = none ∧ sp.σ = vpL.root) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        ∃ γ' T' σP σL k,
          rP.1.1 = some (γ', T', σP, fs.initSender k) ∧
          rL.1 = some (γ', T', σL, fs.initSender k) ∧
          (∀ s, σP = some s → s = σL) ∧
          (postLeak tL gL = false →
            rP.2.σ = σL ∧ rP.1.2.corrRoot = none ∧
              (e + 1 < healEpoch tL → σP = some σL) ∧ (healEpoch tL ≤ e + 1 → σP = none)) ∧
          (postLeak tL gL = true →
            σP = some σL ∧
              (rP.1.2.corrRoot = hP.corrRoot ∨
                (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, vpL.root)))) ∧
          rP.2.b = true ∧
          rP.1.2.cache (e + 1) = some (T', σP, k) ∧
          rL.2.cache (e + 1) = some (T', σL, k) ∧
          (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t' ∧ rL.2.cache t' = hL.cache t') ∧
          (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
          rP.2.table = rL.2.fTable (qep + 1))
      ((simulateQ (pImpl prng)
        (((hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1)).startSend
          gP P (e + 1) vpP.γ vpP.root r_coins).run hP)).run sp)
      (simulateQ lImpl
        (((hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL).startSend
          gL P (e + 1) vpL.γ vpL.root r_coins).run hL)) := by
  have hbody : ∀ (coins : CCoins),
      LeComp (fun rP rL =>
          rP.1.1 = none ∨
          ∃ γ' T' σP σL k,
            rP.1.1 = some (γ', T', σP, fs.initSender k) ∧
            rL.1 = some (γ', T', σL, fs.initSender k) ∧
            (∀ s, σP = some s → s = σL) ∧
            (postLeak tL gL = false →
              rP.2.σ = σL ∧ rP.1.2.corrRoot = none ∧
                (e + 1 < healEpoch tL → σP = some σL) ∧ (healEpoch tL ≤ e + 1 → σP = none)) ∧
            (postLeak tL gL = true →
              σP = some σL ∧
                (rP.1.2.corrRoot = hP.corrRoot ∨
                  (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, vpL.root)))) ∧
            rP.2.b = true ∧
            rP.1.2.cache (e + 1) = some (T', σP, k) ∧
            rL.2.cache (e + 1) = some (T', σL, k) ∧
            (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t' ∧ rL.2.cache t' = hL.cache t') ∧
            (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
            rP.2.table = rL.2.fTable (qep + 1))
        ((simulateQ (pImpl prng)
          ((do
            let c := cka.send vpP.γ coins
            match ← rootPRNGBucketAuthHybrid prng tL (qep + 1) (e + 1) (postLeak tL gP) c.2.2 vpP.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketAuthState T Sig K I =>
                { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hP)).run sp)
        (simulateQ lImpl
          ((do
            let c := cka.send vpL.γ coins
            let (σ', kVal) ← rootLocalBucketAuth prng qep tL (e + 1) (postLeak tL gL) c.2.2 vpL.root
            modify fun s : LocalBucketAuthState T Sig K I =>
              { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run hL)) := by
    intro coins
    rw [hvp.γ_eq, hpl_eq]
    simp only [StateT.run_bind, simulateQ_bind]
    refine (leComp_rootBucketAuthTop prng qep tL (e + 1) (postLeak tL gL)
      (cka.send vpL.γ coins).2.2 vpP.root vpL.root hP sp hL he_lt hb hft htop hcr_pl
      (by simpa using hvp.root_eq) hσ_pl_false (by simpa using hσ_unres)).bind ?_
    rintro ⟨⟨res_root, hP1⟩, sp1⟩ ⟨⟨σL, kL⟩, hL1⟩ hroot
    rcases hroot with hnone | ⟨σP, σL', k, hres_P, hres_L, hσ_rel, hplF, hplT, hb1, hcP1, hcL1, hft1, htop1⟩
    · dsimp only at hnone; subst hnone
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hres_P hres_L
      cases hres_L
      subst hres_P
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨(cka.send vpL.γ coins).1, (cka.send vpL.γ coins).2.1,
        σP, σL, kL, rfl, rfl, hσ_rel, hplF, (by simpa using hplT), hb1, ?_, ?_, ?_, hft1, htop1⟩)
      · simp
      · simp
      · intro t' ht'
        dsimp only
        rw [Function.update_of_ne ht', Function.update_of_ne ht', hcP1, hcL1]
        exact ⟨rfl, rfl⟩
  have hssP : (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1)).startSend =
      (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (qep + 1)).startSend := by
    cases forgedMode <;> rfl
  have hssL : (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL).startSend =
      (hooksLocalBucketAuth cka prng fs Δcka qep tL).startSend := by
    cases forgedMode <;> rfl
  rw [hssP, hssL]
  cases r_coins with
  | some coins =>
    simp only [hooksPRNGBucketAuthHybrid, hooksLocalBucketAuth, pure_bind]
    exact hbody coins
  | none =>
    unfold hooksPRNGBucketAuthHybrid hooksLocalBucketAuth
    dsimp only
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind,
      simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT,
      bind_assoc, bind_assoc]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    simp only [pure_bind]
    exact hbody coins

private def VSendRelBucketAuthTop (qep e : ℕ) (P : Party) (pl : Bool) (tL : Option ℕ)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS)
    (hP : PRNGBucketAuthState T Sig K I) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hL : LocalBucketAuthState T Sig K I)
    (rP : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGBucketAuthState T Sig K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K)
    (rL : Option (VP Γ T Sig SS RS × (Header T × E)) × LocalBucketAuthState T Sig K I) : Prop :=
  let e' := if P.sendsIn (e + 1) then e + 1 else e
  rP.1.1 = none ∨
  ∃ vpP' vpL' c,
    rP.1.1 = some (vpP', c) ∧
    rL.1 = some (vpL', c) ∧
    c.1 = (e', vpL'.curCkaMsg) ∧
    RelVPBucketAuth rP.1.2 e' P vpP' vpL' ∧
    rP.2.b = true ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1) ∧
    (P.sendsIn (e + 1) = true →
      (∀ s, vpP'.root = some s → s = vpL'.root) ∧
      (pl = false → rP.2.σ = vpL'.root ∧ rP.1.2.corrRoot = none ∧
        (e + 1 < healEpoch tL → vpP'.root = some vpL'.root) ∧
        (healEpoch tL ≤ e + 1 → vpP'.root = none)) ∧
      (pl = true → vpP'.root = some vpL'.root ∧
        (rP.1.2.corrRoot = hP.corrRoot ∨
          (hP.corrRoot = none ∧ rP.1.2.corrRoot = some (e, vpL.root)))) ∧
      (∃ T' k, vpL'.curCkaMsg = some T' ∧
        rP.1.2.cache (e + 1) = some (T', vpP'.root, k) ∧
        rL.2.cache (e + 1) = some (T', vpL'.root, k)) ∧
      (∀ t', t' ≠ e + 1 → rP.1.2.cache t' = hP.cache t' ∧ rL.2.cache t' = hL.cache t')) ∧
    (P.sendsIn (e + 1) = false →
      rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL ∧
      vpP'.root = vpP.root ∧ vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg)

private theorem leComp_vSendBucketAuthTop (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {e : ℕ} {P : Party}
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {m : M} {r_coins : Option CCoins}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hpl_eq : postLeak tL gP = postLeak tL gL)
    (hvp : RelVPBucketAuth hP e P vpP vpL)
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1))
    (hb : sp.b = true)
    (he_lt : P.sendsIn (e + 1) = true → e + 1 < qep + 1)
    (hcr_pl : P.sendsIn (e + 1) = true → hP.corrRoot.isSome = true → postLeak tL gL = true)
    (hσ_pl_false : P.sendsIn (e + 1) = true → postLeak tL gL = false → sp.σ = vpL.root)
    (hσ_unres : P.sendsIn (e + 1) = true → postLeak tL gL = true →
      resolveCorrRoot hP e vpP.root = none →
      hP.corrRoot = none ∧ vpP.root = none ∧ sp.σ = vpL.root) :
    LeComp (VSendRelBucketAuthTop qep e P (postLeak tL gL) tL vpP vpL hP sp hL)
      ((simulateQ (pImpl prng)
        ((vSend (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1))
          gP P vpP m none r_coins).run hP)).run sp)
      (simulateQ lImpl
        ((vSend (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL)
          gL P vpL m none r_coins).run hL)) := by
  have hfsP : (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1)).fsSend =
      (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (qep + 1)).fsSend := by
    cases forgedMode <;> rfl
  have hfsL : (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL).fsSend =
      (hooksLocalBucketAuth cka prng fs Δcka qep tL).fsSend := by
    cases forgedMode <;> rfl
  unfold vSend
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hsends : P.sendsIn (e + 1) = true
  · simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind]
    refine (leComp_startSendBucketAuthTop forgedMode cka prng fs Δcka qep tL hpl_eq hvp hft htop hb
      (he_lt hsends) (hcr_pl hsends) (hσ_pl_false hsends) (hσ_unres hsends)).bind ?_
    rintro ⟨⟨res_ssP, hP1⟩, sp1⟩ ⟨res_ssL, hL1⟩ hss
    rcases hss with hnone | ⟨γ', T', σP, σL, k, hP_eq, hL_eq, hσ_rel, hplF, hplT, hb1,
      hcP_self, hcL_self, hc_other, hft1, htop1⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
      rw [hfsP, hfsL]
      simp only [hooksPRNGBucketAuthHybrid, hooksLocalBucketAuth,
        pure_bind, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hsends]), ?_,
        hb1, hft1, htop1, ?_, (fun hns => by rw [hsends] at hns; cases hns)⟩)
      · simp only [hsends, ↓reduceIte]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, ?_⟩
        intro s hs
        by_cases hpl : postLeak tL gL = true
        · have hsome := (hplT hpl).1
          rw [hsome] at hs
          simp [resolveCorrRoot] at hs
          exact hs.symm
        · have hpl0 : postLeak tL gL = false := Bool.eq_false_iff.mpr hpl
          have hcr1 : hP1.corrRoot = none := (hplF hpl0).2.1
          cases σP with
          | some s' =>
            simp [resolveCorrRoot] at hs
            subst hs
            exact hσ_rel s' rfl
          | none =>
            simp [resolveCorrRoot, hcr1] at hs
      · intro _
        exact ⟨hσ_rel, hplF, hplT, ⟨T', k, rfl, hcP_self, hcL_self⟩, hc_other⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have hns : P.sendsIn (e + 1) = false := Bool.eq_false_iff.mpr hsends
    rcases hvSL : vpL.vS with _ | ss
    · have hvSP : vpP.vS = none := hvp.vS_eq.trans hvSL
      simp only [hvSP, hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hb,
        hft, htop, (fun hs => by rw [hns] at hs; cases hs), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact hvp
    · have hvSP : vpP.vS = some ss := hvp.vS_eq.trans hvSL
      rw [hfsP, hfsL]
      simp only [hvSP, hooksPRNGBucketAuthHybrid, hooksLocalBucketAuth,
        hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq, pure_bind, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hb,
        hft, htop, (fun hs => by rw [hns] at hs; cases hs), (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hvp.id_P, rfl, hvp.id_L, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_eq⟩

/-! ### Hop 2c (`ForgedHdr`, `t = qep + 1`, `b = true`) -/

private theorem leComp_startRecvBucketForgedTop
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {e : ℕ} {P : Party} {tn0 : T}
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hplP : postLeak tL gP = false)
    (hplL : postLeak tL gL = false)
    (hcr : hP.corrRoot = none)
    (hvp : RelVPBucketAuth hP e P vpP vpL)
    (hcache : ∀ t', RelCacheBucketAuth hP t' (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1))
    (hb : sp.b = true)
    (he_le : e ≤ qep)
    (hσ_qep : e = qep → sp.σ = vpL.root) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        (rP.1.1 = some none ∧ rL.1 = some none ∧
          rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
        ∃ γ' σP σL k,
          rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
          rL.1 = some (some (γ', σL, fs.initReceiver k)) ∧
          (∀ s, σP = some s → s = σL) ∧
          rP.2.σ = sp.σ ∧
          rP.2.b = true ∧
          rP.1.2.corrRoot = none ∧
          rP.1.2.cache = hP.cache ∧
          rL.2.cache = hL.cache ∧
          (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
          rP.2.table = rL.2.fTable (qep + 1) ∧
          (∀ σc kc, hL.cache (e + 1) = some (tn0, σc, kc) → σL = σc))
      ((simulateQ (pImpl prng)
        (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1)).startRecv
          gP P (e + 1) vpP.γ vpP.root tn0).run hP)).run sp)
      (simulateQ lImpl
        (((hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL).startRecv
          gL P (e + 1) vpL.γ vpL.root tn0).run hL)) := by
  unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid
    hooksLocalBucketAuthForgedHdr hooksLocalBucketAuth
  dsimp only
  rw [hvp.γ_eq, hplP, hplL]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hnot_gt : (!(qep + 1 < e + 1)) = true := by simp; omega
  have hcr_false : hP.corrRoot.isSome = false := by simp [hcr]
  have hoff : (∀ σc kc, hL.cache (e + 1) ≠ some (tn0, σc, kc)) →
      LeComp (fun rP rL =>
          rP.1.1 = none ∨
          (rP.1.1 = some none ∧ rL.1 = some none ∧
            rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
          ∃ γ' σP σL k,
            rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
            rL.1 = some (some (γ', σL, fs.initReceiver k)) ∧
            (∀ s, σP = some s → s = σL) ∧
            rP.2.σ = sp.σ ∧
            rP.2.b = true ∧
            rP.1.2.corrRoot = none ∧
            rP.1.2.cache = hP.cache ∧
            rL.2.cache = hL.cache ∧
            (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
            rP.2.table = rL.2.fTable (qep + 1) ∧
            (∀ σc kc, hL.cache (e + 1) = some (tn0, σc, kc) → σL = σc))
        ((simulateQ (pImpl prng)
          ((if !(qep + 1 < e + 1) && lastLeakGuessAdmissible (2 + Δcka) tL (e + 1) then
              if tL.isSome && decide (e + 1 = healEpoch tL) then
                pure none
              else if (false || hP.corrRoot.isSome || decide (qep + 1 < e + 1)) = true then
                match resolveCorrRoot hP (e + 1 - 1) vpP.root with
                | none => pure none
                | some σ =>
                  let kk := cka.receive vpL.γ tn0
                  let p := prng.up σ kk.2
                  pure (some (some (kk.1, some p.1, fs.initReceiver p.2)))
              else if e + 1 = qep + 1 then do
                let kk := cka.receive vpL.γ tn0
                match ← liftPBucketAuth
                    (CryptoGames.PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
                | none => pure none
                | some (σOut, kOut) =>
                  pure (some (some (kk.1, some σOut, fs.initReceiver kOut)))
              else if !(e + 1 < healEpoch tL) then do
                let kk := cka.receive vpL.γ tn0
                let kOut ← lookupPRNGBucketAuthF (e + 1) kk.2
                pure (some (some (kk.1, none, fs.initReceiver kOut)))
              else pure (some none)
            else pure (some none)).run hP)).run sp)
        (simulateQ lImpl
          ((if !(qep + 1 < e + 1) && lastLeakGuessAdmissible (2 + Δcka) tL (e + 1) then
              if tL.isSome && decide (e + 1 = healEpoch tL) then
                pure none
              else if false = true then
                let kk := cka.receive vpL.γ tn0
                let p := prng.up vpL.root kk.2
                pure (some (some (kk.1, p.1, fs.initReceiver p.2)))
              else if !(e + 1 < healEpoch tL) then do
                let kk := cka.receive vpL.γ tn0
                let kOut ← lookupLocalBucketAuthF (e + 1) kk.2
                pure (some (some (kk.1, (prng.up vpL.root kk.2).1, fs.initReceiver kOut)))
              else pure (some none)
            else pure (some none)).run hL)) := by
    intro hno_cache
    rw [hnot_gt, Bool.true_and]
    by_cases hadm : lastLeakGuessAdmissible (2 + Δcka) tL (e + 1) = true
    · simp only [hadm, ↓reduceIte]
      have hge_prop : healEpoch tL ≤ e + 1 := admissible_ge_healEpoch Δcka tL (e + 1) hadm
      have hge_tH : (!(e + 1 < healEpoch tL)) = true := by simp; omega
      by_cases his_tH : (tL.isSome && decide (e + 1 = healEpoch tL)) = true
      · simp only [his_tH, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have hnot_gt_b : decide (qep + 1 < e + 1) = false := by simp; omega
        simp only [his_tH, hcr_false, hnot_gt_b, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hge_tH]
        by_cases htop_ep : e + 1 = qep + 1
        · have he_eq : e = qep := by omega
          have hσ_eq : sp.σ = vpL.root := hσ_qep he_eq
          simp only [htop_ep, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_challPrfQuery,
            run_challPrfImpl, bind_assoc]
          by_cases hcp : (sp.corr || sp.prng) = true
          · simp only [hcp, ↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [hcp, Bool.false_eq_true, hb, ↓reduceIte]
            unfold lookupLocalBucketAuthF
            simp only [StateT.run_bind, StateT.run_get, pure_bind]
            rw [htop]
            cases hlk : (hL.fTable (qep + 1)).lookup (cka.receive vpL.γ tn0).2 with
            | some R' =>
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
                some (prng.up sp.σ (cka.receive vpL.γ tn0).2).1,
                (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, R', rfl, rfl,
                (fun _ hs => by cases hs; rw [hσ_eq]), rfl, rfl, hcr, rfl, rfl, hft, rfl,
                fun σc kc hc => False.elim (hno_cache σc kc (htop_ep ▸ hc))⟩))
            | none =>
              simp only [bind_assoc, pure_bind, StateT.run_bind, simulateQ_bind,
                simulateQ_lImpl_run_lift_sampleT]
              refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun R' _ => ?_
              simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
                some (prng.up sp.σ (cka.receive vpL.γ tn0).2).1,
                (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, R', rfl, rfl,
                (fun _ hs => by cases hs; rw [hσ_eq]), rfl, rfl, hcr, rfl, rfl, ?_,
                by simp,
                fun σc kc hc => False.elim (hno_cache σc kc (htop_ep ▸ hc))⟩))
              · intro t' ht'
                have hne : t' ≠ qep + 1 := by omega
                simp [hne, hft t' ht']
        · have he1_lt : e + 1 < qep + 1 := by omega
          simp only [htop_ep, ↓reduceIte, StateT.run_bind, simulateQ_bind]
          refine (leComp_lookupBucketAuthF prng qep (e + 1) (cka.receive vpL.γ tn0).2
            hP sp hL hft he1_lt).bind ?_
          rintro ⟨⟨kOut, hP1⟩, sp1⟩ ⟨k', hL1⟩ ⟨hk, hsp1, hcP1, hcr1, hcL1, hft1, htop1⟩
          subst hk hsp1
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ tn0).1,
            none, (prng.up vpL.root (cka.receive vpL.γ tn0).2).1, kOut, rfl, rfl,
            (fun _ hs => by cases hs), rfl, hb, hcr1.trans hcr, hcP1, hcL1, hft1,
            by rw [htop1, ← htop],
            fun σc kc hc => False.elim (hno_cache σc kc hc)⟩))
    · simp only [hadm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
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
      have hres_eq : resolveCorrRoot hP (e + 1) σp = σp := by
        cases σp <;> simp [resolveCorrRoot, hcr]
      rw [hres_eq]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tc).1, σp, σl, k,
        rfl, rfl, (fun s hs => hσ_rel s (by rwa [hres_eq])), rfl, hb, hcr, rfl, rfl, hft, htop,
        fun σc kc hc => by rw [hcL] at hc; cases hc; rfl⟩))
    · conv => arg 2; simp only [hTc, ↓reduceIte]
      conv => arg 3; simp only [hTc, ↓reduceIte]
      exact hoff (fun σc kc hc => by rw [hcL] at hc; cases hc; exact hTc rfl)

private def VRecvRelBucketForgedTop (qep e : ℕ) (P : Party) (c : Header T × E)
    (vpL : VP Γ T Sig SS RS)
    (hP : PRNGBucketAuthState T Sig K I) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hL : LocalBucketAuthState T Sig K I)
    (rP : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGBucketAuthState T Sig K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K)
    (rL : Option (Option (VP Γ T Sig SS RS × ℕ × ℕ × M)) × LocalBucketAuthState T Sig K I) : Prop :=
  let t0 := c.1.1
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧
    rP.1.2.corrRoot = none ∧
    rP.1.2.cache = hP.cache ∧ rL.2.cache = hL.cache ∧
    rP.2.b = true ∧ rP.2.σ = sp.σ ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1)) ∨
  ∃ vpP' vpL' i' m',
    rP.1.1 = some (some (vpP', t0, i', m')) ∧
    rL.1 = some (some (vpL', t0, i', m')) ∧
    t0 ≤ e + 1 ∧
    P.sendsIn t0 = false ∧
    RelVPBucketAuth rP.1.2 (max e t0) P vpP' vpL' ∧
    rP.1.2.corrRoot = none ∧
    rP.1.2.cache = hP.cache ∧
    rL.2.cache = hL.cache ∧
    rP.2.b = true ∧
    rP.2.σ = sp.σ ∧
    (∀ t', t' < qep + 1 → rP.1.2.fTable t' = rL.2.fTable t') ∧
    rP.2.table = rL.2.fTable (qep + 1) ∧
    (t0 ≤ e → vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg) ∧
    (t0 = e + 1 → (∃ tn0, c.1.2 = some tn0) ∧
      ∀ tn0 σc kc, c.1.2 = some tn0 → hL.cache (e + 1) = some (tn0, σc, kc) → vpL'.root = σc)

private theorem leComp_vRecvBucketForgedTop
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {e : ℕ} {P : Party}
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {c : Header T × E} {rec : Option (Record M (Header T × E))}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hplP : postLeak tL gP = false)
    (hplL : postLeak tL gL = false)
    (hcr : hP.corrRoot = none)
    (hvp : RelVPBucketAuth hP e P vpP vpL)
    (hcache : ∀ t', RelCacheBucketAuth hP t' (hP.cache t') (hL.cache t'))
    (hft : ∀ t', t' < qep + 1 → hP.fTable t' = hL.fTable t')
    (htop : sp.table = hL.fTable (qep + 1))
    (hb : sp.b = true)
    (he_le : e ≤ qep)
    (hσ_qep : e = qep → sp.σ = vpL.root) :
    LeComp (VRecvRelBucketForgedTop qep e P c vpL hP sp hL)
      ((simulateQ (pImpl prng)
        ((vRecv (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
          gP P vpP c rec).run hP)).run sp)
      (simulateQ lImpl
        ((vRecv (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          gL P vpL c rec).run hL)) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hguard : (P.sendsIn c.1.1 || decide (e + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr, rfl, rfl, hb, rfl, hft, htop⟩))
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
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr, rfl, rfl, hb, rfl, hft, htop⟩))
      | some Tn =>
        simp only [StateT.run_bind, simulateQ_bind]
        have hns_e1 : P.sendsIn (e + 1) = false := hnew ▸ hns
        refine (leComp_startRecvBucketForgedTop cka prng fs Δcka qep tL
          hplP hplL hcr hvp hcache hft htop hb he_le hσ_qep).bind ?_
        rintro ⟨⟨res_srP, hP1⟩, sp1⟩ ⟨res_srL, hL1⟩ hsr
        rcases hsr with hnone | ⟨hP_none, hL_none, rfl, rfl, rfl⟩ |
          ⟨γ', σP, σL, k, hP_some, hL_some, hσ_rel, hσ1, hb1, hcr1, hcP1, hcL1, hft1, htop1, hcache_hit⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr, rfl, rfl, hb, rfl, hft, htop⟩))
        · dsimp only at hP_some hL_some; subst hP_some hL_some
          simp only [pure_bind, Function.update_self,
            hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid,
            hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth]
          cases hfs : fs.receive (fs.initReceiver k) c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr1, hcP1, hcL1, hb1, hσ1, hft1, htop1⟩))
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]
            refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ?_
            dsimp only [VRecvRelBucketForgedTop]
            rw [hnew, hmax]
            refine Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_e1, ?_,
              hcr1, hcP1, hcL1, hb1, hσ1, hft1, htop1, fun hle_e => by omega, ?_⟩)
            · refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_, ?_⟩
              · intro t'
                dsimp only
                rw [Function.update_idem, Function.update_idem]
                by_cases ht' : t' = e + 1
                · subst ht'; simp only [Function.update_self]
                · simp only [Function.update_of_ne ht', hvp.vR_eq t']
              · intro s hs
                cases σP with
                | some s' =>
                  simp [resolveCorrRoot] at hs
                  subst hs
                  exact hσ_rel s' rfl
                | none =>
                  dsimp only at hcr1
                  simp [resolveCorrRoot, hcr1] at hs
            · intro _
              refine ⟨⟨Tn, hTn⟩, fun tn0 σc kc htn0 hc => ?_⟩
              rw [hTn] at htn0
              cases htn0
              exact hcache_hit σc kc hc
    · simp only [hnew, ↓reduceIte, pure_bind]
      have htle_e : c.1.1 ≤ e := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max e c.1.1 = e := Nat.max_eq_left htle_e
      rcases hvRL : vpL.vR c.1.1 with _ | rs
      · have hvRP : vpP.vR c.1.1 = none := (hvp.vR_eq c.1.1).trans hvRL
        simp only [hvRP, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr, rfl, rfl, hb, rfl, hft, htop⟩))
      · have hvRP : vpP.vR c.1.1 = some rs := (hvp.vR_eq c.1.1).trans hvRL
        simp only [hvRP, hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid,
          hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuth, pure_bind]
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcr, rfl, rfl, hb, rfl, hft, htop⟩))
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            hcr, rfl, rfl, hb, rfl, hft, htop, fun _ => ⟨rfl, rfl⟩, fun heq => False.elim (hnew heq)⟩))
          rw [hmax]
          refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            ?_, hvp.root_eq⟩
          intro t'
          dsimp only
          by_cases ht' : t' = c.1.1
          · subst ht'; simp only [Function.update_self]
          · simp only [Function.update_of_ne ht', hvp.vR_eq t']

private theorem tL_mem_leaks_leak {St Msg C : Type} (s : GameState St Msg C) (l : ℕ) :
    ∀ cur, (s.leak l).tL = some cur → cur ∈ (s.leak l).leaks := by
  intro cur hcur
  simp [CryptoGames.SM.GameState.leak] at hcur ⊢
  omega

private theorem tL_mem_leaks_epMgmt {St Msg C : Type} {s s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hmem : ∀ cur, s.tL = some cur → cur ∈ s.leaks)
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    ∀ cur, s₁.tL = some cur → cur ∈ s₁.leaks := by
  unfold CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (s.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hbl : (bad && !s.safeCh Δ P) = true
      · simp only [hbl, ↓reduceIte]
        exact tL_mem_leaks_leak s (s.epoch P + 1)
      · simp only [hbl, Bool.false_eq_true, ↓reduceIte]
        exact hmem
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact hmem

private theorem tL_mem_leaks_afterCorr {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    ∀ cur, (s.afterCorr P).tL = some cur → cur ∈ (s.afterCorr P).leaks := by
  intro cur hcur
  unfold CryptoGames.SM.GameState.afterCorr at hcur ⊢
  exact tL_mem_leaks_leak _ _ cur hcur

private theorem leak_witness_of_postLeak_true {St Msg C : Type} {tL : Option ℕ} {s : GameState St Msg C}
    (hmem : ∀ cur, s.tL = some cur → cur ∈ s.leaks)
    (hpl : postLeak tL s = true) :
    ∃ cur ∈ s.leaks, ltOpt tL cur = true ∧ ∃ cur', s.tL = some cur' ∧ cur ≤ cur' := by
  unfold postLeak at hpl
  cases htL : s.tL with
  | none => simp [htL] at hpl
  | some cur =>
    simp [htL] at hpl
    exact ⟨cur, hmem cur htL, hpl, cur, rfl, le_rfl⟩

private theorem leak_witness_mono_epMgmt {St Msg C : Type} {tL : Option ℕ} {s s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hw : ∃ cur ∈ s.leaks, ltOpt tL cur = true ∧ ∃ cur', s.tL = some cur' ∧ cur ≤ cur')
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    ∃ cur ∈ s₁.leaks, ltOpt tL cur = true ∧ ∃ cur', s₁.tL = some cur' ∧ cur ≤ cur' := by
  rcases hw with ⟨cur, hcur_mem, hlt, cur', htL_eq, hle⟩
  unfold CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (s.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hbl : (bad && !s.safeCh Δ P) = true
      · simp only [hbl, ↓reduceIte, CryptoGames.SM.GameState.leak, htL_eq, maxOpt]
        exact ⟨cur, List.mem_cons_of_mem _ hcur_mem, hlt, max cur' (s.epoch P + 1), rfl,
          le_trans hle (Nat.le_max_left _ _)⟩
      · simp only [hbl, Bool.false_eq_true, ↓reduceIte]
        exact ⟨cur, hcur_mem, hlt, cur', htL_eq, hle⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨cur, hcur_mem, hlt, cur', htL_eq, hle⟩

private theorem leak_witness_mono_afterCorr {St Msg C : Type} {tL : Option ℕ} (s : GameState St Msg C)
    (P : Party)
    (hw : ∃ cur ∈ s.leaks, ltOpt tL cur = true ∧ ∃ cur', s.tL = some cur' ∧ cur ≤ cur') :
    ∃ cur ∈ (s.afterCorr P).leaks, ltOpt tL cur = true ∧
      ∃ cur', (s.afterCorr P).tL = some cur' ∧ cur ≤ cur' := by
  rcases hw with ⟨cur, hcur_mem, hlt, cur', htL_eq, hle⟩
  simp only [CryptoGames.SM.GameState.afterCorr, CryptoGames.SM.GameState.leak, htL_eq, maxOpt]
  exact ⟨cur, List.mem_cons_of_mem _ hcur_mem, hlt, max cur' (max (s.epoch .A) (s.epoch .B)),
    rfl, le_trans hle (Nat.le_max_left _ _)⟩

@[local simp]
private theorem run_commitE_PRNGBucketChoice
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (forgedMode : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    (commitE (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  cases forgedMode <;>
    simp [hkPRNGBucketChoice, commitE, hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthMain,
      hooksPRNGBucketAuthHybrid, CryptoGames.SM.GameState.accept]

@[local simp]
private theorem run_commitE_LocalBucketChoice
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (forgedMode : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (s : Ctx Γ T Sig SS RS M E) (P : Party)
    (old new : VP Γ T Sig SS RS) (pos : Pos)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)) :
    (commitE (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  cases forgedMode <;>
    simp [hkLocalBucketChoice, commitE, hooksLocalBucketAuthForgedHdr, hooksLocalBucketAuthMain,
      hooksLocalBucketAuth, CryptoGames.SM.GameState.accept]

private structure SyncForgedTop
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)) : Prop where
  abortP : esP.abort = false
  abortL : esL.abort = false
  corrRoot_none : esP.h.corrRoot = none
  pl_false : postLeak tL esL.g = false
  tL_mem_leaks : ∀ cur, esL.g.tL = some cur → cur ∈ esL.g.leaks
  g_eq : eraseSt esP.g = eraseSt esL.g
  vp_rel : ∀ P, RelVPBucketAuth esP.h (esL.g.epoch P) P (esP.g.st P) (esL.g.st P)
  cache_rel : ∀ t', RelCacheBucketAuth esP.h t' (esP.h.cache t') (esL.h.cache t')
  fTable_lt : ∀ t0, t0 < qep + 1 → esP.h.fTable t0 = esL.h.fTable t0
  table_top : sp.table = esL.h.fTable (qep + 1)
  sp_b : sp.b = true
  epoch_le_qep : ∀ P, esL.g.epoch P ≤ qep
  comp_inv : ∀ pos ∈ esL.g.comp, healedBy esL.g.tL (2 + Δcka) pos.epoch = false
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
  root_max : ∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) →
    (esL.g.st P).root = sp.σ
  cache_max : ∀ Tc σc k,
    esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σc, k) →
    σc = sp.σ

private def DeadForged (tL : Option ℕ) (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Prop :=
  st.1.abort = true ∨
  (st.1.g.win = true ∧ ∀ tWin, st.2 = some tWin →
    ∃ cur ∈ st.1.g.leaks, ltOpt tL cur = true ∧ cur < tWin) ∨
  (st.1.g.win = false ∧ st.2 = none ∧
    (∀ P, (st.1.g.st P).id = P ∧ (st.1.g.st P).tcur = st.1.g.epoch P) ∧
    (∀ r ∈ st.1.g.trans, r.ct.1.1 = r.pos.epoch) ∧
    ∃ cur ∈ st.1.g.leaks, ltOpt tL cur = true ∧
      ∃ cur', st.1.g.tL = some cur' ∧ cur ≤ cur')

private def StepRelForgedTop {α : Type}
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (x : (α × PRNGBucketAuthEState Γ T Sig SS RS M E K I) × CryptoGames.PRFPRNG.GameState Sig I K)
    (y : α × LocalBucketAuthEState Γ T Sig SS RS M E K I) : Prop :=
  DeadForged tL x.1.2 ∨
    (x.1.1 = y.1 ∧ x.1.2.2 = y.2.2 ∧
      (x.1.2.1.g.win = false → x.1.2.2 = none) ∧
      SyncForgedTop prng Δcka qep tL x.1.2.1 x.2 y.2.1)

private theorem syncForgedTop_h_step
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp sp1 : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    {hP1 : PRNGBucketAuthState T Sig K I} {hL1 : LocalBucketAuthState T Sig K I}
    (hsync : SyncForgedTop prng Δcka qep tL esP sp esL)
    (hcr1 : hP1.corrRoot = none)
    (hcP1 : hP1.cache = esP.h.cache) (hcL1 : hL1.cache = esL.h.cache)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' < qep + 1 → hP1.fTable t' = hL1.fTable t')
    (htop1 : sp1.table = hL1.fTable (qep + 1)) :
    SyncForgedTop prng Δcka qep tL { esP with h := hP1 } sp1 { esL with h := hL1 } :=
  ⟨hsync.abortP, hsync.abortL, hcr1, hsync.pl_false, hsync.tL_mem_leaks, hsync.g_eq,
    fun P => relVPBucketAuth_of_corrRoot_eq (hsync.corrRoot_none.trans hcr1.symm) (hsync.vp_rel P),
    fun t' => by
      rw [hcP1, hcL1]
      exact relCacheBucketAuth_of_corrRoot_eq (hsync.corrRoot_none.trans hcr1.symm) (hsync.cache_rel t'),
    hft1, htop1, hb1, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    fun P h1 h2 Tc h3 => by rw [hcL1]; exact hsync.vp_curCka P h1 h2 Tc h3,
    fun r hr h1 Tc h2 => by rw [hcL1]; exact hsync.trans_cache r hr h1 Tc h2,
    hsync.epoch_le, hsync.epoch_sends,
    fun P hmax => (hsync.root_max P hmax).trans hσ1.symm,
    fun Tc σc k hc => (hsync.cache_max Tc σc k (hcL1 ▸ hc)).trans hσ1.symm⟩

private theorem syncForgedTop_set_win [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncForgedTop prng Δcka qep tL esP sp esL) :
    SyncForgedTop prng Δcka qep tL
      { esP with g := { esP.g with win := true } } sp
      { esL with g := { esL.g with win := true } } := by
  have hg := hsync.g_eq
  refine ⟨hsync.abortP, hsync.abortL, hsync.corrRoot_none, hsync.pl_false, hsync.tL_mem_leaks,
    ?_, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt, hsync.table_top, hsync.sp_b,
    hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
    hsync.epoch_le, hsync.epoch_sends, hsync.root_max, hsync.cache_max⟩
  simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
    eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
    eraseSt_leaks hg, eraseSt_corrs hg]

private theorem syncForgedTop_of_vRecv_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp sp1 : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    {hP1 : PRNGBucketAuthState T Sig K I} {hL1 : LocalBucketAuthState T Sig K I}
    {P : Party} {c : Header T × E}
    {vpP' : VP Γ T (Option Sig) SS RS} {vpL' : VP Γ T Sig SS RS} {pos : Pos}
    (hsync : SyncForgedTop prng Δcka qep tL esP sp esL)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esL.g.epoch P + 1)
    (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPBucketAuth hP1 (max (esL.g.epoch P) c.1.1) P vpP' vpL')
    (hcr1 : hP1.corrRoot = none)
    (hcP1 : hP1.cache = esP.h.cache) (hcL1 : hL1.cache = esL.h.cache)
    (hb1 : sp1.b = true) (hσ1 : sp1.σ = sp.σ)
    (hft1 : ∀ t', t' < qep + 1 → hP1.fTable t' = hL1.fTable t')
    (htop1 : sp1.table = hL1.fTable (qep + 1))
    (hroot_le : c.1.1 ≤ esL.g.epoch P →
      vpL'.root = (esL.g.st P).root ∧ vpL'.curCkaMsg = (esL.g.st P).curCkaMsg)
    (hnew_hit : c.1.1 = esL.g.epoch P + 1 →
      (∃ tn0, c.1.2 = some tn0) ∧
        ∀ tn0 σc kc, c.1.2 = some tn0 → esL.h.cache (esL.g.epoch P + 1) = some (tn0, σc, kc) →
          vpL'.root = σc)
    (hnew_other : c.1.1 = esL.g.epoch P + 1 →
      c.1.1 ≤ esL.g.epoch P.other ∧
        ∀ tn0, c.1.2 = some tn0 → ∃ σc kc, esL.h.cache (esL.g.epoch P + 1) = some (tn0, σc, kc)) :
    SyncForgedTop prng Δcka qep tL
      { esP with g := esP.g.accept P vpP' pos, h := hP1 } sp1
      { esL with g := esL.g.accept P vpL' pos, h := hL1 } := by
  have hacc_ep : (esL.g.accept P vpL' pos).epoch =
      Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) := by
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
    rw [hpos_ep]
  have hcr_eq : esP.h.corrRoot = hP1.corrRoot := hsync.corrRoot_none.trans hcr1.symm
  refine ⟨hsync.abortP, hsync.abortL, hcr1, hsync.pl_false, hsync.tL_mem_leaks,
    eraseSt_accept hsync.g_eq P vpP' vpL' pos,
    ?_, ?_, hft1, htop1, hb1, ?_,
    comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q
    dsimp only
    rw [hacc_ep]
    dsimp only [CryptoGames.SM.GameState.accept]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact hvp'
    · simp only [Function.update_of_ne hQ]
      exact relVPBucketAuth_of_corrRoot_eq hcr_eq (hsync.vp_rel Q)
  · intro t'
    rw [hcP1, hcL1]
    exact relCacheBucketAuth_of_corrRoot_eq hcr_eq (hsync.cache_rel t')
  · intro Q
    dsimp only
    rw [hacc_ep]
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self]
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · have hc_le := (hnew_other hnew).1
        have hother_qep := hsync.epoch_le_qep P.other
        omega
      · have := hsync.epoch_le_qep P; omega
    · simp only [Function.update_of_ne hQ]; exact hsync.epoch_le_qep Q
  · intro r' hr'
    dsimp only at hr' ⊢
    rw [hacc_ep]
    simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hr'
    obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
    refine ⟨?_, h2⟩
    by_cases hQ : r'.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · intro Q hns_Q hpos_Q Tc hTc
    dsimp only at hns_Q hpos_Q hTc ⊢
    rw [hacc_ep] at hns_Q hpos_Q ⊢
    rw [hcL1]
    dsimp only [CryptoGames.SM.GameState.accept] at hTc
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self] at hns_Q hpos_Q hTc ⊢
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · have hns_e1 : P.sendsIn (esL.g.epoch P + 1) = false := hnew ▸ hns
        have hs_e2 : P.sendsIn ((esL.g.epoch P + 1) + 1) = true :=
          sendsIn_succ_true_of_false_auth P (esL.g.epoch P + 1) hns_e1
        have hmax_e1 : max (esL.g.epoch P) c.1.1 = esL.g.epoch P + 1 := by omega
        rw [hmax_e1, hs_e2] at hns_Q
        cases hns_Q
      · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
        rw [hmax_e] at hns_Q hpos_Q ⊢
        rw [(hroot_le htle_e).2] at hTc
        exact hsync.vp_curCka P hns_Q hpos_Q Tc hTc
    · simp only [Function.update_of_ne hQ] at hns_Q hpos_Q hTc ⊢
      exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
  · intro r' hr' hpos_r Tc hTc
    dsimp only at hr' ⊢
    rw [hcL1]
    simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hr'
    exact hsync.trans_cache r' hr'.1 hpos_r Tc hTc
  · intro Q
    dsimp only
    rw [hacc_ep]
    have hle_P := hsync.epoch_le P
    have hle_other := hsync.epoch_le P.other
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hc_le := (hnew_other hnew).1
      cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hc_le htle hle_P hle_other ⊢ <;> omega
    · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
      rw [hmax_e, Function.update_eq_self]
      exact hsync.epoch_le Q
  · intro Q hlt_Q
    dsimp only at hlt_Q ⊢
    rw [hacc_ep] at hlt_Q ⊢
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hc_le := (hnew_other hnew).1
      have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
        have := hsync.epoch_le P.other
        rw [CryptoGames.Party.other_other] at this
        omega
      cases Q <;> cases P <;> simp [CryptoGames.Party.other, hnew] at heq_other hlt_Q <;> omega
    · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
      rw [hmax_e, Function.update_eq_self] at hlt_Q ⊢
      exact hsync.epoch_sends Q hlt_Q
  · intro Q hQ_max
    dsimp only at hQ_max ⊢
    rw [hacc_ep] at hQ_max
    rw [hσ1]
    dsimp only [CryptoGames.SM.GameState.accept]
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hc_le := (hnew_other hnew).1
      have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
        have := hsync.epoch_le P.other
        rw [CryptoGames.Party.other_other] at this
        omega
      have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
        cases P <;> simp [CryptoGames.Party.other] at heq_other ⊢ <;> omega
      have hmax_new : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .A)
          (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .B) =
          esL.g.epoch P + 1 := by
        rw [hnew]
        exact max_epoch_accept_succ (by omega) (by omega)
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self]
        obtain ⟨⟨tn0, htn0⟩, hhit⟩ := hnew_hit hnew
        obtain ⟨σc, kc, hc_eq⟩ := (hnew_other hnew).2 tn0 htn0
        have hvp_σc : vpL'.root = σc := hhit tn0 σc kc htn0 hc_eq
        rw [hvp_σc]
        rw [← hmax_old] at hc_eq
        exact hsync.cache_max tn0 σc kc hc_eq
      · simp only [Function.update_of_ne hQ] at hQ_max ⊢
        have hQ_eq_max : esL.g.epoch Q = max (esL.g.epoch .A) (esL.g.epoch .B) := by
          rw [hmax_old, ← hmax_new, hQ_max]
        exact hsync.root_max Q hQ_eq_max
    · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
      rw [hmax_e, Function.update_eq_self] at hQ_max
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self, (hroot_le htle_e).1]
        exact hsync.root_max P hQ_max
      · simp only [Function.update_of_ne hQ]
        exact hsync.root_max Q hQ_max
  · intro Tc σc k hc_max
    dsimp only at hc_max ⊢
    rw [hacc_ep, hcL1] at hc_max
    rw [hσ1]
    have hmax_eq : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .A)
        (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .B) =
        max (esL.g.epoch .A) (esL.g.epoch .B) := by
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · have hc_le := (hnew_other hnew).1
        cases P <;> simp [CryptoGames.Party.other] at hc_le ⊢ <;> omega
      · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
        rw [hmax_e, Function.update_eq_self]
    rw [hmax_eq] at hc_max
    exact hsync.cache_max Tc σc k hc_max

private theorem mem_support_vSend_PRNGBucket (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {g : Ctx Γ T (Option Sig) SS RS M E} {P : Party}
    {vp : VP Γ T (Option Sig) SS RS} {m : M} {r_coins : Option CCoins}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {r : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGBucketAuthState T Sig K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (pImpl prng)
      ((vSend (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL t)
        g P vp m none r_coins).run hP)).run sp)) :
    ∀ vp' c, r.1.1 = some (vp', c) →
      vp'.id = vp.id ∧
      vp'.tcur = (if vp.id.sendsIn (vp.tcur + 1) then vp.tcur + 1 else vp.tcur) ∧
      c.1.1 = (if vp.id.sendsIn (vp.tcur + 1) then vp.tcur + 1 else vp.tcur) := by
  have hfsP : (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL t).fsSend =
      (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsSend := by
    cases forgedMode <;> rfl
  unfold vSend at hr
  by_cases hs : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr ⊢
    rcases hr with ⟨⟨⟨res1, h1⟩, sp1⟩, _, hr2⟩
    cases res1 with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr2
      subst hr2
      intro _ _ hnone; cases hnone
    | some val =>
      rcases val with ⟨γ', T', σ', ss'⟩
      rw [hfsP] at hr2
      simp only [hooksPRNGBucketAuthHybrid, pure_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr2
      subst hr2
      intro vp' c heq
      cases heq
      exact ⟨rfl, rfl, rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr ⊢
    cases hvS : vp.vS with
    | none =>
      simp only [hvS, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      intro _ _ hnone; cases hnone; exact ⟨rfl, rfl, rfl⟩
    | some ss =>
      rw [hfsP] at hr
      simp only [hvS, hooksPRNGBucketAuthHybrid, pure_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr
      intro vp' c heq
      cases heq
      exact ⟨rfl, rfl, rfl⟩

private theorem mem_support_vRecv_PRNGBucket (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {g : Ctx Γ T (Option Sig) SS RS M E} {P : Party}
    {vp : VP Γ T (Option Sig) SS RS} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {r : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGBucketAuthState T Sig K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (pImpl prng)
      ((vRecv (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL t)
        g P vp c rec).run hP)).run sp)) :
    ∀ vp' t0 i' m', r.1.1 = some (some (vp', t0, i', m')) →
      t0 = c.1.1 ∧ vp'.id = vp.id ∧ vp'.tcur = max vp.tcur c.1.1 := by
  have hfrP : (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL t).fsRecv =
      (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsRecv := by
    cases forgedMode <;> rfl
  unfold vRecv at hr
  dsimp only at hr
  by_cases hguard : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    intro _ _ _ _ heq; cases heq
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hr
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    have htle : c.1.1 ≤ vp.tcur + 1 := Nat.le_of_not_lt hguard.2
    by_cases hnew : c.1.1 = vp.tcur + 1
    · simp only [hnew, ↓reduceIte] at hr
      cases hTn : c.1.2 with
      | none =>
        simp only [hTn, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr
        subst hr
        intro _ _ _ _ heq; cases heq
      | some Tn =>
        simp only [hTn, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨res1, h1⟩, sp1⟩, _, hr2⟩
        cases res1 with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr2
          subst hr2
          intro _ _ _ _ heq; cases heq
        | some opt =>
          cases opt with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2
            intro _ _ _ _ heq; cases heq
          | some val =>
            rcases val with ⟨γ', σ', rs0⟩
            rw [hfrP] at hr2
            simp only [hooksPRNGBucketAuthHybrid, pure_bind, Function.update_self] at hr2
            cases hfs : fs.receive rs0 c.1 c.2 with
            | none =>
              simp only [hfs, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr2
              subst hr2
              intro _ _ _ _ heq; cases heq
            | some out =>
              rcases out with ⟨rs', i', m'⟩
              simp only [hfs, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr2
              subst hr2
              intro vp' t0 i0 m0 heq
              cases heq
              exact ⟨hnew.symm, rfl, by dsimp only; omega⟩
    · simp only [hnew, ↓reduceIte, pure_bind] at hr
      have htle_e : c.1.1 ≤ vp.tcur := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        intro _ _ _ _ heq; cases heq
      | some rs =>
        rw [hfrP] at hr
        simp only [hvR, hooksPRNGBucketAuthHybrid, pure_bind] at hr
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [hfs, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          intro _ _ _ _ heq; cases heq
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [hfs, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          intro vp' t0 i0 m0 heq
          cases heq
          exact ⟨rfl, rfl, (Nat.max_eq_left htle_e).symm⟩

private abbrev SMSpecAuth (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

private abbrev SMCompAuth (Γ T Sig SS RS M CCoins E : Type) :=
  OracleComp (SMSpecAuth Γ T Sig SS RS M CCoins E)

private def authOutBucketSimple {VPt Msg C HS : Type} [DecidableEq Msg] [DecidableEq C]
    (Δ : ℕ) (tL : Option ℕ) (st : EState VPt Msg C HS × Option ℕ) : Bool :=
  match st.2 with
  | none => false
  | some tWin => !st.1.abort && st.1.g.win && authLosingConditionsAvoided Δ tL tWin st.1.g

private theorem authOutBucketSimple_eq_false_of_deadForged [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δcka : ℕ) (tL : Option ℕ) (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (hd : DeadForged tL st) :
    authOutBucketSimple (2 + Δcka) tL st = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨_, hbad⟩ | ⟨_, hnone, _, _, _⟩
  · dsimp only at hab
    cases winEp <;> simp [authOutBucketSimple, hab]
  · cases winEp with
    | none => rfl
    | some tWin =>
      obtain ⟨cur, hcur_mem, hlt_tL, hlt_win⟩ := hbad tWin rfl
      have hall_false :
          es.g.leaks.all (fun l => !(ltOpt tL l && decide (l < tWin))) = false :=
        List.all_eq_false.mpr ⟨cur, hcur_mem, by simp [hlt_tL, hlt_win]⟩
      have halca : authLosingConditionsAvoided (2 + Δcka) tL tWin es.g = false := by
        unfold authLosingConditionsAvoided
        simp only [hall_false, Bool.false_and, Bool.and_false]
      dsimp only [authOutBucketSimple]
      rw [halca, Bool.and_false]
  · dsimp only at hnone
    subst hnone
    rfl

private def stepPBucketChoice (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecAuth Γ T Sig SS RS M CCoins E).Range q ×
      PRNGBucketAuthEState Γ T Sig SS RS M E K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implPRNGBucketAuthGen
      (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1))
      Δcka qep fs.maxSkip tL forgedMode q).run stP)).run sp

private def stepLBucketChoice (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (stL : LocalBucketAuthEState Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecAuth Γ T Sig SS RS M CCoins E).Range q ×
      LocalBucketAuthEState Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implLocalBucketAuthGen
      (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL)
      Δcka qep fs.maxSkip tL forgedMode q).run stL)

private theorem stepPForgedTop_dead
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hd : DeadForged tL stP) :
    ∀ r ∈ support (stepPBucketChoice true cka prng fs Δcka qep tL q stP sp),
      DeadForged tL r.1.2 := by
  intro r hr
  rcases stP with ⟨es0, winEp0⟩
  rcases hd with hab | ⟨hwin, hbad⟩ | ⟨hnwin, hwnone, hvp_id, htrans_ep, hwit⟩
  · dsimp only at hab
    rcases q with n | ((((arg | arg) | arg) | arg) | P)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, pImpl,
        StateT.run_lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
      rcases hr with ⟨_, _, rfl⟩
      exact Or.inl hab
    · rcases arg with ⟨P, m, r_coins⟩
      simp [stepPBucketChoice, implPRNGBucketAuthGen, hab] at hr
      rcases hr with rfl
      exact Or.inl hab
    · simp [stepPBucketChoice, implPRNGBucketAuthGen] at hr
      rcases hr with rfl
      exact Or.inl hab
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, deliverE, hab] at hr
      rcases hr with rfl
      exact Or.inl hab
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, injectE, hab] at hr
      rcases hr with rfl
      exact Or.inl hab
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, hab] at hr
      rcases hr with rfl
      exact Or.inl hab
  · dsimp only at hwin hbad
    rcases q with n | ((((arg | arg) | arg) | arg) | P)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, pImpl,
        StateT.run_lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
      rcases hr with ⟨_, _, rfl⟩
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
    · rcases arg with ⟨P, m, r_coins⟩
      simp [stepPBucketChoice, implPRNGBucketAuthGen, hwin] at hr
      rcases hr with rfl
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen] at hr
      rcases hr with rfl
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, deliverE, hwin] at hr
      rcases hr with rfl
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, injectE, hwin] at hr
      rcases hr with rfl
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, hwin] at hr
      rcases hr with rfl
      exact Or.inr (Or.inl ⟨hwin, hbad⟩)
  · dsimp only at hnwin hwnone hvp_id htrans_ep hwit
    subst hwnone
    rcases q with n | ((((arg | arg) | arg) | arg) | P)
    · simp [stepPBucketChoice, implPRNGBucketAuthGen, pImpl,
        StateT.run_lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
      rcases hr with ⟨_, _, rfl⟩
      exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
    · rcases arg with ⟨P, m, r_coins⟩
      unfold stepPBucketChoice implPRNGBucketAuthGen at hr
      simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind] at hr
      by_cases hab0 : es0.abort = true
      · simp [hab0] at hr; rcases hr with rfl; exact Or.inl hab0
      · simp only [hab0, hnwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hr
        cases hep : es0.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
        | none =>
          simp [hep] at hr; rcases hr with rfl
          exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
        | some s₁ =>
          simp only [hep, StateT.run_lift, simulateQ_bind, StateT.run_bind, bind_assoc,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vs, h1⟩, sp1⟩, hvs_mem, hr2⟩
          have hs₁_win : s₁.win = false := by
            unfold CryptoGames.SM.GameState.epMgmt at hep
            by_cases hs : P.sendsIn (es0.g.epoch P + 1) = true
            · simp only [hs, ↓reduceIte] at hep
              by_cases hq : qep < es0.g.epoch P + 1
              · simp [hq] at hep
              · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
                subst hep; split <;> simp [CryptoGames.SM.GameState.leak, hnwin]
            · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
              by_cases hq : qep < es0.g.epoch P
              · simp [hq] at hep
              · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
                subst hep; exact hnwin
          have hs₁_st : s₁.st = es0.g.st ∧ s₁.trans = es0.g.trans ∧
              s₁.epoch = Function.update es0.g.epoch P
                (if P.sendsIn (es0.g.epoch P + 1) then es0.g.epoch P + 1 else es0.g.epoch P) := by
            unfold CryptoGames.SM.GameState.epMgmt at hep
            by_cases hs : P.sendsIn (es0.g.epoch P + 1) = true
            · simp only [hs, ↓reduceIte] at hep
              by_cases hq : qep < es0.g.epoch P + 1
              · simp [hq] at hep
              · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
                subst hep
                split <;> simp [CryptoGames.SM.GameState.leak]
            · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
              by_cases hq : qep < es0.g.epoch P
              · simp [hq] at hep
              · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
                subst hep
                have hsf : P.sendsIn (es0.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hs
                simp [hsf, Function.update_eq_self]
          cases res_vs with
          | none =>
            simp [StateT.run_set] at hr2
            rcases hr2 with rfl
            exact Or.inl rfl
          | some pair =>
            rcases pair with ⟨st', ct⟩
            simp [StateT.run_set] at hr2
            rcases hr2 with rfl
            have hvs_props := mem_support_vSend_PRNGBucket true cka prng fs Δcka qep tL (qep + 1)
              hvs_mem st' ct rfl
            rw [hs₁_st.1, (hvp_id P).1, (hvp_id P).2] at hvs_props
            refine Or.inr (Or.inr ⟨hs₁_win, rfl, ?_, ?_, ?_⟩)
            · intro Q
              dsimp only [CryptoGames.SM.GameState.record]
              rw [hs₁_st.2.2]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self]
                exact ⟨hvs_props.1, hvs_props.2.1⟩
              · simp only [Function.update_of_ne hQ, hs₁_st.1]
                exact hvp_id Q
            · intro rec' hrec'
              dsimp only [CryptoGames.SM.GameState.record] at hrec'
              rcases List.mem_cons.mp hrec' with rfl | hmem'
              · dsimp only
                rw [hvs_props.2.2, hs₁_st.2.2]
                simp
              · exact htrans_ep rec' (hs₁_st.2.1 ▸ hmem')
            · dsimp only [CryptoGames.SM.GameState.record]
              exact leak_witness_mono_epMgmt hwit hep
    · simp [stepPBucketChoice, implPRNGBucketAuthGen] at hr
      rcases hr with rfl
      exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
    · rcases arg with ⟨P, c⟩
      unfold stepPBucketChoice implPRNGBucketAuthGen deliverE at hr
      simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
        pure_bind] at hr
      by_cases hab0 : es0.abort = true
      · simp [hab0] at hr; rcases hr with rfl; exact Or.inl hab0
      · simp only [hab0, hnwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hr
        cases htr : es0.g.inTransit P.other c with
        | none =>
          simp [htr, StateT.run_set] at hr; rcases hr with rfl
          exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
        | some rec0 =>
          have hrec0 : rec0 ∈ es0.g.trans ∧ rec0.ct = c := by
            unfold CryptoGames.SM.GameState.inTransit at htr
            have hf := List.find?_some htr
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
            exact ⟨List.mem_of_find?_eq_some htr, hf.2⟩
          simp only [htr, run_liftH, StateT.run_bind, simulateQ_bind, bind_assoc,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vr, h1⟩, sp1⟩, hvr_mem, hr2⟩
          have hcfg_dw : (bucketAuthCfg (M := M) Δcka tL).deliverWin = false := rfl
          cases res_vr with
          | none =>
            simp [abortE, StateT.run_set] at hr2; rcases hr2 with rfl
            exact Or.inl rfl
          | some opt =>
            cases opt with
            | none =>
              simp [hcfg_dw, StateT.run_set] at hr2; rcases hr2 with rfl
              exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
            | some quad =>
              rcases quad with ⟨vp', t0, i', m'⟩
              have hvr_props := mem_support_vRecv_PRNGBucket true cka prng fs Δcka qep tL (qep + 1)
                hvr_mem vp' t0 i' m' rfl
              rw [(hvp_id P).1, (hvp_id P).2] at hvr_props
              simp [run_commitE_PRNGBucketChoice, hcfg_dw, StateT.run_set] at hr2
              rcases hr2 with rfl
              have hpos_ep : rec0.pos.epoch = c.1.1 := by
                rw [← htrans_ep rec0 hrec0.1, hrec0.2]
              refine Or.inr (Or.inr ⟨hnwin, rfl, ?_, ?_, hwit⟩)
              · intro Q
                dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
                by_cases hQ : Q = P
                · subst Q
                  simp only [Function.update_self, hpos_ep]
                  exact ⟨hvr_props.2.1, hvr_props.2.2⟩
                · simp only [Function.update_of_ne hQ]
                  exact hvp_id Q
              · intro rec' hrec'
                simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hrec'
                exact htrans_ep rec' hrec'.1
    · rcases arg with ⟨P, c⟩
      unfold stepPBucketChoice implPRNGBucketAuthGen injectE at hr
      simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
        pure_bind] at hr
      by_cases hab0 : es0.abort = true
      · simp [hab0] at hr; rcases hr with rfl; exact Or.inl hab0
      · simp only [hab0, hnwin, Bool.false_or] at hr
        by_cases hguard : ((es0.g.inTransit P.other c).isSome ||
            !es0.g.safeInj (2 + Δcka)) = true
        · simp [hguard, hnwin, StateT.run_set] at hr; rcases hr with rfl
          exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
        · have hsafe : es0.g.safeInj (2 + Δcka) = true := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
            exact Bool.eq_true_of_not_eq_false hguard.2
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, run_liftH,
            StateT.run_bind, simulateQ_bind, bind_assoc, MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vr, h1⟩, sp1⟩, hvr_mem, hr2⟩
          cases res_vr with
          | none =>
            simp [abortE, hnwin, StateT.run_set] at hr2; rcases hr2 with rfl
            exact Or.inl rfl
          | some opt =>
            cases opt with
            | none =>
              simp [hnwin, StateT.run_set] at hr2; rcases hr2 with rfl
              exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)
            | some quad =>
              rcases quad with ⟨vp', t0, i', m'⟩
              have hvr_props := mem_support_vRecv_PRNGBucket true cka prng fs Δcka qep tL (qep + 1)
                hvr_mem vp' t0 i' m' rfl
              rw [(hvp_id P).1, (hvp_id P).2] at hvr_props
              rcases hvr_props with ⟨rfl, hvp'_id, hvp'_tcur⟩
              simp only [StateT.run_set, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff, exists_eq_left] at hr2
              rcases hr2 with ⟨⟨⟨res2, es2⟩, sp2⟩, hmem2, rfl⟩
              by_cases hqep : qep + 1 < c.1.1
              · rw [ite_eq_left hqep] at hmem2
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hmem2
                rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩
                refine Or.inr (Or.inr ⟨hnwin, ?_, hvp_id, htrans_ep, hwit⟩)
                simp only [hnwin, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              · rw [ite_eq_right hqep] at hmem2
                by_cases htriv : es0.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
                · have hacc_win :
                      (es0.g.accept P vp' ⟨P.other, c.1.1, i'⟩).win = false := hnwin
                  rw [ite_eq_left htriv] at hmem2
                  simp only [StateT.run_bind, run_commitE_PRNGBucketChoice,
                    pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hmem2
                  rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩
                  refine Or.inr (Or.inr ⟨hnwin, ?_, ?_, ?_, hwit⟩)
                  · simp only [hacc_win, Bool.and_false, Bool.false_and,
                      Bool.false_eq_true, ↓reduceIte]
                  · intro Q
                    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
                    by_cases hQ : Q = P
                    · subst Q
                      simp only [Function.update_self]
                      exact ⟨hvp'_id, hvp'_tcur⟩
                    · simp only [Function.update_of_ne hQ]
                      exact hvp_id Q
                  · intro rec' hrec'
                    simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hrec'
                    exact htrans_ep rec' hrec'.1
                · rw [ite_eq_right htriv] at hmem2
                  by_cases hfull : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
                  · rw [ite_eq_left hfull] at hmem2
                    simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                      StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hmem2
                    rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩
                    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
                    intro tWin htWin
                    dsimp only at htWin
                    simp only [Bool.not_false, Bool.not_true, Bool.true_and,
                      Bool.false_or] at htWin
                    by_cases hnf : (decide (c.1.1 = (es0.g.st P).tcur + 1) &&
                        !isHonestHdrPRNGBucket es0.h c.1) = true
                    · simp only [hnf, ↓reduceIte, Option.some.injEq] at htWin
                      subst htWin
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnf
                      have hc_ep : c.1.1 = es0.g.epoch P + 1 := by
                        rw [hnf.1, (hvp_id P).2]
                      rcases hwit with ⟨cur, hcur_mem, hlt_tL, cur', htL_eq, hcur_le⟩
                      unfold CryptoGames.SM.GameState.safeInj healedBy at hsafe
                      rw [htL_eq] at hsafe
                      simp only [decide_eq_true_eq] at hsafe
                      have hmin_le : min (es0.g.epoch .A) (es0.g.epoch .B) ≤ es0.g.epoch P := by
                        cases P <;> simp
                      exact ⟨cur, hcur_mem, hlt_tL, by omega⟩
                    · simp only [hnf, Bool.false_eq_true, ↓reduceIte] at htWin
                      cases htWin
                  · rw [ite_eq_right hfull] at hmem2
                    simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hmem2
                    rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩
                    refine Or.inr (Or.inr ⟨hnwin, ?_, hvp_id, htrans_ep, hwit⟩)
                    simp only [hnwin, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · unfold stepPBucketChoice implPRNGBucketAuthGen at hr
      simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind] at hr
      by_cases hab0 : es0.abort = true
      · simp only [hab0, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hr
        rcases hr with rfl; exact Or.inl hab0
      · simp only [hab0, hnwin, Bool.false_or] at hr
        by_cases hca : es0.g.corrAllowed P = true
        · simp only [hca, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_lift,
            simulateQ_bind, StateT.run_bind, bind_assoc, MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_rv, h1⟩, sp1⟩, _, hr2⟩
          rcases hr2 with ⟨_, rfl, hr2⟩
          cases res_rv with
          | none =>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            rcases hr2 with rfl
            exact Or.inl rfl
          | some stOut =>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            rcases hr2 with rfl
            exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep,
              leak_witness_mono_afterCorr es0.g P hwit⟩)
        · simp only [hca, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr
          rcases hr with rfl
          exact Or.inr (Or.inr ⟨hnwin, rfl, hvp_id, htrans_ep, hwit⟩)

private theorem leComp_dead_left {α β : Type} {R : α → β → Prop}
    (x : ProbComp α) (y : ProbComp β)
    (hx : ∀ a ∈ support x, ∀ b ∈ support y, R a b) :
    LeComp R x y := by
  induction x using OracleComp.inductionOn with
  | pure a => exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left a y (hx a (by simp))
  | query_bind t r ih =>
    intro F₁ F₂ hF
    rw [bind_assoc, ← OracleComp.evalDist_bind_const (liftM (OracleSpec.query t) : ProbComp _) (y >>= F₂)]
    refine evalDist_bind_mono (liftM (OracleSpec.query t)) _ _ fun u _ =>
      ih u (fun a ha b hb => hx a ?_ b hb) F₁ F₂ hF
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

private theorem leComp_deliverEForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncForgedTop prng Δcka qep tL esP sp esL) :
    LeComp (fun rP rL =>
        rP.1.2.abort = true ∨
        (rP.1.1 = rL.1 ∧ rP.1.2.g.win = esP.g.win ∧
          SyncForgedTop prng Δcka qep tL rP.1.2 rP.2 rL.2))
      ((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esP)).run sp)
      (simulateQ lImpl
        ((deliverE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have habw_eq : (esP.abort || esP.g.win) = (false || esL.g.win) := by
    rw [hsync.abortP, eraseSt_win hsync.g_eq]
  rw [habw_eq, hsync.abortL, eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold CryptoGames.SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hσ_qep : esL.g.epoch P = qep → sp.σ = (esL.g.st P).root := by
        intro heq_qep
        have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
          have hA := hsync.epoch_le_qep .A
          have hB := hsync.epoch_le_qep .B
          cases P <;> omega
        exact (hsync.root_max P hmax).symm
      have hplP : postLeak tL esP.g = false := by
        rw [postLeak_eraseSt hsync.g_eq]; exact hsync.pl_false
      have hcfg_dw : (bucketAuthCfg (M := M) Δcka tL).deliverWin = false := rfl
      simp only [StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecvBucketForgedTop cka prng fs Δcka qep tL hplP hsync.pl_false
        hsync.corrRoot_none (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top
        hsync.sp_b (hsync.epoch_le_qep P) hσ_qep).bind ?_
      rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
      rcases hvr with hnone | ⟨hP_none, hL_none, hcr1, hcP1, hcL1, hb1, hσ1, hft1, htop1⟩ |
        ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcr1, hcP1, hcL1, hb1, hσ1,
          hft1, htop1, hroot_le, hnew_hit⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_none hL_none; subst hP_none hL_none
        simp only [hcfg_dw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, pure_bind]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl,
          syncForgedTop_h_step hsync hcr1 hcP1 hcL1 hb1 hσ1 hft1 htop1⟩)
      · dsimp only at hP_some hL_some; subst hP_some hL_some
        have hPRNG_choice : hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1) =
            hkPRNGBucketChoice true cka prng fs Δcka qep tL (qep + 1) := rfl
        have hLoc_choice : hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL =
            hkLocalBucketChoice true cka prng fs Δcka qep tL := rfl
        rw [hPRNG_choice, hLoc_choice]
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucketChoice,
          run_commitE_LocalBucketChoice, hcfg_dw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [eraseSt_chall hsync.g_eq]
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
        have hs_acc := syncForgedTop_of_vRecv_accept hsync hr_pos_ep htle hns hvp'
          hcr1 hcP1 hcL1 hb1 hσ1 hft1 htop1 hroot_le hnew_hit (fun hnew => by
            refine ⟨by rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1, fun tn0 htn0 => ?_⟩
            have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2]; exact htn0
            rw [← hnew, ← hr_pos_ep]
            exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2)
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hs_acc⟩)

private theorem leComp_injectEForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncForgedTop prng Δcka qep tL esP sp esL) :
    LeComp (fun rP rL =>
        rP.1.2.abort = true ∨
        (rP.1.1 = rL.1 ∧ (esP.g.win = true → rP.1.2.g.win = true) ∧
          SyncForgedTop prng Δcka qep tL rP.1.2 rP.2 rL.2))
      ((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esP)).run sp)
      (simulateQ lImpl
        ((injectE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hguard_eq : (esP.abort || esP.g.win || (esP.g.inTransit P.other c).isSome ||
      !esP.g.safeInj (2 + Δcka)) =
      (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
        !esL.g.safeInj (2 + Δcka)) := by
    rw [hsync.abortP, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq,
      eraseSt_safeInj hsync.g_eq]
  rw [hguard_eq, hsync.abortL]
  by_cases hguard : (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, id, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
    have hnwinL : esL.g.win = false := by
      simp only [Bool.or_eq_true, not_or] at hguard
      exact Bool.eq_false_iff.mpr hguard.1.1.2
    have hnwinP : esP.g.win = false := by
      rw [eraseSt_win hsync.g_eq]; exact hnwinL
    have hsafe : esL.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have hσ_qep : esL.g.epoch P = qep → sp.σ = (esL.g.st P).root := by
      intro heq_qep
      have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
        have hA := hsync.epoch_le_qep .A
        have hB := hsync.epoch_le_qep .B
        cases P <;> omega
      exact (hsync.root_max P hmax).symm
    have hplP : postLeak tL esP.g = false := by
      rw [postLeak_eraseSt hsync.g_eq]; exact hsync.pl_false
    refine (leComp_vRecvBucketForgedTop cka prng fs Δcka qep tL hplP hsync.pl_false
      hsync.corrRoot_none (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top
      hsync.sp_b (hsync.epoch_le_qep P) hσ_qep).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hcr1, hcP1, hcL1, hb1, hσ1, hft1, htop1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hcr1, hcP1, hcL1, hb1, hσ1,
        hft1, htop1, hroot_le, hnew_hit⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none; subst hP_none hL_none
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, id,
        syncForgedTop_h_step hsync hcr1 hcP1 hcL1 hb1 hσ1 hft1 htop1⟩)
    · dsimp only at hP_some hL_some; subst hP_some hL_some
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      have hs1 := syncForgedTop_h_step hsync hcr1 hcP1 hcL1 hb1 hσ1 hft1 htop1
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, id, hs1⟩)
      · simp only [hqep, ↓reduceIte]
        rw [eraseSt_trivial hsync.g_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq
            rw [heq] at htriv
            have htf := trivial_false_of_safeInj esL.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv
            cases htriv
          have hPRNG_choice : hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1) =
              hkPRNGBucketChoice true cka prng fs Δcka qep tL (qep + 1) := rfl
          have hLoc_choice : hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL =
              hkLocalBucketChoice true cka prng fs Δcka qep tL := rfl
          rw [hPRNG_choice, hLoc_choice]
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketChoice,
            run_commitE_LocalBucketChoice, StateT.run_pure, StateT.run_modify, pure_bind,
            simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, (fun hw => by rw [hnwinP] at hw; cases hw),
            syncForgedTop_of_vRecv_accept hsync rfl htle hns hvp' hcr1 hcP1 hcL1 hb1 hσ1 hft1 htop1
              hroot_le hnew_hit (fun heq => False.elim (hne_e1 heq))⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, fun _ => rfl, syncForgedTop_set_win hs1⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, id, hs1⟩)

private theorem leComp_stepPForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {stL : LocalBucketAuthEState Γ T Sig SS RS M E K I}
    (hwinEp : stP.2 = stL.2)
    (hwin_none : stP.1.g.win = false → stP.2 = none)
    (hsync : SyncForgedTop prng Δcka qep tL stP.1 sp stL.1) :
    LeComp (StepRelForgedTop prng Δcka qep tL)
      (stepPBucketChoice true cka prng fs Δcka qep tL q stP sp)
      (stepLBucketChoice true cka prng fs Δcka qep tL q stL) := by
  rcases stP with ⟨esP, winEpP⟩
  rcases stL with ⟨esL, winEpL⟩
  dsimp only at hwinEp hwin_none hsync
  subst hwinEp
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [stepPBucketChoice, stepLBucketChoice, implPRNGBucketAuthGen, implLocalBucketAuthGen,
      QueryImpl.add_apply, pImpl, lImpl, StateT.run_lift, map_eq_bind_pure_comp]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind _ fun u _ => CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hwin_none, hsync⟩)
  · rcases arg with ⟨P, m, r_coins⟩
    unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq]
    by_cases habw : (false || esL.g.win) = true
    · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hwin_none, hsync⟩)
    · simp only [habw, Bool.false_eq_true, ↓reduceIte]
      have hnwinL : esL.g.win = false := by simpa using habw
      have hnwinP : esP.g.win = false := by rw [eraseSt_win hsync.g_eq]; exact hnwinL
      have hwnone : winEpP = none := hwin_none hnwinP
      subst hwnone
      rcases epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
        ⟨s₁P, s₁L, h1, h2, hs₁_er, hs₁P_st, hs₁L_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
      · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, fun _ => rfl, hsync⟩)
      · obtain ⟨hs₁_qep, he1_qep⟩ := epMgmt_le_qep_auth hsync.epoch_le_qep h2
        have hmem1L : ∀ cur, s₁L.tL = some cur → cur ∈ s₁L.leaks :=
          tL_mem_leaks_epMgmt hsync.tL_mem_leaks h2
        have hs₁L_win : s₁L.win = false := by
          unfold CryptoGames.SM.GameState.epMgmt at h2
          by_cases hs : P.sendsIn (esL.g.epoch P + 1) = true
          · simp only [hs, ↓reduceIte] at h2
            by_cases hq : qep < esL.g.epoch P + 1
            · simp [hq] at h2
            · simp only [hq, ↓reduceIte, Option.some.injEq] at h2
              subst h2; split <;> simp [CryptoGames.SM.GameState.leak, hnwinL]
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h2
            by_cases hq : qep < esL.g.epoch P
            · simp [hq] at h2
            · simp only [hq, ↓reduceIte, Option.some.injEq] at h2
              subst h2; exact hnwinL
        have hs₁P_win : s₁P.win = false := by rw [eraseSt_win hs₁_er]; exact hs₁L_win
        simp only [h1, h2, hs₁P_st, hs₁L_st, StateT.run_lift, simulateQ_bind, StateT.run_bind,
          bind_assoc]
        by_cases hpl1 : postLeak tL s₁L = true
        · refine leComp_dead_left _ _ fun r hr _ _ => Or.inl ?_
          simp only [MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vs, h1'⟩, sp1⟩, hvs_mem, hr2⟩
          cases res_vs with
          | none =>
            simp [StateT.run_set] at hr2; rcases hr2 with rfl
            exact Or.inl rfl
          | some pair =>
            rcases pair with ⟨st', ct⟩
            simp [StateT.run_set] at hr2; rcases hr2 with rfl
            have hvs_props := mem_support_vSend_PRNGBucket true cka prng fs Δcka qep tL (qep + 1)
              hvs_mem st' ct rfl
            rw [(hsync.vp_rel P).id_P, (hsync.vp_rel P).tcur_P] at hvs_props
            have hs₁P_ep : ∀ Q, s₁P.epoch Q = s₁L.epoch Q := fun Q =>
              congrFun (eraseSt_epoch hs₁_er) Q
            have hmem1P : ∀ cur, s₁P.tL = some cur → cur ∈ s₁P.leaks := by
              intro cur hcur
              rw [eraseSt_leaks hs₁_er]
              exact hmem1L cur (by rw [← eraseSt_tL hs₁_er]; exact hcur)
            have hpl1P : postLeak tL s₁P = true := by
              rw [postLeak_eraseSt hs₁_er tL]; exact hpl1
            refine Or.inr (Or.inr ⟨hs₁P_win, rfl, ?_, ?_, ?_⟩)
            · intro Q
              dsimp only [CryptoGames.SM.GameState.record]
              rw [hs₁P_ep, hs₁_ep_fn]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self]
                refine ⟨hvs_props.1, ?_⟩
                by_cases hs : P.sendsIn (esL.g.epoch P + 1) = true
                · simp only [hs, ↓reduceIte, Function.update_self] at hvs_props ⊢
                  exact hvs_props.2.1
                · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hvs_props ⊢
                  exact hvs_props.2.1
              · simp only [Function.update_of_ne hQ, hs₁P_st]
                refine ⟨(hsync.vp_rel Q).id_P, ?_⟩
                by_cases hs : P.sendsIn (esL.g.epoch P + 1) = true
                · simp only [hs, ↓reduceIte, Function.update_of_ne hQ]
                  exact (hsync.vp_rel Q).tcur_P
                · simp only [hs, Bool.false_eq_true, ↓reduceIte]
                  exact (hsync.vp_rel Q).tcur_P
            · intro rec' hrec'
              dsimp only [CryptoGames.SM.GameState.record] at hrec'
              rcases List.mem_cons.mp hrec' with rfl | hmem'
              · dsimp only
                rw [hvs_props.2.2, hs₁P_ep, hs₁_ep_fn]
                by_cases hs : P.sendsIn (esL.g.epoch P + 1) = true <;> simp [hs]
              · have hmemL : rec' ∈ esL.g.trans := by
                  have htrP : s₁P.trans = esL.g.trans := by
                    rw [eraseSt_trans hs₁_er, hs₁_trans]
                  rwa [htrP] at hmem'
                exact (hsync.trans_epoch rec' hmemL).2
            · dsimp only [CryptoGames.SM.GameState.record]
              exact leak_witness_of_postLeak_true hmem1P hpl1P
        · have hpl1_f : postLeak tL s₁L = false := Bool.eq_false_iff.mpr hpl1
          have hheq : P.sendsIn (esL.g.epoch P + 1) = true →
              esL.g.epoch P = esL.g.epoch P.other :=
            epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
          have hσ : P.sendsIn (esL.g.epoch P + 1) = true → postLeak tL s₁L = false →
              sp.σ = (esL.g.st P).root := by
            intro hsends _
            have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
              (max_epoch_eq_of_eq (hheq hsends)).symm
            exact (hsync.root_max P hmax).symm
          have he_lt : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 < qep + 1 := by
            intro hsends; have := he1_qep hsends; omega
          refine (leComp_vSendBucketAuthTop true cka prng fs Δcka qep tL
            (postLeak_eraseSt hs₁_er tL) (hsync.vp_rel P) hsync.fTable_lt hsync.table_top hsync.sp_b
            he_lt (by rw [hsync.corrRoot_none]; simp) hσ
            (by rw [hpl1_f]; simp)).bind ?_
          rintro ⟨⟨res_vsP, hP1⟩, sp1⟩ ⟨res_vsL, hL1⟩ hvs
          rcases hvs with hnone | ⟨vpP', vpL', c, hP_eq, hL_eq, hc_hdr, hvp', hb1,
            hft1, htop1, hsends_props, hns_props⟩
          · dsimp only at hnone; subst hnone
            simp only [pure_bind, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
            simp only [pure_bind, StateT.run_pure, simulateQ_pure]
            refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ?_
            have hs₁_ep : s₁L.epoch P = if P.sendsIn (esL.g.epoch P + 1) then esL.g.epoch P + 1
                else esL.g.epoch P := by
              rw [hs₁_ep_fn]; split <;> simp
            have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
              intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
            have hs₁P_ep : s₁P.epoch = s₁L.epoch := eraseSt_epoch hs₁_er
            have hs₁P_idx : s₁P.idx = s₁L.idx := eraseSt_idx hs₁_er
            rw [hs₁P_ep, hs₁P_idx]
            have hcr1 : hP1.corrRoot = none := by
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · exact ((hsends_props hsends).2.1 hpl1_f).2.1
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                have hhP1 := (hns_props hns).1
                dsimp only at hhP1
                rw [hhP1]; exact hsync.corrRoot_none
            have hc_rel : ∀ t', RelCacheBucketAuth hP1 t' (hP1.cache t') (hL1.cache t') := by
              intro t'
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · obtain ⟨hroot_s, _, _, ⟨T', k, _, hcP_self, hcL_self⟩, hc_other⟩ := hsends_props hsends
                by_cases ht' : t' = esL.g.epoch P + 1
                · subst ht'
                  refine Or.inr ⟨T', vpP'.root, vpL'.root, k, hcP_self, hcL_self, ?_⟩
                  intro s hs_res
                  cases hr_vp : vpP'.root with
                  | none => simp [resolveCorrRoot, hcr1, hr_vp] at hs_res
                  | some r =>
                    simp only [resolveCorrRoot, hr_vp, Option.some.injEq] at hs_res
                    subst hs_res
                    exact hroot_s r hr_vp
                · rw [(hc_other t' ht').1, (hc_other t' ht').2]
                  exact relCacheBucketAuth_of_corrRoot_eq (hsync.corrRoot_none.trans hcr1.symm)
                    (hsync.cache_rel t')
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨hhP1, _, hhL1, _, _, _⟩ := hns_props hns
                dsimp only at hhP1 hhL1
                rw [hhP1, hhL1]
                exact hsync.cache_rel t'
            have hs₁_comp := hs₁_comp_imp hsync.comp_inv
            refine Or.inr ⟨rfl, rfl, fun _ => rfl,
              ⟨rfl, rfl, hcr1, hpl1_f, hmem1L,
                eraseSt_record hs₁_er (2 + Δcka) P vpP' vpL' _ false,
                ?_, hc_rel, hft1, htop1, hb1, hs₁_qep,
                comp_inv_record s₁L (2 + Δcka) P vpL' _ false rfl hs₁_comp,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
            · intro Q
              dsimp only [CryptoGames.SM.GameState.record]
              by_cases hQ : Q = P
              · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
              · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st]
                exact relVPBucketAuth_of_corrRoot_eq (hsync.corrRoot_none.trans hcr1.symm)
                  (hsync.vp_rel Q)
            · intro r hr
              dsimp only [CryptoGames.SM.GameState.record] at hr ⊢
              rcases List.mem_cons.mp hr with rfl | hr'
              · refine ⟨le_rfl, ?_⟩
                dsimp only; rw [hc_hdr, hs₁_ep]
              · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
                refine ⟨?_, h_eq⟩
                by_cases hQ : r.pos.sender = P
                · rw [hQ, hs₁_ep]; rw [hQ] at h_le; split <;> omega
                · rw [hs₁_ep_other _ hQ]; exact h_le
            · intro Q hns_Q hpos_Q Tc hTc
              dsimp only [CryptoGames.SM.GameState.record] at hns_Q hpos_Q hTc ⊢
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · obtain ⟨_, _, _, ⟨T', k, hT', _, hcL_self⟩, hc_other⟩ := hsends_props hsends
                have heq_other := hheq hsends
                by_cases hQ : Q = P
                · subst Q
                  simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte] at hTc ⊢
                  rw [hT'] at hTc; cases hTc
                  exact ⟨vpL'.root, k, hcL_self⟩
                · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
                  have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                    cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other ⊢ <;> omega
                  rw [(hc_other _ hne).2]
                  exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, _, hhL1, _, _, hcur_eq⟩ := hns_props hns
                dsimp only at hhL1
                rw [hhL1]
                by_cases hQ : Q = P
                · subst Q
                  simp only [Function.update_self, hs₁_ep, hns, Bool.false_eq_true, ↓reduceIte] at hpos_Q hTc ⊢
                  rw [hcur_eq] at hTc
                  exact hsync.vp_curCka P hns hpos_Q Tc hTc
                · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
                  exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
            · intro r hr hpos_r Tc hTc
              dsimp only [CryptoGames.SM.GameState.record] at hr ⊢
              rcases List.mem_cons.mp hr with rfl | hr'
              · dsimp only at hpos_r hTc ⊢
                rw [hc_hdr] at hTc; dsimp only at hTc
                by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
                · obtain ⟨_, _, _, ⟨T', k, hT', _, hcL_self⟩, _⟩ := hsends_props hsends
                  rw [hs₁_ep, hsends]; simp only [↓reduceIte]
                  rw [hT'] at hTc; cases hTc
                  exact ⟨vpL'.root, k, hcL_self⟩
                · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                  obtain ⟨_, _, hhL1, _, _, hcur_eq⟩ := hns_props hns
                  dsimp only at hhL1; rw [hhL1]
                  rw [hs₁_ep] at hpos_r ⊢
                  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hpos_r ⊢
                  rw [hcur_eq] at hTc
                  exact hsync.vp_curCka P hns hpos_r Tc hTc
              · have hr_mem : r ∈ esL.g.trans := hs₁_trans ▸ hr'
                by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
                · obtain ⟨_, _, _, _, hc_other⟩ := hsends_props hsends
                  have heq_other := hheq hsends
                  have hr_le := (hsync.trans_epoch r hr_mem).1
                  have hne : r.pos.epoch ≠ esL.g.epoch P + 1 := by
                    cases hS : r.pos.sender <;> cases P <;>
                      simp [CryptoGames.Party.other, hS] at heq_other hr_le ⊢ <;> omega
                  rw [(hc_other _ hne).2]
                  exact hsync.trans_cache r hr_mem hpos_r Tc hTc
                · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                  obtain ⟨_, _, hhL1, _, _, _⟩ := hns_props hns
                  dsimp only at hhL1; rw [hhL1]
                  exact hsync.trans_cache r hr_mem hpos_r Tc hTc
            · intro Q
              dsimp only [CryptoGames.SM.GameState.record]; rw [hs₁_ep_fn]
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · have heq_other := hheq hsends
                simp only [hsends, ↓reduceIte]
                cases Q <;> cases P <;> simp [CryptoGames.Party.other] at heq_other ⊢ <;> omega
              · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
                exact hsync.epoch_le Q
            · intro Q hlt_Q
              dsimp only [CryptoGames.SM.GameState.record] at hlt_Q ⊢; rw [hs₁_ep_fn] at hlt_Q ⊢
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · have heq_other := hheq hsends
                simp only [hsends, ↓reduceIte] at hlt_Q ⊢
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self]; exact hsends
                · cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other hlt_Q <;> omega
              · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hlt_Q ⊢
                exact hsync.epoch_sends Q hlt_Q
            · intro Q hQ_max
              dsimp only [CryptoGames.SM.GameState.record] at hQ_max ⊢; rw [hs₁_ep_fn] at hQ_max
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · have heq_other := hheq hsends
                simp only [hsends, ↓reduceIte] at hQ_max
                rw [max_epoch_update_succ heq_other] at hQ_max
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self]
                  exact (((hsends_props hsends).2.1 hpl1_f).1).symm
                · rw [Function.update_of_ne hQ] at hQ_max
                  cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other hQ_max <;> omega
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, hsp_eq, _, _, hroot_eq, _⟩ := hns_props hns
                dsimp only at hsp_eq
                simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ_max
                rw [hsp_eq]
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self, hroot_eq]; exact hsync.root_max P hQ_max
                · simp only [Function.update_of_ne hQ, hs₁L_st]; exact hsync.root_max Q hQ_max
            · intro Tc σc k hc_max
              dsimp only [CryptoGames.SM.GameState.record] at hc_max ⊢; rw [hs₁_ep_fn] at hc_max
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · have heq_other := hheq hsends
                simp only [hsends, ↓reduceIte] at hc_max
                rw [max_epoch_update_succ heq_other] at hc_max
                obtain ⟨_, hpl_props, _, ⟨T', k', _, _, hcL_self⟩, _⟩ := hsends_props hsends
                have hsp_σ := (hpl_props hpl1_f).1
                dsimp only at hc_max hcL_self
                rw [hcL_self] at hc_max
                injection hc_max with hc_max
                injection hc_max with _ hc_max
                injection hc_max with hσc _
                rw [← hσc, hsp_σ]
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, hsp_eq, hhL1, _, _, _⟩ := hns_props hns
                dsimp only at hsp_eq hhL1
                simp only [hns, Bool.false_eq_true, ↓reduceIte] at hc_max
                rw [hhL1] at hc_max; rw [hsp_eq]
                exact hsync.cache_max Tc σc k hc_max
  · simp only [stepPBucketChoice, stepLBucketChoice, implPRNGBucketAuthGen, implLocalBucketAuthGen,
      QueryImpl.add_apply, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hwin_none, hsync⟩)
  · unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
      simulateQ_bind, pure_bind, bind_assoc]
    change LeComp _
      (((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esP)).run sp) >>= _)
      ((simulateQ lImpl
        ((deliverE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esL)) >>= _)
    refine (leComp_deliverEForgedTop cka prng fs Δcka qep tL arg hsync).bind ?_
    rintro ⟨⟨outP, esP'⟩, sp'⟩ ⟨outL, esL'⟩ (hab | ⟨hout, hwin_eq, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inl hab))
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, fun hw => hwin_none (hwin_eq ▸ hw), hsync'⟩)
  · rcases arg with ⟨P, c⟩
    unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
      simulateQ_bind, pure_bind, bind_assoc]
    change LeComp _
      (((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run esP)).run sp) >>= _)
      ((simulateQ lImpl
        ((injectE (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run esL)) >>= _)
    refine (leComp_injectEForgedTop cka prng fs Δcka qep tL (P, c) hsync).bind ?_
    rintro ⟨⟨outP, esP'⟩, sp'⟩ ⟨outL, esL'⟩ (hab | ⟨hout, hwin_imp, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inl hab))
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      have hwas : esP.g.win = esL.g.win := eraseSt_win hsync.g_eq
      have hnow : esP'.g.win = esL'.g.win := eraseSt_win hsync'.g_eq
      have htcur_eq : (esP.g.st P).tcur = (esL.g.st P).tcur :=
        (hsync.vp_rel P).tcur_P.trans (hsync.vp_rel P).tcur_L.symm
      have hhon_eq : isHonestHdrPRNGBucket esP.h c.1 = isHonestHdrLocalBucket esL.h c.1 :=
        isHonestHdr_eq_of_relCache c.1 (hsync.cache_rel c.1.1)
      rw [hwas, hnow, htcur_eq, hhon_eq]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, ?_, hsync'⟩)
      intro hnwin'
      have hnwinL' : esL'.g.win = false := hnow ▸ hnwin'
      have hnwinP : esP.g.win = false := by
        cases hw0 : esP.g.win
        · rfl
        · have := hwin_imp hw0; rw [hnwin'] at this; cases this
      simp [hnwinL', hwin_none hnwinP]
  · unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq, eraseSt_corrAllowed hsync.g_eq]
    by_cases hguard : (false || esL.g.win || !esL.g.corrAllowed P) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hwin_none, hsync⟩)
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_lift, simulateQ_bind,
        StateT.run_bind, bind_assoc, hkPRNGBucketChoice, hkLocalBucketChoice,
        hooksPRNGBucketAuthForgedHdr, hooksLocalBucketAuthForgedHdr]
      have hnwinL : esL.g.win = false := by
        simp only [Bool.or_eq_true, not_or] at hguard
        exact Bool.eq_false_iff.mpr hguard.1.2
      have hnwinP : esP.g.win = false := by rw [eraseSt_win hsync.g_eq]; exact hnwinL
      have hvp := hsync.vp_rel P
      rw [hvp.tcur_P, hvp.tcur_L, eraseSt_epoch hsync.g_eq]
      by_cases hrev_guard :
          (!(esL.g.epoch P < healEpoch tL) ||
            !(max (esL.g.epoch .A) (esL.g.epoch .B) < healEpoch tL)) = true
      · simp only [hrev_guard, ↓reduceIte, StateT.run_bind, StateT.run_pure, simulateQ_pure,
          pure_bind, StateT.run_set]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inl rfl))
      · simp only [hrev_guard, Bool.false_eq_true, ↓reduceIte]
        have hmax_lt : max (esL.g.epoch .A) (esL.g.epoch .B) < healEpoch tL := by
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hrev_guard
          exact of_decide_eq_true hrev_guard.2
        rcases hrootP : (esP.g.st P).root with _ | σ
        · simp only [StateT.run_bind, StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inl rfl))
        · have hσ_eq : σ = (esL.g.st P).root := by
            refine hvp.root_eq σ ?_
            simp [resolveCorrRoot, hrootP]
          subst σ
          simp only [StateT.run_bind, StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set]
          have her_ac : eraseSt (esP.g.afterCorr P) = eraseSt (esL.g.afterCorr P) :=
            eraseSt_afterCorr hsync.g_eq P
          have hmem_ac_L : ∀ cur, (esL.g.afterCorr P).tL = some cur →
              cur ∈ (esL.g.afterCorr P).leaks :=
            tL_mem_leaks_afterCorr esL.g P
          by_cases hpl_ac : postLeak tL (esL.g.afterCorr P) = true
          · have hpl_ac_P : postLeak tL (esP.g.afterCorr P) = true := by
              rw [postLeak_eraseSt her_ac tL]; exact hpl_ac
            have hmem_ac_P : ∀ cur, (esP.g.afterCorr P).tL = some cur →
                cur ∈ (esP.g.afterCorr P).leaks := by
              intro cur hcur
              rw [eraseSt_leaks her_ac]
              exact hmem_ac_L cur (by rw [← eraseSt_tL her_ac]; exact hcur)
            refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inr (Or.inr
              ⟨hnwinP, hwin_none hnwinP, ?_, ?_,
                leak_witness_of_postLeak_true hmem_ac_P hpl_ac_P⟩)))
            · intro Q
              exact ⟨(hsync.vp_rel Q).id_P,
                (hsync.vp_rel Q).tcur_P.trans (congrFun (eraseSt_epoch hsync.g_eq) Q).symm⟩
            · intro r hr
              exact (hsync.trans_epoch r (eraseSt_trans hsync.g_eq ▸ hr)).2
          · refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨?_, rfl, ?_, ?_⟩)
            · dsimp only
              congr 1
              unfold realParty
              rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq,
                funext hvp.vR_eq]
            · intro _; exact hwin_none hnwinP
            · exact ⟨rfl, rfl, hsync.corrRoot_none,
                Bool.eq_false_iff.mpr hpl_ac,
                hmem_ac_L,
                her_ac,
                hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt, hsync.table_top, hsync.sp_b,
                hsync.epoch_le_qep,
                comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
                  (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv,
                hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
                hsync.epoch_le, hsync.epoch_sends, hsync.root_max, hsync.cache_max⟩

private def runPBucketChoice (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implPRNGBucketAuthGen
      (hkPRNGBucketChoice forgedMode cka prng fs Δcka qep tL (qep + 1))
      Δcka qep fs.maxSkip tL forgedMode) oa).run stP)).run sp
  pure (authOutBucketSimple (2 + Δcka) tL r.1.2)

private def runLBucketChoice (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    (stL : LocalBucketAuthEState Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implLocalBucketAuthGen
      (hkLocalBucketChoice forgedMode cka prng fs Δcka qep tL)
      Δcka qep fs.maxSkip tL forgedMode) oa).run stL)
  pure (authOutBucketSimple (2 + Δcka) tL r.2)

private theorem runPBucketChoice_pure (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (b : Bool)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runPBucketChoice forgedMode cka prng fs Δcka qep tL (pure b) stP sp =
      pure (authOutBucketSimple (2 + Δcka) tL stP) := by
  simp [runPBucketChoice]

private theorem runLBucketChoice_pure (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (b : Bool)
    (stL : LocalBucketAuthEState Γ T Sig SS RS M E K I) :
    runLBucketChoice forgedMode cka prng fs Δcka qep tL (pure b) stL =
      pure (authOutBucketSimple (2 + Δcka) tL stL) := by
  simp [runLBucketChoice]

private theorem runPBucketChoice_query_bind (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecAuth Γ T Sig SS RS M CCoins E).Range q →
      SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runPBucketChoice forgedMode cka prng fs Δcka qep tL (liftM (OracleSpec.query q) >>= k) stP sp =
      stepPBucketChoice forgedMode cka prng fs Δcka qep tL q stP sp >>= fun r =>
        runPBucketChoice forgedMode cka prng fs Δcka qep tL (k r.1.1) r.1.2 r.2 := by
  simp [runPBucketChoice, stepPBucketChoice, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runLBucketChoice_query_bind (forgedMode : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecAuth Γ T Sig SS RS M CCoins E).Range q →
      SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    (stL : LocalBucketAuthEState Γ T Sig SS RS M E K I) :
    runLBucketChoice forgedMode cka prng fs Δcka qep tL (liftM (OracleSpec.query q) >>= k) stL =
      stepLBucketChoice forgedMode cka prng fs Δcka qep tL q stL >>= fun r =>
        runLBucketChoice forgedMode cka prng fs Δcka qep tL (k r.1) r.2 := by
  simp [runLBucketChoice, stepLBucketChoice, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPForgedTop_dead
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    (hd : DeadForged tL stP) :
    𝒟[runPBucketChoice true cka prng fs Δcka qep tL oa stP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stP sp with
  | pure b' =>
    rw [runPBucketChoice_pure, authOutBucketSimple_eq_false_of_deadForged Δcka tL stP hd]
    simp
  | query_bind q k ih =>
    rw [runPBucketChoice_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPForgedTop_dead cka prng fs Δcka qep tL q stP sp hd r hr)

private theorem runPForgedTop_le_runLForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {stL : LocalBucketAuthEState Γ T Sig SS RS M E K I}
    (hwinEp : stP.2 = stL.2)
    (hwin_none : stP.1.g.win = false → stP.2 = none)
    (hsync : SyncForgedTop prng Δcka qep tL stP.1 sp stL.1) :
    𝒟[runPBucketChoice true cka prng fs Δcka qep tL oa stP sp] {true} ≤
      𝒟[runLBucketChoice true cka prng fs Δcka qep tL oa stL] {true} := by
  induction oa using OracleComp.inductionOn generalizing stP sp stL with
  | pure b' =>
    rw [runPBucketChoice_pure, runLBucketChoice_pure]
    rcases stP with ⟨esP, winEpP⟩
    rcases stL with ⟨esL, winEpL⟩
    dsimp only at hwinEp hsync
    subst hwinEp
    have hout : authOutBucketSimple (2 + Δcka) tL (esP, winEpP) =
        authOutBucketSimple (2 + Δcka) tL (esL, winEpP) := by
      cases winEpP with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketSimple]
        rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq,
          eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPBucketChoice_query_bind, runLBucketChoice_query_bind]
    refine leComp_stepPForgedTop cka prng fs Δcka qep tL q hwinEp hwin_none hsync _ _ ?_
    rintro ⟨⟨uP, stP'⟩, sp'⟩ ⟨uL, stL'⟩ (hd | ⟨hu, hwinEp', hwin_none', hsync'⟩)
    · rw [runPForgedTop_dead cka prng fs Δcka qep tL (k uP) hd]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uP hwinEp' hwin_none' hsync'

theorem prng_branch_true_redPRNGAuthBucketHybridForgedHdr_top_le_local_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (_htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CryptoGames.PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (qep + 1) A)] {true} ≤
      𝒟[localAuthBucketForgedHdr cka prng fs lam Δcka qep tL A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (CryptoGames.PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold CryptoGames.PRFPRNG.branch redPRNGAuthBucketHybridForgedHdr runPRNGAuthBucketHybridGen
    localAuthBucketForgedHdr initPRNGBucketAuthHybrid initLocalBucketAuth
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootBucketAuthTop (T := T) prng qep tL 0 false lam none (prng.init kr)
    ({} : PRNGBucketAuthState T Sig K I) { σ := prng.init kr, b := true }
    ({} : LocalBucketAuthState T Sig K I) (Nat.zero_lt_succ qep) rfl (fun _ _ => rfl) rfl
    (by simp) (by simp [resolveCorrRoot]) (fun _ => rfl) (by simp)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL⟩, hL0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨σP, σL', k', hres_eq, hL_eq, hσ_rel, hpl_props, _, hb0, hcP0, hcL0, hft0, htop0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hres_eq hL_eq
    injection hL_eq with hσL_eq hk_eq
    subst hres_eq hσL_eq hk_eq
    obtain ⟨hsp_σ, hcr0, _, _⟩ := hpl_props rfl
    dsimp only at hsp_σ hcr0 hb0 hcP0 hcL0 hft0 htop0
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc]
    let gP0 : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σP
              (fs.initSender kL) (fs.initReceiver kL)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σP
              (fs.initSender kL) (fs.initReceiver kL)).2, b := false }
    let gL0 : Ctx Γ T Sig SS RS M E :=
      { st := fun P => match P with
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σL
              (fs.initSender kL) (fs.initReceiver kL)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σL
              (fs.initSender kL) (fs.initReceiver kL)).2, b := false }
    have hP_ev :
        ((simulateQ (pImpl prng)
          ((simulateQ (implPRNGBucketAuthGen
            (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
            Δcka qep fs.maxSkip tL true) A).run ({ g := gP0, h := hP0 }, none))).run sp0 >>=
          fun x => (simulateQ (pImpl prng) (match x.1.2.2 with
            | none => pure false
            | some tWin => pure (!x.1.2.1.abort && x.1.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.1.2.1.g))).run x.2 >>=
          pure ∘ fun x => x.1) =
        runPBucketChoice true cka prng fs Δcka qep tL A ({ g := gP0, h := hP0 }, none) sp0 := by
      unfold runPBucketChoice hkPRNGBucketChoice
      congr 1
      ext r
      rcases r with ⟨⟨_, _, winEp⟩, _⟩
      cases winEp <;> simp [authOutBucketSimple]
    have hL_ev :
        (simulateQ lImpl
          ((simulateQ (implLocalBucketAuthGen
            (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
            Δcka qep fs.maxSkip tL true) A).run ({ g := gL0, h := hL0 }, none)) >>=
          fun x => simulateQ lImpl (match x.2.2 with
            | none => pure false
            | some tWin => pure (!x.2.1.abort && x.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.2.1.g))) =
        runLBucketChoice true cka prng fs Δcka qep tL A ({ g := gL0, h := hL0 }, none) := by
      unfold runLBucketChoice hkLocalBucketChoice
      congr 1
      ext r
      rcases r with ⟨_, _, winEp⟩
      cases winEp <;> simp [authOutBucketSimple]
    change 𝒟[((simulateQ (pImpl prng)
          ((simulateQ (implPRNGBucketAuthGen
            (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (qep + 1))
            Δcka qep fs.maxSkip tL true) A).run ({ g := gP0, h := hP0 }, none))).run sp0 >>=
          fun x => (simulateQ (pImpl prng) (match x.1.2.2 with
            | none => pure false
            | some tWin => pure (!x.1.2.1.abort && x.1.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.1.2.1.g))).run x.2 >>=
          pure ∘ fun x => x.1)] {true} ≤
        𝒟[(simulateQ lImpl
          ((simulateQ (implLocalBucketAuthGen
            (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
            Δcka qep fs.maxSkip tL true) A).run ({ g := gL0, h := hL0 }, none)) >>=
          fun x => simulateQ lImpl (match x.2.2 with
            | none => pure false
            | some tWin => pure (!x.2.1.abort && x.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.2.1.g)))] {true}
    rw [hP_ev, hL_ev]
    refine runPForgedTop_le_runLForgedTop cka prng fs Δcka qep tL A rfl (fun _ => rfl) ?_
    refine ⟨rfl, rfl, hcr0, rfl, (fun _ h => by cases h), rfl, ?_, ?_, hft0, htop0, hb0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P
      cases P <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
          fun s hs => hσ_rel s (by
            dsimp only [gP0, mkParties] at hs
            cases σP <;> simp [resolveCorrRoot, hcr0] at hs ⊢
            exact hs)⟩
    · intro t'; rw [hcP0, hcL0]; exact Or.inl ⟨rfl, rfl⟩
    · intro P; simp [gL0]
    · intro pos hpos; cases hpos
    · intro r hr; cases hr
    · intro P _ hpos; simp [gL0] at hpos
    · intro r hr; cases hr
    · intro P; simp [gL0]
    · intro P hlt; simp [gL0] at hlt
    · intro P _; cases P <;> exact hsp_σ.symm
    · intro Tc σc k' hc_eq; dsimp only at hc_eq; rw [hcL0] at hc_eq; cases hc_eq

/-! ### Hop 2c (`Main`, `t = qep + 1`, `b = true`) -/

private theorem resolveCorrRoot_idem
    (h : PRNGBucketAuthState T Sig K I) (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h ep (resolveCorrRoot h ep σv) = resolveCorrRoot h ep σv := by
  cases σv with
  | some s => rfl
  | none =>
    unfold resolveCorrRoot
    cases h.corrRoot with
    | none => rfl
    | some pair =>
      rcases pair with ⟨eC, σC⟩
      by_cases heq : (ep == eC) = true <;> simp [heq]

private theorem ltOpt_mono_right (tL : Option ℕ) {a b : ℕ} (hab : a ≤ b) (h : ltOpt tL a = true) :
    ltOpt tL b = true := by
  cases tL with
  | none => rfl
  | some tL0 =>
    simp only [ltOpt, decide_eq_true_eq] at h ⊢
    omega

private theorem postLeak_true_of_leak {St Msg C : Type} {tL : Option ℕ} {s : GameState St Msg C}
    (t : ℕ) (hpl : postLeak tL s = true) :
    postLeak tL (s.leak t) = true := by
  unfold postLeak at hpl ⊢
  dsimp only [CryptoGames.SM.GameState.leak]
  cases htL : s.tL with
  | none => simp [htL] at hpl
  | some cur =>
    rw [htL] at hpl
    dsimp only [maxOpt]
    exact ltOpt_mono_right tL (Nat.le_max_left cur t) hpl

private theorem postLeak_true_of_epMgmt {St Msg C : Type} {tL : Option ℕ} {s s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hpl : postLeak tL s = true)
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    postLeak tL s₁ = true := by
  unfold CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (s.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hbl : (bad && !s.safeCh Δ P) = true
      · simp only [hbl, ↓reduceIte]
        exact postLeak_true_of_leak _ hpl
      · simp only [hbl, Bool.false_eq_true, ↓reduceIte]
        exact hpl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact hpl

private theorem postLeak_epMgmt_of_sendsIn_false {St Msg C : Type} {tL : Option ℕ}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hns : P.sendsIn (s.epoch P + 1) = false)
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    postLeak tL s₁ = postLeak tL s := by
  unfold CryptoGames.SM.GameState.epMgmt at hep
  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  by_cases hq : qep < s.epoch P
  · simp [hq] at hep
  · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
    subst hep; rfl

private theorem postLeak_true_of_afterCorr_pl {St Msg C : Type} {tL : Option ℕ}
    {s : GameState St Msg C} (P : Party) (hpl : postLeak tL s = true) :
    postLeak tL (s.afterCorr P) = true :=
  postLeak_true_of_leak _ hpl

private theorem postLeak_true_of_afterCorr_ge_tH {St Msg C : Type} {tL : Option ℕ}
    {s : GameState St Msg C} (P : Party)
    (hge : healEpoch tL ≤ max (s.epoch .A) (s.epoch .B)) :
    postLeak tL (s.afterCorr P) = true := by
  unfold CryptoGames.SM.GameState.afterCorr postLeak CryptoGames.SM.GameState.leak
  dsimp only
  cases tL with
  | none =>
    cases s.tL <;> rfl
  | some tL0 =>
    dsimp only [healEpoch] at hge
    cases s.tL with
    | none =>
      dsimp only [maxOpt, ltOpt]
      simp only [decide_eq_true_eq]
      omega
    | some cur =>
      dsimp only [maxOpt, ltOpt]
      simp only [decide_eq_true_eq]
      omega

private theorem relVP_of_set_corrRoot
    {hP0 hP1 : PRNGBucketAuthState T Sig K I} {eC ep : ℕ} {σC : Sig} {P : Party}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    (hcr1 : hP1.corrRoot = some (eC, σC))
    (hvp : RelVPBucketAuth hP0 ep P vpP vpL)
    (heC : ep = eC → vpL.root = σC) :
    RelVPBucketAuth hP1 ep P vpP vpL := by
  refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq,
    hvp.vS_eq, hvp.vR_eq, ?_⟩
  intro s hs
  cases hr : vpP.root with
  | some s' =>
    rw [hr] at hs
    simp only [resolveCorrRoot, Option.some.injEq] at hs
    subst hs
    exact hvp.root_eq s' (by simp [resolveCorrRoot, hr])
  | none =>
    rw [hr] at hs
    simp only [resolveCorrRoot, hcr1] at hs
    by_cases heq : (ep == eC) = true
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      exact (heC (beq_iff_eq.mp heq)).symm
    · simp [heq] at hs

private theorem relCache_of_set_corrRoot
    {hP0 hP1 : PRNGBucketAuthState T Sig K I} {eC ep : ℕ} {σC : Sig}
    {cP : Option (T × Option Sig × K)} {cL : Option (T × Sig × K)}
    (hcr1 : hP1.corrRoot = some (eC, σC))
    (hc : RelCacheBucketAuth hP0 ep cP cL)
    (heC : ep = eC → ∀ Tc σL k, cL = some (Tc, σL, k) → σL = σC) :
    RelCacheBucketAuth hP1 ep cP cL := by
  rcases hc with ⟨hP_n, hL_n⟩ | ⟨Tc, σP, σL, k, hP_s, hL_s, hres⟩
  · exact Or.inl ⟨hP_n, hL_n⟩
  · refine Or.inr ⟨Tc, σP, σL, k, hP_s, hL_s, ?_⟩
    intro s hs
    cases hr : σP with
    | some s' =>
      rw [hr] at hs
      simp only [resolveCorrRoot, Option.some.injEq] at hs
      subst hs
      exact hres s' (by simp [resolveCorrRoot, hr])
    | none =>
      rw [hr] at hs
      simp only [resolveCorrRoot, hcr1] at hs
      by_cases heq : (ep == eC) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        exact (heC (beq_iff_eq.mp heq) Tc σL k hL_s).symm
      · simp [heq] at hs

private theorem leComp_startRecvBucketMainTop
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {P : Party} {t0 : ℕ} {γ0 : Γ} {σv0 : Option Sig} {σ0 : Sig} {tn0 : T}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hcache : RelCacheBucketAuth hP t0 (hP.cache t0) (hL.cache t0)) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        (rP.1.1 = some none ∧ rL.1 = some none ∧
          rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
        ∃ γ' σP' σL' rs0 σP_c kc,
          rP.1.1 = some (some (γ', σP', rs0)) ∧
          rL.1 = some (some (γ', σL', rs0)) ∧
          rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL ∧
          hP.cache t0 = some (tn0, σP_c, kc) ∧
          hL.cache t0 = some (tn0, σL', kc) ∧
          σP' = resolveCorrRoot hP t0 σP_c ∧
          (∀ s, resolveCorrRoot hP t0 σP' = some s → s = σL'))
      ((simulateQ (pImpl prng)
        (((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1)).startRecv
          gP P t0 γ0 σv0 tn0).run hP)).run sp)
      (simulateQ lImpl
        (((hooksLocalBucketAuthMain cka prng fs Δcka qep tL).startRecv
          gL P t0 γ0 σ0 tn0).run hL)) := by
  unfold hooksPRNGBucketAuthMain hooksLocalBucketAuthMain
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache with ⟨hcP_none, hcL_none⟩ | ⟨Tc, σP_c, σL_c, kc, hcP_some, hcL_some, hσc_rel⟩
  · rw [hcP_none, hcL_none]
    dsimp only
    by_cases hg : (!(decide (qep + 1 < t0)) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
        (tL.isSome && decide (t0 = healEpoch tL))) = true
    · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl rfl)
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · simp only [hcP_some, hcL_some]
    by_cases hTeq : Tc = tn0
    · subst hTeq
      simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 Tc).1,
        resolveCorrRoot hP t0 σP_c, σL_c, fs.initReceiver kc, σP_c, kc,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩))
      intro s hs
      rw [resolveCorrRoot_idem] at hs
      exact hσc_rel s hs
    · simp only [hTeq, ↓reduceIte]
      by_cases hg : (!(decide (qep + 1 < t0)) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
          (tL.isSome && decide (t0 = healEpoch tL))) = true
      · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl rfl)
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))

private def VRecvRelBucketMainTop (e : ℕ) (P : Party) (c : Header T × E)
    (vpP : VP Γ T (Option Sig) SS RS) (vpL : VP Γ T Sig SS RS)
    (hP : PRNGBucketAuthState T Sig K I) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hL : LocalBucketAuthState T Sig K I)
    (rP : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGBucketAuthState T Sig K I) ×
      CryptoGames.PRFPRNG.GameState Sig I K)
    (rL : Option (Option (VP Γ T Sig SS RS × ℕ × ℕ × M)) × LocalBucketAuthState T Sig K I) : Prop :=
  let t0 := c.1.1
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧
    rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
  ∃ vpP' vpL' i' m',
    rP.1.1 = some (some (vpP', t0, i', m')) ∧
    rL.1 = some (some (vpL', t0, i', m')) ∧
    t0 ≤ e + 1 ∧
    P.sendsIn t0 = false ∧
    RelVPBucketAuth hP (max e t0) P vpP' vpL' ∧
    rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL ∧
    (t0 ≤ e → vpP'.root = vpP.root ∧ vpL'.root = vpL.root ∧ vpL'.curCkaMsg = vpL.curCkaMsg) ∧
    (t0 = e + 1 → ∃ tn0 σP_c kc,
      c.1.2 = some tn0 ∧
      hP.cache (e + 1) = some (tn0, σP_c, kc) ∧
      hL.cache (e + 1) = some (tn0, vpL'.root, kc) ∧
      vpP'.root = resolveCorrRoot hP (e + 1) σP_c)

private theorem leComp_vRecvBucketMainTop
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {e : ℕ} {P : Party}
    {gP : GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : GameState (VP Γ T Sig SS RS) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS} {vpL : VP Γ T Sig SS RS}
    {c : Header T × E} {rec : Option (Record M (Header T × E))}
    {hP : PRNGBucketAuthState T Sig K I} {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL : LocalBucketAuthState T Sig K I}
    (hvp : RelVPBucketAuth hP e P vpP vpL)
    (hcache : ∀ t', RelCacheBucketAuth hP t' (hP.cache t') (hL.cache t')) :
    LeComp (VRecvRelBucketMainTop e P c vpP vpL hP sp hL)
      ((simulateQ (pImpl prng)
        ((vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
          gP P vpP c rec).run hP)).run sp)
      (simulateQ lImpl
        ((vRecv (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          gL P vpL c rec).run hL)) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hguard : (P.sendsIn c.1.1 || decide (e + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    have hns : P.sendsIn c.1.1 = false := Bool.eq_false_iff.mpr hguard.1
    have htle : c.1.1 ≤ e + 1 := Nat.le_of_not_lt hguard.2
    by_cases hnew : c.1.1 = e + 1
    · simp only [hnew, ↓reduceIte]
      cases hTn : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
      | some Tn =>
        rw [hvp.γ_eq]
        simp only [StateT.run_bind, simulateQ_bind]
        refine (leComp_startRecvBucketMainTop cka prng fs Δcka qep tL (hcache (e + 1))).bind ?_
        rintro ⟨⟨resP, hP1⟩, sp1⟩ ⟨resL, hL1⟩ hsr
        rcases hsr with hnone | ⟨hP_none, hL_none, hhP1, hsp1, hhL1⟩ |
          ⟨γ', σP', σL', rs0, σP_c, kc, hP_some, hL_some, hhP1, hsp1, hhL1,
            hcP_hit, hcL_hit, hσP'_eq, hσ_rel⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none hhP1 hsp1 hhL1
          subst hP_none hL_none hhP1 hsp1 hhL1
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
        · dsimp only at hP_some hL_some hhP1 hsp1 hhL1
          subst hP_some hL_some hhP1 hsp1 hhL1
          simp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
            hooksLocalBucketAuthMain, hooksLocalBucketAuth, pure_bind,
            Function.update_self]
          cases hfs : fs.receive rs0 c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]
            refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ?_
            dsimp only [VRecvRelBucketMainTop]
            rw [hnew]
            refine Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, Nat.le_refl _, hnew ▸ hns, ?_,
              rfl, rfl, rfl, fun hle => by omega,
              fun _ => ⟨Tn, σP_c, kc, hTn, hcP_hit, ?_, ?_⟩⟩)
            · have hmax : max e (e + 1) = e + 1 := by omega
              rw [hmax]
              refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_, ?_⟩
              · intro t'
                by_cases ht1 : t' = e + 1
                · subst ht1; simp
                · simp [ht1, hvp.vR_eq t']
              · intro s hs
                exact hσ_rel s hs
            · exact hcL_hit
            · exact hσP'_eq
    · simp only [hnew, ↓reduceIte, pure_bind]
      have htle_e : c.1.1 ≤ e := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max e c.1.1 = e := Nat.max_eq_left htle_e
      rw [hvp.vR_eq c.1.1]
      cases hvR : vpL.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
      | some rs =>
        simp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
          hooksLocalBucketAuthMain, hooksLocalBucketAuth, pure_bind]
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun heq => False.elim (hnew heq)⟩))
          rw [hmax]
          refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq,
            hvp.vS_eq, ?_, hvp.root_eq⟩
          intro t'
          by_cases ht1 : t' = c.1.1
          · subst ht1; simp
          · simp [ht1, hvp.vR_eq t']

private structure SyncMainTop
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)) : Prop where
  abortP : esP.abort = false
  abortL : esL.abort = false
  g_eq : eraseSt esP.g = eraseSt esL.g
  vp_rel : ∀ P, RelVPBucketAuth esP.h (esL.g.epoch P) P (esP.g.st P) (esL.g.st P)
  cache_rel : ∀ t', RelCacheBucketAuth esP.h t' (esP.h.cache t') (esL.h.cache t')
  fTable_lt : ∀ t0, t0 < qep + 1 → esP.h.fTable t0 = esL.h.fTable t0
  table_top : sp.table = esL.h.fTable (qep + 1)
  sp_b : sp.b = true
  epoch_le_qep : ∀ P, esL.g.epoch P ≤ qep
  comp_inv : ∀ pos ∈ esL.g.comp, healedBy esL.g.tL (2 + Δcka) pos.epoch = false
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
  cache_zero : esL.h.cache 0 = none
  cache_lt_max : ∀ t', max (esL.g.epoch .A) (esL.g.epoch .B) < t' → esL.h.cache t' = none
  vp_cache_root : ∀ P, 0 < esL.g.epoch P →
    ∃ Tc σP k, esP.h.cache (esL.g.epoch P) = some (Tc, σP, k) ∧
      esL.h.cache (esL.g.epoch P) = some (Tc, (esL.g.st P).root, k) ∧
      (∀ s, σP = some s → (esP.g.st P).root = some s) ∧
      (esP.h.corrRoot = none → (esP.g.st P).root = σP)
  vp_zero_root : ∀ P Q, esL.g.epoch P = 0 → esL.g.epoch Q = 0 →
    (esL.g.st P).root = (esL.g.st Q).root
  zero_some_lt_tH : ∀ P, esP.h.corrRoot = none → esL.g.epoch P = 0 →
    (esP.g.st P).root.isSome = true → 0 < healEpoch tL
  cache_some_pl : ∀ e0, healEpoch tL ≤ e0 →
    ∀ Tc σs k, esP.h.cache e0 = some (Tc, some σs, k) → postLeak tL esL.g = true
  cache_some_mono : ∀ e0 t', healEpoch tL ≤ e0 → e0 ≤ t' →
    (∃ Tc0 σs0 k0, esP.h.cache e0 = some (Tc0, some σs0, k0)) →
    ∀ Tc σP k, esP.h.cache t' = some (Tc, σP, k) → σP.isSome = true
  corrRoot_bound : ∀ eC σC, esP.h.corrRoot = some (eC, σC) →
    postLeak tL esL.g = true ∧ eC ≤ max (esL.g.epoch .A) (esL.g.epoch .B) ∧
      (∀ t', eC < t' → ∀ Tc σP k, esP.h.cache t' = some (Tc, σP, k) → σP.isSome = true)
  root_max_of_none : ∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) →
    (postLeak tL esL.g = false ∨ (esP.h.corrRoot = none ∧ (esP.g.st P).root = none)) →
    (esL.g.st P).root = sp.σ

private theorem syncMainTop_corrRoot_pl
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    (hcr : esP.h.corrRoot.isSome = true) :
    postLeak tL esL.g = true := by
  cases h : esP.h.corrRoot with
  | none => rw [h] at hcr; simp at hcr
  | some pair => exact (hsync.corrRoot_bound pair.1 pair.2 h).1

private theorem syncMainTop_max_unres
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    {P : Party} (hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B))
    (hunres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = none) :
    esP.h.corrRoot = none ∧ (esP.g.st P).root = none ∧ (esL.g.st P).root = sp.σ := by
  have hvp_none : (esP.g.st P).root = none := by
    cases hr : (esP.g.st P).root with
    | none => rfl
    | some s => rw [hr] at hunres; simp [resolveCorrRoot] at hunres
  have hcr_none : esP.h.corrRoot = none := by
    cases hcr : esP.h.corrRoot with
    | none => rfl
    | some pair =>
      rcases pair with ⟨eC, σC⟩
      obtain ⟨_, heC_le, hgt_some⟩ := hsync.corrRoot_bound eC σC hcr
      rw [← hmax] at heC_le
      by_cases heq : esL.g.epoch P = eC
      · rw [hvp_none, heq] at hunres
        simp [resolveCorrRoot, hcr] at hunres
      · have hgt : eC < esL.g.epoch P := Nat.lt_of_le_of_ne heC_le (Ne.symm heq)
        obtain ⟨Tc, σP, k, hcP, _, hs_imp, _⟩ := hsync.vp_cache_root P (by omega)
        have his : σP.isSome = true := hgt_some (esL.g.epoch P) hgt Tc σP k hcP
        cases σP with
        | none => simp at his
        | some s =>
          have := hs_imp s rfl
          rw [hvp_none] at this; cases this
  exact ⟨hcr_none, hvp_none, hsync.root_max_of_none P hmax (Or.inr ⟨hcr_none, hvp_none⟩)⟩

private theorem syncMainTop_set_win [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL) :
    SyncMainTop prng Δcka qep tL
      { esP with g := { esP.g with win := true } } sp
      { esL with g := { esL.g with win := true } } := by
  have hg := hsync.g_eq
  refine ⟨hsync.abortP, hsync.abortL, ?_, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
    hsync.table_top, hsync.sp_b, hsync.epoch_le_qep, hsync.comp_inv, hsync.trans_epoch,
    hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
    hsync.cache_zero, hsync.cache_lt_max, hsync.vp_cache_root, hsync.vp_zero_root,
    hsync.zero_some_lt_tH, hsync.cache_some_pl, hsync.cache_some_mono,
    hsync.corrRoot_bound, hsync.root_max_of_none⟩
  simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
    eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
    eraseSt_leaks hg, eraseSt_corrs hg]

private theorem syncMainTop_of_vRecv_accept [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    {P : Party} {c : Header T × E}
    {vpP' : VP Γ T (Option Sig) SS RS} {vpL' : VP Γ T Sig SS RS} {pos : Pos}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esL.g.epoch P + 1)
    (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPBucketAuth esP.h (max (esL.g.epoch P) c.1.1) P vpP' vpL')
    (hroot_le : c.1.1 ≤ esL.g.epoch P →
      vpP'.root = (esP.g.st P).root ∧ vpL'.root = (esL.g.st P).root ∧
        vpL'.curCkaMsg = (esL.g.st P).curCkaMsg)
    (hnew_hit : c.1.1 = esL.g.epoch P + 1 →
      ∃ tn0 σP_c kc,
        c.1.2 = some tn0 ∧
        esP.h.cache (esL.g.epoch P + 1) = some (tn0, σP_c, kc) ∧
        esL.h.cache (esL.g.epoch P + 1) = some (tn0, vpL'.root, kc) ∧
        vpP'.root = resolveCorrRoot esP.h (esL.g.epoch P + 1) σP_c) :
    SyncMainTop prng Δcka qep tL
      { esP with g := esP.g.accept P vpP' pos } sp
      { esL with g := esL.g.accept P vpL' pos } := by
  have hacc_ep : (esL.g.accept P vpL' pos).epoch =
      Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) := by
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
    rw [hpos_ep]
  have hnew_le_other : c.1.1 = esL.g.epoch P + 1 → c.1.1 ≤ esL.g.epoch P.other := by
    intro hnew
    obtain ⟨tn0, _, kc, _, _, hcL_hit, _⟩ := hnew_hit hnew
    have hnot_gt : ¬ (max (esL.g.epoch .A) (esL.g.epoch .B) < esL.g.epoch P + 1) := by
      intro hgt
      have hnone := hsync.cache_lt_max (esL.g.epoch P + 1) hgt
      rw [hnone] at hcL_hit; cases hcL_hit
    cases P <;> simp [CryptoGames.Party.other] at hnew hnot_gt ⊢ <;> omega
  have hmax_acc_eq :
      max ((esL.g.accept P vpL' pos).epoch .A) ((esL.g.accept P vpL' pos).epoch .B) =
        max (esL.g.epoch .A) (esL.g.epoch .B) := by
    rw [hacc_ep]
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hle_o := hnew_le_other hnew
      cases P <;> simp [CryptoGames.Party.other, hnew] at hle_o ⊢ <;> omega
    · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
      rw [hm, Function.update_eq_self]
  refine ⟨hsync.abortP, hsync.abortL, eraseSt_accept hsync.g_eq P vpP' vpL' pos,
    ?_, hsync.cache_rel, hsync.fTable_lt, hsync.table_top, hsync.sp_b, ?_,
    comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv,
    ?_, ?_, ?_, ?_, ?_, hsync.cache_zero, ?_, ?_, ?_, ?_, ?_, hsync.cache_some_mono, ?_, ?_⟩
  · intro Q
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self, hpos_ep]; exact hvp'
    · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
  · intro Q
    rw [hacc_ep]
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self]
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · have := hnew_le_other hnew
        have := hsync.epoch_le_qep P.other
        omega
      · have : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have := hsync.epoch_le_qep P
        omega
    · simp only [Function.update_of_ne hQ]
      exact hsync.epoch_le_qep Q
  · intro r hr
    simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hr
    obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r hr.1
    refine ⟨?_, h_eq⟩
    rw [hacc_ep]
    by_cases hQ : r.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h_le; omega
    · rw [Function.update_of_ne hQ]; exact h_le
  · intro Q hns_Q hpos_Q Tc hTc
    rw [hacc_ep] at hns_Q hpos_Q ⊢
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete] at hTc
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self] at hns_Q hpos_Q hTc ⊢
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P + 1 := by omega
        rw [hm, ← hnew] at hns_Q
        have hs_sends : P.sendsIn (c.1.1 + 1) = true := sendsIn_succ_true_of_false_auth P c.1.1 hns
        rw [hs_sends] at hns_Q; cases hns_Q
      · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
        rw [hm] at hns_Q hpos_Q ⊢
        rw [(hroot_le hle_e).2.2] at hTc
        exact hsync.vp_curCka P hns_Q hpos_Q Tc hTc
    · simp only [Function.update_of_ne hQ] at hns_Q hpos_Q hTc ⊢
      exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
  · intro r hr hpos_r Tc hTc
    simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete, List.mem_filter] at hr
    exact hsync.trans_cache r hr.1 hpos_r Tc hTc
  · intro Q
    rw [hacc_ep]
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hle_o := hnew_le_other hnew
      have ho_le := hsync.epoch_le P.other
      cases Q <;> cases P <;> simp [CryptoGames.Party.other, hnew] at hle_o ho_le ⊢ <;> omega
    · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
      rw [hm, Function.update_eq_self]
      exact hsync.epoch_le Q
  · intro Q hlt_Q
    rw [hacc_ep] at hlt_Q ⊢
    by_cases hnew : c.1.1 = esL.g.epoch P + 1
    · have hle_o := hnew_le_other hnew
      by_cases hQ : Q = P
      · subst Q; cases P <;> simp [CryptoGames.Party.other, hnew] at hle_o hlt_Q <;> omega
      · cases Q <;> cases P <;> simp [CryptoGames.Party.other, hnew] at hQ hle_o hlt_Q ⊢
        · exact hsync.epoch_sends .A (by simp [CryptoGames.Party.other]; omega)
        · exact hsync.epoch_sends .B (by simp [CryptoGames.Party.other]; omega)
    · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
      rw [hm, Function.update_eq_self] at hlt_Q ⊢
      exact hsync.epoch_sends Q hlt_Q
  · intro t' hgt
    rw [hmax_acc_eq] at hgt
    exact hsync.cache_lt_max t' hgt
  · intro Q hpos_Q
    rw [hacc_ep] at hpos_Q ⊢
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self] at hpos_Q ⊢
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · obtain ⟨tn0, σP_c, kc, _, hcP_hit, hcL_hit, hvpP_eq⟩ := hnew_hit hnew
        have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P + 1 := by omega
        rw [hm]
        refine ⟨tn0, σP_c, kc, hcP_hit, hcL_hit, ?_, ?_⟩
        · intro s hs; rw [hvpP_eq, hs]; rfl
        · intro hcr_none; rw [hvpP_eq]; cases σP_c <;> simp [resolveCorrRoot, hcr_none]
      · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
        rw [hm] at hpos_Q ⊢
        rw [(hroot_le hle_e).1, (hroot_le hle_e).2.1]
        exact hsync.vp_cache_root P hpos_Q
    · simp only [Function.update_of_ne hQ] at hpos_Q ⊢
      exact hsync.vp_cache_root Q hpos_Q
  · intro Q1 Q2 h1 h2
    rw [hacc_ep] at h1 h2
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete]
    have hroot_at_zero : ∀ Q, Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) Q = 0 →
        esL.g.epoch Q = 0 ∧ (Function.update esL.g.st P vpL' Q).root = (esL.g.st Q).root := by
      intro Q hQ0
      by_cases hQP : Q = P
      · subst Q
        simp only [Function.update_self] at hQ0 ⊢
        have he0 : esL.g.epoch P = 0 := by omega
        have hc0 : c.1.1 = 0 := by omega
        exact ⟨he0, (hroot_le (by omega)).2.1⟩
      · rw [Function.update_of_ne hQP] at hQ0
        rw [Function.update_of_ne hQP]
        exact ⟨hQ0, rfl⟩
    obtain ⟨he1, hr1⟩ := hroot_at_zero Q1 h1
    obtain ⟨he2, hr2⟩ := hroot_at_zero Q2 h2
    rw [hr1, hr2]
    exact hsync.vp_zero_root Q1 Q2 he1 he2
  · intro Q hcr_none hQ0 his
    rw [hacc_ep] at hQ0
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete] at his
    by_cases hQP : Q = P
    · subst Q
      simp only [Function.update_self] at hQ0 his
      have he0 : esL.g.epoch P = 0 := by omega
      have hc0 : c.1.1 = 0 := by omega
      rw [(hroot_le (by omega)).1] at his
      exact hsync.zero_some_lt_tH P hcr_none he0 his
    · simp only [Function.update_of_ne hQP] at hQ0 his
      exact hsync.zero_some_lt_tH Q hcr_none hQ0 his
  · intro e0 he0 Tc σs k hc
    exact hsync.cache_some_pl e0 he0 Tc σs k hc
  · intro eC σC hcr
    rw [hmax_acc_eq]
    exact hsync.corrRoot_bound eC σC hcr
  · intro Q hQ_max hcond
    rw [hmax_acc_eq, hacc_ep] at hQ_max
    dsimp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete] at hcond ⊢
    by_cases hQP : Q = P
    · subst Q
      simp only [Function.update_self] at hQ_max hcond ⊢
      by_cases hnew : c.1.1 = esL.g.epoch P + 1
      · obtain ⟨tn0, σP_c, kc, _, hcP_hit, hcL_hit, hvpP_eq⟩ := hnew_hit hnew
        have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P + 1 := by omega
        rw [hm] at hQ_max
        have hle_o := hnew_le_other hnew
        have ho_le_max : esL.g.epoch P.other ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
          cases P <;> simp [CryptoGames.Party.other]
        have ho_eq : esL.g.epoch P.other = esL.g.epoch P + 1 := by omega
        have ho_max : esL.g.epoch P.other = max (esL.g.epoch .A) (esL.g.epoch .B) := by omega
        obtain ⟨Tc_o, σP_o, k_o, hcP_o, hcL_o, _, hcr_o⟩ :=
          hsync.vp_cache_root P.other (by omega)
        rw [ho_eq] at hcP_o hcL_o
        have hL_eq_o : vpL'.root = (esL.g.st P.other).root := by
          rw [hcL_hit] at hcL_o
          exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hcL_o)).2).1
        rw [hL_eq_o]
        rcases hcond with hpl_f | ⟨hcr_none, hvpP_none⟩
        · exact hsync.root_max_of_none P.other ho_max (Or.inl hpl_f)
        · have hσP_c_none : σP_c = none := by
            rw [hvpP_eq] at hvpP_none
            cases σP_c <;> simp [resolveCorrRoot, hcr_none] at hvpP_none ⊢
          have hσP_o_eq : σP_o = σP_c := by
            rw [hcP_hit] at hcP_o
            exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hcP_o)).2).1.symm
          have ho_root_none : (esP.g.st P.other).root = none := by
            rw [hcr_o hcr_none, hσP_o_eq, hσP_c_none]
          exact hsync.root_max_of_none P.other ho_max (Or.inr ⟨hcr_none, ho_root_none⟩)
      · have hle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
        have hm : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left hle_e
        rw [hm] at hQ_max
        rw [(hroot_le hle_e).2.1]
        rw [(hroot_le hle_e).1] at hcond
        exact hsync.root_max_of_none P hQ_max hcond
    · simp only [Function.update_of_ne hQP] at hQ_max hcond ⊢
      exact hsync.root_max_of_none Q hQ_max hcond

private theorem syncMainTop_heC_vp
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    (P Q : Party) (heq : esL.g.epoch Q = esL.g.epoch P) :
    (esL.g.st Q).root = (esL.g.st P).root := by
  by_cases h0 : esL.g.epoch P = 0
  · exact hsync.vp_zero_root Q P (heq.trans h0) h0
  · have hposP : 0 < esL.g.epoch P := Nat.pos_of_ne_zero h0
    have hposQ : 0 < esL.g.epoch Q := by omega
    obtain ⟨_, _, _, _, hcLP, _, _⟩ := hsync.vp_cache_root P hposP
    obtain ⟨_, _, _, _, hcLQ, _, _⟩ := hsync.vp_cache_root Q hposQ
    rw [heq, hcLP] at hcLQ
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hcLQ)).2).1.symm

private theorem syncMainTop_heC_cache
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    (P : Party) {ep : ℕ} (hep : ep = esL.g.epoch P) :
    ∀ Tc σL k, esL.h.cache ep = some (Tc, σL, k) → σL = (esL.g.st P).root := by
  subst hep
  intro Tc σL k hcL
  by_cases h0 : esL.g.epoch P = 0
  · rw [h0, hsync.cache_zero] at hcL; cases hcL
  · obtain ⟨_, _, _, _, hcLP, _, _⟩ := hsync.vp_cache_root P (Nat.pos_of_ne_zero h0)
    rw [hcLP] at hcL
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hcL)).2).1.symm

private theorem syncMainTop_cacheP_none
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL)
    {t' : ℕ} (hcL_none : esL.h.cache t' = none) :
    esP.h.cache t' = none := by
  rcases hsync.cache_rel t' with ⟨hP, _⟩ | ⟨_, _, _, _, _, hL, _⟩
  · exact hP
  · rw [hcL_none] at hL; cases hL

private theorem leComp_deliverEMainTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL) :
    LeComp (fun rP rL =>
        rP.1.2.abort = true ∨
        (rP.1.1 = rL.1 ∧ SyncMainTop prng Δcka qep tL rP.1.2 rP.2 rL.2))
      ((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esP)).run sp)
      (simulateQ lImpl
        ((deliverE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold CryptoGames.SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hcfg_dw : (bucketAuthCfg (M := M) Δcka tL).deliverWin = false := rfl
      simp only [StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecvBucketMainTop cka prng fs Δcka qep tL
        (hsync.vp_rel P) hsync.cache_rel).bind ?_
      rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
      rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hsp1, hhL1⟩ |
        ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hsp1, hhL1,
          hroot_le, hnew_hit⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_none hL_none hhP1 hsp1 hhL1
        subst hP_none hL_none hhP1 hsp1 hhL1
        simp only [hcfg_dw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, pure_bind]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · dsimp only at hP_some hL_some hhP1 hsp1 hhL1
        subst hP_some hL_some hhP1 hsp1 hhL1
        have hPRNG_choice : hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1) =
            hkPRNGBucketChoice false cka prng fs Δcka qep tL (qep + 1) := rfl
        have hLoc_choice : hooksLocalBucketAuthMain cka prng fs Δcka qep tL =
            hkLocalBucketChoice false cka prng fs Δcka qep tL := rfl
        rw [hPRNG_choice, hLoc_choice]
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucketChoice,
          run_commitE_LocalBucketChoice, hcfg_dw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [eraseSt_chall hsync.g_eq]
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
        have hs_acc := syncMainTop_of_vRecv_accept hsync hr_pos_ep htle hns hvp'
          hroot_le hnew_hit
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs_acc⟩)

private theorem leComp_injectEMainTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I)}
    (hsync : SyncMainTop prng Δcka qep tL esP sp esL) :
    LeComp (fun rP rL =>
        rP.1.2.abort = true ∨
        (rP.1.1 = rL.1 ∧ SyncMainTop prng Δcka qep tL rP.1.2 rP.2 rL.2))
      ((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esP)).run sp)
      (simulateQ lImpl
        ((injectE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hguard_eq : (esP.abort || esP.g.win || (esP.g.inTransit P.other c).isSome ||
      !esP.g.safeInj (2 + Δcka)) =
      (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
        !esL.g.safeInj (2 + Δcka)) := by
    rw [hsync.abortP, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq,
      eraseSt_safeInj hsync.g_eq]
  rw [hguard_eq, hsync.abortL]
  by_cases hguard : (false || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esL.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    refine (leComp_vRecvBucketMainTop cka prng fs Δcka qep tL
      (hsync.vp_rel P) hsync.cache_rel).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hsp1, hhL1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hsp1, hhL1,
        hroot_le, hnew_hit⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none hhP1 hsp1 hhL1
      subst hP_none hL_none hhP1 hsp1 hhL1
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · dsimp only at hP_some hL_some hhP1 hsp1 hhL1
      subst hP_some hL_some hhP1 hsp1 hhL1
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hqep, ↓reduceIte]
        rw [eraseSt_trivial hsync.g_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq
            rw [heq] at htriv
            have htf := trivial_false_of_safeInj esL.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv
            cases htriv
          have hPRNG_choice : hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1) =
              hkPRNGBucketChoice false cka prng fs Δcka qep tL (qep + 1) := rfl
          have hLoc_choice : hooksLocalBucketAuthMain cka prng fs Δcka qep tL =
              hkLocalBucketChoice false cka prng fs Δcka qep tL := rfl
          rw [hPRNG_choice, hLoc_choice]
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucketChoice,
            run_commitE_LocalBucketChoice, StateT.run_pure, StateT.run_modify, pure_bind,
            simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncMainTop_of_vRecv_accept (pos := ⟨P.other, c.1.1, i'⟩) hsync rfl htle hns hvp'
              hroot_le hnew_hit⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncMainTop_set_win hsync⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)

private def StepRelMainTop {α : Type}
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (rP : (α × PRNGBucketAuthEState Γ T Sig SS RS M E K I) × CryptoGames.PRFPRNG.GameState Sig I K)
    (rL : α × LocalBucketAuthEState Γ T Sig SS RS M E K I) : Prop :=
  rP.1.2.1.abort = true ∨
  (rP.1.1 = rL.1 ∧ rP.1.2.2 = rL.2.2 ∧
    SyncMainTop prng Δcka qep tL rP.1.2.1 rP.2 rL.2.1)

private theorem authOutBucketSimple_eq_false_of_abort [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δ : ℕ) (tL : Option ℕ)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (hab : st.1.abort = true) :
    authOutBucketSimple Δ tL st = false := by
  rcases st with ⟨es, winEp⟩
  dsimp only at hab
  cases winEp <;> simp [authOutBucketSimple, hab]

private theorem stepPMainTop_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hab : stP.1.abort = true) :
    ∀ r ∈ support (stepPBucketChoice false cka prng fs Δcka qep tL q stP sp),
      r.1.2.1.abort = true := by
  rcases stP with ⟨esP, winEpP⟩
  dsimp only at hab
  intro r hr
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply, pImpl,
      StateT.run_lift, simulateQ_query] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hab
  · rcases arg with ⟨P, m, r_coins⟩
    simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply, hab] at hr
    rcases hr with rfl
    exact hab
  · simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply] at hr
    rcases hr with rfl
    exact hab
  · rcases arg with ⟨P, c⟩
    simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply, deliverE, hab,
      StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set] at hr
    rcases hr with rfl
    exact hab
  · rcases arg with ⟨P, c⟩
    simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply, injectE, hab,
      StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set] at hr
    rcases hr with rfl
    exact hab
  · simp [stepPBucketChoice, implPRNGBucketAuthGen, QueryImpl.add_apply, hab] at hr
    rcases hr with rfl
    exact hab

private theorem leComp_stepPMainTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {stL : LocalBucketAuthEState Γ T Sig SS RS M E K I}
    (hwinEp : stP.2 = stL.2)
    (hsync : SyncMainTop prng Δcka qep tL stP.1 sp stL.1) :
    LeComp (StepRelMainTop prng Δcka qep tL)
      (stepPBucketChoice false cka prng fs Δcka qep tL q stP sp)
      (stepLBucketChoice false cka prng fs Δcka qep tL q stL) := by
  rcases stP with ⟨esP, winEpP⟩
  rcases stL with ⟨esL, winEpL⟩
  dsimp only at hwinEp hsync
  subst hwinEp
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [stepPBucketChoice, stepLBucketChoice, implPRNGBucketAuthGen, implLocalBucketAuthGen,
      QueryImpl.add_apply, pImpl, lImpl, StateT.run_lift, map_eq_bind_pure_comp]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind _ fun u _ => CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · rcases arg with ⟨P, m, r_coins⟩
    unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq]
    by_cases habw : (false || esL.g.win) = true
    · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
    · simp only [habw, Bool.false_eq_true, ↓reduceIte]
      rcases epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
        ⟨s₁P, s₁L, h1, h2, hs₁_er, hs₁P_st, hs₁L_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
      · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
      · obtain ⟨hs₁_qep, he1_qep⟩ := epMgmt_le_qep_auth hsync.epoch_le_qep h2
        have hheq : P.sendsIn (esL.g.epoch P + 1) = true →
            esL.g.epoch P = esL.g.epoch P.other :=
          epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
        have he_lt : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 < qep + 1 := by
          intro hsends; have := he1_qep hsends; omega
        have hcr_pl : P.sendsIn (esL.g.epoch P + 1) = true → esP.h.corrRoot.isSome = true →
            postLeak tL s₁L = true := by
          intro _ hcr
          exact postLeak_true_of_epMgmt (syncMainTop_corrRoot_pl hsync hcr) h2
        have hσ_pl_false : P.sendsIn (esL.g.epoch P + 1) = true → postLeak tL s₁L = false →
            sp.σ = (esL.g.st P).root := by
          intro hsends hpl1_f
          have hpl0_f : postLeak tL esL.g = false := by
            cases hpl0 : postLeak tL esL.g
            · rfl
            · rw [postLeak_true_of_epMgmt hpl0 h2] at hpl1_f; cases hpl1_f
          have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
            (max_epoch_eq_of_eq (hheq hsends)).symm
          exact (hsync.root_max_of_none P hmax (Or.inl hpl0_f)).symm
        have hσ_unres : P.sendsIn (esL.g.epoch P + 1) = true → postLeak tL s₁L = true →
            resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = none →
            esP.h.corrRoot = none ∧ (esP.g.st P).root = none ∧ sp.σ = (esL.g.st P).root := by
          intro hsends _ hunres
          have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
            (max_epoch_eq_of_eq (hheq hsends)).symm
          obtain ⟨hcr0, hvp0, hσ0⟩ := syncMainTop_max_unres hsync hmax hunres
          exact ⟨hcr0, hvp0, hσ0.symm⟩
        simp only [h1, h2, hs₁P_st, hs₁L_st, StateT.run_lift, simulateQ_bind, StateT.run_bind,
          bind_assoc]
        refine (leComp_vSendBucketAuthTop false cka prng fs Δcka qep tL
          (postLeak_eraseSt hs₁_er tL) (hsync.vp_rel P) hsync.fTable_lt hsync.table_top hsync.sp_b
          he_lt hcr_pl hσ_pl_false hσ_unres).bind ?_
        rintro ⟨⟨res_vsP, hP1⟩, sp1⟩ ⟨res_vsL, hL1⟩ hvs
        rcases hvs with hnone | ⟨vpP', vpL', c, hP_eq, hL_eq, hc_hdr, hvp', hb1,
          hft1, htop1, hsends_props, hns_props⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ?_
          have hs₁_ep : s₁L.epoch P = if P.sendsIn (esL.g.epoch P + 1) then esL.g.epoch P + 1
              else esL.g.epoch P := by
            rw [hs₁_ep_fn]; split <;> simp
          have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
            intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
          have hs₁P_ep : s₁P.epoch = s₁L.epoch := eraseSt_epoch hs₁_er
          have hs₁P_idx : s₁P.idx = s₁L.idx := eraseSt_idx hs₁_er
          rw [hs₁P_ep, hs₁P_idx]
          have hs₁_comp := hs₁_comp_imp hsync.comp_inv
          have hcr_cases : hP1.corrRoot = esP.h.corrRoot ∨
              (P.sendsIn (esL.g.epoch P + 1) = true ∧ postLeak tL s₁L = true ∧
                esP.h.corrRoot = none ∧
                hP1.corrRoot = some (esL.g.epoch P, (esL.g.st P).root)) := by
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, hplF, hplT, _, _⟩ := hsends_props hsends
              by_cases hpl1 : postLeak tL s₁L = true
              · rcases (hplT hpl1).2 with hcr_eq | ⟨hcr0, hcr_set⟩
                · exact Or.inl hcr_eq
                · exact Or.inr ⟨hsends, hpl1, hcr0, hcr_set⟩
              · have hpl1_f : postLeak tL s₁L = false := Bool.eq_false_iff.mpr hpl1
                have hcr1_none : hP1.corrRoot = none := (hplF hpl1_f).2.1
                have hcr0_none : esP.h.corrRoot = none := by
                  cases hcr0 : esP.h.corrRoot with
                  | none => rfl
                  | some p =>
                    have := hcr_pl hsends (by simp [hcr0])
                    rw [hpl1_f] at this; cases this
                exact Or.inl (hcr1_none.trans hcr0_none.symm)
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              have hhP1 := (hns_props hns).1
              dsimp only at hhP1
              rw [hhP1]
              exact Or.inl rfl
          refine Or.inr ⟨rfl, rfl,
            ⟨rfl, rfl,
              eraseSt_record hs₁_er (2 + Δcka) P vpP' vpL' _ false,
              ?_, ?_, hft1, htop1, hb1, hs₁_qep,
              comp_inv_record s₁L (2 + Δcka) P vpL' _ false rfl hs₁_comp,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
          · intro Q
            dsimp only [CryptoGames.SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st]
              rcases hcr_cases with hcr_eq | ⟨_, _, _, hcr_set⟩
              · exact relVPBucketAuth_of_corrRoot_eq hcr_eq.symm (hsync.vp_rel Q)
              · exact relVP_of_set_corrRoot hcr_set (hsync.vp_rel Q)
                  (syncMainTop_heC_vp hsync P Q)
          · intro t'
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, _, _, ⟨T', k, _, hcP_self, hcL_self⟩, hc_other⟩ := hsends_props hsends
              by_cases ht' : t' = esL.g.epoch P + 1
              · subst ht'
                have hvp'_e1 : RelVPBucketAuth hP1 (esL.g.epoch P + 1) P vpP' vpL' := by
                  simpa [hsends] using hvp'
                exact Or.inr ⟨T', vpP'.root, vpL'.root, k, hcP_self, hcL_self, hvp'_e1.root_eq⟩
              · rw [(hc_other t' ht').1, (hc_other t' ht').2]
                rcases hcr_cases with hcr_eq | ⟨_, _, _, hcr_set⟩
                · exact relCacheBucketAuth_of_corrRoot_eq hcr_eq.symm (hsync.cache_rel t')
                · exact relCache_of_set_corrRoot hcr_set (hsync.cache_rel t')
                    (syncMainTop_heC_cache hsync P)
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, _, hhL1, _, _, _⟩ := hns_props hns
              dsimp only at hhP1 hhL1
              rw [hhP1, hhL1]
              exact hsync.cache_rel t'
          · intro r hr
            dsimp only [CryptoGames.SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · refine ⟨le_rfl, ?_⟩
              dsimp only; rw [hc_hdr, hs₁_ep]
            · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
              refine ⟨?_, h_eq⟩
              by_cases hQ : r.pos.sender = P
              · rw [hQ, hs₁_ep]; rw [hQ] at h_le; split <;> omega
              · rw [hs₁_ep_other _ hQ]; exact h_le
          · intro Q hns_Q hpos_Q Tc hTc
            dsimp only [CryptoGames.SM.GameState.record] at hns_Q hpos_Q hTc ⊢
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, _, _, ⟨T', k, hT', _, hcL_self⟩, hc_other⟩ := hsends_props hsends
              have heq_other := hheq hsends
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte] at hTc ⊢
                rw [hT'] at hTc; cases hTc
                exact ⟨vpL'.root, k, hcL_self⟩
              · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
                have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                  cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other ⊢ <;> omega
                rw [(hc_other _ hne).2]
                exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, _, hhL1, _, _, hcur_eq⟩ := hns_props hns
              dsimp only at hhL1
              rw [hhL1]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hs₁_ep, hns, Bool.false_eq_true, ↓reduceIte] at hpos_Q hTc ⊢
                rw [hcur_eq] at hTc
                exact hsync.vp_curCka P hns hpos_Q Tc hTc
              · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st] at hns_Q hpos_Q hTc ⊢
                exact hsync.vp_curCka Q hns_Q hpos_Q Tc hTc
          · intro r hr hpos_r Tc hTc
            dsimp only [CryptoGames.SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · dsimp only at hpos_r hTc ⊢
              rw [hc_hdr] at hTc; dsimp only at hTc
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · obtain ⟨_, _, _, ⟨T', k, hT', _, hcL_self⟩, _⟩ := hsends_props hsends
                rw [hs₁_ep, hsends]; simp only [↓reduceIte]
                rw [hT'] at hTc; cases hTc
                exact ⟨vpL'.root, k, hcL_self⟩
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, _, hhL1, _, _, hcur_eq⟩ := hns_props hns
                dsimp only at hhL1; rw [hhL1]
                rw [hs₁_ep] at hpos_r ⊢
                simp only [hns, Bool.false_eq_true, ↓reduceIte] at hpos_r ⊢
                rw [hcur_eq] at hTc
                exact hsync.vp_curCka P hns hpos_r Tc hTc
            · have hr_mem : r ∈ esL.g.trans := hs₁_trans ▸ hr'
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · obtain ⟨_, _, _, _, hc_other⟩ := hsends_props hsends
                have heq_other := hheq hsends
                have hr_le := (hsync.trans_epoch r hr_mem).1
                have hne : r.pos.epoch ≠ esL.g.epoch P + 1 := by
                  cases hS : r.pos.sender <;> cases P <;>
                    simp [CryptoGames.Party.other, hS] at heq_other hr_le ⊢ <;> omega
                rw [(hc_other _ hne).2]
                exact hsync.trans_cache r hr_mem hpos_r Tc hTc
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, _, hhL1, _, _, _⟩ := hns_props hns
                dsimp only at hhL1; rw [hhL1]
                exact hsync.trans_cache r hr_mem hpos_r Tc hTc
          · intro Q
            dsimp only [CryptoGames.SM.GameState.record]; rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte]
              cases Q <;> cases P <;> simp [CryptoGames.Party.other] at heq_other ⊢ <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
              exact hsync.epoch_le Q
          · intro Q hlt_Q
            dsimp only [CryptoGames.SM.GameState.record] at hlt_Q ⊢; rw [hs₁_ep_fn] at hlt_Q ⊢
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hlt_Q ⊢
              by_cases hQ : Q = P
              · subst Q; simp only [Function.update_self]; exact hsends
              · cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other hlt_Q <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hlt_Q ⊢
              exact hsync.epoch_sends Q hlt_Q
          · by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, _, _, _, hc_other⟩ := hsends_props hsends
              rw [(hc_other 0 (by omega)).2]
              exact hsync.cache_zero
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, _, hhL1, _, _, _⟩ := hns_props hns
              dsimp only at hhL1; rw [hhL1]
              exact hsync.cache_zero
          · intro t' hgt
            dsimp only [CryptoGames.SM.GameState.record] at hgt; rw [hs₁_ep_fn] at hgt
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hgt
              rw [max_epoch_update_succ heq_other] at hgt
              obtain ⟨_, _, _, _, hc_other⟩ := hsends_props hsends
              rw [(hc_other t' (by omega)).2]
              exact hsync.cache_lt_max t' (by rw [max_epoch_eq_of_eq heq_other]; omega)
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, _, hhL1, _, _, _⟩ := hns_props hns
              dsimp only at hhL1; rw [hhL1]
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hgt
              exact hsync.cache_lt_max t' hgt
          · intro Q hpos_Q
            dsimp only [CryptoGames.SM.GameState.record] at hpos_Q ⊢
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, _, _, ⟨T', k, _, hcP_self, hcL_self⟩, hc_other⟩ := hsends_props hsends
              have heq_other := hheq hsends
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hs₁_ep, hsends, ↓reduceIte]
                exact ⟨T', vpP'.root, k, hcP_self, hcL_self, fun _ hs => hs, fun _ => rfl⟩
              · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st] at hpos_Q ⊢
                have hne : esL.g.epoch Q ≠ esL.g.epoch P + 1 := by
                  cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other ⊢ <;> omega
                obtain ⟨Tc0, σP0, k0, hcP0, hcL0, hs_imp, hcr_imp⟩ := hsync.vp_cache_root Q hpos_Q
                refine ⟨Tc0, σP0, k0, (hc_other _ hne).1.trans hcP0, (hc_other _ hne).2.trans hcL0,
                  hs_imp, fun hcr1_none => hcr_imp ?_⟩
                rcases hcr_cases with hcr_eq | ⟨_, _, _, hcr_set⟩
                · exact hcr_eq.symm.trans hcr1_none
                · rw [hcr1_none] at hcr_set; cases hcr_set
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, _, hhL1, hvpP_eq, hvpL_eq, _⟩ := hns_props hns
              dsimp only at hhP1 hhL1
              rw [hhP1, hhL1]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hs₁_ep, hns, Bool.false_eq_true, ↓reduceIte] at hpos_Q ⊢
                rw [hvpP_eq, hvpL_eq]
                exact hsync.vp_cache_root P hpos_Q
              · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st] at hpos_Q ⊢
                exact hsync.vp_cache_root Q hpos_Q
          · intro Q1 Q2 h1 h2
            dsimp only [CryptoGames.SM.GameState.record] at h1 h2 ⊢
            have hroot_z : ∀ Q, s₁L.epoch Q = 0 →
                esL.g.epoch Q = 0 ∧ (Function.update s₁L.st P vpL' Q).root = (esL.g.st Q).root := by
              intro Q hQ0
              by_cases hQ : Q = P
              · subst Q
                rw [hs₁_ep] at hQ0
                by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
                · simp [hsends] at hQ0
                · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ0
                  simp only [Function.update_self]
                  exact ⟨hQ0, (hns_props hns).2.2.2.2.1⟩
              · rw [hs₁_ep_other Q hQ] at hQ0
                rw [Function.update_of_ne hQ, hs₁L_st]
                exact ⟨hQ0, rfl⟩
            obtain ⟨he1, hr1⟩ := hroot_z Q1 h1
            obtain ⟨he2, hr2⟩ := hroot_z Q2 h2
            rw [hr1, hr2]
            exact hsync.vp_zero_root Q1 Q2 he1 he2
          · intro Q hcr1_none hQ0 his
            dsimp only [CryptoGames.SM.GameState.record] at hQ0 his
            have hcr0_none : esP.h.corrRoot = none := by
              rcases hcr_cases with hcr_eq | ⟨_, _, _, hcr_set⟩
              · exact hcr_eq.symm.trans hcr1_none
              · rw [hcr1_none] at hcr_set; cases hcr_set
            by_cases hQ : Q = P
            · subst Q
              rw [hs₁_ep] at hQ0
              by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
              · simp [hsends] at hQ0
              · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ0
                simp only [Function.update_self, (hns_props hns).2.2.2.1] at his
                exact hsync.zero_some_lt_tH P hcr0_none hQ0 his
            · rw [hs₁_ep_other Q hQ] at hQ0
              simp only [Function.update_of_ne hQ, hs₁P_st] at his
              exact hsync.zero_some_lt_tH Q hcr0_none hQ0 his
          · intro e0 he0 Tc σs k hc
            change postLeak tL s₁L = true
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, hplF, _, ⟨T', k0, _, hcP_self, _⟩, hc_other⟩ := hsends_props hsends
              by_cases heq : e0 = esL.g.epoch P + 1
              · subst heq
                dsimp only at hc hcP_self
                rw [hcP_self] at hc
                have hvp_some : vpP'.root = some σs :=
                  (Prod.mk.inj (Prod.mk.inj (Option.some.inj hc)).2).1
                cases hpl1 : postLeak tL s₁L
                · have hvp_none := (hplF hpl1).2.2.2 he0
                  rw [hvp_some] at hvp_none; cases hvp_none
                · rfl
              · rw [(hc_other e0 heq).1] at hc
                exact postLeak_true_of_epMgmt (hsync.cache_some_pl e0 he0 Tc σs k hc) h2
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, _, _, _, _, _⟩ := hns_props hns
              dsimp only at hhP1; rw [hhP1] at hc
              rw [postLeak_epMgmt_of_sendsIn_false hns h2]
              exact hsync.cache_some_pl e0 he0 Tc σs k hc
          · intro e0 t' he0 hle ⟨Tc0, σs0, k0, hc0⟩ Tc σP k hct'
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, _, hplT, ⟨T', kv, _, hcP_self, _⟩, hc_other⟩ := hsends_props hsends
              have heq_other := hheq hsends
              by_cases ht' : t' = esL.g.epoch P + 1
              · subst ht'
                by_cases heq0 : e0 = esL.g.epoch P + 1
                · subst heq0
                  rw [hc0] at hct'
                  have hσ_eq : σP = some σs0 :=
                    (Prod.mk.inj (Prod.mk.inj (Option.some.inj hct')).2).1.symm
                  simp [hσ_eq]
                · rw [(hc_other e0 heq0).1] at hc0
                  have hpl0 := hsync.cache_some_pl e0 he0 Tc0 σs0 k0 hc0
                  have hpl1 := postLeak_true_of_epMgmt hpl0 h2
                  have hvp_some := (hplT hpl1).1
                  dsimp only at hct' hcP_self
                  rw [hcP_self] at hct'
                  have hσ_eq : σP = vpP'.root :=
                    (Prod.mk.inj (Prod.mk.inj (Option.some.inj hct')).2).1.symm
                  simp [hσ_eq, hvp_some]
              · rw [(hc_other t' ht').1] at hct'
                by_cases heq0 : e0 = esL.g.epoch P + 1
                · subst heq0
                  have hgt_max : max (esL.g.epoch .A) (esL.g.epoch .B) < t' := by
                    rw [max_epoch_eq_of_eq heq_other]; omega
                  have hcP_none := syncMainTop_cacheP_none hsync (hsync.cache_lt_max t' hgt_max)
                  rw [hcP_none] at hct'; cases hct'
                · rw [(hc_other e0 heq0).1] at hc0
                  exact hsync.cache_some_mono e0 t' he0 hle ⟨Tc0, σs0, k0, hc0⟩ Tc σP k hct'
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, _, _, _, _, _⟩ := hns_props hns
              dsimp only at hhP1; rw [hhP1] at hc0 hct'
              exact hsync.cache_some_mono e0 t' he0 hle ⟨Tc0, σs0, k0, hc0⟩ Tc σP k hct'
          · intro eC σC hcr1_some
            dsimp only [CryptoGames.SM.GameState.record]
            change postLeak tL s₁L = true ∧ eC ≤ max (s₁L.epoch .A) (s₁L.epoch .B) ∧ _
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, hplF, hplT, ⟨T', kv, _, hcP_self, _⟩, hc_other⟩ := hsends_props hsends
              have heq_other := hheq hsends
              have hpl1 : postLeak tL s₁L = true := by
                cases hpl : postLeak tL s₁L
                · have hcr1_none := (hplF hpl).2.1
                  dsimp only at hcr1_none hcr1_some
                  rw [hcr1_none] at hcr1_some; cases hcr1_some
                · rfl
              have hvp_some := (hplT hpl1).1
              have hmax_s1 : max (s₁L.epoch .A) (s₁L.epoch .B) = esL.g.epoch P + 1 := by
                rw [hs₁_ep_fn]; simp only [hsends, ↓reduceIte]
                exact max_epoch_update_succ heq_other
              rw [hmax_s1]
              rcases (hplT hpl1).2 with hcr_eq | ⟨_, hcr_set⟩
              · dsimp only at hcr_eq hcr1_some
                have hcr0_some : esP.h.corrRoot = some (eC, σC) := hcr_eq.symm.trans hcr1_some
                obtain ⟨_, heC_le, hgt_some⟩ := hsync.corrRoot_bound eC σC hcr0_some
                rw [max_epoch_eq_of_eq heq_other] at heC_le
                refine ⟨hpl1, by omega, fun t' ht' Tc σP k hct' => ?_⟩
                by_cases ht1 : t' = esL.g.epoch P + 1
                · subst ht1
                  dsimp only at hct' hcP_self
                  rw [hcP_self] at hct'
                  have hσ_eq : σP = vpP'.root :=
                    (Prod.mk.inj (Prod.mk.inj (Option.some.inj hct')).2).1.symm
                  simp [hσ_eq, hvp_some]
                · rw [(hc_other t' ht1).1] at hct'
                  exact hgt_some t' ht' Tc σP k hct'
              · dsimp only at hcr_set hcr1_some
                rw [hcr_set] at hcr1_some
                injection hcr1_some with hp_eq
                have heC_eq : esL.g.epoch P = eC := (Prod.mk.inj hp_eq).1
                subst heC_eq
                refine ⟨hpl1, by omega, fun t' ht' Tc σP k hct' => ?_⟩
                by_cases ht1 : t' = esL.g.epoch P + 1
                · subst ht1
                  dsimp only at hct' hcP_self
                  rw [hcP_self] at hct'
                  have hσ_eq : σP = vpP'.root :=
                    (Prod.mk.inj (Prod.mk.inj (Option.some.inj hct')).2).1.symm
                  simp [hσ_eq, hvp_some]
                · rw [(hc_other t' ht1).1] at hct'
                  have hgt_max : max (esL.g.epoch .A) (esL.g.epoch .B) < t' := by
                    rw [max_epoch_eq_of_eq heq_other]; omega
                  have hcP_none := syncMainTop_cacheP_none hsync (hsync.cache_lt_max t' hgt_max)
                  rw [hcP_none] at hct'; cases hct'
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, _, _, _, _, _⟩ := hns_props hns
              dsimp only at hhP1 hcr1_some
              rw [hhP1] at hcr1_some ⊢
              rw [postLeak_epMgmt_of_sendsIn_false hns h2, hs₁_ep_fn]
              simp only [hns, Bool.false_eq_true, ↓reduceIte]
              exact hsync.corrRoot_bound eC σC hcr1_some
          · intro Q hQ_max hcond
            dsimp only [CryptoGames.SM.GameState.record] at hQ_max hcond ⊢
            change (postLeak tL s₁L = false ∨ _) at hcond
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · obtain ⟨_, hplF, hplT, _, _⟩ := hsends_props hsends
              have heq_other := hheq hsends
              rw [hs₁_ep_fn] at hQ_max
              simp only [hsends, ↓reduceIte] at hQ_max
              rw [max_epoch_update_succ heq_other] at hQ_max
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self] at hQ_max hcond ⊢
                rcases hcond with hpl1_f | ⟨_, hvp_none⟩
                · exact ((hplF hpl1_f).1).symm
                · cases hpl1 : postLeak tL s₁L
                  · exact ((hplF hpl1).1).symm
                  · have hvp_some := (hplT hpl1).1
                    rw [hvp_some] at hvp_none; cases hvp_none
              · rw [Function.update_of_ne hQ] at hQ_max
                cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other hQ_max <;> omega
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨hhP1, hsp1, _, hvpP_eq, hvpL_eq, _⟩ := hns_props hns
              dsimp only at hhP1 hsp1
              rw [postLeak_epMgmt_of_sendsIn_false hns h2, hhP1] at hcond
              rw [hs₁_ep_fn] at hQ_max
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ_max
              rw [hsp1]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self] at hcond ⊢
                rw [hvpP_eq] at hcond; rw [hvpL_eq]
                exact hsync.root_max_of_none P hQ_max hcond
              · simp only [Function.update_of_ne hQ, hs₁P_st, hs₁L_st] at hcond ⊢
                exact hsync.root_max_of_none Q hQ_max hcond
  · simp only [stepPBucketChoice, stepLBucketChoice, implPRNGBucketAuthGen, implLocalBucketAuthGen,
      QueryImpl.add_apply, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
      simulateQ_bind, pure_bind, bind_assoc]
    change LeComp _
      (((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esP)).run sp) >>= _)
      ((simulateQ lImpl
        ((deliverE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esL)) >>= _)
    refine (leComp_deliverEMainTop cka prng fs Δcka qep tL arg hsync).bind ?_
    rintro ⟨⟨outP, esP'⟩, sp'⟩ ⟨outL, esL'⟩ (hab | ⟨hout, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl hab)
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)
  · rcases arg with ⟨P, c⟩
    unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift,
      simulateQ_bind, pure_bind, bind_assoc]
    change LeComp _
      (((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run esP)).run sp) >>= _)
      ((simulateQ lImpl
        ((injectE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run esL)) >>= _)
    refine (leComp_injectEMainTop cka prng fs Δcka qep tL (P, c) hsync).bind ?_
    rintro ⟨⟨outP, esP'⟩, sp'⟩ ⟨outL, esL'⟩ (hab | ⟨hout, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl hab)
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
        Bool.not_false, Bool.true_or, Bool.and_true]
      have hwas : esP.g.win = esL.g.win := eraseSt_win hsync.g_eq
      have hnow : esP'.g.win = esL'.g.win := eraseSt_win hsync'.g_eq
      rw [hwas, hnow]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)
  · unfold stepPBucketChoice stepLBucketChoice implPRNGBucketAuthGen implLocalBucketAuthGen
    simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
    rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq, eraseSt_corrAllowed hsync.g_eq]
    by_cases hguard : (false || esL.g.win || !esL.g.corrAllowed P) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_lift, simulateQ_bind,
        StateT.run_bind, bind_assoc, hkPRNGBucketChoice, hkLocalBucketChoice,
        hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
        hooksLocalBucketAuthMain, hooksLocalBucketAuth,
        StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind]
      have hvp := hsync.vp_rel P
      rw [hvp.tcur_P, eraseSt_epoch hsync.g_eq, postLeak_eraseSt hsync.g_eq tL]
      have hout_eq :
          realParty (esP.g.st P) (esP.g.st P).γ (esL.g.st P).root (esP.g.st P).vS (esP.g.st P).vR =
            realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
        dsimp only [realParty]
        rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq,
          funext hvp.vR_eq]
      have hcomp_ac := comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
        (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv
      have her_ac := eraseSt_afterCorr hsync.g_eq P
      cases hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root with
      | some σ =>
        have hσ_eq : σ = (esL.g.st P).root := hvp.root_eq σ hres
        subst σ
        by_cases hset : (!(esL.g.epoch P < healEpoch tL) && esP.h.corrRoot.isNone) = true
        · simp only [hset, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, pure_bind, StateT.run_set, hout_eq]
          have hge_tH : healEpoch tL ≤ esL.g.epoch P := by
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hset
            exact Nat.le_of_not_lt (of_decide_eq_false hset.1)
          have hcr_none : esP.h.corrRoot = none := by
            simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hset
            exact hset.2
          have he_le_max : esL.g.epoch P ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
            cases P <;> simp
          have hpl_ac : postLeak tL (esL.g.afterCorr P) = true :=
            postLeak_true_of_afterCorr_ge_tH P (Nat.le_trans hge_tH he_le_max)
          have hvpP_some : (esP.g.st P).root = some (esL.g.st P).root := by
            cases hrP : (esP.g.st P).root with
            | none => simp [resolveCorrRoot, hcr_none, hrP] at hres
            | some s =>
              simp [resolveCorrRoot, hrP] at hres
              simp [hres]
          have he_pos : 0 < esL.g.epoch P := by
            by_cases he0 : esL.g.epoch P = 0
            · have := hsync.zero_some_lt_tH P hcr_none he0 (by simp [hvpP_some])
              omega
            · exact Nat.pos_of_ne_zero he0
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl,
            ⟨rfl, rfl, her_ac,
              fun Q => relVP_of_set_corrRoot rfl (hsync.vp_rel Q) (syncMainTop_heC_vp hsync P Q),
              fun t' => relCache_of_set_corrRoot rfl (hsync.cache_rel t')
                (syncMainTop_heC_cache hsync P),
              hsync.fTable_lt, hsync.table_top, hsync.sp_b, hsync.epoch_le_qep,
              hcomp_ac, hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
              hsync.epoch_le, hsync.epoch_sends, hsync.cache_zero, hsync.cache_lt_max,
              ?_, hsync.vp_zero_root, ?_, fun _ _ _ _ _ _ => hpl_ac,
              hsync.cache_some_mono, ?_, ?_⟩⟩)
          · intro Q hpos_Q
            obtain ⟨Tc0, σP0, k0, hcP0, hcL0, hs_imp, _⟩ := hsync.vp_cache_root Q hpos_Q
            exact ⟨Tc0, σP0, k0, hcP0, hcL0, hs_imp, fun h => by simp at h⟩
          · intro _ h; simp at h
          · intro eC σC hcr'
            dsimp only at hcr'
            injection hcr' with hp_eq
            have heC_eq : esL.g.epoch P = eC := (Prod.mk.inj hp_eq).1
            subst heC_eq
            refine ⟨hpl_ac, he_le_max, fun t' ht' Tc σP k hct' => ?_⟩
            obtain ⟨Tc0, σP0, k0, hcP0, _, _, hcr_imp⟩ := hsync.vp_cache_root P he_pos
            have hσP0_some : σP0 = some (esL.g.st P).root :=
              (hcr_imp hcr_none).symm.trans hvpP_some
            rw [hσP0_some] at hcP0
            exact hsync.cache_some_mono _ t' hge_tH (by omega)
              ⟨Tc0, (esL.g.st P).root, k0, hcP0⟩ Tc σP k hct'
          · intro _ _ hcond
            rcases hcond with hpl_f | ⟨hcr_n, _⟩
            · dsimp only at hpl_f; rw [hpl_ac] at hpl_f; cases hpl_f
            · simp at hcr_n
        · simp only [hset, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            simulateQ_pure, pure_bind, StateT.run_set, hout_eq]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl,
            ⟨rfl, rfl, her_ac, hsync.vp_rel, hsync.cache_rel,
              hsync.fTable_lt, hsync.table_top, hsync.sp_b, hsync.epoch_le_qep,
              hcomp_ac, hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
              hsync.epoch_le, hsync.epoch_sends, hsync.cache_zero, hsync.cache_lt_max,
              hsync.vp_cache_root, hsync.vp_zero_root, hsync.zero_some_lt_tH,
              fun e0 he0 Tc σs k hc =>
                postLeak_true_of_afterCorr_pl P (hsync.cache_some_pl e0 he0 Tc σs k hc),
              hsync.cache_some_mono, ?_, ?_⟩⟩)
          · intro eC σC hcr'
            obtain ⟨hpl0, heC_le, hgt⟩ := hsync.corrRoot_bound eC σC hcr'
            exact ⟨postLeak_true_of_afterCorr_pl P hpl0, heC_le, hgt⟩
          · intro Q hQ_max hcond
            dsimp only at hQ_max hcond ⊢
            rcases hcond with hpl_f | hcr_vp
            · have hpl0_f : postLeak tL esL.g = false := by
                cases hpl0 : postLeak tL esL.g
                · rfl
                · rw [postLeak_true_of_afterCorr_pl P hpl0] at hpl_f; cases hpl_f
              exact hsync.root_max_of_none Q hQ_max (Or.inl hpl0_f)
            · exact hsync.root_max_of_none Q hQ_max (Or.inr hcr_vp)
      | none =>
        by_cases hcond_q :
            (!postLeak tL esL.g && esP.h.corrRoot.isNone &&
              !(esL.g.epoch P < healEpoch tL) &&
              (esL.g.epoch P == max (esL.g.epoch .A) (esL.g.epoch .B))) = true
        · simp only [hcond_q, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_corrQuery, run_corrImpl, bind_assoc]
          have hge_tH : healEpoch tL ≤ esL.g.epoch P := by
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond_q
            exact Nat.le_of_not_lt (of_decide_eq_false hcond_q.1.2)
          have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond_q
            exact hcond_q.2
          obtain ⟨_, _, hroot_sp⟩ := syncMainTop_max_unres hsync hmax hres
          rcases sp with ⟨σ_sp, b_sp, corr_sp, prng_sp, prf_sp, table_sp⟩
          dsimp only at hroot_sp
          subst σ_sp
          cases prf_sp
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set, hout_eq]
            have hpl_ac : postLeak tL (esL.g.afterCorr P) = true :=
              postLeak_true_of_afterCorr_ge_tH P (hmax ▸ hge_tH)
            have he_le_max : esL.g.epoch P ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
              cases P <;> simp
            refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl,
              ⟨rfl, rfl, her_ac,
                fun Q => relVP_of_set_corrRoot rfl (hsync.vp_rel Q) (syncMainTop_heC_vp hsync P Q),
                fun t' => relCache_of_set_corrRoot rfl (hsync.cache_rel t')
                  (syncMainTop_heC_cache hsync P),
                hsync.fTable_lt, hsync.table_top, hsync.sp_b, hsync.epoch_le_qep,
                hcomp_ac, hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
                hsync.epoch_le, hsync.epoch_sends, hsync.cache_zero, hsync.cache_lt_max,
                ?_, hsync.vp_zero_root, ?_, fun _ _ _ _ _ _ => hpl_ac,
                hsync.cache_some_mono, ?_, ?_⟩⟩)
            · intro Q hpos_Q
              obtain ⟨Tc0, σP0, k0, hcP0, hcL0, hs_imp, _⟩ := hsync.vp_cache_root Q hpos_Q
              exact ⟨Tc0, σP0, k0, hcP0, hcL0, hs_imp, fun h => by simp at h⟩
            · intro _ h; simp at h
            · intro eC σC hcr'
              dsimp only at hcr'
              injection hcr' with hp_eq
              have heC_eq : esL.g.epoch P = eC := (Prod.mk.inj hp_eq).1
              subst heC_eq
              refine ⟨hpl_ac, he_le_max, fun t' ht' Tc σP k hct' => ?_⟩
              have hgt_max : max (esL.g.epoch .A) (esL.g.epoch .B) < t' := hmax ▸ ht'
              have hcP_none := syncMainTop_cacheP_none hsync (hsync.cache_lt_max t' hgt_max)
              rw [hcP_none] at hct'; cases hct'
            · intro _ _ hcond
              rcases hcond with hpl_f | ⟨hcr_n, _⟩
              · dsimp only at hpl_f; rw [hpl_ac] at hpl_f; cases hpl_f
              · simp at hcr_n
          · simp only [↓reduceIte, StateT.run_bind, StateT.run_pure,
              simulateQ_pure, pure_bind, StateT.run_set]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hcond_q, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            simulateQ_pure, pure_bind, StateT.run_set]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private theorem runPMainTop_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    (hab : stP.1.abort = true) :
    𝒟[runPBucketChoice false cka prng fs Δcka qep tL oa stP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stP sp with
  | pure b' =>
    rw [runPBucketChoice_pure, authOutBucketSimple_eq_false_of_abort (2 + Δcka) tL stP hab]
    simp
  | query_bind q k ih =>
    rw [runPBucketChoice_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPMainTop_abort cka prng fs Δcka qep tL q stP sp hab r hr)

private theorem runPMainTop_le_runLMainTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ)
    (oa : SMCompAuth Γ T Sig SS RS M CCoins E Bool)
    {stP : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    {stL : LocalBucketAuthEState Γ T Sig SS RS M E K I}
    (hwinEp : stP.2 = stL.2)
    (hsync : SyncMainTop prng Δcka qep tL stP.1 sp stL.1) :
    𝒟[runPBucketChoice false cka prng fs Δcka qep tL oa stP sp] {true} ≤
      𝒟[runLBucketChoice false cka prng fs Δcka qep tL oa stL] {true} := by
  induction oa using OracleComp.inductionOn generalizing stP sp stL with
  | pure b' =>
    rw [runPBucketChoice_pure, runLBucketChoice_pure]
    rcases stP with ⟨esP, winEpP⟩
    rcases stL with ⟨esL, winEpL⟩
    dsimp only at hwinEp hsync
    subst hwinEp
    have hout : authOutBucketSimple (2 + Δcka) tL (esP, winEpP) =
        authOutBucketSimple (2 + Δcka) tL (esL, winEpP) := by
      cases winEpP with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketSimple]
        rw [hsync.abortP, hsync.abortL, eraseSt_win hsync.g_eq,
          eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPBucketChoice_query_bind, runLBucketChoice_query_bind]
    refine leComp_stepPMainTop cka prng fs Δcka qep tL q hwinEp hsync _ _ ?_
    rintro ⟨⟨uP, stP'⟩, sp'⟩ ⟨uL, stL'⟩ (hab | ⟨hu, hwinEp', hsync'⟩)
    · rw [runPMainTop_abort cka prng fs Δcka qep tL (k uP) hab]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uP hwinEp' hsync'

theorem prng_branch_true_redPRNGAuthBucketHybridMain_top_le_local_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (_htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CryptoGames.PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (qep + 1) A)] {true} ≤
      𝒟[localAuthBucketMain cka prng fs lam Δcka qep tL A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (CryptoGames.PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold CryptoGames.PRFPRNG.branch redPRNGAuthBucketHybridMain runPRNGAuthBucketHybridGen
    localAuthBucketMain initPRNGBucketAuthHybrid initLocalBucketAuth
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootBucketAuthTop (T := T) prng qep tL 0 false lam none (prng.init kr)
    ({} : PRNGBucketAuthState T Sig K I) { σ := prng.init kr, b := true }
    ({} : LocalBucketAuthState T Sig K I) (Nat.zero_lt_succ qep) rfl (fun _ _ => rfl) rfl
    (by simp) (by simp [resolveCorrRoot]) (fun _ => rfl) (by simp)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL⟩, hL0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨σP, σL', k', hres_eq, hL_eq, hσ_rel, hpl_props, _, hb0, hcP0, hcL0, hft0, htop0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hres_eq hL_eq
    injection hL_eq with hσL_eq hk_eq
    subst hres_eq hσL_eq hk_eq
    obtain ⟨hsp_σ, hcr0, _, hge0_none⟩ := hpl_props rfl
    dsimp only at hsp_σ hcr0 hge0_none hb0 hcP0 hcL0 hft0 htop0
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc]
    let gP0 : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σP
              (fs.initSender kL) (fs.initReceiver kL)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σP
              (fs.initSender kL) (fs.initReceiver kL)).2, b := false }
    let gL0 : Ctx Γ T Sig SS RS M E :=
      { st := fun P => match P with
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σL
              (fs.initSender kL) (fs.initReceiver kL)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σL
              (fs.initSender kL) (fs.initReceiver kL)).2, b := false }
    have hP_ev :
        ((simulateQ (pImpl prng)
          ((simulateQ (implPRNGBucketAuthGen
            (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
            Δcka qep fs.maxSkip tL false) A).run ({ g := gP0, h := hP0 }, none))).run sp0 >>=
          fun x => (simulateQ (pImpl prng) (match x.1.2.2 with
            | none => pure false
            | some tWin => pure (!x.1.2.1.abort && x.1.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.1.2.1.g))).run x.2 >>=
          pure ∘ fun x => x.1) =
        runPBucketChoice false cka prng fs Δcka qep tL A ({ g := gP0, h := hP0 }, none) sp0 := by
      unfold runPBucketChoice hkPRNGBucketChoice
      congr 1
      ext r
      rcases r with ⟨⟨_, _, winEp⟩, _⟩
      cases winEp <;> simp [authOutBucketSimple]
    have hL_ev :
        (simulateQ lImpl
          ((simulateQ (implLocalBucketAuthGen
            (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
            Δcka qep fs.maxSkip tL false) A).run ({ g := gL0, h := hL0 }, none)) >>=
          fun x => simulateQ lImpl (match x.2.2 with
            | none => pure false
            | some tWin => pure (!x.2.1.abort && x.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.2.1.g))) =
        runLBucketChoice false cka prng fs Δcka qep tL A ({ g := gL0, h := hL0 }, none) := by
      unfold runLBucketChoice hkLocalBucketChoice
      congr 1
      ext r
      rcases r with ⟨_, _, winEp⟩
      cases winEp <;> simp [authOutBucketSimple]
    change 𝒟[((simulateQ (pImpl prng)
          ((simulateQ (implPRNGBucketAuthGen
            (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (qep + 1))
            Δcka qep fs.maxSkip tL false) A).run ({ g := gP0, h := hP0 }, none))).run sp0 >>=
          fun x => (simulateQ (pImpl prng) (match x.1.2.2 with
            | none => pure false
            | some tWin => pure (!x.1.2.1.abort && x.1.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.1.2.1.g))).run x.2 >>=
          pure ∘ fun x => x.1)] {true} ≤
      𝒟[simulateQ lImpl
          ((simulateQ (implLocalBucketAuthGen
            (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
            Δcka qep fs.maxSkip tL false) A).run ({ g := gL0, h := hL0 }, none)) >>=
          fun x => simulateQ lImpl (match x.2.2 with
            | none => pure false
            | some tWin => pure (!x.2.1.abort && x.2.1.g.win &&
                authLosingConditionsAvoided (2 + Δcka) tL tWin x.2.1.g))] {true}
    rw [hP_ev, hL_ev]
    refine runPMainTop_le_runLMainTop cka prng fs Δcka qep tL A rfl ?_
    refine ⟨rfl, rfl, rfl, ?_, ?_, hft0, htop0, hb0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P
      cases P <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
          fun s hs => hσ_rel s (by
            dsimp only [gP0, mkParties] at hs
            cases σP <;> simp [resolveCorrRoot, hcr0] at hs ⊢
            exact hs)⟩
    · intro t'; rw [hcP0, hcL0]; exact Or.inl ⟨rfl, rfl⟩
    · intro P; simp [gL0]
    · intro pos hpos; cases hpos
    · intro r hr; cases hr
    · intro P _ hpos; simp [gL0] at hpos
    · intro r hr; cases hr
    · intro P; simp [gL0]
    · intro P hlt; simp [gL0] at hlt
    · dsimp only; rw [hcL0]
    · intro t' _; dsimp only; rw [hcL0]
    · intro P hpos; simp [gL0] at hpos
    · intro P Q _ _; cases P <;> cases Q <;> rfl
    · intro P _ _ his
      have his_σP : σP.isSome = true := by cases P <;> exact his
      by_contra hnot_lt
      have hnone_σP := hge0_none (Nat.le_of_not_lt hnot_lt)
      rw [hnone_σP] at his_σP; cases his_σP
    · intro _ _ _ _ _ hc; dsimp only at hc; rw [hcP0] at hc; cases hc
    · intro _ _ _ _ ⟨_, _, _, hc0⟩ _ _ _ _; dsimp only at hc0; rw [hcP0] at hc0; cases hc0
    · intro _ _ hcr; dsimp only at hcr; rw [hcr0] at hcr; cases hcr
    · intro P _ _; cases P <;> exact hsp_σ.symm

end Hop2cProofs

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2c
