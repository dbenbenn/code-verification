/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import VCVio.OracleComp.EvalDist.Measure

/-!
# Hop 2b (`ForgedHdr` Adjacent-Epoch Step) for `BucketPRNGAuth`

Proves `prng_branch_true_redPRNGAuthBucketHybridForgedHdr_le_succ_false` (no placeholders) against the
exact definitions in `Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth`.-/

open scoped MeasureTheory
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.SM (Pos Record authLosingConditionsAvoided healedBy lastLeakGuessAdmissible ltOpt)
open CryptoGames.SM.Construction (Header PartyState SchemeAdversary healEpoch mkParties realParty)
open CryptoGames.SM.Engine (Ctx EState HM Hooks VP abortE commitE deliverE injectE liftH vRecv vSend)

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bForgedHdr

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
  (postLeak bucketAuthCfg PRNGBucketAuthState resolveCorrRoot liftPBucketAuth
   lookupPRNGBucketAuthF rootPRNGBucketAuthHybrid hooksPRNGBucketAuthHybrid
   initPRNGBucketAuthHybrid PRNGBucketAuthEState isHonestHdrPRNGBucket
   hooksPRNGBucketAuthForgedHdr implPRNGBucketAuthGen runPRNGAuthBucketHybridGen
   redPRNGAuthBucketHybridForgedHdr)

section Hop2bForgedHdr

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

/-! ### 1. Generic `LeComp`, `resolveCorrRoot`, and `lookupPRNGBucketAuthF` Step Helpers -/

private theorem leComp_of_support_left {α β : Type} {R : α → β → Prop}
    (x : ProbComp α) (y : ProbComp β) (hx : ∀ a ∈ support x, ∀ b ∈ support y, R a b) :
    CryptoGames.SM.Construction.AuthL11.LeComp R x y := by
  induction x using OracleComp.inductionOn with
  | pure a => exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left a y (hx a (by simp))
  | query_bind t r ih =>
    intro F₁ F₂ hF
    rw [bind_assoc, ← OracleComp.evalDist_bind_const (query t) (y >>= F₂)]
    refine CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono (query t) _ _ fun u _ => ih u (fun a ha => hx a ?_) F₁ F₂ hF
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

private theorem resolveCorrRoot_of_none {h : PRNGBucketAuthState T Sig K I}
    (hcr : h.corrRoot = none) (ep : ℕ) (σv : Option Sig) :
    resolveCorrRoot h ep σv = σv := by
  cases σv <;> simp [resolveCorrRoot, hcr]

private theorem simulateQ_pImpl_liftPBucketAuth
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (x : CryptoGames.PRFPRNG.AdversaryComp Sig I K α)
    (h : PRNGBucketAuthState T Sig K I) :
    simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng) ((liftPBucketAuth (T := T) x).run h) =
      (simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng) x >>= fun a => pure (a, h)) := by
  simp [liftPBucketAuth, StateT.run_lift, map_eq_bind_pure_comp, simulateQ_bind]

private theorem sendsIn_succ_true_of_false (P : Party) (n : ℕ)
    (h : P.sendsIn n = false) : P.sendsIn (n + 1) = true := by
  cases P <;> simp [CryptoGames.Party.sendsIn] at h ⊢ <;> omega

private theorem ltOpt_mono {tL : Option ℕ} {c1 c2 : ℕ} (h : ltOpt tL c1 = true) (hle : c1 ≤ c2) :
    ltOpt tL c2 = true := by
  cases tL with
  | none => rfl
  | some l => simp only [ltOpt, decide_eq_true_eq] at h ⊢; omega

private theorem healedBy_some_le {cur Δ ep : ℕ}
    (h : healedBy (some cur) Δ ep = true) : cur + Δ ≤ ep := by
  simp only [healedBy, decide_eq_true_eq] at h
  exact h

private theorem leComp_lookupBucketAuthF_step
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t t0 : ℕ) (ik : I)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : CryptoGames.PRFPRNG.GameState Sig I K)
    (hne : t0 ≠ t)
    (hft : ∀ t', t' ≠ t → hL.fTable t' = hR.fTable t') :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (K × PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = r2.1.1 ∧
        r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
        r1.1.2.corrRoot = hL.corrRoot ∧ r2.1.2.corrRoot = hR.corrRoot ∧
        r1.2 = spL ∧ r2.2 = spR ∧
        (∀ t', t' ≠ t → r1.1.2.fTable t' = r2.1.2.fTable t') ∧
        r2.1.2.fTable t = hR.fTable t)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t0 ik).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t0 ik).run hR)).run spR) := by
  unfold lookupPRNGBucketAuthF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft t0 hne]
  cases hlk : (hR.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT,
      bind_assoc]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩
    · by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · simp [hne.symm]

private theorem leComp_challPrf_lookupAuthF
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t : ℕ) (ik : I)
    (hR : PRNGBucketAuthState T Sig K I) (spL spR : CryptoGames.PRFPRNG.GameState Sig I K)
    (hbL : spL.b = true)
    (htab : spL.table = hR.fTable t) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : Option (Sig × K) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1 = none ∨
        (r1.1 = some ((prng.up spL.σ ik).1, r2.1.1) ∧
          r2.1.2.cache = hR.cache ∧ r2.1.2.corrRoot = hR.corrRoot ∧ r2.2 = spR ∧
          r1.2.σ = spL.σ ∧ r1.2.b = true ∧
          (∀ t', t' ≠ t → r2.1.2.fTable t' = hR.fTable t') ∧
          r1.2.table = r2.1.2.fTable t))
      ((CryptoGames.PRFPRNG.challPrfImpl prng ik).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t ik).run hR)).run spR) := by
  rw [CryptoGames.SM.Construction.AuthL11.run_challPrfImpl]
  by_cases hbadL : (spL.corr || spL.prng) = true
  · simp only [hbadL, ↓reduceIte]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · unfold lookupPRNGBucketAuthF
    simp only [hbadL, hbL, Bool.false_eq_true, ↓reduceIte, htab,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases hlk : (hR.fTable t).lookup ik with
    | some k =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩)
    | none =>
      simp only [StateT.run_bind, simulateQ_bind,
        CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun k _ => ?_
      simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩)
      · simp [ht']
      · simp

/-! ### 2. Root, Cache, Virtual-Party Relations, `DoomedForgedHdr`, and `SyncStepAuth` -/

private def RelStepRoot (tH t : ℕ) (σR_sp : Sig) (e : ℕ) (rL rR : Option Sig) : Prop :=
  (e < tH ∧ ∃ σ, rL = some σ ∧ rR = some σ) ∨
  (tH ≤ e ∧ e < t ∧ rL = none ∧ rR = none) ∨
  (e = t ∧ rL = some σR_sp ∧ rR = none) ∨
  (t < e ∧ ∃ σ, rL = some σ ∧ rR = some σ)

private theorem RelStepRoot.change_σ {tH t : ℕ} {σ₁ σ₂ : Sig} {e : ℕ} {rL rR : Option Sig}
    (hne : e ≠ t) (h : RelStepRoot tH t σ₁ e rL rR) : RelStepRoot tH t σ₂ e rL rR := by
  rcases h with h1 | h2 | ⟨heq, _⟩ | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact False.elim (hne heq)
  · exact Or.inr (Or.inr (Or.inr h4))

private def RelCacheStep (tH t : ℕ) (σR_sp : Sig) (e : ℕ)
    (cL cR : Option (T × Option Sig × K)) : Prop :=
  (cL = none ∧ cR = none) ∨
  ∃ Tc rL rR k, cL = some (Tc, rL, k) ∧ cR = some (Tc, rR, k) ∧ RelStepRoot tH t σR_sp e rL rR

private theorem RelCacheStep.change_σ {tH t : ℕ} {σ₁ σ₂ : Sig} {e : ℕ}
    {cL cR : Option (T × Option Sig × K)}
    (hcond : e ≠ t ∨ (cL = none ∧ cR = none))
    (h : RelCacheStep tH t σ₁ e cL cR) : RelCacheStep tH t σ₂ e cL cR := by
  rcases hcond with hne | hnone
  · rcases h with h0 | ⟨Tc, rL, rR, k, hcL, hcR, hr⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Tc, rL, rR, k, hcL, hcR, hr.change_σ hne⟩
  · exact Or.inl hnone

private theorem isHonestHdrPRNGBucket_eq_of_relCacheStep [DecidableEq T]
    {tH t : ℕ} {σR_sp : Sig} {hL hR : PRNGBucketAuthState T Sig K I}
    (hdr : Header T)
    (hcache : RelCacheStep tH t σR_sp hdr.1 (hL.cache hdr.1) (hR.cache hdr.1)) :
    isHonestHdrPRNGBucket hL hdr = isHonestHdrPRNGBucket hR hdr := by
  rcases hdr with ⟨ep, _ | Tn⟩
  · rcases hcache with ⟨hcL, hcR⟩ | ⟨Tc, rL, rR, k, hcL, hcR, _⟩ <;>
      simp [isHonestHdrPRNGBucket, hcL, hcR]
  · rcases hcache with ⟨hcL, hcR⟩ | ⟨Tc, rL, rR, k, hcL, hcR, _⟩ <;>
      simp [isHonestHdrPRNGBucket, hcL, hcR]

private structure RelVPStep (tH t : ℕ) (σR_sp : Sig) (e : ℕ) (P : Party)
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

private theorem RelVPStep.change_σ {tH t : ℕ} {σ₁ σ₂ : Sig} {e : ℕ} {P : Party}
    {vpL vpR : VP Γ T (Option Sig) SS RS}
    (hne : e ≠ t) (h : RelVPStep tH t σ₁ e P vpL vpR) : RelVPStep tH t σ₂ e P vpL vpR :=
  ⟨h.id_L, h.tcur_L, h.id_R, h.tcur_R, h.γ_eq, h.Tcur_eq, h.vS_eq, h.vR_eq,
    h.root_rel.change_σ hne⟩

private def authOutForgedHdr [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δcka : ℕ) (tL : Option ℕ)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Bool :=
  match st.2 with
  | none => false
  | some tWin =>
    !st.1.abort && st.1.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin st.1.g

private def DoomedForgedHdr (tL : Option ℕ)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Prop :=
  st.1.abort = true ∨
  (st.1.g.win = true ∧ st.2 = none) ∨
  (st.1.g.win = true ∧ ∃ tWin cur,
    st.2 = some tWin ∧ cur ∈ st.1.g.leaks ∧ ltOpt tL cur = true ∧ cur < tWin) ∨
  (st.1.g.win = false ∧ st.2 = none ∧
    (∀ P, (st.1.g.st P).id = P ∧ (st.1.g.st P).tcur = st.1.g.epoch P) ∧
    (∀ r ∈ st.1.g.trans, r.ct.1.1 = r.pos.epoch) ∧
    ∃ cur, st.1.g.tL = some cur ∧ cur ∈ st.1.g.leaks ∧ ltOpt tL cur = true)

private theorem authOutForgedHdr_eq_false_of_doomed [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ}
    {st : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    (hd : DoomedForgedHdr tL st) :
    authOutForgedHdr Δcka tL st = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨_, hnone⟩ | ⟨_, tWin, cur, hsome, hmem, hlt, hcur_lt⟩ | ⟨_, hnone, _⟩
  · dsimp only at hab
    cases winEp <;> simp [authOutForgedHdr, hab]
  · dsimp only at hnone; subst hnone; rfl
  · dsimp only at hsome; subst hsome
    have hall_false :
        es.g.leaks.all (fun l => !(ltOpt tL l && decide (l < tWin))) = false := by
      rw [List.all_eq_false]
      exact ⟨cur, hmem, by simp [hlt, hcur_lt]⟩
    dsimp only [authOutForgedHdr, authLosingConditionsAvoided]
    rw [hall_false]
    simp
  · dsimp only at hnone; subst hnone; rfl

private structure SyncStepAuth
    (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spL : CryptoGames.PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spR : CryptoGames.PRFPRNG.GameState Sig I K) : Prop where
  abortL : esL.abort = false
  abortR : esR.abort = false
  g_eq : CryptoGames.SM.Construction.AuthL11.eraseSt esL.g = CryptoGames.SM.Construction.AuthL11.eraseSt esR.g
  no_postLeak : postLeak tL esR.g = false
  corrRootL : esL.h.corrRoot = none
  corrRootR : esR.h.corrRoot = none
  tL_mem : ∀ cur, esR.g.tL = some cur → cur ∈ esR.g.leaks
  vp_rel : ∀ P, RelVPStep (healEpoch tL) t spR.σ (esR.g.epoch P) P (esL.g.st P) (esR.g.st P)
  cache_rel : ∀ e, RelCacheStep (healEpoch tL) t spR.σ e (esL.h.cache e) (esR.h.cache e)
  cache_gt_max : ∀ e, max (esR.g.epoch .A) (esR.g.epoch .B) < e →
    esL.h.cache e = none ∧ esR.h.cache e = none
  fTable_ne : ∀ t0, t0 ≠ t → esL.h.fTable t0 = esR.h.fTable t0
  table_t : spL.table = esR.h.fTable t
  spL_b : spL.b = true
  spR_b : spR.b = false
  sp_σ_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL.σ = spR.σ
  spR_prf_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spR.prf = false
  spR_prng : spR.prng = false
  spR_corr : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) → spR.corr = false
  comp_inv : ∀ pos ∈ esR.g.comp, healedBy esR.g.tL (2 + Δcka) pos.epoch = false
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

/-! ### 3. Initial & Send `rootPRNGBucketAuthHybrid` Coupling (`pl = false`, `corrRoot = none`) -/

private theorem leComp_rootInit_step
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t : ℕ) (lam : I) (σ0 : Sig)
    (htH : healEpoch tL ≤ t) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ rL rR kVal,
          r1.1.1 = some (rL, kVal) ∧ r2.1.1 = some (rR, kVal) ∧
          RelStepRoot (healEpoch tL) t r2.2.σ 0 rL rR ∧
          r1.1.2.cache = (fun _ => none) ∧ r2.1.2.cache = (fun _ => none) ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (0 < t → r1.2.σ = r2.2.σ) ∧
          (0 < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ 0 → r2.2.corr = false))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t 0 false lam none).run
          ({} : PRNGBucketAuthState T Sig K I))).run { σ := σ0, b := true })
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (t + 1) 0 false lam none).run
          ({} : PRNGBucketAuthState T Sig K I))).run { σ := σ0, b := false }) := by
  have h0_nlt_t : ¬ (t < 0) := by omega
  have h0_nlt_t1 : ¬ (t + 1 < 0) := by omega
  have h0_ne_t1 : ¬ (0 = t + 1) := by omega
  have hcr_empty : ({} : PRNGBucketAuthState T Sig K I).corrRoot = none := rfl
  unfold rootPRNGBucketAuthHybrid
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, Option.isSome_none,
    Bool.or_self, Bool.false_eq_true,
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
        Option.isSome_none, Bool.false_and, Bool.false_eq_true,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrfQuery,
        CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery, CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind]
      refine (leComp_challPrf_lookupAuthF prng 0 lam {}
        { σ := σ0, b := true } { σ := (prng.up σ0 lam).1, b := false }
        rfl rfl).bind ?_
      rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
      rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
      · dsimp only at hnone; subst hnone
        simp only [StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
        subst hresL hspR1
        simp only [StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, none, kOut, rfl, rfl,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), rfl, hcR1, rfl, hcrR1,
          fun t0 ht0 => (hft1 t0 ht0).symm, htab1,
          hbL1, rfl, False.elim, False.elim, rfl, fun _ => rfl⟩)
    · have h0_lt_t : 0 < t := by omega
      simp only [h0_eq_t, healEpoch, Nat.lt_irrefl, decide_false, Bool.not_false, ↓reduceIte,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery, CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind]
      refine (leComp_lookupBucketAuthF_step prng t 0 lam {} {}
        { σ := (prng.up σ0 lam).1, b := true } { σ := (prng.up σ0 lam).1, b := false }
        h0_eq_t (fun _ _ => rfl)).bind ?_
      rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩
        ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
      dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
      subst hk_eq hspL1 hspR1
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
        Or.inr (Or.inl ⟨by simp, h0_lt_t, rfl, rfl⟩), hcL1, hcR1, hcrL1, hcrR1, hft1,
        htab1.symm, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩)
  · have h0_lt_tH : 0 < healEpoch tL := by
      by_contra hle; exact hge_tH (by simp [hle])
    have h0_ne_t : ¬ (0 = t) := by omega
    simp only [h0_ne_t, hge_tH, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
      CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery, CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_corrQuery,
      CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind, CryptoGames.SM.Construction.AuthL11.run_corrImpl,
      StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, some (prng.up σ0 lam).1,
      (prng.up σ0 lam).2, rfl, rfl, Or.inl ⟨h0_lt_tH, (prng.up σ0 lam).1, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl,
      fun hle => by omega⟩)

private theorem leComp_rootSend_step
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t eMax : ℕ) (ik0 : I)
    (rL0 rR0 : Option Sig)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : CryptoGames.PRFPRNG.GameState Sig I K)
    (htH : healEpoch tL ≤ t)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t spR.σ eMax rL0 rR0)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ rL' rR' kVal,
          r1.1.1 = some (rL', kVal) ∧ r2.1.1 = some (rR', kVal) ∧
          RelStepRoot (healEpoch tL) t r2.2.σ (eMax + 1) rL' rR' ∧
          (t ≤ eMax → r2.2.σ = spR.σ) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
          (eMax + 1 < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 → r2.2.corr = false))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t (eMax + 1) false ik0 rL0).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (t + 1) (eMax + 1) false ik0 rR0).run hR)).run spR) := by
  rcases spL with ⟨σL, bL, corrL, prngL, prfL, tabL⟩
  rcases spR with ⟨σR, bR, corrR, prngR, prfR, tabR⟩
  dsimp only at hr0 htab hbL hbR hσ_lt hprfR_lt hprngR hcorrR
  subst hbL hbR hprngR htab
  by_cases ht_lt : t < eMax + 1
  · by_cases heq_t1 : eMax + 1 = t + 1
    · have heMax_eq : eMax = t := by omega
      have hcorrR0 : corrR = false := hcorrR (by omega)
      subst hcorrR0
      have hrL0_eq : rL0 = some σR := by
        rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩
        · omega
        · omega
        · exact h
        · omega
      have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
      have his_tH_false : (tL.isSome && decide (t + 1 = healEpoch tL)) = false := by
        simp [show t + 1 ≠ healEpoch tL by omega]
      unfold rootPRNGBucketAuthHybrid
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hcrR, Option.isSome_none,
        Bool.or_self, Bool.false_eq_true, resolveCorrRoot_of_none hcrL,
        ht_lt, hnlt_t1, ↓reduceIte]
      simp only [heq_t1, ↓reduceIte]
      simp only [his_tH_false, Bool.false_eq_true, ↓reduceIte,
        hrL0_eq, StateT.run_pure, simulateQ_pure,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrfQuery, CryptoGames.SM.Construction.AuthL11.run_challPrfImpl,
        Bool.or_self, pure_bind]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σR ik0).1, some (prng.up σR ik0).1,
        (prng.up σR ik0).2, rfl, rfl,
        Or.inr (Or.inr (Or.inr ⟨by omega, (prng.up σR ik0).1, rfl, rfl⟩)),
        fun _ => rfl, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
        fun h => by omega, fun h => by omega, rfl, fun _ => rfl⟩)
    · have ht1_lt : t + 1 < eMax + 1 := by omega
      obtain ⟨σ0, hrL0_eq, hrR0_eq⟩ : ∃ σ0, rL0 = some σ0 ∧ rR0 = some σ0 := by
        rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · omega
        · omega
        · omega
        · exact h
      unfold rootPRNGBucketAuthHybrid
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind,
        resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR,
        ht_lt, ht1_lt, ↓reduceIte, hrL0_eq, hrR0_eq, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, some (prng.up σ0 ik0).1,
        (prng.up σ0 ik0).2, rfl, rfl,
        Or.inr (Or.inr (Or.inr ⟨ht_lt, (prng.up σ0 ik0).1, rfl, rfl⟩)),
        fun _ => rfl, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
        fun h => by omega, fun h => by omega, rfl,
        fun _ => hcorrR (by omega)⟩)
  · have heMax_lt_t : eMax < t := by omega
    have hprfR := hprfR_lt heMax_lt_t
    subst hprfR
    have hσ_eq := hσ_lt heMax_lt_t
    subst hσ_eq
    have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
    have hne_t1 : ¬ (eMax + 1 = t + 1) := by omega
    unfold rootPRNGBucketAuthHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hcrL, hcrR, Option.isSome_none,
      Bool.or_self, Bool.false_eq_true,
      ht_lt, hnlt_t1, hne_t1, ↓reduceIte]
    by_cases heq_t : eMax + 1 = t
    · have hge_tH : (!(eMax + 1 < healEpoch tL)) = true := by simp; omega
      simp only [heq_t, ↓reduceIte]
      have hge_t : (!(t < healEpoch tL)) = true := by rw [← heq_t]; exact hge_tH
      have his_eq : (tL.isSome && decide (t = healEpoch tL)) =
          (tL.isSome && decide (eMax + 1 = healEpoch tL)) := by rw [heq_t]
      by_cases his_tH : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = true
      · have his_t : (tL.isSome && decide (t = healEpoch tL)) = true := his_eq.trans his_tH
        simp only [hge_t, his_t, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrngQuery,
          CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery,
          CryptoGames.SM.Construction.AuthL11.run_challPrngImpl_none, CryptoGames.SM.Construction.AuthL11.run_processImpl_none,
          Bool.false_eq_true, pure_bind]
        refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        cases prfL
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc,
            StateT.run_bind, CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
          simp only [pure_bind, bind_assoc, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftPBucketAuth, CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_corrQuery,
            CryptoGames.SM.Construction.AuthL11.run_corrImpl, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL Ir).1, none, kRand, rfl, rfl,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
            fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
            fun h => by omega, fun h => by omega, rfl, fun _ => rfl⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have his_t_false : (tL.isSome && decide (t = healEpoch tL)) = false :=
          his_eq.trans (Bool.eq_false_iff.mpr his_tH)
        simp only [hge_t, his_t_false, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrfQuery,
          CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery, CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind]
        refine (leComp_challPrf_lookupAuthF prng t ik0 hR
          { σ := σL, b := true, corr := corrL, prng := prngL, prf := prfL, table := hR.fTable t }
          { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false, prf := false,
            table := tabR }
          rfl rfl).bind ?_
        rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
        rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
          subst hresL hspR1
          simp only [StateT.run_pure, simulateQ_pure]
          have hcorrR0 : corrR = false := by
            apply hcorrR
            cases tL with
            | none => simp [healEpoch]
            | some l =>
              simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at his_tH
              omega
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, none, kOut, rfl, rfl,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
            fun h => by omega, rfl, hcR1, hcrL, hcrR1.trans hcrR,
            fun t0 ht0 => (hft t0 ht0).trans (hft1 t0 ht0).symm, htab1, hbL1, rfl,
            fun h => by omega, fun h => by omega, rfl, fun _ => hcorrR0⟩)
    · have heMax1_lt_t : eMax + 1 < t := by omega
      simp only [heq_t, ↓reduceIte]
      by_cases hge_tH : (!(eMax + 1 < healEpoch tL)) = true
      · simp only [hge_tH, ↓reduceIte]
        by_cases his_tH : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = true
        · simp only [his_tH, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
            CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery,
            CryptoGames.SM.Construction.AuthL11.run_processImpl_none, Bool.false_eq_true, pure_bind]
          cases prfL
          · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
            refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
            simp only [pure_bind, bind_assoc, StateT.run_bind, simulateQ_bind,
              CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT]
            refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
            simp only [StateT.run_pure, simulateQ_pure]
            have hge_tH_prop : healEpoch tL ≤ eMax + 1 := by
              simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH; omega
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨none, none, kRand, rfl, rfl,
              Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
              fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
              fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [his_tH, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
            CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery, CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind]
          cases prfL
          · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind, simulateQ_bind]
            refine (leComp_lookupBucketAuthF_step prng t (eMax + 1) ik0 hL hR
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
            have hcorrR0 : corrR = false := by
              apply hcorrR
              simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH
              cases tL with
              | none => simp [healEpoch]
              | some l =>
                simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at his_tH
                omega
            have hge_tH_prop : healEpoch tL ≤ eMax + 1 := by
              simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH; omega
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
              Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
              fun h => by omega, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR,
              hft1, htab1.symm, rfl, rfl,
              fun _ => rfl, fun _ => rfl, rfl, fun _ => hcorrR0⟩)
          · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have hlt_tH : eMax + 1 < healEpoch tL := by
          by_contra hle; exact hge_tH (by simp [hle])
        simp only [hge_tH, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_processQuery,
          CryptoGames.SM.Construction.AuthL11.run_processImpl_some, pure_bind]
        cases prfL
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc,
            StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftPBucketAuth,
            CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_corrQuery, CryptoGames.SM.Construction.AuthL11.run_corrImpl,
            StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, some (prng.up σL ik0).1,
            (prng.up σL ik0).2, rfl, rfl,
            Or.inl ⟨hlt_tH, (prng.up σL ik0).1, rfl, rfl⟩,
            fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
            fun _ => rfl, fun _ => rfl, rfl, fun h => by omega⟩)
        · simp only [↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

/-! ### 4. Support Helpers, `hooksPRNGBucketAuthForgedHdr` Step Couplings, & `SyncStepAuth` -/

private theorem run_commitE_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    (commitE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid,
    CryptoGames.SM.Construction.AuthL11.run_liftH, _root_.CryptoGames.SM.GameState.accept]

private theorem eraseSt_postLeak {St₁ St₂ Msg C : Type}
    {g₁ : _root_.CryptoGames.SM.GameState St₁ Msg C}
    {g₂ : _root_.CryptoGames.SM.GameState St₂ Msg C}
    (he : CryptoGames.SM.Construction.AuthL11.eraseSt g₁ = CryptoGames.SM.Construction.AuthL11.eraseSt g₂) (tL : Option ℕ) :
    postLeak tL g₁ = postLeak tL g₂ := by
  have htL_eq : g₁.tL = g₂.tL := congrArg _root_.CryptoGames.SM.GameState.tL he
  simp only [postLeak, htL_eq]

private theorem tL_mem_epMgmt {St Msg C : Type}
    {g s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hmem : ∀ cur, g.tL = some cur → cur ∈ g.leaks)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    ∀ cur, s₁.tL = some cur → cur ∈ s₁.leaks := by
  unfold _root_.CryptoGames.SM.GameState.epMgmt at hep
  split at hep
  · split at hep
    · cases hep
    · simp only [Option.some.injEq] at hep; subst hep
      dsimp only
      split
      · intro cur hcur
        simp only [_root_.CryptoGames.SM.GameState.leak, Option.some.injEq] at hcur ⊢
        subst hcur
        exact List.mem_cons_self
      · exact hmem
  · split at hep
    · cases hep
    · simp only [Option.some.injEq] at hep; subst hep; exact hmem

private theorem ex_tL_of_postLeak {St Msg C : Type}
    {s : _root_.CryptoGames.SM.GameState St Msg C} {tL : Option ℕ}
    (hmem : ∀ cur, s.tL = some cur → cur ∈ s.leaks)
    (hpl : postLeak tL s = true) :
    ∃ cur, s.tL = some cur ∧ cur ∈ s.leaks ∧ ltOpt tL cur = true := by
  cases htL : s.tL with
  | none => simp [postLeak, htL] at hpl
  | some cur =>
    simp only [postLeak, htL] at hpl
    exact ⟨cur, rfl, hmem cur htL, hpl⟩

private theorem support_vSend_props [DecidableEq I] [Inhabited E] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (ep : ℕ) (m : M) (r_coins : Option CCoins)
    (h0 : PRNGBucketAuthState T Sig K I) (sp0 : CryptoGames.PRFPRNG.GameState Sig I K)
    {r : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
          PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {ct : Header T × E}
    (hid : vp.id = P) (htcur : vp.tcur = ep)
    (hr : r ∈ support ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
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

private theorem support_vRecv_props [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (vp : VP Γ T (Option Sig) SS RS)
    (ep : ℕ) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h0 : PRNGBucketAuthState T Sig K I) (sp0 : CryptoGames.PRFPRNG.GameState Sig I K)
    {r : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
          PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K}
    {vp' : VP Γ T (Option Sig) SS RS} {t' i' : ℕ} {m' : M}
    (hid : vp.id = P) (htcur : vp.tcur = ep)
    (hr : r ∈ support ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
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

private theorem leComp_startSend_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {r_coins : Option CCoins}
    {hL hR : PRNGBucketAuthState T Sig K I} {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (htH : healEpoch tL ≤ t)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t spR.σ eMax P vpL vpR)
    (hcache : ∀ e', RelCacheStep (healEpoch tL) t spR.σ e' (hL.cache e') (hR.cache e'))
    (hcache_gt : ∀ e', eMax < e' → hL.cache e' = none ∧ hR.cache e' = none)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) ×
                  CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        ∃ γ' T' rL' rR' kVal,
          r1.1.1 = some (γ', T', rL', fs.initSender kVal) ∧
          r2.1.1 = some (γ', T', rR', fs.initSender kVal) ∧
          RelStepRoot (healEpoch tL) t r2.2.σ (eMax + 1) rL' rR' ∧
          (t ≤ eMax → r2.2.σ = spR.σ) ∧
          (∀ e', RelCacheStep (healEpoch tL) t r2.2.σ e' (r1.1.2.cache e') (r2.1.2.cache e')) ∧
          (∀ e', eMax + 1 < e' → r1.1.2.cache e' = none ∧ r2.1.2.cache e' = none) ∧
          r2.1.2.cache (eMax + 1) = some (T', rR', kVal) ∧
          (∀ e', e' ≠ eMax + 1 → r2.1.2.cache e' = hR.cache e') ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
          (eMax + 1 < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 → r2.2.corr = false))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t).startSend
          ctxL P (eMax + 1) vpL.γ vpL.root r_coins).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (t + 1)).startSend
          ctxR P (eMax + 1) vpR.γ vpR.root r_coins).run hR)).run spR) := by
  have hbody : ∀ (coins : CCoins),
      CryptoGames.SM.Construction.AuthL11.LeComp
        (fun (r1 : (Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) ×
                    CryptoGames.PRFPRNG.GameState Sig I K)
             (r2 : (Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) ×
                    CryptoGames.PRFPRNG.GameState Sig I K) =>
          r1.1.1 = none ∨
          ∃ γ' T' rL' rR' kVal,
            r1.1.1 = some (γ', T', rL', fs.initSender kVal) ∧
            r2.1.1 = some (γ', T', rR', fs.initSender kVal) ∧
            RelStepRoot (healEpoch tL) t r2.2.σ (eMax + 1) rL' rR' ∧
            (t ≤ eMax → r2.2.σ = spR.σ) ∧
            (∀ e', RelCacheStep (healEpoch tL) t r2.2.σ e' (r1.1.2.cache e') (r2.1.2.cache e')) ∧
            (∀ e', eMax + 1 < e' → r1.1.2.cache e' = none ∧ r2.1.2.cache e' = none) ∧
            r2.1.2.cache (eMax + 1) = some (T', rR', kVal) ∧
            (∀ e', e' ≠ eMax + 1 → r2.1.2.cache e' = hR.cache e') ∧
            r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
            (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
            r1.2.table = r2.1.2.fTable t ∧
            r1.2.b = true ∧ r2.2.b = false ∧
            (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
            (eMax + 1 < t → r2.2.prf = false) ∧
            r2.2.prng = false ∧
            (healEpoch tL ≤ eMax + 1 → r2.2.corr = false))
        ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
          ((do
            let c := cka.send vpL.γ coins
            match ← rootPRNGBucketAuthHybrid prng tL t (eMax + 1) false c.2.2 vpL.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketAuthState T Sig K I =>
                { s with cache := Function.update s.cache (eMax + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hL)).run spL)
        ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
          ((do
            let c := cka.send vpR.γ coins
            match ← rootPRNGBucketAuthHybrid prng tL (t + 1) (eMax + 1) false c.2.2 vpR.root with
            | none => return none
            | some (σ', kVal) =>
              modify fun s : PRNGBucketAuthState T Sig K I =>
                { s with cache := Function.update s.cache (eMax + 1) (some (c.2.1, σ', kVal)) }
              return some (c.1, c.2.1, σ', fs.initSender kVal)).run hR)).run spR) := by
    intro coins
    rw [hvp.γ_eq]
    simp only [StateT.run_bind, simulateQ_bind]
    refine (leComp_rootSend_step prng tL t eMax (cka.send vpR.γ coins).2.2 vpL.root vpR.root
      hL hR spL spR htH hcrL hcrR hvp.root_rel hft htab hbL hbR
      hσ_lt hprfR_lt hprngR hcorrR).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hroot
    rcases hroot with hnone |
      ⟨rL', rR', kVal, hresL, hresR, hr', hσR_ge, hcL1, hcR1, hcrL1, hcrR1,
        hft1, htab1, hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1⟩
    · dsimp only at hnone; subst hnone
      simp only [StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hresL hresR
      subst hresL hresR
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨(cka.send vpR.γ coins).1, (cka.send vpR.γ coins).2.1,
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
            · rw [hσR_ge hle]; exact hcache e'
            · exact (hcache e').change_σ (Or.inr (hcache_gt e' (by omega)))
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
    simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, hplL, hplR, pure_bind]
    exact hbody coins
  | none =>
    unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid
    dsimp only
    rw [hplL, hplR,
      StateT.run_bind, simulateQ_bind, StateT.run_bind,
      CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc,
      StateT.run_bind, simulateQ_bind, StateT.run_bind,
      CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT, bind_assoc]
    refine CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    simp only [pure_bind]
    exact hbody coins

private theorem leComp_vSend_step
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t e eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {m : M} {r_coins : Option CCoins}
    {hL hR : PRNGBucketAuthState T Sig K I} {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (htH : healEpoch tL ≤ t)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t spR.σ e P vpL vpR)
    (hcache : ∀ e', RelCacheStep (healEpoch tL) t spR.σ e' (hL.cache e') (hR.cache e'))
    (hcache_gt : ∀ e', eMax < e' → hL.cache e' = none ∧ hR.cache e' = none)
    (he_eq_max : P.sendsIn (e + 1) = true → e = eMax)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        let e' := if P.sendsIn (e + 1) then e + 1 else e
        r1.1.1 = none ∨
        ∃ vpL' vpR' c,
          r1.1.1 = some (vpL', c) ∧
          r2.1.1 = some (vpR', c) ∧
          c.1 = (e', vpR'.curCkaMsg) ∧
          RelVPStep (healEpoch tL) t r2.2.σ e' P vpL' vpR' ∧
          (∀ e'', RelCacheStep (healEpoch tL) t r2.2.σ e'' (r1.1.2.cache e'') (r2.1.2.cache e'')) ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧
          r2.2.prng = false ∧
          (P.sendsIn (e + 1) = true →
            (t ≤ eMax → r2.2.σ = spR.σ) ∧
            (∀ e'', eMax + 1 < e'' → r1.1.2.cache e'' = none ∧ r2.1.2.cache e'' = none) ∧
            (∃ T' rR' k, vpR'.curCkaMsg = some T' ∧ r2.1.2.cache (e + 1) = some (T', rR', k)) ∧
            (∀ e'', e'' ≠ e + 1 → r2.1.2.cache e'' = hR.cache e'') ∧
            (eMax + 1 < t → r1.2.σ = r2.2.σ) ∧
            (eMax + 1 < t → r2.2.prf = false) ∧
            (healEpoch tL ≤ eMax + 1 → r2.2.corr = false)) ∧
          (P.sendsIn (e + 1) = false →
            r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR ∧
            vpR'.curCkaMsg = vpR.curCkaMsg))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t)
          ctxL P vpL m none r_coins).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vSend (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (t + 1))
          ctxR P vpR m none r_coins).run hR)).run spR) := by
  unfold vSend
  rw [hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R]
  by_cases hsends : P.sendsIn (e + 1) = true
  · have he_max := he_eq_max hsends
    subst he_max
    simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind]
    refine (leComp_startSend_step cka prng fs Δcka qep tL t e htH hplL hplR hcrL hcrR
      hvp hcache hcache_gt hft htab hbL hbR hσ_lt hprfR_lt hprngR hcorrR).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hss
    rcases hss with hnone |
      ⟨γ', T', rL', rR', kVal, hL_eq, hR_eq, hr', hσR_ge, hc_rel, hc_gt, hc_self, hc_other,
        hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hL_eq hR_eq; subst hL_eq hR_eq
      simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, pure_bind,
        StateT.run_pure, simulateQ_pure]
      refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, hr'⟩, hc_rel, hcrL1, hcrR1,
        hft1, htab1, hbL1, hbR1, hprng1,
        (fun _ => ⟨hσR_ge, hc_gt, ⟨T', rR', kVal, rfl, hc_self⟩, hc_other, hσ1, hprf1, hcorr1⟩),
        (fun hns => by cases hns)⟩)
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rcases hvSR : vpR.vS with _ | ss
    · have hvSL : vpL.vS = none := hvp.vS_eq.trans hvSR
      simp only [hvSL, hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl, hvp, hcache, hcrL, hcrR,
        hft, htab, hbL, hbR, hprngR, False.elim, (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩)
    · have hvSL : vpL.vS = some ss := hvp.vS_eq.trans hvSR
      simp only [hvSL, hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid,
        hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, pure_bind, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, rfl,
        ⟨hvp.id_L, rfl, hvp.id_R, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_rel⟩, hcache,
        hcrL, hcrR, hft, htab, hbL, hbR, hprngR, False.elim,
        (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩)

private theorem leComp_vRecv_cached_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {ep : ℕ} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {c : Header T × E} {rec : Option (Record M (Header T × E))}
    {hL hR : PRNGBucketAuthState T Sig K I} {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t spR.σ ep P vpL vpR)
    (hcache : ∀ e, RelCacheStep (healEpoch tL) t spR.σ e (hL.cache e) (hR.cache e))
    (hc_hit : c.1.1 = ep + 1 → ∀ tn0, c.1.2 = some tn0 →
      ∃ rR kc, hR.cache (ep + 1) = some (tn0, rR, kc)) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR) ∨
        ∃ vpL' vpR' i' m',
          r1.1.1 = some (some (vpL', c.1.1, i', m')) ∧
          r2.1.1 = some (some (vpR', c.1.1, i', m')) ∧
          c.1.1 ≤ ep + 1 ∧ P.sendsIn c.1.1 = false ∧
          RelVPStep (healEpoch tL) t spR.σ (max ep c.1.1) P vpL' vpR' ∧
          r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR ∧
          (c.1.1 ≤ ep → vpR'.curCkaMsg = vpR.curCkaMsg))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t)
          ctxL P vpL c rec).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (t + 1))
          ctxR P vpR c rec).run hR)).run spR) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
  by_cases hrej : (P.sendsIn c.1.1 || decide (ep + 1 < c.1.1)) = true
  · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
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
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | some tn0 =>
        obtain ⟨rR, kc, hcR_eq⟩ := hc_hit hnew tn0 htn0
        obtain ⟨Tc, rL, rR', kc', hcL_eq, hcR_eq', hr_rel⟩ :
            ∃ Tc rL rR' kc', hL.cache (ep + 1) = some (Tc, rL, kc') ∧
              hR.cache (ep + 1) = some (Tc, rR', kc') ∧
              RelStepRoot (healEpoch tL) t spR.σ (ep + 1) rL rR' := by
          rcases hcache (ep + 1) with ⟨_, hnone⟩ | hsome
          · rw [hcR_eq] at hnone; cases hnone
          · exact hsome
        rw [hcR_eq] at hcR_eq'
        cases hcR_eq'
        have hns_ep1 : P.sendsIn (ep + 1) = false := hnew ▸ hns
        simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid,
          StateT.run_bind, StateT.run_get, pure_bind, hcL_eq, hcR_eq, ↓reduceIte,
          resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR,
          StateT.run_pure, hvp.γ_eq, Function.update_self]
        cases hfs : fs.receive (fs.initReceiver kc) c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_ep1, ?_,
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
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | some v =>
        simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, pure_bind]
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, rfl, rfl, fun _ => rfl⟩)
          rw [hmax]
          refine ⟨hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            fun t' => ?_, hvp.root_rel⟩
          by_cases ht' : t' = c.1.1
          · subst ht'; simp
          · simp [Function.update_of_ne ht', hvp.vR_eq t']

private def startRecvForgedMiss [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t t0 : ℕ) (pl : Bool)
    (γ0 : Γ) (σv0 : Option Sig) (tn0 : T) (h0 : PRNGBucketAuthState T Sig K I) :
    HM (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      (Option (Option (Γ × Option Sig × RS))) := do
  let tH := healEpoch tL
  if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 then
    if tL.isSome && t0 = tH then
      return none
    else if pl || h0.corrRoot.isSome || t < t0 then
      match resolveCorrRoot h0 (t0 - 1) σv0 with
      | none => return none
      | some σ =>
        let kk := cka.receive γ0 tn0
        let p := prng.up σ kk.2
        return some (some (kk.1, some p.1, fs.initReceiver p.2))
    else if t0 = t then
      let kk := cka.receive γ0 tn0
      match ← liftPBucketAuth (CryptoGames.PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
      | none => return none
      | some (σOut, kOut) =>
        return some (some (kk.1, some σOut, fs.initReceiver kOut))
    else if !(t0 < tH) then
      let kk := cka.receive γ0 tn0
      let kOut ← lookupPRNGBucketAuthF t0 kk.2
      return some (some (kk.1, none, fs.initReceiver kOut))
    else
      return some none
  else
    return some none

private theorem startRecv_forgedHdr_run_eq_miss
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (γ0 : Γ) (σv0 : Option Sig) (tn0 : T) (h0 : PRNGBucketAuthState T Sig K I)
    (hmiss : ∀ σc kVal, h0.cache t0 ≠ some (tn0, σc, kVal)) :
    (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t).startRecv
      ctx P t0 γ0 σv0 tn0).run h0) =
    ((startRecvForgedMiss cka prng fs Δcka qep tL t t0 (postLeak tL ctx) γ0 σv0 tn0 h0).run h0) := by
  unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid startRecvForgedMiss
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hc : h0.cache t0 with
  | none => rfl
  | some tup =>
    rcases tup with ⟨Tc, σc, kVal⟩
    have hne : Tc ≠ tn0 := fun heq => hmiss σc kVal (heq ▸ hc)
    simp only [hne, ↓reduceIte]
    rfl

private theorem leComp_startRecv_inject_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t ep eMax : ℕ)
    (ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (γ0 : Γ) (rL0 rR0 : Option Sig) (tn0 : T)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : CryptoGames.PRFPRNG.GameState Sig I K)
    (hep_le : ep ≤ eMax)
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t spR.σ ep rL0 rR0)
    (hc0 : RelCacheStep (healEpoch tL) t spR.σ (ep + 1) (hL.cache (ep + 1)) (hR.cache (ep + 1)))
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Option (Γ × Option Sig × RS)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (Γ × Option Sig × RS)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax → r2.2.corr = false)) ∨
        (∃ γ' rL' rR' rs,
          r1.1.1 = some (some (γ', rL', rs)) ∧
          r2.1.1 = some (some (γ', rR', rs)) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax → r2.2.corr = false)))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t).startRecv
          ctxL P (ep + 1) γ0 rL0 tn0).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        (((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (t + 1)).startRecv
          ctxR P (ep + 1) γ0 rR0 tn0).run hR)).run spR) := by
  by_cases hhit : ∃ Tc rL' rR' kVal,
      hL.cache (ep + 1) = some (Tc, rL', kVal) ∧
      hR.cache (ep + 1) = some (Tc, rR', kVal) ∧ Tc = tn0
  · obtain ⟨Tc, rL', rR', kVal, hcL, hcR, rfl⟩ := hhit
    unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL, hcR, ↓reduceIte,
      resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR,
      StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 Tc).1,
      rL', rR', fs.initReceiver kVal,
      rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
  · have hmissL : ∀ σc kVal, hL.cache (ep + 1) ≠ some (tn0, σc, kVal) := by
      intro σc kVal heq
      rcases hc0 with ⟨hcL, _⟩ | ⟨Tc, rL', rR', kVal', hcL, hcR, _⟩
      · simp [hcL] at heq
      · rw [hcL] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        exact hhit ⟨Tc, rL', rR', kVal', hcL, hcR, heq.1⟩
    have hmissR : ∀ σc kVal, hR.cache (ep + 1) ≠ some (tn0, σc, kVal) := by
      intro σc kVal heq
      rcases hc0 with ⟨_, hcR⟩ | ⟨Tc, rL', rR', kVal', hcL, hcR, _⟩
      · simp [hcR] at heq
      · rw [hcR] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        exact hhit ⟨Tc, rL', rR', kVal', hcL, hcR, heq.1⟩
    rw [startRecv_forgedHdr_run_eq_miss cka prng fs Δcka qep tL t (ep + 1) ctxL P γ0 rL0 tn0 hL hmissL,
        startRecv_forgedHdr_run_eq_miss cka prng fs Δcka qep tL (t + 1) (ep + 1) ctxR P γ0 rR0 tn0 hR hmissR,
        hplL, hplR]
    unfold startRecvForgedMiss
    dsimp only
    by_cases hcond : (!(decide (qep + 1 < ep + 1)) &&
        lastLeakGuessAdmissible (2 + Δcka) tL (ep + 1)) = true
    · simp only [hcond, ↓reduceIte]
      by_cases his_tH : (tL.isSome && decide (ep + 1 = healEpoch tL)) = true
      · simp only [his_tH, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · have hge_tH : (!(ep + 1 < healEpoch tL)) = true := by
          simp only [Bool.and_eq_true] at hcond
          have hadm := hcond.2
          cases tL with
          | none => simp [healEpoch]
          | some l =>
            simp [lastLeakGuessAdmissible, healedBy, healEpoch] at hadm ⊢
            omega
        have htH_lt : healEpoch tL < ep + 1 := by
          cases tL with
          | none => simp [healEpoch]
          | some l =>
            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH
            simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at his_tH
            omega
        simp only [his_tH, hcrL, hcrR, Option.isSome_none, Bool.or_self, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte]
        by_cases ht_lt : t < ep + 1
        · by_cases heq_t1 : ep + 1 = t + 1
          · have hnlt_t1 : ¬ (t + 1 < ep + 1) := by omega
            have hrL0_eq : rL0 = some spR.σ := by
              rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩
              · omega
              · omega
              · exact h
              · omega
            have hcorrR0 : spR.corr = false := hcorrR (by omega)
            simp only [ht_lt, hnlt_t1, decide_true, decide_false, Bool.false_eq_true,
              resolveCorrRoot_of_none hcrL, ↓reduceIte]
            simp only [heq_t1, ↓reduceIte, hrL0_eq,
              StateT.run_pure, simulateQ_pure,
              StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
              CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrfQuery, CryptoGames.SM.Construction.AuthL11.run_challPrfImpl,
              hcorrR0, hprngR, hbR, Bool.or_self, pure_bind]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
              some (prng.up spR.σ (cka.receive γ0 tn0).2).1,
              some (prng.up spR.σ (cka.receive γ0 tn0).2).1,
              fs.initReceiver (prng.up spR.σ (cka.receive γ0 tn0).2).2,
              rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, rfl, rfl,
              fun h => by omega, fun h => by omega, rfl, fun _ => rfl⟩))
          · have ht1_lt : t + 1 < ep + 1 := by omega
            obtain ⟨σ0, hrL0_eq, hrR0_eq⟩ : ∃ σ0, rL0 = some σ0 ∧ rR0 = some σ0 := by
              rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
              · omega
              · omega
              · omega
              · exact h
            simp only [ht_lt, ht1_lt, decide_true,
              resolveCorrRoot_of_none hcrL, resolveCorrRoot_of_none hcrR,
              ↓reduceIte, hrL0_eq, hrR0_eq, StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
              some (prng.up σ0 (cka.receive γ0 tn0).2).1,
              some (prng.up σ0 (cka.receive γ0 tn0).2).1,
              fs.initReceiver (prng.up σ0 (cka.receive γ0 tn0).2).2,
              rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl,
              fun h => by omega, fun h => by omega, hprngR, hcorrR⟩))
        · have hnlt_t1 : ¬ (t + 1 < ep + 1) := by omega
          have hne_t1 : ¬ (ep + 1 = t + 1) := by omega
          simp only [ht_lt, hnlt_t1, hne_t1, decide_false, Bool.false_eq_true, ↓reduceIte]
          by_cases heq_t : ep + 1 = t
          · simp only [heq_t, ↓reduceIte]
            have hge_t : (!(t < healEpoch tL)) = true := by rw [← heq_t]; exact hge_tH
            simp only [hge_t, ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc,
              simulateQ_pImpl_liftPBucketAuth, CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_challPrfQuery, pure_bind]
            refine (leComp_challPrf_lookupAuthF prng t (cka.receive γ0 tn0).2 hR spL spR
              hbL htab).bind ?_
            rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
            rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
            · dsimp only at hnone; subst hnone
              simp only [StateT.run_pure, simulateQ_pure]
              exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
            · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
              subst hresL hspR1
              simp only [StateT.run_pure, simulateQ_pure]
              exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
                some (prng.up spL.σ (cka.receive γ0 tn0).2).1, none, fs.initReceiver kOut,
                rfl, rfl, rfl, hcR1, hcrL, hcrR1.trans hcrR,
                fun t0 ht0 => (hft t0 ht0).trans (hft1 t0 ht0).symm, htab1, hbL1, hbR, rfl,
                fun h => (hσL1.trans (hσ_lt h)), hprfR_lt, hprngR, hcorrR⟩))
          · simp only [heq_t, hge_tH, ↓reduceIte,
              StateT.run_bind, simulateQ_bind]
            refine (leComp_lookupBucketAuthF_step prng t (ep + 1) (cka.receive γ0 tn0).2 hL hR spL spR
              heq_t hft).bind ?_
            rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩
              ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
            dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
            subst hk_eq hspL1 hspR1
            simp only [StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨(cka.receive γ0 tn0).1,
              none, none, fs.initReceiver kL,
              rfl, rfl, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR,
              hft1, by rw [htab1, ← htab],
              hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
        hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))

private theorem leComp_vRecv_inject_step
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t eMax : ℕ)
    {ctxL ctxR : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {ep : ℕ} {vpL vpR : VP Γ T (Option Sig) SS RS}
    {c : Header T × E}
    {hL hR : PRNGBucketAuthState T Sig K I} {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hplL : postLeak tL ctxL = false) (hplR : postLeak tL ctxR = false)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hvp : RelVPStep (healEpoch tL) t spR.σ ep P vpL vpR)
    (hcache : ∀ e, RelCacheStep (healEpoch tL) t spR.σ e (hL.cache e) (hR.cache e))
    (heMax : ep ≤ eMax)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfR_lt : eMax < t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    CryptoGames.SM.Construction.AuthL11.LeComp
      (fun (r1 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) ×
                  PRNGBucketAuthState T Sig K I) × CryptoGames.PRFPRNG.GameState Sig I K) =>
        r1.1.1 = none ∨
        (r1.1.1 = some none ∧ r2.1.1 = some none ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          r1.1.2.corrRoot = none ∧ r2.1.2.corrRoot = none ∧
          (∀ t0, t0 ≠ t → r1.1.2.fTable t0 = r2.1.2.fTable t0) ∧
          r1.2.table = r2.1.2.fTable t ∧
          r1.2.b = true ∧ r2.2.b = false ∧ r2.2.σ = spR.σ ∧
          (eMax < t → r1.2.σ = r2.2.σ) ∧
          (eMax < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax → r2.2.corr = false)) ∨
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
          (eMax < t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax → r2.2.corr = false) ∧
          (c.1.1 ≤ ep →
            RelVPStep (healEpoch tL) t spR.σ ep P vpL' vpR' ∧
            vpR'.curCkaMsg = vpR.curCkaMsg ∧
            r1.1.2 = hL ∧ r2.1.2 = hR ∧ r1.2 = spL ∧ r2.2 = spR))
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t)
          ctxL P vpL c none).run hL)).run spL)
      ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
        ((vRecv (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (t + 1))
          ctxR P vpR c none).run hR)).run spR) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
  by_cases hrej : (P.sendsIn c.1.1 || decide (ep + 1 < c.1.1)) = true
  · simp only [hrej, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
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
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
          hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
      | some tn0 =>
        simp only [StateT.run_bind, simulateQ_bind]
        rw [hvp.γ_eq]
        refine (leComp_startRecv_inject_step cka prng fs Δcka qep tL t ep eMax
          ctxL ctxR P vpR.γ vpL.root vpR.root tn0 hL hR spL spR
          heMax hplL hplR hcrL hcrR hvp.root_rel (hcache (ep + 1)) hft htab hbL hbR
          hσ_lt hprfR_lt hprngR hcorrR).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hsr
        rcases hsr with hnone |
          ⟨hL_none, hR_none, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
            hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩ |
          ⟨γ', rL', rR', rs, hL_some, hR_some, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
            hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hL_none hR_none; subst hL_none hR_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcL1, hcR1, hcrL1, hcrR1,
            hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩))
        · dsimp only at hL_some hR_some; subst hL_some hR_some
          have hns_ep1 : P.sendsIn (ep + 1) = false := hnew ▸ hns
          simp only [pure_bind, Function.update_self, hooksPRNGBucketAuthForgedHdr,
            hooksPRNGBucketAuthHybrid]
          cases hfs : fs.receive rs c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, hcL1, hcR1, hcrL1, hcrR1,
              hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩))
          | some res =>
            rcases res with ⟨v', i', m'⟩
            simp only [StateT.run_pure, simulateQ_pure]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_ep1,
              hcL1, hcR1, hcrL1, hcrR1, hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1,
              fun h => by omega⟩))
    · have htle_ep : c.1.1 ≤ ep := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      simp only [hnew, ↓reduceIte, pure_bind]
      rw [hvp.vR_eq c.1.1]
      cases hvR : vpR.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
          hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
      | some v =>
        simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, pure_bind]
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hcrL, hcrR, hft, htab,
            hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR⟩))
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns,
            rfl, rfl, hcrL, hcrR, hft, htab, hbL, hbR, rfl, hσ_lt, hprfR_lt, hprngR, hcorrR,
            fun _ => ⟨?_, rfl, rfl, rfl, rfl, rfl⟩⟩))
          refine ⟨hvp.id_L, hvp.tcur_L, hvp.id_R, hvp.tcur_R, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            fun t' => ?_, hvp.root_rel⟩
          by_cases ht' : t' = c.1.1
          · subst ht'; simp
          · simp [Function.update_of_ne ht', hvp.vR_eq t']

private theorem syncStepAuth_h_step {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR spL1 spR1 : CryptoGames.PRFPRNG.GameState Sig I K}
    {hL1 hR1 : PRNGBucketAuthState T Sig K I}
    (hsync : SyncStepAuth Δcka tL t esL spL esR spR)
    (hcL1 : hL1.cache = esL.h.cache) (hcR1 : hR1.cache = esR.h.cache)
    (hcrL1 : hL1.corrRoot = none) (hcrR1 : hR1.corrRoot = none)
    (hft1 : ∀ t0, t0 ≠ t → hL1.fTable t0 = hR1.fTable t0)
    (htab1 : spL1.table = hR1.fTable t)
    (hbL1 : spL1.b = true) (hbR1 : spR1.b = false)
    (hσR1 : spR1.σ = spR.σ)
    (hσ1 : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL1.σ = spR1.σ)
    (hprf1 : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spR1.prf = false)
    (hprng1 : spR1.prng = false)
    (hcorr1 : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) → spR1.corr = false) :
    SyncStepAuth Δcka tL t { esL with h := hL1 } spL1 { esR with h := hR1 } spR1 := by
  refine ⟨hsync.abortL, hsync.abortR, hsync.g_eq, hsync.no_postLeak, hcrL1, hcrR1, hsync.tL_mem,
    ?_, ?_, ?_, hft1, htab1, hbL1, hbR1, hσ1, hprf1, hprng1, hcorr1, hsync.comp_inv,
    hsync.trans_epoch, ?_, ?_, hsync.epoch_le, hsync.epoch_sends⟩
  · intro P; rw [hσR1]; exact hsync.vp_rel P
  · intro e; rw [hσR1, hcL1, hcR1]; exact hsync.cache_rel e
  · intro e hgt; rw [hcL1, hcR1]; exact hsync.cache_gt_max e hgt
  · intro P hns hpos Tc hTc; rw [hcR1]; exact hsync.vp_curCka P hns hpos Tc hTc
  · intro r hr hpos Tc hTc; rw [hcR1]; exact hsync.trans_cache r hr hpos Tc hTc

private theorem syncStepAuth_set_win {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsync : SyncStepAuth Δcka tL t esL spL esR spR) :
    SyncStepAuth Δcka tL t { esL with g := { esL.g with win := true } } spL
      { esR with g := { esR.g with win := true } } spR := by
  refine ⟨hsync.abortL, hsync.abortR, ?_, hsync.no_postLeak, hsync.corrRootL, hsync.corrRootR,
    hsync.tL_mem, hsync.vp_rel, hsync.cache_rel, hsync.cache_gt_max,
    hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b, hsync.sp_σ_lt, hsync.spR_prf_lt,
    hsync.spR_prng, hsync.spR_corr, hsync.comp_inv, hsync.trans_epoch, hsync.vp_curCka,
    hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends⟩
  have hg := hsync.g_eq
  rcases esL with ⟨gL, hL, abL⟩
  rcases esR with ⟨gR, hR, abR⟩
  rcases gL with ⟨stL, epL, idxL, tLL, trL, chL, cpL, maL, bL, wL, lkL, crL⟩
  rcases gR with ⟨stR, epR, idxR, tLR, trR, chR, cpR, maR, bR, wR, lkR, crR⟩
  dsimp only [CryptoGames.SM.Construction.AuthL11.eraseSt] at hg ⊢
  injection hg with _ hep hidx htL_eq htr hch hcp hma hb _ hlk hcr
  subst hep hidx htL_eq htr hch hcp hma hb hlk hcr
  rfl

private theorem syncStepAuth_of_vRecv_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    {P : Party} {c : Header T × E}
    {vpL' vpR' : VP Γ T (Option Sig) SS RS} {pos : Pos}
    (hsync : SyncStepAuth Δcka tL t esL spL esR spR)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esR.g.epoch P + 1)
    (hns : P.sendsIn c.1.1 = false)
    (hvp' : RelVPStep (healEpoch tL) t spR.σ (max (esR.g.epoch P) c.1.1) P vpL' vpR')
    (hcur_le : c.1.1 ≤ esR.g.epoch P → vpR'.curCkaMsg = (esR.g.st P).curCkaMsg)
    (hnew_le_other : c.1.1 = esR.g.epoch P + 1 → c.1.1 ≤ esR.g.epoch P.other) :
    SyncStepAuth Δcka tL t
      { esL with g := esL.g.accept P vpL' pos } spL
      { esR with g := esR.g.accept P vpR' pos } spR := by
  have hacc_ep : (esR.g.accept P vpR' pos).epoch =
      Function.update esR.g.epoch P (max (esR.g.epoch P) c.1.1) := by
    dsimp only [_root_.CryptoGames.SM.GameState.accept, _root_.CryptoGames.SM.GameState.delete]
    rw [hpos_ep]
  have hmax_eq : max ((esR.g.accept P vpR' pos).epoch .A) ((esR.g.accept P vpR' pos).epoch .B) =
      max (esR.g.epoch .A) (esR.g.epoch .B) := by
    rw [hacc_ep]
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      cases P <;> simp [CryptoGames.Party.other] at hc_le ⊢ <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self]
  refine ⟨hsync.abortL, hsync.abortR,
    CryptoGames.SM.Construction.AuthL11.eraseSt_accept hsync.g_eq P vpL' vpR' pos,
    hsync.no_postLeak, hsync.corrRootL, hsync.corrRootR, hsync.tL_mem,
    ?_, hsync.cache_rel, ?_, hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b,
    ?_, ?_, hsync.spR_prng, ?_,
    CryptoGames.SM.Construction.AuthL11.comp_inv_accept esR.g (2 + Δcka) P vpR' pos hsync.comp_inv,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro Q
    dsimp only
    rw [hacc_ep]
    dsimp only [_root_.CryptoGames.SM.GameState.accept]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self]; exact hvp'
    · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
  · intro e hgt; rw [hmax_eq] at hgt; exact hsync.cache_gt_max e hgt
  · rw [hmax_eq]; exact hsync.sp_σ_lt
  · rw [hmax_eq]; exact hsync.spR_prf_lt
  · rw [hmax_eq]; exact hsync.spR_corr
  · intro r' hr'
    dsimp only at hr' ⊢
    rw [hacc_ep]
    simp only [_root_.CryptoGames.SM.GameState.accept, _root_.CryptoGames.SM.GameState.delete,
      List.mem_filter] at hr'
    obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
    refine ⟨?_, h2⟩
    by_cases hQ : r'.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · intro Q hns_Q hpos_Q Tc hTc
    dsimp only at hns_Q hpos_Q hTc ⊢
    rw [hacc_ep] at hns_Q hpos_Q ⊢
    dsimp only [_root_.CryptoGames.SM.GameState.accept] at hTc
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
    simp only [_root_.CryptoGames.SM.GameState.accept, _root_.CryptoGames.SM.GameState.delete,
      List.mem_filter] at hr'
    exact hsync.trans_cache r' hr'.1 hpos_r Tc hTc
  · intro Q
    dsimp only
    rw [hacc_ep]
    have hle_P := hsync.epoch_le P
    have hle_other := hsync.epoch_le P.other
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hc_le htle hle_P hle_other ⊢ <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self]
      exact hsync.epoch_le Q
  · intro Q hlt_Q
    dsimp only at hlt_Q ⊢
    rw [hacc_ep] at hlt_Q ⊢
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have heq_other : esR.g.epoch P.other = esR.g.epoch P + 1 := by
        have := hsync.epoch_le P.other
        rw [CryptoGames.Party.other_other] at this
        have hc_le := hnew_le_other hnew
        omega
      cases Q <;> cases P <;> simp [CryptoGames.Party.other, hnew] at heq_other hlt_Q <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hlt_Q ⊢
      exact hsync.epoch_sends Q hlt_Q

/-! ### 5. Oracle-Dispatcher Step Coupling, `DoomedForgedHdr` Absorption, & Top Theorem -/

private theorem support_liftH_g_eq [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (x : HM (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    {r : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) ×
         CryptoGames.PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng) ((liftH x).run es)).run sp)) :
    r.1.2.g = es.g ∧ r.1.2.abort = es.abort := by
  rw [CryptoGames.SM.Construction.AuthL11.run_liftH, simulateQ_bind, StateT.run_bind] at hr
  rw [MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨a, h'⟩, sp'⟩, _, hr2⟩
  simp at hr2
  rcases hr2 with rfl
  exact ⟨rfl, rfl⟩

private theorem epMgmt_preserving_props {St Msg C : Type}
    {g s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁.win = g.win ∧ s₁.st = g.st ∧ s₁.trans = g.trans ∧
    s₁.epoch P = (if P.sendsIn (g.epoch P + 1) then g.epoch P + 1 else g.epoch P) ∧
    (∀ Q, Q ≠ P → s₁.epoch Q = g.epoch Q) := by
  unfold _root_.CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep ⊢
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hc : (bad && !g.safeCh Δ P) = true
      · refine ⟨?_, ?_, ?_, ?_, fun Q hQ => ?_⟩ <;>
          simp [_root_.CryptoGames.SM.GameState.leak, Function.update_of_ne, *]
      · refine ⟨?_, ?_, ?_, ?_, fun Q hQ => ?_⟩ <;>
          simp [Function.update_of_ne, *]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep ⊢
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

private theorem epMgmt_doomed_mem {St Msg C : Type}
    {g s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    {tL : Option ℕ} {cur Δ qep : ℕ} {P : Party} {bad : Bool}
    (hcur : g.tL = some cur) (hmem : cur ∈ g.leaks) (hlt : ltOpt tL cur = true)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    ∃ cur', s₁.tL = some cur' ∧ cur' ∈ s₁.leaks ∧ ltOpt tL cur' = true := by
  unfold _root_.CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      by_cases hc : (bad && !g.safeCh Δ P) = true
      · simp only [hc, ↓reduceIte, _root_.CryptoGames.SM.GameState.leak, hcur,
          _root_.CryptoGames.SM.maxOpt]
        exact ⟨_, rfl, List.mem_cons_self, ltOpt_mono hlt (Nat.le_max_left _ _)⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨cur, hcur, hmem, hlt⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < g.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨cur, hcur, hmem, hlt⟩

private theorem doomed_branch4_of_record
    {Δcka : ℕ} {tL : Option ℕ}
    {abort0 : Bool}
    {s₁ : Ctx Γ T (Option Sig) SS RS M E}
    {P : Party} {st' : VP Γ T (Option Sig) SS RS} {m : M} {ct : Header T × E}
    {h' : PRNGBucketAuthState T Sig K I} {ep0 cur : ℕ}
    (hwin1 : s₁.win = false)
    (hvp_s1 : ∀ Q, Q ≠ P → (s₁.st Q).id = Q ∧ (s₁.st Q).tcur = s₁.epoch Q)
    (htr_s1 : ∀ r ∈ s₁.trans, r.ct.1.1 = r.pos.epoch)
    (hep_P : s₁.epoch P = if P.sendsIn (ep0 + 1) then ep0 + 1 else ep0)
    (hst'_id : st'.id = P)
    (hst'_tcur : st'.tcur = if P.sendsIn (ep0 + 1) then ep0 + 1 else ep0)
    (hct_ep : ct.1.1 = st'.tcur)
    (hcur : s₁.tL = some cur) (hmem : cur ∈ s₁.leaks) (hlt : ltOpt tL cur = true) :
    DoomedForgedHdr tL
      ({ g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false
         h := h'
         abort := abort0 }, none) := by
  refine Or.inr (Or.inr (Or.inr ⟨hwin1, rfl, ?_, ?_, ⟨cur, hcur, hmem, hlt⟩⟩))
  · intro Q
    dsimp only [_root_.CryptoGames.SM.GameState.record]
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self]
      exact ⟨hst'_id, hst'_tcur.trans hep_P.symm⟩
    · simp only [Function.update_of_ne hQ]
      exact hvp_s1 Q hQ
  · intro r hr
    dsimp only [_root_.CryptoGames.SM.GameState.record] at hr ⊢
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hct_ep.trans (hst'_tcur.trans hep_P.symm)
    · exact htr_s1 r hr'

private theorem doomed_branch4_of_accept [DecidableEq T] [DecidableEq E]
    {tL : Option ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {P : Party} {vp' : VP Γ T (Option Sig) SS RS} {pos : Pos}
    {h' : PRNGBucketAuthState T Sig K I} {cur : ℕ}
    (hwin : es.g.win = false)
    (hvp_inv : ∀ Q, (es.g.st Q).id = Q ∧ (es.g.st Q).tcur = es.g.epoch Q)
    (htr_inv : ∀ r ∈ es.g.trans, r.ct.1.1 = r.pos.epoch)
    (hvp'_id : vp'.id = P)
    (hvp'_tcur : vp'.tcur = max (es.g.epoch P) pos.epoch)
    (hcur : es.g.tL = some cur) (hmem : cur ∈ es.g.leaks) (hlt : ltOpt tL cur = true) :
    DoomedForgedHdr tL ({ es with g := es.g.accept P vp' pos, h := h' }, none) := by
  refine Or.inr (Or.inr (Or.inr ⟨hwin, rfl, ?_, ?_, ⟨cur, hcur, hmem, hlt⟩⟩))
  · intro Q
    dsimp only [_root_.CryptoGames.SM.GameState.accept, _root_.CryptoGames.SM.GameState.delete]
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self]
      exact ⟨hvp'_id, hvp'_tcur⟩
    · simp only [Function.update_of_ne hQ]
      exact hvp_inv Q
  · intro r hr
    dsimp only [_root_.CryptoGames.SM.GameState.accept, _root_.CryptoGames.SM.GameState.delete] at hr ⊢
    rw [List.mem_filter] at hr
    exact htr_inv r hr.1

private abbrev SMSpecAuth (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

private def SyncForgedHdr
    (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (stL : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (spL : CryptoGames.PRFPRNG.GameState Sig I K)
    (stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (spR : CryptoGames.PRFPRNG.GameState Sig I K) : Prop :=
  SyncStepAuth Δcka tL t stL.1 spL stR.1 spR ∧
  stL.2 = stR.2 ∧
  (stR.1.g.win = false → stR.2 = none)

private def StepRelForgedHdr (Δcka : ℕ) (tL : Option ℕ) (t : ℕ) {α : Type}
    (r1 r2 : (α × PRNGBucketAuthEState Γ T Sig SS RS M E K I) × CryptoGames.PRFPRNG.GameState Sig I K) : Prop :=
  DoomedForgedHdr tL r1.1.2 ∨
  (r1.1.1 = r2.1.1 ∧ SyncForgedHdr Δcka tL t r1.1.2 r1.2 r2.1.2 r2.2)

private def stepForgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecAuth Γ T Sig SS RS M CCoins E).Range q ×
      PRNGBucketAuthEState Γ T Sig SS RS M E K I) × CryptoGames.PRFPRNG.GameState Sig I K) :=
  (simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
    ((implPRNGBucketAuthGen
      (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t)
      Δcka qep fs.maxSkip tL true q).run st)).run sp

private theorem leComp_i1_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (arg : Party × M × Option CCoins)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdr Δcka tL t)
      (stepForgedHdr cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl arg))))) stL spL)
      (stepForgedHdr cka prng fs Δcka qep tL (t + 1) (.inr (.inl (.inl (.inl (.inl arg))))) stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hsync, hwinEp, hwin_none⟩
  dsimp only at hsync hwinEp hwin_none
  subst hwinEp
  rcases arg with ⟨P, m, r_coins⟩
  unfold stepForgedHdr implPRNGBucketAuthGen
  simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    have hwR : esR.g.win = false := by simpa using habw
    have hwL : esL.g.win = false := (CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq).trans hwR
    have hwe0 : winEpL = none := hwin_none hwR
    rcases CryptoGames.SM.Construction.AuthL11.epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁L, s₁R, h1, h2, hs₁_er, hs₁L_st, hs₁R_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
    · simp only [h1, h2, hs₁L_st, hs₁R_st, StateT.run_bind, StateT.run_lift,
        simulateQ_bind, pure_bind, bind_assoc]
      have htL_memR : ∀ cur, s₁R.tL = some cur → cur ∈ s₁R.leaks :=
        tL_mem_epMgmt hsync.tL_mem h2
      by_cases hplR : postLeak tL s₁R = true
      · subst hwe0
        have hplL : postLeak tL s₁L = true := (eraseSt_postLeak hs₁_er tL).trans hplR
        have htL_memL : ∀ cur, s₁L.tL = some cur → cur ∈ s₁L.leaks := by
          have htL_mem0L : ∀ cur, esL.g.tL = some cur → cur ∈ esL.g.leaks := by
            intro cur hcur
            have htL_eq : esL.g.tL = esR.g.tL := congrArg (fun g => g.tL) hsync.g_eq
            have hlk_eq : esL.g.leaks = esR.g.leaks :=
              congrArg (fun g => g.leaks) hsync.g_eq
            rw [hlk_eq]
            exact hsync.tL_mem cur (htL_eq.symm.trans hcur)
          exact tL_mem_epMgmt htL_mem0L h1
        obtain ⟨cur, hcur, hmem_cur, hlt_cur⟩ := ex_tL_of_postLeak htL_memL hplL
        obtain ⟨hs₁L_win, _, hs₁L_tr, hs₁L_epP, hs₁L_epQ⟩ := epMgmt_preserving_props h1
        refine leComp_of_support_left _ _ fun rL hrL _ _ => ?_
        simp only [MonadAttach.mem_support_bind] at hrL
        rcases hrL with ⟨⟨⟨res_vs, h'⟩, sp1⟩, hr_vs, hr_rest⟩
        cases res_vs with
        | none =>
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          subst hr_rest
          exact Or.inl (Or.inl rfl)
        | some vc =>
          rcases vc with ⟨st', ct⟩
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          subst hr_rest
          have hep_eq : esL.g.epoch = esR.g.epoch :=
            congrArg (fun g => g.epoch) hsync.g_eq
          have htr_eq : esL.g.trans = esR.g.trans :=
            congrArg (fun g => g.trans) hsync.g_eq
          obtain ⟨hst'_id, hst'_tcur, hct_ep⟩ := support_vSend_props prng
            (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) s₁L P (esL.g.st P)
            (esL.g.epoch P) m r_coins esL.h spL
            (hsync.vp_rel P).id_L
            ((hsync.vp_rel P).tcur_L.trans (congrFun hep_eq.symm P))
            hr_vs rfl
          refine Or.inl (doomed_branch4_of_record (hs₁L_win.trans hwL) ?_ ?_ hs₁L_epP
            hst'_id hst'_tcur hct_ep hcur hmem_cur hlt_cur)
          · intro Q hQ
            rw [hs₁L_st, hs₁L_epQ Q hQ]
            exact ⟨(hsync.vp_rel Q).id_L,
              (hsync.vp_rel Q).tcur_L.trans (congrFun hep_eq.symm Q)⟩
          · intro rec hrec
            rw [hs₁L_tr, htr_eq] at hrec
            exact (hsync.trans_epoch rec hrec).2
      · have hplR_f : postLeak tL s₁R = false := Bool.eq_false_iff.mpr hplR
        have hplL_f : postLeak tL s₁L = false := (eraseSt_postLeak hs₁_er tL).trans hplR_f
        have hheq : P.sendsIn (esR.g.epoch P + 1) = true →
            esR.g.epoch P = esR.g.epoch P.other :=
          CryptoGames.SM.Construction.AuthL11.epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
        have he_eq_max : P.sendsIn (esR.g.epoch P + 1) = true →
            esR.g.epoch P = max (esR.g.epoch .A) (esR.g.epoch .B) :=
          fun hsends => (CryptoGames.SM.Construction.AuthL11.max_epoch_eq_of_eq (hheq hsends)).symm
        refine (leComp_vSend_step cka prng fs Δcka qep tL t (esR.g.epoch P)
          (max (esR.g.epoch .A) (esR.g.epoch .B)) htH hplL_f hplR_f
          hsync.corrRootL hsync.corrRootR (hsync.vp_rel P) hsync.cache_rel
          hsync.cache_gt_max he_eq_max hsync.fTable_ne hsync.table_t hsync.spL_b hsync.spR_b
          hsync.sp_σ_lt hsync.spR_prf_lt hsync.spR_prng hsync.spR_corr).bind ?_
        rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvs
        rcases hvs with hnone |
          ⟨vpL', vpR', c, hL_eq, hR_eq, hc_hdr, hvp', hc_rel, hcrL1, hcrR1, hft1, htab1,
            hbL1, hbR1, hprng1, hsends_props, hns_props⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
        · dsimp only at hL_eq hR_eq; subst hL_eq hR_eq
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          refine CryptoGames.SM.Construction.AuthL11.LeComp.pure ?_
          have hs₁_ep : s₁R.epoch P = if P.sendsIn (esR.g.epoch P + 1) then esR.g.epoch P + 1
              else esR.g.epoch P := by
            rw [hs₁_ep_fn]; split <;> simp
          have hs₁_ep_other : ∀ Q, Q ≠ P → s₁R.epoch Q = esR.g.epoch Q := by
            intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
          have hs₁_comp := hs₁_comp_imp hsync.comp_inv
          refine Or.inr ⟨rfl, ⟨rfl, rfl, ?_, hplR_f, hcrL1, hcrR1, htL_memR,
            ?_, hc_rel, ?_, hft1, htab1, hbL1, hbR1, ?_, ?_, hprng1, ?_,
            CryptoGames.SM.Construction.AuthL11.comp_inv_record s₁R (2 + Δcka) P vpR' _ false rfl hs₁_comp,
            ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ => hwe0⟩
          · rw [CryptoGames.SM.Construction.AuthL11.eraseSt_epoch hs₁_er, CryptoGames.SM.Construction.AuthL11.eraseSt_idx hs₁_er]
            exact CryptoGames.SM.Construction.AuthL11.eraseSt_record hs₁_er (2 + Δcka) P vpL' vpR' _ false
          · intro Q
            dsimp only [_root_.CryptoGames.SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁_ep]; exact hvp'
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁L_st, hs₁R_st]
              by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
              · obtain ⟨hσR_ge, _⟩ := hsends_props hsends
                by_cases hQt : esR.g.epoch Q = t
                · have hle_max : t ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
                    rw [← hQt]; cases Q <;> simp
                  rw [hσR_ge hle_max]; exact hsync.vp_rel Q
                · exact (hsync.vp_rel Q).change_σ hQt
              · obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props (Bool.eq_false_iff.mpr hsends)
                dsimp only at hspR_eq; rw [hspR_eq]; exact hsync.vp_rel Q
          · intro e' hgt
            dsimp only [_root_.CryptoGames.SM.GameState.record] at hgt ⊢
            rw [hs₁_ep_fn] at hgt
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · simp only [hsends, ↓reduceIte] at hgt
              rw [CryptoGames.SM.Construction.AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends] at hgt
              exact (hsends_props hsends).2.1 e' hgt
            · have hns := Bool.eq_false_iff.mpr hsends
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hgt
              obtain ⟨hhL1, hhR1, _⟩ := hns_props hns
              dsimp only at hhL1 hhR1; rw [hhL1, hhR1]
              exact hsync.cache_gt_max e' hgt
          · dsimp only [_root_.CryptoGames.SM.GameState.record]
            rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · simp only [hsends, ↓reduceIte]
              rw [CryptoGames.SM.Construction.AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
              exact (hsends_props hsends).2.2.2.2.1
            · have hns := Bool.eq_false_iff.mpr hsends
              simp only [hns, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨_, _, hspL_eq, hspR_eq, _⟩ := hns_props hns
              dsimp only at hspL_eq hspR_eq; rw [hspL_eq, hspR_eq]
              exact hsync.sp_σ_lt
          · dsimp only [_root_.CryptoGames.SM.GameState.record]
            rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · simp only [hsends, ↓reduceIte]
              rw [CryptoGames.SM.Construction.AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
              exact (hsends_props hsends).2.2.2.2.2.1
            · have hns := Bool.eq_false_iff.mpr hsends
              simp only [hns, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props hns
              dsimp only at hspR_eq; rw [hspR_eq]
              exact hsync.spR_prf_lt
          · dsimp only [_root_.CryptoGames.SM.GameState.record]
            rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · simp only [hsends, ↓reduceIte]
              rw [CryptoGames.SM.Construction.AuthL11.max_epoch_update_succ (hheq hsends), he_eq_max hsends]
              exact (hsends_props hsends).2.2.2.2.2.2
            · have hns := Bool.eq_false_iff.mpr hsends
              simp only [hns, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨_, _, _, hspR_eq, _⟩ := hns_props hns
              dsimp only at hspR_eq; rw [hspR_eq]
              exact hsync.spR_corr
          · intro r hr
            dsimp only [_root_.CryptoGames.SM.GameState.record] at hr ⊢
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
            dsimp only [_root_.CryptoGames.SM.GameState.record] at hns_Q hpos_Q hTc ⊢
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
                  cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other ⊢ <;> omega
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
            dsimp only [_root_.CryptoGames.SM.GameState.record] at hr ⊢
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
                    simp [CryptoGames.Party.other, hS] at heq_other hr_le ⊢ <;> omega
                rw [hc_other _ hne]
                exact hsync.trans_cache r hr_mem hpos_r Tc hTc
              · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
                obtain ⟨_, hhR1, _⟩ := hns_props hns
                dsimp only at hhR1
                rw [hhR1]
                exact hsync.trans_cache r hr_mem hpos_r Tc hTc
          · intro Q
            dsimp only [_root_.CryptoGames.SM.GameState.record]
            rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte]
              cases Q <;> cases P <;> simp [CryptoGames.Party.other] at heq_other ⊢ <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
              exact hsync.epoch_le Q
          · intro Q hlt_Q
            dsimp only [_root_.CryptoGames.SM.GameState.record] at hlt_Q ⊢
            rw [hs₁_ep_fn] at hlt_Q ⊢
            by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hlt_Q ⊢
              by_cases hQ : Q = P
              · subst Q; simp only [Function.update_self]; exact hsends
              · cases Q <;> cases P <;> simp [CryptoGames.Party.other] at hQ heq_other hlt_Q <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hlt_Q ⊢
              exact hsync.epoch_sends Q hlt_Q

private theorem leComp_i3_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (arg : Party × (Header T × E))
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdr Δcka tL t)
      (stepForgedHdr cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr arg)))) stL spL)
      (stepForgedHdr cka prng fs Δcka qep tL (t + 1) (.inr (.inl (.inl (.inr arg)))) stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hsync, hwinEp, hwin_none⟩
  dsimp only at hsync hwinEp hwin_none
  subst hwinEp
  rcases arg with ⟨P, c⟩
  unfold stepForgedHdr implPRNGBucketAuthGen deliverE
  simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind,
    simulateQ_bind, bind_assoc]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    have hwR : esR.g.win = false := by simpa using habw
    have hwe0 : winEpL = none := hwin_none hwR
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
    | some r =>
      have hr_mem : r ∈ esR.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold _root_.CryptoGames.SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hr_ep := hsync.trans_epoch r hr_mem.1
      have hr_pos_ep : r.pos.epoch = c.1.1 := by rw [← hr_ep.2, hr_mem.2.2]
      have hc_hit : c.1.1 = esR.g.epoch P + 1 → ∀ tn0, c.1.2 = some tn0 →
          ∃ rR kc, esR.h.cache (esR.g.epoch P + 1) = some (tn0, rR, kc) := by
        intro hnew tn0 htn0
        have hct2 : r.ct.1.2 = some tn0 := by rw [hr_mem.2.2]; exact htn0
        rw [← hnew, ← hr_pos_ep]
        exact hsync.trans_cache r hr_mem.1 (by omega) tn0 hct2
      simp only [CryptoGames.SM.Construction.AuthL11.run_liftH, StateT.run_bind, simulateQ_bind, bind_assoc, bucketAuthCfg,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      refine (leComp_vRecv_cached_step cka prng fs Δcka qep tL t
        hsync.corrRootL hsync.corrRootR (hsync.vp_rel P) hsync.cache_rel hc_hit).bind ?_
      rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvr
      rcases hvr with ⟨hL_none, hR_none, hhL1, hhR1, hspL1, hspR1⟩ |
        ⟨vpL', vpR', i', m', hL_some, hR_some, htle, hns, hvp', hhL1, hhR1, hspL1, hspR1, hcur_le⟩
      · dsimp only at hL_none hR_none hhL1 hhR1 hspL1 hspR1
        subst hL_none hR_none hhL1 hhR1 hspL1 hspR1
        simp only [pure_bind, StateT.run_pure, StateT.run_set, simulateQ_pure]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
      · dsimp only at hL_some hR_some hhL1 hhR1 hspL1 hspR1
        subst hL_some hR_some hhL1 hhR1 hspL1 hspR1
        simp only [pure_bind, StateT.run_bind, run_commitE_forgedHdr,
          StateT.run_pure, StateT.run_modify, StateT.run_set, simulateQ_pure]
        rw [CryptoGames.SM.Construction.AuthL11.eraseSt_chall hsync.g_eq]
        have hs_acc := syncStepAuth_of_vRecv_accept hsync hr_pos_ep htle hns hvp' hcur_le
          (fun _ => by rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1)
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs_acc, rfl, fun _ => hwe0⟩)

private theorem leComp_i4_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (arg : Party × (Header T × E))
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdr Δcka tL t)
      (stepForgedHdr cka prng fs Δcka qep tL t (.inr (.inl (.inr arg))) stL spL)
      (stepForgedHdr cka prng fs Δcka qep tL (t + 1) (.inr (.inl (.inr arg))) stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hsync, hwinEp, hwin_none⟩
  dsimp only at hsync hwinEp hwin_none
  subst hwinEp
  rcases arg with ⟨P, c⟩
  have hnf_eq :
      (decide (c.1.1 = (esL.g.st P).tcur + 1) && !isHonestHdrPRNGBucket esL.h c.1) =
      (decide (c.1.1 = (esR.g.st P).tcur + 1) && !isHonestHdrPRNGBucket esR.h c.1) := by
    rw [(hsync.vp_rel P).tcur_L, (hsync.vp_rel P).tcur_R,
      isHonestHdrPRNGBucket_eq_of_relCacheStep c.1 (hsync.cache_rel c.1.1)]
  unfold stepForgedHdr implPRNGBucketAuthGen injectE
  simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind,
    simulateQ_bind, bind_assoc, Bool.not_true, Bool.false_or]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
    CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.g_eq, CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hsync.g_eq, hnf_eq]
  by_cases hguard : (false || esR.g.win || (esR.g.inTransit P.other c).isSome ||
      !esR.g.safeInj (2 + Δcka)) = true
  · have hno_flip : (!esR.g.win && esR.g.win &&
        (decide (c.1.1 = (esR.g.st P).tcur + 1) && !isHonestHdrPRNGBucket esR.h c.1)) = false := by
      cases esR.g.win <;> simp
    simp only [hguard, ↓reduceIte, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure]
    rw [CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq, hno_flip]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      CryptoGames.SM.Construction.AuthL11.run_liftH, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc]
    have hwR : esR.g.win = false := by
      simp only [Bool.or_eq_true, not_or] at hguard
      exact Bool.eq_false_iff.mpr hguard.1.1.2
    have hwe0 : winEpL = none := hwin_none hwR
    have hsafe : esR.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have heMax : esR.g.epoch P ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
      cases P <;> simp
    have hplL : postLeak tL esL.g = false :=
      (eraseSt_postLeak hsync.g_eq tL).trans hsync.no_postLeak
    refine (leComp_vRecv_inject_step cka prng fs Δcka qep tL t
      (max (esR.g.epoch .A) (esR.g.epoch .B)) hplL hsync.no_postLeak
      hsync.corrRootL hsync.corrRootR (hsync.vp_rel P) hsync.cache_rel heMax
      hsync.fTable_ne hsync.table_t hsync.spL_b hsync.spR_b
      hsync.sp_σ_lt hsync.spR_prf_lt hsync.spR_prng hsync.spR_corr).bind ?_
    rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hvr
    rcases hvr with hnone |
      ⟨hL_none, hR_none, hcL1, hcR1, hcrL1, hcrR1, hft1, htab1,
        hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1⟩ |
      ⟨vpL', vpR', i', m', hL_some, hR_some, htle, hns, hcL1, hcR1, hcrL1, hcrR1,
        hft1, htab1, hbL1, hbR1, hσR1, hσ1, hprf1, hprng1, hcorr1, hle_props⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_set,
        StateT.run_pure, simulateQ_pure]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
    · dsimp only at hL_none hR_none; subst hL_none hR_none
      have hwL : esL.g.win = false := (CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq).trans hwR
      simp only [pure_bind, StateT.run_pure, StateT.run_set, simulateQ_pure,
        hwL, hwR, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
        syncStepAuth_h_step hsync hcL1 hcR1 hcrL1 hcrR1 hft1 htab1 hbL1 hbR1
          hσR1 hσ1 hprf1 hprng1 hcorr1,
        rfl, fun _ => hwe0⟩)
    · dsimp only at hL_some hR_some; subst hL_some hR_some
      have hwL : esL.g.win = false := (CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq).trans hwR
      dsimp only
      have hs1 := syncStepAuth_h_step hsync hcL1 hcR1 hcrL1 hcrR1 hft1 htab1
        hbL1 hbR1 hσR1 hσ1 hprf1 hprng1 hcorr1
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, StateT.run_set,
          simulateQ_pure, hwL, hwR, Bool.not_false, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, pure_bind]
        exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1, rfl, fun _ => hwe0⟩)
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
          have hvp_max : RelVPStep (healEpoch tL) t spR1.σ (max (esR.g.epoch P) c.1.1) P vpL' vpR' := by
            rw [Nat.max_eq_left htle_ep]; exact hvp_ep
          have haccL_win : (esL.g.accept P vpL' ⟨P.other, c.1.1, i'⟩).win = false := hwL
          have haccR_win : (esR.g.accept P vpR' ⟨P.other, c.1.1, i'⟩).win = false := hwR
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_forgedHdr,
            StateT.run_pure, StateT.run_modify, StateT.run_set, pure_bind, simulateQ_pure,
            hwR, haccL_win, haccR_win, Bool.not_false, Bool.true_and, Bool.false_and,
            Bool.false_eq_true]
          exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl,
            syncStepAuth_of_vRecv_accept hsync rfl htle hns hvp_max
              (fun _ => hcur_eq) (fun heq => False.elim (hne_e1 heq)),
            rfl, fun _ => hwe0⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_set,
              pure_bind, StateT.run_pure, simulateQ_pure, hwR, Bool.not_false, Bool.true_and]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, syncStepAuth_set_win hs1, rfl,
              fun h => by cases h⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              StateT.run_set, pure_bind, simulateQ_pure, hwL, hwR, Bool.not_false, Bool.true_and,
              Bool.false_and]
            exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hs1, rfl, fun _ => hwe0⟩)

private theorem leComp_i5_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (P : Party)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdr Δcka tL t)
      (stepForgedHdr cka prng fs Δcka qep tL t (.inr (.inr P)) stL spL)
      (stepForgedHdr cka prng fs Δcka qep tL (t + 1) (.inr (.inr P)) stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  rcases hsf with ⟨hsync, hwinEp, hwin_none⟩
  dsimp only at hsync hwinEp hwin_none
  subst hwinEp
  have hca_eq : esL.g.corrAllowed P = esR.g.corrAllowed P := by
    have hch : esL.g.chall = esR.g.chall := congrArg (fun g => g.chall) hsync.g_eq
    have htr : esL.g.trans = esR.g.trans := congrArg (fun g => g.trans) hsync.g_eq
    have hcp : esL.g.comp = esR.g.comp := congrArg (fun g => g.comp) hsync.g_eq
    simp only [_root_.CryptoGames.SM.GameState.corrAllowed, hch, htr, hcp]
  unfold stepForgedHdr implPRNGBucketAuthGen
  simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq, hca_eq]
  by_cases hguard : (false || esR.g.win || !esR.g.corrAllowed P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync, rfl, hwin_none⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_lift,
      simulateQ_bind, pure_bind, bind_assoc,
      hooksPRNGBucketAuthForgedHdr]
    have hwR : esR.g.win = false := by
      simp only [Bool.or_eq_true, not_or] at hguard
      exact Bool.eq_false_iff.mpr hguard.1.2
    have hwL : esL.g.win = false := (CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq).trans hwR
    have hwe0 : winEpL = none := hwin_none hwR
    have hvp := hsync.vp_rel P
    have hep_eq : esL.g.epoch = esR.g.epoch :=
      congrArg (fun g => g.epoch) hsync.g_eq
    rw [hvp.tcur_L, hvp.tcur_R, hep_eq]
    by_cases hrev_rej : (!(decide (esR.g.epoch P < healEpoch tL)) ||
        !(decide (max (esR.g.epoch .A) (esR.g.epoch .B) < healEpoch tL))) = true
    · simp only [hrev_rej, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
        StateT.run_bind, StateT.run_set]
      exact CryptoGames.SM.Construction.AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
    · have hep_lt_tH : esR.g.epoch P < healEpoch tL := by
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or,
          not_not] at hrev_rej
        exact hrev_rej.1
      obtain ⟨σ, hrL, hrR⟩ : ∃ σ, (esL.g.st P).root = some σ ∧ (esR.g.st P).root = some σ := by
        rcases hvp.root_rel with ⟨_, s, h1, h2⟩ | ⟨hge, _⟩ | ⟨heq, _⟩ | ⟨hgt, _⟩
        · exact ⟨s, h1, h2⟩
        · omega
        · omega
        · omega
      simp only [hrev_rej, Bool.false_eq_true, ↓reduceIte, hrL, hrR,
        StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_set]
      have hac_er := CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hsync.g_eq P
      by_cases hpl : postLeak tL (esR.g.afterCorr P) = true
      · subst hwe0
        have hplL : postLeak tL (esL.g.afterCorr P) = true :=
          (eraseSt_postLeak hac_er tL).trans hpl
        have htL_mem_acL : ∀ cur, (esL.g.afterCorr P).tL = some cur →
            cur ∈ (esL.g.afterCorr P).leaks := by
          intro cur hcur
          simp only [_root_.CryptoGames.SM.GameState.afterCorr,
            _root_.CryptoGames.SM.GameState.leak, Option.some.injEq] at hcur ⊢
          subst hcur
          exact List.mem_cons_self
        obtain ⟨cur, hcur, hmem_cur, hlt_cur⟩ := ex_tL_of_postLeak htL_mem_acL hplL
        have htr_eq : esL.g.trans = esR.g.trans :=
          congrArg (fun g => g.trans) hsync.g_eq
        refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inl (Or.inr (Or.inr (Or.inr ⟨hwL, rfl, ?_, ?_,
          ⟨cur, hcur, hmem_cur, hlt_cur⟩⟩))))
        · intro Q
          exact ⟨(hsync.vp_rel Q).id_L,
            (hsync.vp_rel Q).tcur_L.trans (congrFun hep_eq.symm Q)⟩
        · intro r hr
          dsimp only [_root_.CryptoGames.SM.GameState.afterCorr,
            _root_.CryptoGames.SM.GameState.leak] at hr
          rw [htr_eq] at hr
          exact (hsync.trans_epoch r hr).2
      · have hpl_f : postLeak tL (esR.g.afterCorr P) = false := Bool.eq_false_iff.mpr hpl
        have htL_mem_acR : ∀ cur, (esR.g.afterCorr P).tL = some cur →
            cur ∈ (esR.g.afterCorr P).leaks := by
          intro cur hcur
          simp only [_root_.CryptoGames.SM.GameState.afterCorr,
            _root_.CryptoGames.SM.GameState.leak, Option.some.injEq] at hcur ⊢
          subst hcur
          exact List.mem_cons_self
        refine CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨?_, ?_, rfl, fun _ => hwe0⟩)
        · dsimp only [realParty]
          congr 1
          rw [hvp.id_L, hvp.id_R, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_L, hvp.tcur_R, hvp.vS_eq,
            funext hvp.vR_eq]
        · exact ⟨rfl, rfl, hac_er, hpl_f, hsync.corrRootL, hsync.corrRootR,
            htL_mem_acR, hsync.vp_rel, hsync.cache_rel,
            hsync.cache_gt_max, hsync.fTable_ne, hsync.table_t, hsync.spL_b, hsync.spR_b,
            hsync.sp_σ_lt, hsync.spR_prf_lt, hsync.spR_prng, hsync.spR_corr,
            CryptoGames.SM.Construction.AuthL11.comp_inv_afterCorr esR.g (2 + Δcka) (by omega) P
              (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv,
            hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache,
            hsync.epoch_le, hsync.epoch_sends⟩

private theorem leComp_stepForgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    CryptoGames.SM.Construction.AuthL11.LeComp (StepRelForgedHdr Δcka tL t)
      (stepForgedHdr cka prng fs Δcka qep tL t q stL spL)
      (stepForgedHdr cka prng fs Δcka qep tL (t + 1) q stR spR) := by
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [stepForgedHdr, implPRNGBucketAuthGen, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.sample_bind _ fun u _ => CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf⟩)
  · exact leComp_i1_forgedHdr cka prng fs Δcka qep tL t htH arg hsf
  · simp only [stepForgedHdr, implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_pure, simulateQ_pure]
    exact CryptoGames.SM.Construction.AuthL11.LeComp.pure (Or.inr ⟨rfl, hsf⟩)
  · exact leComp_i3_forgedHdr cka prng fs Δcka qep tL t arg hsf
  · exact leComp_i4_forgedHdr cka prng fs Δcka qep tL t arg hsf
  · exact leComp_i5_forgedHdr cka prng fs Δcka qep tL t htH P hsf

private theorem stepForgedHdr_state_eq_of_abort_or_win
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp : Option ℕ) (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (haw : es.abort = true ∨ es.g.win = true) :
    ∀ r ∈ support (stepForgedHdr cka prng fs Δcka qep tL t q (es, winEp) sp),
      r.1.2 = (es, winEp) := by
  intro r hr
  have hor : (es.abort || es.g.win) = true := by
    rcases haw with h | h <;> simp [h]
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [stepForgedHdr, implPRNGBucketAuthGen, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
    rcases hr with ⟨_, _, rfl⟩
    rfl
  · rcases arg with ⟨P, m, r_coins⟩
    simp only [stepForgedHdr, implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte,
      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp [stepForgedHdr, implPRNGBucketAuthGen] at hr
    subst hr; rfl
  · rcases arg with ⟨P, c⟩
    simp only [stepForgedHdr, implPRNGBucketAuthGen, deliverE, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, hor, ↓reduceIte,
      StateT.run_pure, StateT.run_set, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · rcases arg with ⟨P, c⟩
    have hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !es.g.safeInj (2 + Δcka)) = true := by
      simp [hor]
    have hno_flip : (!es.g.win && es.g.win && (!true ||
        (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1))) = false := by
      cases es.g.win <;> simp
    simp only [stepForgedHdr, implPRNGBucketAuthGen, injectE, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, hguard, ↓reduceIte,
      StateT.run_pure, StateT.run_set, simulateQ_pure, hno_flip,
      Bool.false_eq_true, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · have hguard : (es.abort || es.g.win || !es.g.corrAllowed P) = true := by
      simp [hor]
    simp only [stepForgedHdr, implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte,
      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

private theorem stepForgedHdr_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K)
    (hd : DoomedForgedHdr tL st) :
    ∀ r ∈ support (stepForgedHdr cka prng fs Δcka qep tL t q st sp),
      DoomedForgedHdr tL r.1.2 := by
  intro r hr
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | ⟨hwin, hnone⟩ | ⟨hwin, tWin, cur, hsome, hmem, hlt, hcur_lt⟩ |
    ⟨hwin, hnone, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩
  · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t q es winEp sp (Or.inl hab) r hr]
    exact Or.inl hab
  · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t q es winEp sp (Or.inr hwin) r hr]
    exact Or.inr (Or.inl ⟨hwin, hnone⟩)
  · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t q es winEp sp (Or.inr hwin) r hr]
    exact Or.inr (Or.inr (Or.inl ⟨hwin, tWin, cur, hsome, hmem, hlt, hcur_lt⟩))
  · dsimp only at hwin hnone hvp_inv htr_inv hcur hmem
    subst hnone
    rcases q with n | ((((arg | arg) | arg) | arg) | P)
    · simp [stepForgedHdr, implPRNGBucketAuthGen, CryptoGames.SM.Construction.AuthL11.pImpl, StateT.run_lift, simulateQ_bind,
        simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
      rcases hr with ⟨_, _, rfl⟩
      exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
    · rcases arg with ⟨P, m, r_coins⟩
      by_cases hab : es.abort = true
      · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t _ es none sp (Or.inl hab) r hr]
        exact Or.inl hab
      · have hor_f : (es.abort || es.g.win) = false := by
          simp [Bool.eq_false_iff.mpr hab, hwin]
        simp only [stepForgedHdr, implPRNGBucketAuthGen, QueryImpl.add_apply,
          StateT.run_bind, StateT.run_get, pure_bind, hor_f, Bool.false_eq_true, ↓reduceIte] at hr
        cases hep : es.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        | some s₁ =>
          obtain ⟨hs₁_win, hs₁_st, hs₁_tr, hs₁_epP, hs₁_epQ⟩ := epMgmt_preserving_props hep
          obtain ⟨cur', hcur', hmem', hlt'⟩ := epMgmt_doomed_mem hcur hmem hlt hep
          simp only [hep, hs₁_st, StateT.run_bind, StateT.run_lift,
            simulateQ_bind, pure_bind, bind_assoc,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vs, h'⟩, sp1⟩, hr_vs, hr_rest⟩
          cases res_vs with
          | none =>
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some vc =>
            rcases vc with ⟨st', ct⟩
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest
            obtain ⟨hst'_id, hst'_tcur, hct_ep⟩ := support_vSend_props prng
              (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) s₁ P (es.g.st P)
              (es.g.epoch P) m r_coins es.h sp
              (hvp_inv P).1 (hvp_inv P).2 hr_vs rfl
            refine doomed_branch4_of_record (hs₁_win.trans hwin) ?_ ?_ hs₁_epP
              hst'_id hst'_tcur hct_ep hcur' hmem' hlt'
            · intro Q hQ
              rw [hs₁_st, hs₁_epQ Q hQ]
              exact hvp_inv Q
            · intro rec hrec
              rw [hs₁_tr] at hrec
              exact htr_inv rec hrec
    · simp [stepForgedHdr, implPRNGBucketAuthGen] at hr
      subst hr
      exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
    · rcases arg with ⟨P, c⟩
      by_cases hab : es.abort = true
      · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t _ es none sp (Or.inl hab) r hr]
        exact Or.inl hab
      · have hor_f : (es.abort || es.g.win) = false := by
          simp [Bool.eq_false_iff.mpr hab, hwin]
        simp only [stepForgedHdr, implPRNGBucketAuthGen, deliverE, QueryImpl.add_apply,
          StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, hor_f,
          Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc] at hr
        cases htr : es.g.inTransit P.other c with
        | none =>
          simp only [htr, StateT.run_pure, StateT.run_set, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        | some rec =>
          have hrec_mem : rec ∈ es.g.trans ∧ rec.ct = c := by
            unfold _root_.CryptoGames.SM.GameState.inTransit at htr
            have hfind := List.find?_some htr
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
            exact ⟨List.mem_of_find?_eq_some htr, hfind.2⟩
          have hc_ep : c.1.1 = rec.pos.epoch := by
            rw [← hrec_mem.2]
            exact htr_inv rec hrec_mem.1
          simp only [htr, CryptoGames.SM.Construction.AuthL11.run_liftH, StateT.run_bind, StateT.run_pure,
            simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc,
            bucketAuthCfg, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vr, h1⟩, sp1⟩, hr_vr, hr_rest⟩
          cases res_vr with
          | none =>
            simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_set,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
              exists_eq_left] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some opt_vr =>
            cases opt_vr with
            | none =>
              simp only [StateT.run_pure, StateT.run_set,
                simulateQ_pure, support_pure, Set.mem_singleton_iff, exists_eq_left] at hr_rest
              subst hr_rest
              exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
            | some vtim =>
              rcases vtim with ⟨vp', t', i', m'⟩
              dsimp only at hr_rest
              simp only [pure_bind, StateT.run_bind, run_commitE_forgedHdr,
                StateT.run_pure, StateT.run_modify, StateT.run_set, simulateQ_pure,
                support_pure, Set.mem_singleton_iff, exists_eq_left] at hr_rest
              subst hr_rest
              obtain ⟨_, _, hvp'_id, hvp'_tcur⟩ := support_vRecv_props prng
                (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) es.g P (es.g.st P)
                (es.g.epoch P) c (some rec) es.h sp
                (hvp_inv P).1 (hvp_inv P).2 hr_vr rfl
              rw [hc_ep] at hvp'_tcur
              exact doomed_branch4_of_accept hwin hvp_inv htr_inv hvp'_id hvp'_tcur
                hcur hmem hlt
    · rcases arg with ⟨P, c⟩
      by_cases hab : es.abort = true
      · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t _ es none sp (Or.inl hab) r hr]
        exact Or.inl hab
      · have hor_f : (es.abort || es.g.win) = false := by
          simp [Bool.eq_false_iff.mpr hab, hwin]
        simp only [stepForgedHdr, implPRNGBucketAuthGen, injectE, QueryImpl.add_apply,
          StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, hor_f, Bool.false_or,
          simulateQ_bind, bind_assoc, Bool.not_true] at hr
        by_cases hguard : ((es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, StateT.run_set, pure_bind,
            simulateQ_pure, hwin, Bool.not_false, Bool.true_and, Bool.false_and,
            Bool.false_eq_true, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        · have hsafe : es.g.safeInj (2 + Δcka) = true := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
            exact Bool.eq_true_of_not_eq_false hguard.2
          have hcur_le_epP : cur + (2 + Δcka) ≤ es.g.epoch P := by
            unfold _root_.CryptoGames.SM.GameState.safeInj at hsafe
            rw [hcur] at hsafe
            have hmin := healedBy_some_le hsafe
            have hleP : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
              cases P <;> simp
            omega
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.Construction.AuthL11.run_liftH,
            StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, pure_bind,
            bind_assoc, MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_vr, h1⟩, sp1⟩, hr_vr, hr_rest⟩
          cases res_vr with
          | none =>
            simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_set,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
              exists_eq_left] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some opt_vr =>
            cases opt_vr with
            | none =>
              simp only [StateT.run_pure, StateT.run_set,
                simulateQ_pure, hwin, Bool.not_false, Bool.true_and, Bool.false_and,
                Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff,
                exists_eq_left] at hr_rest
              subst hr_rest
              exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
            | some vtim =>
              rcases vtim with ⟨vp', t', i', m'⟩
              obtain ⟨ht'_eq, _, hvp'_id, hvp'_tcur⟩ := support_vRecv_props prng
                (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) es.g P (es.g.st P)
                (es.g.epoch P) c none es.h sp
                (hvp_inv P).1 (hvp_inv P).2 hr_vr rfl
              subst ht'_eq
              dsimp only at hr_rest
              by_cases hqep : qep + 1 < c.1.1
              · simp only [hqep, ↓reduceIte, StateT.run_pure, StateT.run_set,
                  simulateQ_pure, hwin, Bool.not_false, Bool.true_and, Bool.false_and,
                  Bool.false_eq_true, support_pure, Set.mem_singleton_iff,
                  exists_eq_left] at hr_rest
                subst hr_rest
                exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
              · simp only [hqep, ↓reduceIte] at hr_rest
                by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
                · have hacc_win : (es.g.accept P vp' ⟨P.other, c.1.1, i'⟩).win = false := hwin
                  simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_forgedHdr,
                    StateT.run_pure, StateT.run_modify, StateT.run_set, pure_bind, simulateQ_pure,
                    hwin, hacc_win, Bool.not_false, Bool.true_and, Bool.false_and,
                    Bool.false_eq_true, support_pure, Set.mem_singleton_iff,
                    exists_eq_left] at hr_rest
                  subst hr_rest
                  exact doomed_branch4_of_accept hwin hvp_inv htr_inv hvp'_id hvp'_tcur
                    hcur hmem hlt
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_rest
                  by_cases hfull : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
                  · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify,
                      StateT.run_set, pure_bind, StateT.run_pure, simulateQ_pure, hwin,
                      Bool.not_false, Bool.true_and, support_pure, Set.mem_singleton_iff,
                      exists_eq_left] at hr_rest
                    subst hr_rest
                    by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) &&
                        !isHonestHdrPRNGBucket es.h c.1) = true
                    · simp only [hnf, ↓reduceIte]
                      have hc_eq : c.1.1 = es.g.epoch P + 1 := by
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hnf
                        rw [(hvp_inv P).2] at hnf
                        exact hnf.1
                      exact Or.inr (Or.inr (Or.inl ⟨rfl, c.1.1, cur, rfl, hmem, hlt, by omega⟩))
                    · simp only [hnf, Bool.false_eq_true, ↓reduceIte]
                      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                      StateT.run_set, simulateQ_pure, hwin,
                      Bool.not_false, Bool.true_and, Bool.false_and, support_pure,
                      Set.mem_singleton_iff, exists_eq_left] at hr_rest
                    subst hr_rest
                    exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
    · by_cases hab : es.abort = true
      · rw [stepForgedHdr_state_eq_of_abort_or_win cka prng fs Δcka qep tL t _ es none sp (Or.inl hab) r hr]
        exact Or.inl hab
      · simp only [stepForgedHdr, implPRNGBucketAuthGen, QueryImpl.add_apply,
          StateT.run_bind, StateT.run_get, pure_bind] at hr
        by_cases hguard : (es.abort || es.g.win || !es.g.corrAllowed P) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr
          exact Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv, cur, hcur, hmem, hlt⟩))
        · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            simulateQ_bind, pure_bind, bind_assoc,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨⟨res_rv, h'⟩, sp1⟩, _, hr_rest⟩
          cases res_rv with
          | none =>
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest; exact Or.inl rfl
          | some stOut =>
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
            subst hr_rest
            refine Or.inr (Or.inr (Or.inr ⟨hwin, rfl, hvp_inv, htr_inv,
              _root_.CryptoGames.SM.maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)),
              by simp [_root_.CryptoGames.SM.GameState.afterCorr, _root_.CryptoGames.SM.GameState.leak],
              by simp [_root_.CryptoGames.SM.GameState.afterCorr, _root_.CryptoGames.SM.GameState.leak],
              ?_⟩))
            rw [hcur]
            exact ltOpt_mono hlt (Nat.le_max_left _ _)

private def runForgedHdrStep
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (oa : OracleComp (SMSpecAuth Γ T Sig SS RS M CCoins E) Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (CryptoGames.SM.Construction.AuthL11.pImpl prng)
    ((simulateQ (implPRNGBucketAuthGen
      (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t)
      Δcka qep fs.maxSkip tL true) oa).run st)).run sp
  pure (authOutForgedHdr Δcka tL r.1.2)

private theorem runForgedHdrStep_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runForgedHdrStep cka prng fs Δcka qep tL t (pure b) st sp =
      pure (authOutForgedHdr Δcka tL st) := by
  simp [runForgedHdrStep]

private theorem runForgedHdrStep_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (SMSpecAuth Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecAuth Γ T Sig SS RS M CCoins E).Range q →
      OracleComp (SMSpecAuth Γ T Sig SS RS M CCoins E) Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : CryptoGames.PRFPRNG.GameState Sig I K) :
    runForgedHdrStep cka prng fs Δcka qep tL t (liftM (OracleSpec.query q) >>= k) st sp =
      stepForgedHdr cka prng fs Δcka qep tL t q st sp >>= fun r =>
        runForgedHdrStep cka prng fs Δcka qep tL t (k r.1.1) r.1.2 r.2 := by
  simp [runForgedHdrStep, stepForgedHdr]

private theorem runForgedHdrStep_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (oa : OracleComp (SMSpecAuth Γ T Sig SS RS M CCoins E) Bool)
    {st : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : CryptoGames.PRFPRNG.GameState Sig I K}
    (hd : DoomedForgedHdr tL st) :
    𝒟[runForgedHdrStep cka prng fs Δcka qep tL t oa st sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing st sp with
  | pure b' =>
    rw [runForgedHdrStep_pure, authOutForgedHdr_eq_false_of_doomed hd]
    simp
  | query_bind q k ih =>
    rw [runForgedHdrStep_query_bind]
    exact CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepForgedHdr_doomed cka prng fs Δcka qep tL t q st sp hd r hr)

private theorem runForgedHdrStep_le_succ
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htH : healEpoch tL ≤ t)
    (oa : OracleComp (SMSpecAuth Γ T Sig SS RS M CCoins E) Bool)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : CryptoGames.PRFPRNG.GameState Sig I K}
    (hsf : SyncForgedHdr Δcka tL t stL spL stR spR) :
    𝒟[runForgedHdrStep cka prng fs Δcka qep tL t oa stL spL] {true} ≤
      𝒟[runForgedHdrStep cka prng fs Δcka qep tL (t + 1) oa stR spR] {true} := by
  induction oa using OracleComp.inductionOn generalizing stL stR spL spR with
  | pure b' =>
    rw [runForgedHdrStep_pure, runForgedHdrStep_pure]
    rcases stL with ⟨esL, winEpL⟩
    rcases stR with ⟨esR, winEpR⟩
    rcases hsf with ⟨hsync, hwinEp, _⟩
    dsimp only at hsync hwinEp
    subst hwinEp
    have hout : authOutForgedHdr Δcka tL (esL, winEpL) =
        authOutForgedHdr Δcka tL (esR, winEpL) := by
      cases winEpL with
      | none => rfl
      | some tWin =>
        simp only [authOutForgedHdr]
        rw [hsync.abortL, hsync.abortR, CryptoGames.SM.Construction.AuthL11.eraseSt_win hsync.g_eq,
          CryptoGames.SM.Construction.AuthL11.eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runForgedHdrStep_query_bind, runForgedHdrStep_query_bind]
    refine leComp_stepForgedHdr cka prng fs Δcka qep tL t htH q hsf _ _ ?_
    rintro ⟨⟨uL, stL'⟩, spL'⟩ ⟨⟨uR, stR'⟩, spR'⟩ (hd | ⟨hu, hsf'⟩)
    · rw [runForgedHdrStep_doomed cka prng fs Δcka qep tL t (k uL) hd]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uL hsf'

/-- Hop 2b (`ForgedHdr` adjacent-epoch step): ideal PRNG (`b = true`) on `ForgedHdr` at epoch
`t` is bounded by real PRNG (`b = false`) on `ForgedHdr` at epoch `t + 1` for
`healEpoch tL ≤ t < qep + 1`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridForgedHdr_le_succ_false_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CryptoGames.PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[CryptoGames.PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (t + 1) A)] {true} := by
  let _ := htHi
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (CryptoGames.PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = CryptoGames.SM.Construction.AuthL11.pImpl prng := rfl
  unfold CryptoGames.PRFPRNG.branch redPRNGAuthBucketHybridForgedHdr
    runPRNGAuthBucketHybridGen initPRNGBucketAuthHybrid
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    CryptoGames.SM.Construction.AuthL11.simulateQ_pImpl_run_lift_sampleT, pure_bind]
  refine CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  refine (leComp_rootInit_step (T := T) prng tL t lam (prng.init kr) htLo) _ _ ?_
  rintro ⟨⟨resL, hL0⟩, spL0⟩ ⟨⟨resR, hR0⟩, spR0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨rL0, rR0, kVal, hresL, hresR, hr0, hcL0, hcR0, hcrL0, hcrR0, hft0, htab0,
      hbL0, hbR0, hσ0, hprf0, hprng0, hcorr0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hresL hresR
    subst hresL hresR
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc]
    let pL := mkParties (T := T) (cka.initA kc) (cka.initB kc) rL0
      (fs.initSender kVal) (fs.initReceiver kVal)
    let pR := mkParties (T := T) (cka.initA kc) (cka.initB kc) rR0
      (fs.initSender kVal) (fs.initReceiver kVal)
    let esL0 : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I) :=
      { g := { st := (fun P => match P with | .A => pL.1 | .B => pL.2), b := false }, h := hL0 }
    let esR0 : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I) :=
      { g := { st := (fun P => match P with | .A => pR.1 | .B => pR.2), b := false }, h := hR0 }
    refine le_of_eq_of_le ?_ (le_of_le_of_eq
      (runForgedHdrStep_le_succ cka prng fs Δcka qep tL t htLo A
        (stL := (esL0, none)) (spL := spL0) (stR := (esR0, none)) (spR := spR0)
        ⟨?_, rfl, fun _ => rfl⟩) ?_)
    · dsimp only [esL0, pL, runForgedHdrStep]
      exact congrArg (fun c => 𝒟[c] {true}) (congrArg (_ >>= ·) (funext fun x => by
        rcases x with ⟨⟨_, es, winEp⟩, sp'⟩
        cases winEp <;> simp [authOutForgedHdr, Function.comp_def]))
    · dsimp only [esL0, esR0, pL, pR]
      refine ⟨rfl, rfl, rfl, rfl, hcrL0, hcrR0, ?_, ?_, ?_, ?_, hft0, htab0, hbL0, hbR0,
        ?_, ?_, hprng0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro cur hcur; cases hcur
      · intro P
        cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hr0⟩
      · intro e'; rw [hcL0, hcR0]; exact Or.inl ⟨rfl, rfl⟩
      · intro e' _; rw [hcL0, hcR0]; exact ⟨rfl, rfl⟩
      · simpa using hσ0
      · simpa using hprf0
      · simpa using hcorr0
      · intro pos hpos; cases hpos
      · intro r hr; cases hr
      · intro P _ hpos; simp at hpos
      · intro r hr; cases hr
      · intro P; simp
      · intro P hlt; simp at hlt
    · dsimp only [esR0, pR, runForgedHdrStep]
      exact (congrArg (fun c => 𝒟[c] {true}) (congrArg (_ >>= ·) (funext fun x => by
        rcases x with ⟨⟨_, es, winEp⟩, sp'⟩
        cases winEp <;> simp [authOutForgedHdr, Function.comp_def]))).symm

end Hop2bForgedHdr

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bForgedHdr
