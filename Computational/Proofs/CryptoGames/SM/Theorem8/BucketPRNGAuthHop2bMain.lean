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
# Stage-2 `canon`-Bucket Multi-Epoch PRNG Hybrid: Hop 2b `Main` Step

Proves `prng_branch_true_redPRNGAuthBucketHybridMain_le_succ_false_impl`, bounding the ideal
(`b = true`) `PRFPRNG` branch of `redPRNGAuthBucketHybridMain` at epoch `t` by the real (`b = false`)
branch at epoch `t + 1` for `healEpoch tL ≤ t < qep + 1`.-/

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bMain

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM
  (Config GameState Pos Record RecvResult
   authLosingConditionsAvoided canon healedBy lastLeakGuessAdmissible ltOpt maxOpt spec)
open _root_.CryptoGames.SM.Engine
  (VP Ctx HM EState EM Hooks abortE liftH vSend vRecv commitE deliverE injectE)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch realParty mkParties sampleT SchemeAdversary)
open _root_.CryptoGames.SM.Construction.AuthL11
  (LeComp SMSpec SMComp eraseSt pImpl
   eraseSt_epoch eraseSt_idx eraseSt_tL eraseSt_trans eraseSt_chall eraseSt_comp
   eraseSt_maxAcc eraseSt_b eraseSt_win eraseSt_leaks eraseSt_corrs eraseSt_update_st
   eraseSt_safeCh eraseSt_safeInj eraseSt_inTransit eraseSt_trivial
   eraseSt_corrAllowed eraseSt_afterCorr eraseSt_record eraseSt_accept eraseSt_authOK
   sendsIn_other sendsIn_succ_false max_epoch_eq_of_eq max_epoch_update_succ
   epoch_eq_other_of_sendsIn_succ epMgmt_sync run_liftH
   simulateQ_pImpl_run_lift_sampleT simulateQ_pImpl_processQuery
   simulateQ_pImpl_challPrngQuery simulateQ_pImpl_challPrfQuery simulateQ_pImpl_corrQuery
   run_processImpl_some run_processImpl_none run_challPrngImpl_none run_challPrfImpl run_corrImpl
   evalDist_bind_mono evalDist_bind_eq_zero)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
  (PRNGBucketAuthEState PRNGBucketAuthState bucketAuthCfg hooksPRNGBucketAuthHybrid
   hooksPRNGBucketAuthMain implPRNGBucketAuthGen initPRNGBucketAuthHybrid liftPBucketAuth
   lookupPRNGBucketAuthF postLeak redPRNGAuthBucketHybridMain resolveCorrRoot
   rootPRNGBucketAuthHybrid runPRNGAuthBucketHybridGen)

section Hop2bMain

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

/-! ### 1. Pure `postLeak`, `resolveCorrRoot`, `DoomedMain`, and `GameState` Helpers -/

@[local simp]
private theorem simulateQ_pImpl_liftPBucketAuth
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K] {α : Type}
    (prng : PRFPRNG KR Sig I K) (x : PRFPRNG.AdversaryComp Sig I K α)
    (h : PRNGBucketAuthState T Sig K I) :
    simulateQ (pImpl prng) ((liftPBucketAuth (T := T) x).run h) =
      (simulateQ (pImpl prng) x >>= fun u => pure (u, h)) := by
  simp [liftPBucketAuth, StateT.run_lift, map_eq_bind_pure_comp]

@[local simp]
private theorem resolveCorrRoot_some (h : PRNGBucketAuthState T Sig K I) (ep : ℕ) (σ : Sig) :
    resolveCorrRoot h ep (some σ) = some σ := rfl

private theorem resolveCorrRoot_of_corrRoot_none {h : PRNGBucketAuthState T Sig K I}
    (hc : h.corrRoot = none) (ep : ℕ) (r : Option Sig) :
    resolveCorrRoot h ep r = r := by
  cases r <;> simp [resolveCorrRoot, hc]

private theorem resolveCorrRoot_set_of_isNone {h : PRNGBucketAuthState T Sig K I}
    (hnone : h.corrRoot.isNone = true) {ep : ℕ} {r : Option Sig} {τ : Sig}
    (hres : resolveCorrRoot h ep r = some τ) (v : Option (ℕ × Sig)) :
    resolveCorrRoot { h with corrRoot := v } ep r = some τ := by
  have hc : h.corrRoot = none := Option.isNone_iff_eq_none.mp hnone
  rw [resolveCorrRoot_of_corrRoot_none hc] at hres
  subst hres
  rfl

private theorem eraseSt_postLeak {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (tL : Option ℕ) :
    postLeak tL g₁ = postLeak tL g₂ := by
  have htL : g₁.tL = g₂.tL := congrArg GameState.tL h
  simp [postLeak, htL]

private theorem ltOpt_of_ge_healEpoch {tL : Option ℕ} {n : ℕ} (h : healEpoch tL ≤ n) :
    ltOpt tL n = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp only [healEpoch] at h
    simp only [ltOpt, decide_eq_true_eq]
    omega

private theorem ltOpt_mono {tL : Option ℕ} {a b : ℕ} (hab : a ≤ b) (h : ltOpt tL a = true) :
    ltOpt tL b = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp only [ltOpt, decide_eq_true_eq] at h ⊢
    omega

private theorem postLeak_leak_of_true {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (h : postLeak tL g = true) (l : ℕ) :
    postLeak tL (g.leak l) = true := by
  unfold postLeak GameState.leak at *
  cases htL : g.tL with
  | none => simp [htL] at h
  | some cur =>
    simp only [htL] at h
    dsimp only [maxOpt]
    exact ltOpt_mono (Nat.le_max_left cur l) h

private theorem postLeak_leak_of_ge_healEpoch {St Msg C : Type} {tL : Option ℕ}
    (g : GameState St Msg C) {l : ℕ} (hl : healEpoch tL ≤ l) :
    postLeak tL (g.leak l) = true := by
  unfold postLeak GameState.leak
  dsimp only
  have hle : l ≤ maxOpt g.tL l := by
    cases g.tL <;> simp [maxOpt]
  exact ltOpt_of_ge_healEpoch (le_trans hl hle)

private theorem postLeak_epMgmt_of_true {St Msg C : Type} {tL : Option ℕ}
    {g g' : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hpl : postLeak tL g = true) (hep : g.epMgmt Δ qep P bad = some g') :
    postLeak tL g' = true := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hq1 hc hq2
  · cases hep
    simpa [postLeak] using postLeak_leak_of_true hpl (g.epoch P + 1)
  · cases hep
    simpa [postLeak] using hpl
  · cases hep
    exact hpl

private theorem safeCh_true_of_postLeak_false_admissible {St Msg C : Type} {tL : Option ℕ} {Δcka : ℕ}
    {g : GameState St Msg C} {P : Party}
    (hpl : postLeak tL g = false)
    (hadm : lastLeakGuessAdmissible (2 + Δcka) tL (g.epoch P) = true) :
    g.safeCh (2 + Δcka) P = true := by
  unfold GameState.safeCh
  cases hgtL : g.tL with
  | none => simp [healedBy]
  | some cur =>
    simp only [postLeak, hgtL] at hpl
    cases tL with
    | none => simp [ltOpt] at hpl
    | some l =>
      simp only [ltOpt, decide_eq_false_iff_not] at hpl
      simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hadm ⊢
      omega

private def authOutBucketMain (Δ : ℕ) (tL : Option ℕ)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Bool :=
  match st.2 with
  | none => false
  | some tWin => !st.1.abort && st.1.g.win && authLosingConditionsAvoided Δ tL tWin st.1.g

private def DoomedMain (Δcka : ℕ) (tL : Option ℕ)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Prop :=
  st.1.abort = true ∨
  (∀ P : Party, ∃ e, (P, e) ∈ st.1.g.corrs ∧ ltOpt tL e = true) ∨
  (∃ l ∈ st.1.g.leaks, ltOpt tL l = true ∧
    ∀ tWin, lastLeakGuessAdmissible (2 + Δcka) tL tWin = true → l < tWin)

private theorem authOutBucketMain_eq_false_of_doomedMain {Δcka : ℕ} {tL : Option ℕ}
    {st : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    (hd : DoomedMain Δcka tL st) :
    authOutBucketMain (2 + Δcka) tL st = false := by
  rcases st with ⟨es, winEp⟩
  rcases hd with hab | hcorrs | ⟨l_bad, hmem_l, hlt_l, hgt_l⟩
  · dsimp only at hab
    cases winEp <;> simp [authOutBucketMain, hab]
  · cases winEp with
    | none => rfl
    | some tWin =>
      dsimp only [authOutBucketMain]
      obtain ⟨e, hmem, hlt⟩ := hcorrs (Party.receiverOf tWin)
      have hall_false :
          es.g.corrs.all (fun pe => !(pe.1 == Party.receiverOf tWin && ltOpt tL pe.2)) = false := by
        rw [List.all_eq_false]
        exact ⟨(Party.receiverOf tWin, e), hmem, by simp [hlt]⟩
      unfold authLosingConditionsAvoided
      rw [hall_false]
      simp
  · cases winEp with
    | none => rfl
    | some tWin =>
      dsimp only [authOutBucketMain]
      unfold authLosingConditionsAvoided
      by_cases hadm : lastLeakGuessAdmissible (2 + Δcka) tL tWin = true
      · have hlt_win : l_bad < tWin := hgt_l tWin hadm
        have hleaks_false :
            es.g.leaks.all (fun l => !(ltOpt tL l && decide (l < tWin))) = false := by
          rw [List.all_eq_false]
          exact ⟨l_bad, hmem_l, by simp [hlt_l, hlt_win]⟩
        rw [hleaks_false]
        simp
      · simp [Bool.eq_false_iff.mpr hadm]

/-! ### 2. Coupling Relations: `VPBaseRel`, `ModePre`, `ModeAllResolved`, `ModePostCorr`, `SyncStepMain` -/

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

private theorem RelStepRoot.eq_of_ne_t {tH t : ℕ} {σR_sp : Sig} {e : ℕ} {rL rR : Option Sig}
    (hne : e ≠ t) (h : RelStepRoot tH t σR_sp e rL rR) : rL = rR := by
  rcases h with ⟨_, σ, hL, hR⟩ | ⟨_, _, hL, hR⟩ | ⟨heq, _⟩ | ⟨_, σ, hL, hR⟩
  · rw [hL, hR]
  · rw [hL, hR]
  · exact False.elim (hne heq)
  · rw [hL, hR]

private theorem RelStepRoot.some_of_lt_tH {tH t : ℕ} {σR_sp : Sig} {e : ℕ} {rL rR : Option Sig}
    (htLo : tH ≤ t) (hlt : e < tH) (h : RelStepRoot tH t σR_sp e rL rR) :
    ∃ σ, rL = some σ ∧ rR = some σ := by
  rcases h with ⟨_, h1⟩ | ⟨hle, _⟩ | ⟨heq, _⟩ | ⟨hgt, _⟩
  · exact h1
  · omega
  · omega
  · omega

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

private structure VPBaseRel (e : ℕ) (P : Party)
    (vpL vpR : VP Γ T (Option Sig) SS RS) : Prop where
  id_L : vpL.id = P
  tcur_L : vpL.tcur = e
  id_R : vpR.id = P
  tcur_R : vpR.tcur = e
  γ_eq : vpL.γ = vpR.γ
  Tcur_eq : vpL.curCkaMsg = vpR.curCkaMsg
  vS_eq : vpL.vS = vpR.vS
  vR_eq : ∀ t', vpL.vR t' = vpR.vR t'

private structure ModePre (tL : Option ℕ) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop where
  pl_false : postLeak tL esR.g = false
  corrRootL : esL.h.corrRoot = none
  corrRootR : esR.h.corrRoot = none
  vp_root : ∀ P, RelStepRoot (healEpoch tL) t spR.σ (esR.g.epoch P)
    (esL.g.st P).root (esR.g.st P).root
  cache_rel : ∀ e, RelCacheStep (healEpoch tL) t spR.σ e (esL.h.cache e) (esR.h.cache e)
  fTable_ne : ∀ t0, t0 ≠ t → esL.h.fTable t0 = esR.h.fTable t0
  table_t : spL.table = esR.h.fTable t
  spL_b : spL.b = true
  spR_b : spR.b = false
  sp_σ_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL.σ = spR.σ
  spL_prf_lt : max (esR.g.epoch .A) (esR.g.epoch .B) < t → spL.prf = false
  spR_prf_le : max (esR.g.epoch .A) (esR.g.epoch .B) ≤ t → spR.prf = false
  spR_prng : spR.prng = false
  spR_corr : healEpoch tL ≤ max (esR.g.epoch .A) (esR.g.epoch .B) → spR.corr = false

private structure ModeAllResolved (tL : Option ℕ)
    (esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
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

private def ModePostCorr (tL : Option ℕ) (t : ℕ)
    (esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
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

private inductive ModeMain (tL : Option ℕ) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop
  | pre (hm : ModePre tL t esL spL esR spR)
  | allResolved (hm : ModeAllResolved tL esL esR)
  | postCorr (hm : ModePostCorr tL t esL esR)

private structure SyncStepMain (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (esL : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spL : PRFPRNG.GameState Sig I K)
    (esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (spR : PRFPRNG.GameState Sig I K) : Prop where
  abortL : esL.abort = false
  abortR : esR.abort = false
  g_eq : eraseSt esL.g = eraseSt esR.g
  vp_base : ∀ P, VPBaseRel (esR.g.epoch P) P (esL.g.st P) (esR.g.st P)
  cache_gt_max : ∀ e, max (esR.g.epoch .A) (esR.g.epoch .B) < e →
    esL.h.cache e = none ∧ esR.h.cache e = none
  epoch_le : ∀ P, esR.g.epoch P ≤ esR.g.epoch P.other + 1
  epoch_sends : ∀ P, esR.g.epoch P.other < esR.g.epoch P → P.sendsIn (esR.g.epoch P) = true
  trans_epoch : ∀ r ∈ esR.g.trans,
    r.pos.epoch ≤ esR.g.epoch r.pos.sender ∧ r.ct.1.1 = r.pos.epoch
  comp_epoch : ∀ pos ∈ esR.g.comp, pos.epoch ≤ esR.g.epoch pos.sender
  ahead_in_trans :
    postLeak tL esR.g = false →
    ∀ Q : Party, esR.g.epoch Q.other < esR.g.epoch Q →
      lastLeakGuessAdmissible (2 + Δcka) tL (esR.g.epoch Q) = true →
      ∃ r ∈ esR.g.trans,
        r.pos.sender = Q ∧ r.pos.epoch = esR.g.epoch Q ∧ r.pos ∉ esR.g.comp
  mode : ModeMain tL t esL spL esR spR

private theorem SyncStepMain.corr_epoch_dichotomy
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR)
    (hpl : postLeak tL esR.g = false)
    {P : Party} (hallow : esR.g.corrAllowed P = true) :
    esR.g.epoch P.other ≤ esR.g.epoch P ∨
    (esR.g.epoch P.other = esR.g.epoch P + 1 ∧
      lastLeakGuessAdmissible (2 + Δcka) tL (esR.g.epoch P + 1) = false) := by
  by_cases hle : esR.g.epoch P.other ≤ esR.g.epoch P
  · exact Or.inl hle
  · have hlt : esR.g.epoch P < esR.g.epoch P.other := Nat.lt_of_not_le hle
    have hle1 : esR.g.epoch P.other ≤ esR.g.epoch P + 1 := by
      simpa [Party.other_other] using hsync.epoch_le P.other
    have heq_other : esR.g.epoch P.other = esR.g.epoch P + 1 := by omega
    refine Or.inr ⟨heq_other, ?_⟩
    by_contra hadm_not
    have hadm : lastLeakGuessAdmissible (2 + Δcka) tL (esR.g.epoch P + 1) = true :=
      Bool.eq_true_of_not_eq_false hadm_not
    obtain ⟨r, hr_mem, hr_send, _, hr_ncomp⟩ :=
      hsync.ahead_in_trans hpl P.other (by simpa [Party.other_other] using hlt)
        (by rw [heq_other]; exact hadm)
    unfold GameState.corrAllowed at hallow
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hallow
    have hnot := hallow.2 r hr_mem
    simp [hr_send, hr_ncomp] at hnot

/-! ### 3. `PRFPRNG`, `lookupPRNGBucketAuthF`, and `rootPRNGBucketAuthHybrid` Coupling -/

private theorem leComp_lookupBucketAuthF_step
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t t0 : ℕ) (ik : I)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hne : t0 ≠ t)
    (hft : ∀ t', t' ≠ t → hL.fTable t' = hR.fTable t') :
    LeComp
      (fun (r1 : (K × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1.1 = r2.1.1 ∧
        r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
        r1.1.2.corrRoot = hL.corrRoot ∧ r2.1.2.corrRoot = hR.corrRoot ∧
        r1.2 = spL ∧ r2.2 = spR ∧
        (∀ t', t' ≠ t → r1.1.2.fTable t' = r2.1.2.fTable t') ∧
        r2.1.2.fTable t = hR.fTable t)
      ((simulateQ (pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t0 ik).run hL)).run spL)
      ((simulateQ (pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t0 ik).run hR)).run spR) := by
  unfold lookupPRNGBucketAuthF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft t0 hne]
  cases hlk : (hR.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hft, rfl⟩
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_pImpl_run_lift_sampleT,
      bind_assoc]
    refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    refine LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩
    · by_cases heq : t' = t0
      · subst heq; simp
      · simp [heq, hft t' ht']
    · simp [hne.symm]

private theorem leComp_challPrf_lookupAuthF
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t : ℕ) (ik : I)
    (hR : PRNGBucketAuthState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (hbL : spL.b = true)
    (htab : spL.table = hR.fTable t) :
    LeComp
      (fun (r1 : Option (Sig × K) × PRFPRNG.GameState Sig I K)
           (r2 : (K × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        r1.1 = none ∨
        (r1.1 = some ((prng.up spL.σ ik).1, r2.1.1) ∧
          r2.1.2.cache = hR.cache ∧ r2.1.2.corrRoot = hR.corrRoot ∧ r2.2 = spR ∧
          r1.2.σ = spL.σ ∧ r1.2.b = true ∧
          (∀ t', t' ≠ t → r2.1.2.fTable t' = hR.fTable t') ∧
          r1.2.table = r2.1.2.fTable t))
      ((PRFPRNG.challPrfImpl prng ik).run spL)
      ((simulateQ (pImpl prng)
        ((lookupPRNGBucketAuthF (T := T) (Sig := Sig) t ik).run hR)).run spR) := by
  rw [run_challPrfImpl]
  by_cases hbadL : (spL.corr || spL.prng) = true
  · simp only [hbadL, ↓reduceIte]
    exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
  · unfold lookupPRNGBucketAuthF
    simp only [hbadL, hbL, Bool.false_eq_true, ↓reduceIte, htab,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases hlk : (hR.fTable t).lookup ik with
    | some k =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩)
    | none =>
      simp only [StateT.run_bind, simulateQ_bind,
        simulateQ_pImpl_run_lift_sampleT, bind_assoc]
      refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
      simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      refine LeComp.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun t' ht' => ?_, ?_⟩)
      · simp [ht']
      · simp

private theorem leComp_rootInit_main
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t : ℕ) (lam : I) (σ0 : Sig)
    (htLo : healEpoch tL ≤ t) :
    LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K) =>
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
          (0 < t → r1.2.prf = false) ∧
          r2.2.prf = false ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ 0 → r2.2.corr = false))
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t 0 false lam none).run
          ({} : PRNGBucketAuthState T Sig K I))).run { σ := σ0, b := true })
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (t + 1) 0 false lam none).run
          ({} : PRNGBucketAuthState T Sig K I))).run { σ := σ0, b := false }) := by
  have h0_nlt_t : ¬ (t < 0) := by omega
  have h0_nlt_t1 : ¬ (t + 1 < 0) := by omega
  have h0_ne_t1 : ¬ (0 = t + 1) := by omega
  unfold rootPRNGBucketAuthHybrid
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
        Option.isSome_none, Bool.false_and, Bool.false_eq_true,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        simulateQ_pImpl_challPrfQuery,
        simulateQ_pImpl_processQuery, run_processImpl_some, pure_bind]
      refine (leComp_challPrf_lookupAuthF prng 0 lam {}
        { σ := σ0, b := true } { σ := (prng.up σ0 lam).1, b := false } rfl rfl).bind ?_
      rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
      rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
      · dsimp only at hnone; subst hnone
        simp only [StateT.run_pure, simulateQ_pure]
        exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hresL hcR1 hcrR1 hspR1 hσL1 hbL1 hft1 htab1
        subst hresL hspR1
        simp only [StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, none, kOut, rfl, rfl,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), rfl, hcR1, rfl, hcrR1,
          fun t0 ht0 => (hft1 t0 ht0).symm, htab1,
          hbL1, rfl, False.elim, False.elim, rfl, rfl, fun _ => rfl⟩)
    · have h0_lt_t : 0 < t := by omega
      simp only [h0_eq_t, healEpoch, Nat.lt_irrefl, decide_false, Bool.not_false, ↓reduceIte,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        simulateQ_pImpl_processQuery, run_processImpl_some, pure_bind]
      refine (leComp_lookupBucketAuthF_step prng t 0 lam {} {}
        { σ := (prng.up σ0 lam).1, b := true } { σ := (prng.up σ0 lam).1, b := false }
        h0_eq_t (fun _ _ => rfl)).bind ?_
      rintro ⟨⟨kL, hL1⟩, spL1⟩ ⟨⟨kR, hR1⟩, spR1⟩
        ⟨hk_eq, hcL1, hcR1, hcrL1, hcrR1, hspL1, hspR1, hft1, htab1⟩
      dsimp only at hk_eq hcL1 hcR1 hcrL1 hcrR1 hspL1 hspR1 hft1 htab1
      subst hk_eq hspL1 hspR1
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
        Or.inr (Or.inl ⟨by simp, h0_lt_t, rfl, rfl⟩), hcL1, hcR1, hcrL1, hcrR1, hft1,
        htab1.symm, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩)
  · have h0_lt_tH : 0 < healEpoch tL := by
      by_contra hle; exact hge_tH (by simp [hle])
    have h0_ne_t : ¬ (0 = t) := by omega
    simp only [h0_ne_t, hge_tH, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
      simulateQ_pImpl_processQuery, simulateQ_pImpl_corrQuery,
      run_processImpl_some, pure_bind, run_corrImpl,
      StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨some (prng.up σ0 lam).1, some (prng.up σ0 lam).1,
      (prng.up σ0 lam).2, rfl, rfl, Or.inl ⟨h0_lt_tH, (prng.up σ0 lam).1, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
      rfl, rfl, fun hle => by omega⟩)

private theorem leComp_rootSend_pre
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t eMax : ℕ) (ik0 : I)
    (rL0 rR0 : Option Sig)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (htLo : healEpoch tL ≤ t)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t spR.σ eMax rL0 rR0)
    (hft : ∀ t0, t0 ≠ t → hL.fTable t0 = hR.fTable t0)
    (htab : spL.table = hR.fTable t)
    (hbL : spL.b = true) (hbR : spR.b = false)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfL_lt : eMax < t → spL.prf = false)
    (hprfR_le : eMax ≤ t → spR.prf = false)
    (hprngR : spR.prng = false)
    (hcorrR : healEpoch tL ≤ eMax → spR.corr = false) :
    LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K) =>
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
          (eMax + 1 < t → r1.2.prf = false) ∧
          (eMax + 1 ≤ t → r2.2.prf = false) ∧
          r2.2.prng = false ∧
          (healEpoch tL ≤ eMax + 1 → r2.2.corr = false))
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t (eMax + 1) false ik0 rL0).run hL)).run spL)
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (t + 1) (eMax + 1) false ik0 rR0).run hR)).run spR) := by
  rcases spL with ⟨σL, bL, corrL, prngL, prfL, tabL⟩
  rcases spR with ⟨σR, bR, corrR, prngR, prfR, tabR⟩
  dsimp only at hr0 htab hbL hbR hσ_lt hprfL_lt hprfR_le hprngR hcorrR
  subst hbL hbR hprngR htab
  have hresL0 : resolveCorrRoot hL eMax rL0 = rL0 := resolveCorrRoot_of_corrRoot_none hcrL eMax rL0
  have hresR0 : resolveCorrRoot hR eMax rR0 = rR0 := resolveCorrRoot_of_corrRoot_none hcrR eMax rR0
  have hisSomeL : (false || hL.corrRoot.isSome) = false := by simp [hcrL]
  have hisSomeR : (false || hR.corrRoot.isSome) = false := by simp [hcrR]
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
      simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
        hresL0, ht_lt, hnlt_t1, hisSomeR, Bool.false_eq_true, ↓reduceIte]
      simp only [heq_t1, ↓reduceIte]
      simp only [his_tH_false, Bool.false_eq_true, ↓reduceIte,
        hrL0_eq, StateT.run_pure, simulateQ_pure,
        StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
        simulateQ_pImpl_challPrfQuery, run_challPrfImpl,
        Bool.or_self, pure_bind]
      exact LeComp.pure (Or.inr ⟨some (prng.up σR ik0).1, some (prng.up σR ik0).1,
        (prng.up σR ik0).2, rfl, rfl,
        Or.inr (Or.inr (Or.inr ⟨by omega, (prng.up σR ik0).1, rfl, rfl⟩)),
        fun _ => rfl, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
        fun h => by omega, fun h => by omega, fun h => by omega, rfl, fun _ => rfl⟩)
    · have ht1_lt : t + 1 < eMax + 1 := by omega
      obtain ⟨σ0, hrL0_eq, hrR0_eq⟩ : ∃ σ0, rL0 = some σ0 ∧ rR0 = some σ0 := by
        rcases hr0 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · omega
        · omega
        · omega
        · exact h
      unfold rootPRNGBucketAuthHybrid
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
        ht_lt, ht1_lt, ↓reduceIte, hrL0_eq, hrR0_eq]
      exact LeComp.pure (Or.inr ⟨some (prng.up σ0 ik0).1, some (prng.up σ0 ik0).1,
        (prng.up σ0 ik0).2, rfl, rfl,
        Or.inr (Or.inr (Or.inr ⟨ht_lt, (prng.up σ0 ik0).1, rfl, rfl⟩)),
        fun _ => rfl, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
        fun h => by omega, fun h => by omega, fun h => by omega, rfl,
        fun _ => hcorrR (by omega)⟩)
  · have heMax_lt_t : eMax < t := by omega
    have hprfL := hprfL_lt heMax_lt_t
    have hprfR := hprfR_le (Nat.le_of_lt heMax_lt_t)
    have hσ_eq := hσ_lt heMax_lt_t
    subst hprfL hprfR hσ_eq
    have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
    have hne_t1 : ¬ (eMax + 1 = t + 1) := by omega
    unfold rootPRNGBucketAuthHybrid
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
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          simulateQ_pImpl_challPrngQuery,
          simulateQ_pImpl_processQuery,
          run_challPrngImpl_none, run_processImpl_none,
          Bool.false_eq_true, pure_bind]
        refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        simp only [pure_bind, bind_assoc, simulateQ_pImpl_run_lift_sampleT]
        refine LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
        simp only [pure_bind,
          simulateQ_pImpl_corrQuery,
          run_corrImpl, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨some (prng.up σL Ir).1, none, kRand, rfl, rfl,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
          fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
          fun h => by omega, fun h => by omega, fun _ => rfl, rfl, fun _ => rfl⟩)
      · have his_t_false : (tL.isSome && decide (t = healEpoch tL)) = false :=
          his_eq.trans (Bool.eq_false_iff.mpr his_tH)
        simp only [hge_t, his_t_false, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          simulateQ_pImpl_challPrfQuery,
          simulateQ_pImpl_processQuery, run_processImpl_some, pure_bind]
        refine (leComp_challPrf_lookupAuthF prng t ik0 hR
          { σ := σL, b := true, corr := corrL, prng := prngL, prf := false, table := hR.fTable t }
          { σ := (prng.up σL ik0).1, b := false, corr := corrR, prng := false, prf := false,
            table := tabR }
          rfl rfl).bind ?_
        rintro ⟨resL, spL1⟩ ⟨⟨kOut, hR1⟩, spR1⟩ hrel
        rcases hrel with hnone | ⟨hresL, hcR1, hcrR1, hspR1, hσL1, hbL1, hft1, htab1⟩
        · dsimp only at hnone; subst hnone
          simp only [StateT.run_pure, simulateQ_pure]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
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
          exact LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, none, kOut, rfl, rfl,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
            fun h => by omega, rfl, hcR1, hcrL, hcrR1.trans hcrR,
            fun t0 ht0 => (hft t0 ht0).trans (hft1 t0 ht0).symm, htab1, hbL1, rfl,
            fun h => by omega, fun h => by omega, fun _ => rfl, rfl, fun _ => hcorrR0⟩)
    · have heMax1_lt_t : eMax + 1 < t := by omega
      simp only [heq_t, ↓reduceIte]
      by_cases hge_tH : (!(eMax + 1 < healEpoch tL)) = true
      · simp only [hge_tH, ↓reduceIte]
        by_cases his_tH : (tL.isSome && decide (eMax + 1 = healEpoch tL)) = true
        · simp only [his_tH, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
            simulateQ_pImpl_processQuery,
            run_processImpl_none, Bool.false_eq_true, pure_bind]
          refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
          simp only [pure_bind, bind_assoc,
            simulateQ_pImpl_run_lift_sampleT]
          refine LeComp.sample_bind ($ᵗ K) fun kRand _ => ?_
          simp only [StateT.run_pure, simulateQ_pure]
          have hge_tH_prop : healEpoch tL ≤ eMax + 1 := by
            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hge_tH; omega
          exact LeComp.pure (Or.inr ⟨none, none, kRand, rfl, rfl,
            Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
            fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
            fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩)
        · simp only [his_tH, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
            simulateQ_pImpl_processQuery, run_processImpl_some, pure_bind,
            StateT.run_bind, simulateQ_bind]
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
          exact LeComp.pure (Or.inr ⟨none, none, kL, rfl, rfl,
            Or.inr (Or.inl ⟨hge_tH_prop, heMax1_lt_t, rfl, rfl⟩),
            fun h => by omega, hcL1, hcR1, hcrL1.trans hcrL, hcrR1.trans hcrR,
            hft1, htab1.symm, rfl, rfl,
            fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => hcorrR0⟩)
      · have hlt_tH : eMax + 1 < healEpoch tL := by
          by_contra hle; exact hge_tH (by simp [hle])
        simp only [hge_tH, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
          simulateQ_pImpl_processQuery, simulateQ_pImpl_corrQuery,
          run_processImpl_some, run_corrImpl,
          Bool.false_eq_true, pure_bind, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨some (prng.up σL ik0).1, some (prng.up σL ik0).1,
          (prng.up σL ik0).2, rfl, rfl,
          Or.inl ⟨hlt_tH, (prng.up σL ik0).1, rfl, rfl⟩,
          fun h => by omega, rfl, rfl, hcrL, hcrR, hft, rfl, rfl, rfl,
          fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun h => by omega⟩)

private theorem run_rootSend_post
    [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (m t0 : ℕ) (ik0 : I)
    (r0 : Option Sig) (h : PRNGBucketAuthState T Sig K I) (σ : Sig)
    (hres : resolveCorrRoot h (t0 - 1) r0 = some σ) :
    (rootPRNGBucketAuthHybrid prng tL m t0 true ik0 r0).run h =
      pure (some (some (prng.up σ ik0).1, (prng.up σ ik0).2), h) := by
  unfold rootPRNGBucketAuthHybrid
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hres, Bool.true_or, ↓reduceIte]
  split_ifs <;> rfl

private theorem leComp_rootSend_postLeak_from_pre
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t eMax : ℕ) (ik0 : I)
    (rL0 rR0 : Option Sig) (rOtherL rOtherR : Option Sig)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (htLo : healEpoch tL ≤ t)
    (hcrL : hL.corrRoot = none) (hcrR : hR.corrRoot = none)
    (hr0 : RelStepRoot (healEpoch tL) t spR.σ eMax rL0 rR0)
    (hrOther : RelStepRoot (healEpoch tL) t spR.σ eMax rOtherL rOtherR)
    (hσ_lt : eMax < t → spL.σ = spR.σ)
    (hprfL_lt : eMax < t → spL.prf = false)
    (hprfR_le : eMax ≤ t → spR.prf = false) :
    LeComp
      (fun (r1 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K)
           (r2 : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K) =>
        ∃ σNew kVal σOther,
          r1.1.1 = some (some σNew, kVal) ∧ r2.1.1 = some (some σNew, kVal) ∧
          r1.1.2.cache = hL.cache ∧ r2.1.2.cache = hR.cache ∧
          resolveCorrRoot r1.1.2 eMax rOtherL = some σOther ∧
          resolveCorrRoot r2.1.2 eMax rOtherR = some σOther)
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t (eMax + 1) true ik0 rL0).run hL)).run spL)
      ((simulateQ (pImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL (t + 1) (eMax + 1) true ik0 rR0).run hR)).run spR) := by
  have hresL0 : resolveCorrRoot hL eMax rL0 = rL0 := resolveCorrRoot_of_corrRoot_none hcrL eMax rL0
  have hresR0 : resolveCorrRoot hR eMax rR0 = rR0 := resolveCorrRoot_of_corrRoot_none hcrR eMax rR0
  rcases hr0 with ⟨hlt_tH, σ0, hrL0, hrR0⟩ | ⟨hge_tH, hlt_t, hrL0, hrR0⟩ |
      ⟨heq_t, hrL0, hrR0⟩ | ⟨hgt_t, σ0, hrL0, hrR0⟩
  · obtain ⟨σO, hrOL, hrOR⟩ : ∃ σO, rOtherL = some σO ∧ rOtherR = some σO := by
      rcases hrOther with ⟨_, h1⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h1
      · omega
      · omega
      · omega
    have hrunL := run_rootSend_post (T := T) prng tL t (eMax + 1) ik0 rL0 hL σ0
      (by simp [hrL0])
    have hrunR := run_rootSend_post (T := T) prng tL (t + 1) (eMax + 1) ik0 rR0 hR σ0
      (by simp [hrR0])
    rw [hrunL, hrunR]
    simp only [simulateQ_pure, StateT.run_pure]
    exact LeComp.pure ⟨(prng.up σ0 ik0).1, (prng.up σ0 ik0).2, σO, rfl, rfl, rfl, rfl,
      by simp [hrOL], by simp [hrOR]⟩
  · have hrOL : rOtherL = none ∧ rOtherR = none := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, _, h1, h2⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · omega
      · exact ⟨h1, h2⟩
      · omega
      · omega
    subst hrL0 hrR0
    have hprfL := hprfL_lt hlt_t
    have hprfR := hprfR_le (Nat.le_of_lt hlt_t)
    have hσ_eq := hσ_lt hlt_t
    have hnlt_t : ¬ (t < eMax + 1) := by omega
    have hnlt_t1 : ¬ (t + 1 < eMax + 1) := by omega
    unfold rootPRNGBucketAuthHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
      hresL0, hresR0, hnlt_t, hnlt_t1, Bool.true_or, ↓reduceIte,
      simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
      simulateQ_pImpl_corrQuery, run_corrImpl, hprfL, hprfR, hσ_eq,
      Bool.false_eq_true, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure ⟨(prng.up spR.σ ik0).1, (prng.up spR.σ ik0).2, spR.σ, rfl, rfl, rfl, rfl,
      by simp [resolveCorrRoot, hrOL.1], by simp [resolveCorrRoot, hrOL.2]⟩
  · subst eMax
    have hrOL : rOtherL = some spR.σ ∧ rOtherR = none := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, h1, h2⟩ | ⟨h, _⟩
      · omega
      · omega
      · exact ⟨h1, h2⟩
      · omega
    subst hrL0 hrR0
    have hprfR := hprfR_le le_rfl
    have ht_lt : t < t + 1 := by omega
    have hnlt_t1 : ¬ (t + 1 < t + 1) := by omega
    unfold rootPRNGBucketAuthHybrid
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.add_sub_cancel,
      hresL0, hresR0, ht_lt, hnlt_t1, Bool.true_or, ↓reduceIte,
      simulateQ_bind, bind_assoc, simulateQ_pImpl_liftPBucketAuth,
      simulateQ_pImpl_corrQuery, run_corrImpl, hprfR,
      Bool.false_eq_true, StateT.run_modify, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure ⟨(prng.up spR.σ ik0).1, (prng.up spR.σ ik0).2, spR.σ, rfl, rfl, rfl, rfl,
      by simp [hrOL.1], by simp [resolveCorrRoot, hrOL.2]⟩
  · obtain ⟨σO, hrOL, hrOR⟩ : ∃ σO, rOtherL = some σO ∧ rOtherR = some σO := by
      rcases hrOther with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h1⟩
      · omega
      · omega
      · omega
      · exact h1
    have hrunL := run_rootSend_post (T := T) prng tL t (eMax + 1) ik0 rL0 hL σ0
      (by simp [hrL0])
    have hrunR := run_rootSend_post (T := T) prng tL (t + 1) (eMax + 1) ik0 rR0 hR σ0
      (by simp [hrR0])
    rw [hrunL, hrunR]
    simp only [simulateQ_pure, StateT.run_pure]
    exact LeComp.pure ⟨(prng.up σ0 ik0).1, (prng.up σ0 ik0).2, σO, rfl, rfl, rfl, rfl,
      by simp [hrOL], by simp [hrOR]⟩

/-! ### 4. Hook & Oracle Step Coupling (`vRecv`, `deliverE`, `inject`, `transmit`, `corr`) -/

private def StepRelMainRaw (Δcka : ℕ) (tL : Option ℕ) (t : ℕ) {α : Type}
    (rL rR : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) ×
             PRFPRNG.GameState Sig I K) : Prop :=
  DoomedMain Δcka tL (rL.1.2, none) ∨
  (rL.1.1 = rR.1.1 ∧ SyncStepMain Δcka tL t rL.1.2 rL.2 rR.1.2 rR.2)

private def StepRelMain (Δcka : ℕ) (tL : Option ℕ) (t : ℕ) {α : Type}
    (rL rR : (α × PRNGBucketAuthEState Γ T Sig SS RS M E K I) ×
             PRFPRNG.GameState Sig I K) : Prop :=
  DoomedMain Δcka tL rL.1.2 ∨
  (rL.1.1 = rR.1.1 ∧ rL.1.2.2 = rR.1.2.2 ∧
    SyncStepMain Δcka tL t rL.1.2.1 rL.2 rR.1.2.1 rR.2)

private theorem doomedMain_independent_winEp {Δcka : ℕ} {tL : Option ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {w1 w2 : Option ℕ} (hd : DoomedMain Δcka tL (es, w1)) :
    DoomedMain Δcka tL (es, w2) := hd

@[local simp]
private theorem run_commitE_main [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    (commitE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL m) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
    StateT.run_bind, StateT.run_pure, GameState.accept]

private theorem syncStepMain_set_win {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) :
    SyncStepMain Δcka tL t
      { esL with g := { esL.g with win := true } } spL
      { esR with g := { esR.g with win := true } } spR := by
  refine ⟨hsync.abortL, hsync.abortR, ?_, hsync.vp_base, hsync.cache_gt_max,
    hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hsync.comp_epoch,
    hsync.ahead_in_trans, ?_⟩
  · have hg := hsync.g_eq
    rcases esL with ⟨gL, hL, abL⟩
    rcases esR with ⟨gR, hR, abR⟩
    rcases gL with ⟨stL, epL, idxL, tLL, trL, chL, cpL, maL, bL, wL, lkL, crL⟩
    rcases gR with ⟨stR, epR, idxR, tLR, trR, chR, cpR, maR, bR, wR, lkR, crR⟩
    dsimp only [eraseSt] at hg ⊢
    injection hg with _ hep hidx htL_eq htr hch hcp hma hb _ hlk hcr
    subst hep hidx htL_eq htr hch hcp hma hb hlk hcr
    rfl
  · rcases hsync.mode with hm | hm | hm
    · exact .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, hm.vp_root, hm.cache_rel,
        hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spL_prf_lt,
        hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩
    · exact .allResolved ⟨hm.pl_true, hm.vp_res, hm.cache_res⟩
    · exact .postCorr hm

private theorem syncStepMain_of_accept
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    {P : Party} {c : Header T × E}
    {vpL' vpR' : VP Γ T (Option Sig) SS RS} {pos : Pos}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR)
    (hpos_sender : pos.sender = P.other)
    (hpos_ep : pos.epoch = c.1.1)
    (htle : c.1.1 ≤ esR.g.epoch P + 1)
    (hns : P.sendsIn c.1.1 = false)
    (hvp_base' : VPBaseRel (max (esR.g.epoch P) c.1.1) P vpL' vpR')
    (hroot_le : c.1.1 ≤ esR.g.epoch P →
      vpL'.root = (esL.g.st P).root ∧ vpR'.root = (esR.g.st P).root)
    (hnew_cache : c.1.1 = esR.g.epoch P + 1 →
      ∃ Tc rL rR k,
        esL.h.cache c.1.1 = some (Tc, rL, k) ∧
        esR.h.cache c.1.1 = some (Tc, rR, k) ∧
        vpL'.root = resolveCorrRoot esL.h c.1.1 rL ∧
        vpR'.root = resolveCorrRoot esR.h c.1.1 rR) :
    SyncStepMain Δcka tL t
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
    dsimp only [GameState.accept, GameState.delete]
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
    eraseSt_accept hsync.g_eq P vpL' vpR' pos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q
    dsimp only
    rw [hacc_ep]
    dsimp only [GameState.accept]
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
    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr'
    obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
    refine ⟨?_, h2⟩
    by_cases hQ : r'.pos.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · intro pos' hpos'
    dsimp only at hpos' ⊢
    rw [hacc_ep]
    simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos'
    have h1 := hsync.comp_epoch pos' hpos'.1
    by_cases hQ : pos'.sender = P
    · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
    · rw [Function.update_of_ne hQ]; exact h1
  · intro hpl Q hlt_Q hadm_Q
    dsimp only at hpl hlt_Q hadm_Q ⊢
    rw [hacc_ep] at hlt_Q hadm_Q ⊢
    by_cases hnew : c.1.1 = esR.g.epoch P + 1
    · have hc_le := hnew_le_other hnew
      have heq_other : esR.g.epoch P.other = esR.g.epoch P + 1 := by
        have := hsync.epoch_le P.other
        rw [Party.other_other] at this
        omega
      exfalso
      cases Q <;> cases P <;> simp [Party.other, hnew] at heq_other hlt_Q <;> omega
    · have htle_e : c.1.1 ≤ esR.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hlt_Q hadm_Q ⊢
      obtain ⟨r0, hr0_mem, hr0_send, hr0_ep, hr0_ncomp⟩ :=
        hsync.ahead_in_trans hpl Q hlt_Q hadm_Q
      have hne_pos : r0.pos ≠ pos := by
        intro heq_pos
        have hs_eq : r0.pos.sender = pos.sender := congrArg Pos.sender heq_pos
        have hep_eq : r0.pos.epoch = pos.epoch := congrArg Pos.epoch heq_pos
        rw [hr0_send, hpos_sender] at hs_eq
        rw [hr0_ep, hpos_ep, hs_eq] at hep_eq
        rw [hs_eq, Party.other_other] at hlt_Q
        omega
      refine ⟨r0, ?_, hr0_send, hr0_ep, ?_⟩
      · simp [GameState.accept, GameState.delete, hr0_mem, hne_pos]
      · simp only [GameState.accept, GameState.delete, List.mem_filter, not_and]
        intro hmem; exact False.elim (hr0_ncomp hmem)
  · rcases hsync.mode with hm | hm | hm
    · refine .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, ?_, hm.cache_rel,
        hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b,
        by dsimp only; rw [hmax_eq]; exact hm.sp_σ_lt,
        by dsimp only; rw [hmax_eq]; exact hm.spL_prf_lt,
        by dsimp only; rw [hmax_eq]; exact hm.spR_prf_le,
        hm.spR_prng,
        by dsimp only; rw [hmax_eq]; exact hm.spR_corr⟩
      intro Q
      dsimp only [GameState.accept, GameState.delete]
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
      dsimp only [GameState.accept, GameState.delete]
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
          dsimp only [GameState.accept, GameState.delete]
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
          dsimp only [GameState.accept, GameState.delete]
          by_cases hQ : Q = P
          · subst Q; simp [hrL', hrR']
          · simp [Function.update_of_ne hQ]
        refine .postCorr ⟨hpl, Q_corr, eC, σC, htH_eC,
          by dsimp only [GameState.accept, GameState.delete]; exact hmem_corr,
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

private theorem cache_at_succ_main
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) (P : Party) :
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

private theorem run_vRecv_main
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR)
    (P : Party) (c : Header T × E)
    (recL recR : Option (Record M (Header T × E))) :
    let runL := (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t)
      esL.g P (esL.g.st P) c recL).run esL.h
    let runR := (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (t + 1))
      esR.g P (esR.g.st P) c recR).run esR.h
    (runL = pure (none, esL.h) ∧ runR = pure (none, esR.h)) ∨
    (runL = pure (some none, esL.h) ∧ runR = pure (some none, esR.h)) ∨
    ∃ vpL' vpR' i' m',
      runL = pure (some (some (vpL', c.1.1, i', m')), esL.h) ∧
      runR = pure (some (some (vpR', c.1.1, i', m')), esR.h) ∧
      c.1.1 ≤ esR.g.epoch P + 1 ∧
      P.sendsIn c.1.1 = false ∧
      VPBaseRel (max (esR.g.epoch P) c.1.1) P vpL' vpR' ∧
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
  dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
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
        rcases cache_at_succ_main hsync P with ⟨hcL, hcR⟩ | ⟨Tc, rL, rR, k, hcL, hcR⟩
        · simp only [hcL, hcR]
          by_cases habort : (!(decide (qep + 1 < esR.g.epoch P + 1)) &&
              lastLeakGuessAdmissible (2 + Δcka) tL (esR.g.epoch P + 1) &&
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
                lastLeakGuessAdmissible (2 + Δcka) tL (esR.g.epoch P + 1) &&
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

private theorem leComp_deliverE_main
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) :
    LeComp (StepRelMainRaw Δcka tL t)
      ((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t)
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esL)).run spL)
      ((simulateQ (pImpl prng)
        ((deliverE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (t + 1))
          fs.maxSkip (bucketAuthCfg Δcka tL) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esR.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esR.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esL.g.mustBeCorrect fs.maxSkip P r = esR.g.mustBeCorrect fs.maxSkip P r := by
        simp [GameState.mustBeCorrect, eraseSt_comp hsync.g_eq, eraseSt_maxAcc hsync.g_eq]
      have hr_pos_ep : r.pos.epoch = c.1.1 := by
        rw [← (hsync.trans_epoch r hr_mem.1).2, hr_mem.2.2]
      simp only [hmust_eq, StateT.run_bind, run_liftH]
      rcases run_vRecv_main cka prng fs Δcka qep tL t hsync P c (some r) (some r) with
        ⟨hrunL, hrunR⟩ | ⟨hrunL, hrunR⟩ |
        ⟨vpL', vpR', i', m', hrunL, hrunR, htle, hns, hvp_base', hroot_le, hnew_cache⟩
      · rw [hrunL, hrunR]
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inl (Or.inl rfl))
      · rw [hrunL, hrunR]
        simp only [pure_bind]
        by_cases hmust : ((bucketAuthCfg Δcka tL : Config M).deliverWin &&
            esR.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure]
          exact LeComp.pure (Or.inr ⟨rfl, syncStepMain_set_win hsync⟩)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · rw [hrunL, hrunR]
        simp only [pure_bind, StateT.run_bind, run_commitE_main,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [eraseSt_chall hsync.g_eq]
        have hs_acc := syncStepMain_of_accept hsync hr_mem.2.1 hr_pos_ep htle hns
          hvp_base' hroot_le hnew_cache
        by_cases hbad : (((bucketAuthCfg Δcka tL : Config M).deliverWin &&
            esR.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg))) = true
        · simp only [hbad, ↓reduceIte]
          exact LeComp.pure (Or.inr ⟨rfl, syncStepMain_set_win hs_acc⟩)
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
          exact LeComp.pure (Or.inr ⟨rfl, hs_acc⟩)

private theorem leComp_injectE_main
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (arg : Party × (Header T × E))
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) :
    LeComp (StepRelMainRaw Δcka tL t)
      ((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esL)).run spL)
      ((simulateQ (pImpl prng)
        ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (t + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL) arg).run esR)).run spR) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, eraseSt_win hsync.g_eq,
    eraseSt_inTransit hsync.g_eq, eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (false || esR.g.win || (esR.g.inTransit P.other c).isSome ||
      !esR.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, run_liftH]
    rcases run_vRecv_main cka prng fs Δcka qep tL t hsync P c none none with
      ⟨hrunL, hrunR⟩ | ⟨hrunL, hrunR⟩ |
      ⟨vpL', vpR', i', m', hrunL, hrunR, htle, hns, hvp_base', hroot_le, hnew_cache⟩
    · rw [hrunL, hrunR]
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inl (Or.inl rfl))
    · rw [hrunL, hrunR]
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · rw [hrunL, hrunR]
      simp only [pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hqep, ↓reduceIte]
        rw [eraseSt_trivial hsync.g_eq]
        by_cases htriv : esR.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_main,
            StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          exact LeComp.pure (Or.inr ⟨rfl,
            syncStepMain_of_accept hsync rfl rfl htle hns hvp_base' hroot_le hnew_cache⟩)
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (bucketAuthCfg Δcka tL : Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            exact LeComp.pure (Or.inr ⟨rfl, syncStepMain_set_win hsync⟩)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)

private theorem epMgmt_eq_of_sendsIn_false {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hns : P.sendsIn (s.epoch P + 1) = false)
    (hep : s.epMgmt Δ qep P bad = some s₁) : s₁ = s := by
  unfold GameState.epMgmt at hep
  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split_ifs at hep with hq
  simp only [Option.some.injEq] at hep
  exact hep.symm

private theorem epMgmt_fields_of_sendsIn_true {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hs : P.sendsIn (s.epoch P + 1) = true)
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    s₁.epoch = Function.update s.epoch P (s.epoch P + 1) ∧
    s₁.idx = Function.update s.idx P 0 ∧
    s₁.st = s.st ∧ s₁.trans = s.trans ∧ s₁.comp = s.comp ∧ s₁.corrs = s.corrs := by
  unfold GameState.epMgmt at hep
  simp only [hs, ↓reduceIte] at hep
  split_ifs at hep
  all_goals
    simp only [Option.some.injEq] at hep
    subst hep
    simp [GameState.leak]

private theorem RelStepRoot.resolve_after_set_corrRoot
    {tH t e : ℕ} {σR σC : Sig} {rL rR : Option Sig}
    {hL hR : PRNGBucketAuthState T Sig K I}
    (hr : RelStepRoot tH t σR e rL rR)
    (hge : tH ≤ e)
    (hσC : e ≤ t → σC = σR) :
    ∃ σOut,
      resolveCorrRoot { hL with corrRoot := some (e, σC) } e rL = some σOut ∧
      resolveCorrRoot { hR with corrRoot := some (e, σC) } e rR = some σOut := by
  rcases hr with ⟨hlt, _⟩ | ⟨_, hlt_t, hrL, hrR⟩ | ⟨heq_t, hrL, hrR⟩ | ⟨_, σ, hrL, hrR⟩
  · omega
  · subst hrL hrR
    exact ⟨σC, by simp [resolveCorrRoot], by simp [resolveCorrRoot]⟩
  · subst e hrL hrR
    rw [hσC le_rfl]
    exact ⟨σR, by simp [resolveCorrRoot], by simp [resolveCorrRoot]⟩
  · subst hrL hrR
    exact ⟨σ, by simp [resolveCorrRoot], by simp [resolveCorrRoot]⟩

private theorem leComp_vSend_sendsIn_true_coins
    [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {α₀ β₀ α₁ β₁ α β : Type} {R : α → β → Prop}
    (prng : PRFPRNG KR Sig I K) (r_coins : Option CCoins)
    (fL : CCoins → HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) α₀)
    (fR : CCoins → HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) β₀)
    (gL : α₀ → HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) α₁)
    (gR : β₀ → HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) β₁)
    (hL hR : PRNGBucketAuthState T Sig K I) (spL spR : PRFPRNG.GameState Sig I K)
    (kL : (α₁ × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K → ProbComp α)
    (kR : (β₁ × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K → ProbComp β)
    (hk : ∀ c0,
      LeComp R
        ((simulateQ (pImpl prng) ((fL c0 >>= gL).run hL)).run spL >>= kL)
        ((simulateQ (pImpl prng) ((fR c0 >>= gR).run hR)).run spR >>= kR)) :
    LeComp R
      ((simulateQ (pImpl prng)
        (((match r_coins with
           | some c => pure c >>= fL
           | none => StateT.lift (sampleT CCoins) >>= fL) >>= gL).run hL)).run spL >>= kL)
      ((simulateQ (pImpl prng)
        (((match r_coins with
           | some c => pure c >>= fR
           | none => StateT.lift (sampleT CCoins) >>= fR) >>= gR).run hR)).run spR >>= kR) := by
  cases r_coins with
  | some c0 =>
    simp only [pure_bind]
    exact hk c0
  | none =>
    simp only [bind_assoc, StateT.run_bind, simulateQ_bind,
      simulateQ_pImpl_run_lift_sampleT, pure_bind]
    exact LeComp.sample_bind ($ᵗ CCoins) fun c0 _ => by
      simpa only [StateT.run_bind, simulateQ_bind, bind_assoc] using hk c0

private theorem leComp_transmit_main
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (arg : Party × M × Option CCoins)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {winEp : Option ℕ}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) :
    LeComp (StepRelMain Δcka tL t)
      ((simulateQ (pImpl prng)
        ((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t)
          Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inl arg)))))).run
          (esL, winEp))).run spL)
      ((simulateQ (pImpl prng)
        ((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (t + 1))
          Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inl arg)))))).run
          (esR, winEp))).run spR) := by
  rcases arg with ⟨P, msg, r_coins⟩
  simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, eraseSt_win hsync.g_eq]
  by_cases habw : (false || esR.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁L, s₁R, h1, h2, hs₁_er, hs₁L_st, hs₁R_st, hs₁_trans, hs₁_ep_fn, _⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
    · have hvp := hsync.vp_base P
      by_cases hsends : P.sendsIn (esR.g.epoch P + 1) = true
      · obtain ⟨hs₁R_ep, _, _, _, hs₁R_comp, hs₁R_corrs⟩ := epMgmt_fields_of_sendsIn_true hsends h2
        have hsendsL : P.sendsIn (esL.g.epoch P + 1) = true := by
          rw [eraseSt_epoch hsync.g_eq]; exact hsends
        have heq_other : esR.g.epoch P = esR.g.epoch P.other :=
          epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends hsends
        let eMax := max (esR.g.epoch .A) (esR.g.epoch .B)
        have he_eq_max : esR.g.epoch P = eMax := (max_epoch_eq_of_eq heq_other).symm
        have he_other_max : esR.g.epoch P.other = eMax := heq_other.symm.trans he_eq_max
        have hs₁_pl_eq : postLeak tL s₁L = postLeak tL s₁R := eraseSt_postLeak hs₁_er tL
        have hs₁R_ep_P : s₁R.epoch P = eMax + 1 := by simp [hs₁R_ep, he_eq_max]
        have hs₁R_ep_other : ∀ Q, Q ≠ P → s₁R.epoch Q = eMax := by
          intro Q hQ
          have hQo : Q = P.other := by
            cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
          subst Q; simp [hs₁R_ep, Function.update_of_ne hQ, he_other_max]
        have hs₁R_max : max (s₁R.epoch .A) (s₁R.epoch .B) = eMax + 1 := by
          rw [hs₁R_ep, max_epoch_update_succ heq_other, he_eq_max]
        have hs₁R_min : min (s₁R.epoch .A) (s₁R.epoch .B) = eMax := by
          rw [hs₁R_ep]
          cases P <;> simp [Party.other] at he_eq_max he_other_max ⊢ <;> omega
        simp only [h1, h2, hs₁L_st, hs₁R_st, StateT.run_bind, StateT.run_lift,
          simulateQ_bind, bind_assoc]
        unfold vSend
        dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
        rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R, hvp.γ_eq, hsends]
        simp only [↓reduceIte, hs₁_pl_eq, he_eq_max]
        refine leComp_vSend_sendsIn_true_coins prng r_coins _ _ _ _ esL.h esR.h spL spR _ _ fun c0 => ?_
        simp only [StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind]
        let ck := cka.send (esR.g.st P).γ c0
        have hcommon_sync : ∀ {vpL' vpR' : VP Γ T (Option Sig) SS RS}
            {hL1 hR1 : PRNGBucketAuthState T Sig K I}
            {spL1 spR1 : PRFPRNG.GameState Sig I K} {ct : Header T × E},
            ct.1.1 = eMax + 1 →
            VPBaseRel (eMax + 1) P vpL' vpR' →
            (∀ e', eMax + 1 < e' → hL1.cache e' = none ∧ hR1.cache e' = none) →
            (postLeak tL s₁R = false →
              ∀ Q : Party, (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q.other <
                (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q →
                lastLeakGuessAdmissible (2 + Δcka) tL
                  ((s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q) = true →
                ∃ r ∈ (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).trans,
                  r.pos.sender = Q ∧
                  r.pos.epoch = (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q ∧
                  r.pos ∉ (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).comp) →
            ModeMain tL t
              { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := hL1 } spL1
              { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := hR1 } spR1 →
            SyncStepMain Δcka tL t
              { g := s₁L.record (2 + Δcka) P vpL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, msg, ct⟩ false, h := hL1 } spL1
              { g := s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false, h := hR1 } spR1 := by
          intro vpL' vpR' hL1 hR1 spL1 spR1 ct hct_ep hvp' hcache_gt hahead hmode'
          refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hahead, hmode'⟩
          · rw [eraseSt_epoch hs₁_er, eraseSt_idx hs₁_er]
            exact eraseSt_record hs₁_er (2 + Δcka) P vpL' vpR' _ false
          · intro Q
            dsimp only [GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hs₁R_ep_P]; exact hvp'
            · simp only [Function.update_of_ne hQ, hs₁R_ep_other Q hQ, hs₁L_st, hs₁R_st]
              have hQo : Q = P.other := by
                cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
              subst Q
              simpa [he_other_max] using hsync.vp_base P.other
          · intro e' hgt
            dsimp only [GameState.record] at hgt
            rw [hs₁R_max] at hgt
            exact hcache_gt e' hgt
          · intro Q
            dsimp only [GameState.record]
            rw [hs₁R_ep]
            cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
          · intro Q hlt_Q
            dsimp only [GameState.record] at hlt_Q ⊢
            rw [hs₁R_ep] at hlt_Q ⊢
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hsends
            · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          · intro r hr
            dsimp only [GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact ⟨le_rfl, by dsimp only; rw [hct_ep, hs₁R_ep_P]⟩
            · obtain ⟨h_le, h_eq⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
              refine ⟨?_, h_eq⟩
              rw [hs₁R_ep]
              by_cases hQ : r.pos.sender = P
              · rw [hQ, Function.update_self]; rw [hQ] at h_le; omega
              · rw [Function.update_of_ne hQ]; exact h_le
          · intro pos' hpos'
            dsimp only [GameState.record] at hpos' ⊢
            rw [hs₁R_comp] at hpos'
            have hmem_or : pos' = ⟨P, s₁R.epoch P, s₁R.idx P + 1⟩ ∨ pos' ∈ esR.g.comp := by
              split_ifs at hpos' with hsc
              · exact Or.inr hpos'
              · exact List.mem_cons.mp hpos'
            rcases hmem_or with rfl | hmem
            · exact le_rfl
            · have h_le := hsync.comp_epoch pos' hmem
              rw [hs₁R_ep]
              by_cases hQ : pos'.sender = P
              · rw [hQ, Function.update_self]; rw [hQ] at h_le; omega
              · rw [Function.update_of_ne hQ]; exact h_le
        have hahead_sends : ∀ {vpR' : VP Γ T (Option Sig) SS RS} {ct : Header T × E},
            postLeak tL s₁R = false →
            ∀ Q : Party, (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q.other <
              (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q →
              lastLeakGuessAdmissible (2 + Δcka) tL
                ((s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q) = true →
              ∃ r ∈ (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).trans,
                r.pos.sender = Q ∧
                r.pos.epoch = (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).epoch Q ∧
                r.pos ∉ (s₁R.record (2 + Δcka) P vpR' ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩ false).comp := by
          intro vpR' ct hpl1 Q hlt_Q hadm_Q
          dsimp only [GameState.record] at hlt_Q hadm_Q ⊢
          have hQ_eq_P : Q = P := by
            by_contra hQ
            rw [hs₁R_ep] at hlt_Q
            cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
          subst Q
          have hsc : s₁R.safeCh (2 + Δcka) P = true :=
            safeCh_true_of_postLeak_false_admissible hpl1 hadm_Q
          refine ⟨⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, msg, ct⟩, List.mem_cons_self, rfl, rfl, ?_⟩
          rw [hs₁R_comp]
          simp only [hsc, ↓reduceIte]
          intro hmem_comp
          have h_le := hsync.comp_epoch _ hmem_comp
          dsimp only at h_le
          rw [hs₁R_ep_P, he_eq_max] at h_le
          omega
        rcases hsync.mode with hm | hm | hm
        · by_cases hpl1 : postLeak tL s₁R = true
          · simp only [hpl1]
            have hrP : RelStepRoot (healEpoch tL) t spR.σ eMax (esL.g.st P).root (esR.g.st P).root := by
              simpa [he_eq_max] using hm.vp_root P
            have hrO : RelStepRoot (healEpoch tL) t spR.σ eMax (esL.g.st P.other).root (esR.g.st P.other).root := by
              simpa [he_other_max] using hm.vp_root P.other
            refine (leComp_rootSend_postLeak_from_pre (T := T) prng tL t eMax ck.2.2
              (esL.g.st P).root (esR.g.st P).root (esL.g.st P.other).root (esR.g.st P.other).root
              esL.h esR.h spL spR htLo hm.corrRootL hm.corrRootR hrP hrO
              hm.sp_σ_lt hm.spL_prf_lt hm.spR_prf_le).bind ?_
            rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩
              ⟨σNew, kVal, σOther, hresL, hresR, hcL1, hcR1, hresOL, hresOR⟩
            dsimp only at hresL hresR hcL1 hcR1 hresOL hresOR
            subst hresL hresR
            simp only [StateT.run_modify, StateT.run_pure, pure_bind, StateT.run_bind,
              StateT.run_set, simulateQ_pure]
            refine LeComp.pure (Or.inr ⟨rfl, rfl, hcommon_sync rfl
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq⟩
              (fun e' hgt => by
                dsimp only
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcL1, hcR1]
                exact hsync.cache_gt_max e' (by omega))
              (fun h => by rw [hpl1] at h; cases h) ?_⟩)
            refine .allResolved ⟨hpl1, ?_, ?_⟩
            · intro Q
              dsimp only [GameState.record]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hs₁R_ep_P]
                exact ⟨σNew, rfl, rfl⟩
              · have hQo : Q = P.other := by
                  cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
                subst Q
                simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
                exact ⟨σOther, hresOL, hresOR⟩
            · intro e' he'
              dsimp only [GameState.record] at he' ⊢
              rw [hs₁R_min] at he'
              by_cases heq_e1 : e' = eMax + 1
              · subst e'
                simp only [Function.update_self]
                exact Or.inr ⟨ck.2.1, some σNew, some σNew, kVal, σNew, rfl, rfl, rfl, rfl⟩
              · have hgt_max : eMax < e' := he'
                rw [Function.update_of_ne heq_e1, Function.update_of_ne heq_e1, hcL1, hcR1]
                exact Or.inl (hsync.cache_gt_max e' hgt_max)
          · have hpl1_f : postLeak tL s₁R = false := Bool.eq_false_iff.mpr hpl1
            simp only [hpl1_f]
            have hrP : RelStepRoot (healEpoch tL) t spR.σ eMax (esL.g.st P).root (esR.g.st P).root := by
              simpa [he_eq_max] using hm.vp_root P
            refine (leComp_rootSend_pre (T := T) prng tL t eMax ck.2.2
              (esL.g.st P).root (esR.g.st P).root esL.h esR.h spL spR
              htLo hm.corrRootL hm.corrRootR hrP hm.fTable_ne hm.table_t
              hm.spL_b hm.spR_b hm.sp_σ_lt hm.spL_prf_lt hm.spR_prf_le
              hm.spR_prng hm.spR_corr).bind ?_
            rintro ⟨⟨resL, hL1⟩, spL1⟩ ⟨⟨resR, hR1⟩, spR1⟩ hrel
            rcases hrel with hnone |
              ⟨rL', rR', kVal, hresL, hresR, hr_new, hσR_ge, hcL1, hcR1, hcrL1, hcrR1,
                hft1, htab1, hbL1, hbR1, hσ_lt1, hprfL1, hprfR1, hprng1, hcorr1⟩
            · dsimp only at hnone; subst hnone
              simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
              exact LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
            · dsimp only at hresL hresR hcL1 hcR1 hcrL1 hcrR1
              subst hresL hresR
              simp only [StateT.run_modify, StateT.run_pure, pure_bind, StateT.run_bind,
                StateT.run_set, simulateQ_pure]
              refine LeComp.pure (Or.inr ⟨rfl, rfl, hcommon_sync rfl
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq⟩
                (fun e' hgt => by
                  dsimp only
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcL1, hcR1]
                  exact hsync.cache_gt_max e' (by omega))
                hahead_sends ?_⟩)
              refine .pre ⟨hpl1_f, hcrL1, hcrR1, ?_, ?_, hft1, htab1, hbL1, hbR1,
                by dsimp only [GameState.record]; rw [hs₁R_max]; exact hσ_lt1,
                by dsimp only [GameState.record]; rw [hs₁R_max]; exact hprfL1,
                by dsimp only [GameState.record]; rw [hs₁R_max]; exact hprfR1,
                hprng1,
                by dsimp only [GameState.record]; rw [hs₁R_max]; exact hcorr1⟩
              · intro Q
                dsimp only [GameState.record]
                by_cases hQ : Q = P
                · subst Q
                  simp only [Function.update_self, hs₁R_ep_P]
                  exact hr_new
                · have hQo : Q = P.other := by
                    cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
                  subst Q
                  simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
                  have hrO : RelStepRoot (healEpoch tL) t spR.σ eMax
                      (esL.g.st P.other).root (esR.g.st P.other).root := by
                    simpa [he_other_max] using hm.vp_root P.other
                  by_cases het : eMax = t
                  · rw [hσR_ge (by omega)]; exact hrO
                  · exact hrO.change_σ het
              · intro e'
                dsimp only
                by_cases heq_e1 : e' = eMax + 1
                · subst e'
                  simp only [Function.update_self]
                  exact Or.inr ⟨ck.2.1, rL', rR', kVal, rfl, rfl, hr_new⟩
                · simp only [Function.update_of_ne heq_e1, hcL1, hcR1]
                  by_cases het : e' = t
                  · subst e'
                    by_cases hle : t ≤ eMax
                    · rw [hσR_ge hle]; exact hm.cache_rel t
                    · obtain ⟨hnoneL, hnoneR⟩ := hsync.cache_gt_max t (by omega)
                      exact Or.inl ⟨hnoneL, hnoneR⟩
                  · exact (hm.cache_rel e').change_σ (Or.inl het)
        · have hpl1 : postLeak tL s₁R = true := postLeak_epMgmt_of_true hm.pl_true h2
          obtain ⟨σ, hresL, hresR⟩ := hm.vp_res P
          rw [he_eq_max] at hresL hresR
          obtain ⟨σO, hresOL, hresOR⟩ := hm.vp_res P.other
          rw [he_other_max] at hresOL hresOR
          have hrunL := run_rootSend_post (T := T) prng tL t (eMax + 1) ck.2.2 (esL.g.st P).root esL.h σ
            (by simpa [Nat.add_sub_cancel] using hresL)
          have hrunR := run_rootSend_post (T := T) prng tL (t + 1) (eMax + 1) ck.2.2 (esR.g.st P).root esR.h σ
            (by simpa [Nat.add_sub_cancel] using hresR)
          simp only [hpl1]
          rw [hrunL, hrunR]
          simp only [StateT.run_bind, pure_bind, StateT.run_modify, StateT.run_pure,
            StateT.run_set, simulateQ_pure]
          let σNew := (prng.up σ ck.2.2).1
          let kVal := (prng.up σ ck.2.2).2
          refine LeComp.pure (Or.inr ⟨rfl, rfl, hcommon_sync rfl
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq⟩
            (fun e' hgt => by
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hsync.cache_gt_max e' (by omega))
            (fun h => by rw [hpl1] at h; cases h) ?_⟩)
          refine .allResolved ⟨hpl1, ?_, ?_⟩
          · intro Q
            dsimp only [GameState.record]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁R_ep_P]
              exact ⟨σNew, rfl, rfl⟩
            · have hQo : Q = P.other := by
                cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
              subst Q
              simp only [Function.update_of_ne hQ, hs₁R_ep_other P.other hQ, hs₁L_st, hs₁R_st]
              exact ⟨σO, hresOL, hresOR⟩
          · intro e' he'
            dsimp only [GameState.record] at he' ⊢
            rw [hs₁R_min] at he'
            by_cases heq_e1 : e' = eMax + 1
            · subst e'
              simp only [Function.update_self]
              exact Or.inr ⟨ck.2.1, some σNew, some σNew, kVal, σNew, rfl, rfl, rfl, rfl⟩
            · rw [Function.update_of_ne heq_e1, Function.update_of_ne heq_e1]
              exact Or.inl (hsync.cache_gt_max e' he')
        · exfalso
          rcases hm with ⟨_, Q_corr, eC, _, _, _, _, _, hep_Qc, _, hep_Qo, _, _, _⟩
          cases Q_corr <;> cases P <;> simp [Party.other] at heq_other hep_Qc hep_Qo <;> omega
      · have hns : P.sendsIn (esR.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
        have hnsL : P.sendsIn (esL.g.epoch P + 1) = false := by
          rw [eraseSt_epoch hsync.g_eq]; exact hns
        have hs₁L_eq := epMgmt_eq_of_sendsIn_false hnsL h1
        have hs₁R_eq := epMgmt_eq_of_sendsIn_false hns h2
        subst hs₁L_eq hs₁R_eq
        simp only [h1, h2, StateT.run_bind, StateT.run_lift,
          simulateQ_bind, bind_assoc]
        unfold vSend
        dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
        rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R]
        simp only [hns, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [hvp.id_L, hvp.id_R, hvp.tcur_L, hvp.tcur_R, hvp.Tcur_eq, hvp.vS_eq]
        have hrec_sync : ∀ {vpL' vpR' : VP Γ T (Option Sig) SS RS} {ct : Header T × E},
            ct.1.1 = esR.g.epoch P →
            VPBaseRel (esR.g.epoch P) P vpL' vpR' →
            vpL'.root = (esL.g.st P).root →
            vpR'.root = (esR.g.st P).root →
            SyncStepMain Δcka tL t
              { g := esL.g.record (2 + Δcka) P vpL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, msg, ct⟩ false, h := esL.h } spL
              { g := esR.g.record (2 + Δcka) P vpR' ⟨⟨P, esR.g.epoch P, esR.g.idx P + 1⟩, msg, ct⟩ false, h := esR.h } spR := by
          intro vpL' vpR' ct hct_ep hvp' hrL' hrR'
          have hroot_same : ∀ Q,
              ((esL.g.record (2 + Δcka) P vpL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, msg, ct⟩ false).st Q).root =
                (esL.g.st Q).root ∧
              ((esR.g.record (2 + Δcka) P vpR' ⟨⟨P, esR.g.epoch P, esR.g.idx P + 1⟩, msg, ct⟩ false).st Q).root =
                (esR.g.st Q).root := by
            intro Q
            dsimp only [GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp [hrL', hrR']
            · simp [Function.update_of_ne hQ]
          refine ⟨rfl, rfl, ?_, ?_, hsync.cache_gt_max,
            hsync.epoch_le, hsync.epoch_sends, ?_, ?_, ?_, ?_⟩
          · rw [eraseSt_epoch hsync.g_eq, eraseSt_idx hsync.g_eq]
            exact eraseSt_record hsync.g_eq (2 + Δcka) P vpL' vpR' _ false
          · intro Q
            dsimp only [GameState.record]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; exact hvp'
            · simp only [Function.update_of_ne hQ]; exact hsync.vp_base Q
          · intro r hr
            dsimp only [GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact ⟨le_rfl, hct_ep⟩
            · exact hsync.trans_epoch r hr'
          · intro pos' hpos'
            dsimp only [GameState.record] at hpos' ⊢
            split_ifs at hpos' with hsc
            · exact hsync.comp_epoch pos' hpos'
            · rcases List.mem_cons.mp hpos' with rfl | hmem
              · exact le_rfl
              · exact hsync.comp_epoch pos' hmem
          · intro hpl Q hlt_Q hadm_Q
            dsimp only [GameState.record] at hpl hlt_Q hadm_Q ⊢
            obtain ⟨r0, hr0_mem, hr0_send, hr0_ep, hr0_ncomp⟩ :=
              hsync.ahead_in_trans hpl Q hlt_Q hadm_Q
            refine ⟨r0, List.mem_cons_of_mem _ hr0_mem, hr0_send, hr0_ep, ?_⟩
            split_ifs with hsc
            · exact hr0_ncomp
            · simp only [List.mem_cons, not_or]
              refine ⟨?_, hr0_ncomp⟩
              intro heq_pos
              have hs_eq : r0.pos.sender = P := congrArg Pos.sender heq_pos
              have hep_eq : r0.pos.epoch = esR.g.epoch P := congrArg Pos.epoch heq_pos
              rw [hr0_send] at hs_eq; subst Q
              have hsc_true := safeCh_true_of_postLeak_false_admissible hpl hadm_Q
              dsimp only [GameState.record, GameState.safeCh] at hsc_true
              rw [hs_eq] at hsc_true
              exact hsc hsc_true
          · rcases hsync.mode with hm | hm | hm
            · refine .pre ⟨hm.pl_false, hm.corrRootL, hm.corrRootR, ?_, hm.cache_rel,
                hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spL_prf_lt,
                hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩
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
          simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_set]
          exact LeComp.pure (Or.inr ⟨rfl, rfl, hrec_sync rfl hvp rfl rfl⟩)
        | some v =>
          simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_set]
          exact LeComp.pure (Or.inr ⟨rfl, rfl, hrec_sync rfl
            ⟨rfl, rfl, rfl, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq⟩
            rfl rfl⟩)

private theorem leComp_corr_main
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (P : Party)
    {esL esR : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {winEp : Option ℕ}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hsync : SyncStepMain Δcka tL t esL spL esR spR) :
    LeComp (StepRelMain Δcka tL t)
      ((simulateQ (pImpl prng)
        ((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t)
          Δcka qep fs.maxSkip tL false (.inr (.inr P))).run (esL, winEp))).run spL)
      ((simulateQ (pImpl prng)
        ((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (t + 1))
          Δcka qep fs.maxSkip tL false (.inr (.inr P))).run (esR, winEp))).run spR) := by
  simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortL, hsync.abortR, eraseSt_win hsync.g_eq, eraseSt_corrAllowed hsync.g_eq P]
  by_cases hguard : (false || esR.g.win || !esR.g.corrAllowed P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · have hallow : esR.g.corrAllowed P = true := by
      simp only [Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have hvp := hsync.vp_base P
    have hac_er := eraseSt_afterCorr hsync.g_eq P
    have hpl_eq := eraseSt_postLeak hsync.g_eq (tL := tL)
    have hep_eq := eraseSt_epoch hsync.g_eq
    have hreal_eq : ∀ σ : Sig,
        realParty (esL.g.st P) (esL.g.st P).γ σ (esL.g.st P).vS (esL.g.st P).vR =
        realParty (esR.g.st P) (esR.g.st P).γ σ (esR.g.st P).vS (esR.g.st P).vR := by
      intro σ
      dsimp only [realParty]
      rw [hvp.id_L, hvp.id_R, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_L, hvp.tcur_R,
        hvp.vS_eq, funext hvp.vR_eq]
    have hcomp_ac : ∀ pos' ∈ (esR.g.afterCorr P).comp,
        pos'.epoch ≤ (esR.g.afterCorr P).epoch pos'.sender := by
      intro pos' hpos'
      dsimp only [GameState.afterCorr, GameState.leak] at hpos' ⊢
      rcases List.mem_append.mp hpos' with hmap | hmem
      · obtain ⟨r, hr_filt, rfl⟩ := List.mem_map.mp hmap
        exact (hsync.trans_epoch r (List.mem_filter.mp hr_filt).1).1
      · exact hsync.comp_epoch pos' hmem
    simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      simulateQ_bind, bind_assoc]
    dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rw [hvp.tcur_L, hvp.tcur_R, hep_eq, hpl_eq]
    rcases hsync.mode with hm | hm | hm
    · let e := esR.g.epoch P
      have hresL0 : resolveCorrRoot esL.h (esR.g.epoch P) (esL.g.st P).root = (esL.g.st P).root :=
        resolveCorrRoot_of_corrRoot_none hm.corrRootL _ _
      have hresR0 : resolveCorrRoot esR.h (esR.g.epoch P) (esR.g.st P).root = (esR.g.st P).root :=
        resolveCorrRoot_of_corrRoot_none hm.corrRootR _ _
      rw [hresL0, hresR0]
      rcases hsync.corr_epoch_dichotomy hm.pl_false hallow with hle_other | ⟨heq_other, hadm_f⟩
      · have he_max : esR.g.epoch P = max (esR.g.epoch .A) (esR.g.epoch .B) := by
          cases P <;> simp [Party.other] at hle_other ⊢ <;> omega
        by_cases hlt_tH : esR.g.epoch P < healEpoch tL
        · obtain ⟨l, htL_l, he_lt_l2⟩ : ∃ l, tL = some l ∧ esR.g.epoch P < l + 2 := by
            cases tL with
            | none => simp [healEpoch] at hlt_tH
            | some l => exact ⟨l, rfl, by simpa [healEpoch] using hlt_tH⟩
          subst htL_l
          obtain ⟨σ, hrL, hrR⟩ := RelStepRoot.some_of_lt_tH htLo hlt_tH (hm.vp_root P)
          simp only [hrL, hrR, hlt_tH,
            decide_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
          by_cases he_le_l : esR.g.epoch P ≤ l
          · have hpl_ac : postLeak (some l) (esR.g.afterCorr P) = false := by
              have hpl0 := hm.pl_false
              unfold postLeak at hpl0 ⊢
              dsimp only [GameState.afterCorr, GameState.leak]
              rw [← he_max]
              cases hcur : esR.g.tL with
              | none =>
                simp [maxOpt, ltOpt]
                exact decide_eq_false_iff_not.mpr (Nat.not_lt.mpr he_le_l)
              | some cur =>
                rw [hcur] at hpl0
                have hcur_le : ¬ l < cur := decide_eq_false_iff_not.mp hpl0
                simp [maxOpt, ltOpt]
                exact ⟨Nat.le_of_not_lt hcur_le, he_le_l⟩
            refine LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl,
              ⟨rfl, rfl, hac_er, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
                (fun _ Q _ hadm_Q => by
                  dsimp only [GameState.afterCorr, GameState.leak] at hadm_Q
                  simp [lastLeakGuessAdmissible, healedBy] at hadm_Q
                  have hQ_le : esR.g.epoch Q ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
                    cases Q <;> simp
                  omega),
                .pre ⟨hpl_ac, hm.corrRootL, hm.corrRootR, hm.vp_root, hm.cache_rel,
                  hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spL_prf_lt,
                  hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩⟩⟩)
          · have he_eq_l1 : esR.g.epoch P = l + 1 := by omega
            refine LeComp.pure (Or.inl (Or.inr (Or.inr ⟨l + 1, ?_, by simp [ltOpt], ?_⟩)))
            · dsimp only [GameState.afterCorr, GameState.leak]
              have hpl0 : postLeak (some l) esL.g = false := by rw [hpl_eq]; exact hm.pl_false
              unfold postLeak at hpl0
              have heMaxL : max (esL.g.epoch .A) (esL.g.epoch .B) = l + 1 := by
                rw [hep_eq, ← he_max, he_eq_l1]
              rw [heMaxL]
              cases hcur : esL.g.tL with
              | none => simp [maxOpt]
              | some cur =>
                rw [hcur] at hpl0
                simp [ltOpt] at hpl0
                have hmax_l1 : max cur (l + 1) = l + 1 := by omega
                simp [maxOpt, hmax_l1]
            · intro tWin hadm_win
              simp [lastLeakGuessAdmissible, healedBy] at hadm_win
              omega
        · have hge_tH : healEpoch tL ≤ esR.g.epoch P := Nat.le_of_not_lt hlt_tH
          have hpl_ac : postLeak tL (esR.g.afterCorr P) = true := by
            dsimp only [GameState.afterCorr]
            exact postLeak_leak_of_ge_healEpoch esR.g (by rw [← he_max]; exact hge_tH)
          have hfinish_ge : ∀ (σC : Sig)
              (spL1 spR1 : PRFPRNG.GameState Sig I K),
              (esR.g.epoch P ≤ t → σC = spR.σ) →
              SyncStepMain Δcka tL t
                { g := esL.g.afterCorr P, h := { esL.h with corrRoot := some (e, σC) } } spL1
                { g := esR.g.afterCorr P, h := { esR.h with corrRoot := some (e, σC) } } spR1 := by
            intro σC spL1 spR1 hσC
            refine ⟨rfl, rfl, hac_er, hsync.vp_base, hsync.cache_gt_max,
              hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
              (fun h => by rw [hpl_ac] at h; cases h), ?_⟩
            have hres_P := (hm.vp_root P).resolve_after_set_corrRoot (hL := esL.h) (hR := esR.h)
              hge_tH hσC
            by_cases heq_o : esR.g.epoch P.other = e
            · refine .allResolved ⟨hpl_ac, ?_, ?_⟩
              · intro Q
                dsimp only [GameState.afterCorr, GameState.leak]
                by_cases hQ : Q = P
                · subst Q; exact hres_P
                · have hQo : Q = P.other := by
                    cases Q <;> cases P <;> first | exact False.elim (hQ rfl) | rfl
                  subst Q
                  have hrO : RelStepRoot (healEpoch tL) t spR.σ e
                      (esL.g.st P.other).root (esR.g.st P.other).root := by
                    simpa [heq_o] using hm.vp_root P.other
                  simpa [heq_o] using hrO.resolve_after_set_corrRoot (hL := esL.h) (hR := esR.h)
                    hge_tH hσC
              · intro e' he'
                dsimp only [GameState.afterCorr, GameState.leak] at he' ⊢
                have hmin_e : min (esR.g.epoch .A) (esR.g.epoch .B) = esR.g.epoch P := by
                  dsimp only [e] at heq_o
                  cases P <;> simp [Party.other] at heq_o ⊢ <;> omega
                rw [hmin_e, he_max] at he'
                exact Or.inl (hsync.cache_gt_max e' he')
            · have hlt_o : esR.g.epoch P.other < esR.g.epoch P := Nat.lt_of_le_of_ne hle_other heq_o
              have hle_1 := hsync.epoch_le P
              have hep_Qo : esR.g.epoch P.other + 1 = e := by
                dsimp only [e]; omega
              have hsends_P : P.sendsIn e = true := hsync.epoch_sends P hlt_o
              refine .postCorr ⟨hpl_ac, P, e, σC, hge_tH,
                by simp [GameState.afterCorr, e], rfl, rfl, rfl, hres_P,
                hep_Qo, hsends_P, ?_, ?_⟩
              · intro hne_t
                dsimp only [e] at hne_t
                have hne_o : esR.g.epoch P.other ≠ t := by omega
                exact (hm.vp_root P.other).eq_of_ne_t hne_o
              · intro e' he'
                dsimp only
                by_cases heq_e : e' = e
                · subst e'
                  rcases hm.cache_rel e with hnone | ⟨Tc, rL, rR, k, hcL, hcR, hr_c⟩
                  · exact Or.inl hnone
                  · obtain ⟨σOut, h1, h2⟩ := hr_c.resolve_after_set_corrRoot
                      (hL := esL.h) (hR := esR.h) hge_tH hσC
                    exact Or.inr ⟨Tc, rL, rR, k, σOut, hcL, hcR, h1, h2⟩
                · dsimp only [e] at heq_e
                  have hgt_max : max (esR.g.epoch .A) (esR.g.epoch .B) < e' := by
                    dsimp only [e] at he'
                    rw [← he_max]
                    omega
                  exact Or.inl (hsync.cache_gt_max e' hgt_max)
          rcases hm.vp_root P with ⟨hlt, _⟩ | ⟨_, hlt_t, hrL, hrR⟩ | ⟨heq_t, hrL, hrR⟩ | ⟨hgt_t, σ, hrL, hrR⟩
          · omega
          · have hprfL := hm.spL_prf_lt (by rw [← he_max]; exact hlt_t)
            have hprfR := hm.spR_prf_le (by rw [← he_max]; omega)
            have hσ_eq := hm.sp_σ_lt (by rw [← he_max]; exact hlt_t)
            simp only [hrL, hrR,
              hm.pl_false, hm.corrRootL, hm.corrRootR, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, ← he_max, beq_self_eq_true, Bool.and_self,
              ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind,
              simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_corrQuery, run_corrImpl,
              hprfL, hprfR, hσ_eq, Bool.false_eq_true,
              StateT.run_modify, StateT.run_pure, StateT.run_set, simulateQ_pure]
            exact LeComp.pure (Or.inr ⟨congrArg some (hreal_eq spR.σ), rfl,
              hfinish_ge spR.σ _ _ (fun _ => rfl)⟩)
          · have hprfR := hm.spR_prf_le (by rw [← he_max]; omega)
            simp only [hrL, hrR,
              hm.pl_false, hm.corrRootL, hm.corrRootR, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, ← he_max, beq_self_eq_true, Bool.and_self,
              ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind,
              simulateQ_pImpl_liftPBucketAuth, simulateQ_pImpl_corrQuery, run_corrImpl,
              hprfR, Bool.false_eq_true,
              StateT.run_modify, StateT.run_pure, StateT.run_set, simulateQ_pure]
            exact LeComp.pure (Or.inr ⟨congrArg some (hreal_eq spR.σ), rfl,
              hfinish_ge spR.σ _ _ (fun _ => rfl)⟩)
          · simp only [hrL, hrR,
              hm.corrRootL, hm.corrRootR, Option.isNone_none,
              hlt_tH, decide_false, Bool.not_false, Bool.and_self,
              ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, StateT.run_set, simulateQ_pure]
            exact LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl,
              hfinish_ge σ _ _ (fun h => by omega)⟩)
      · have heMax_eq : max (esR.g.epoch .A) (esR.g.epoch .B) = esR.g.epoch P + 1 := by
          cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
        have hne_max : (esR.g.epoch P == max (esR.g.epoch .A) (esR.g.epoch .B)) = false := by
          rw [heMax_eq]; simp only [beq_eq_false_iff_ne, ne_eq]; omega
        obtain ⟨l, htL_l, hadm_lt⟩ : ∃ l, tL = some l ∧ esR.g.epoch P + 1 < l + (2 + Δcka) := by
          cases tL with
          | none => simp [lastLeakGuessAdmissible, healedBy] at hadm_f
          | some l =>
            simp [lastLeakGuessAdmissible, healedBy] at hadm_f
            exact ⟨l, rfl, hadm_f⟩
        subst htL_l
        by_cases he1_le_l : esR.g.epoch P + 1 ≤ l
        · have hlt_tH : esR.g.epoch P < healEpoch (some l) := by simp [healEpoch]; omega
          obtain ⟨σ, hrL, hrR⟩ := RelStepRoot.some_of_lt_tH htLo hlt_tH (hm.vp_root P)
          have hpl_ac : postLeak (some l) (esR.g.afterCorr P) = false := by
            have hpl0 := hm.pl_false
            unfold postLeak at hpl0 ⊢
            dsimp only [GameState.afterCorr, GameState.leak]
            rw [heMax_eq]
            cases hcur : esR.g.tL with
            | none => simp [maxOpt, ltOpt]; omega
            | some cur =>
              rw [hcur] at hpl0
              simp [ltOpt] at hpl0
              simp [maxOpt, ltOpt]; omega
          simp only [hrL, hrR, hlt_tH,
            decide_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
          refine LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl,
            ⟨rfl, rfl, hac_er, hsync.vp_base, hsync.cache_gt_max,
              hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
              (fun _ Q _ hadm_Q => by
                dsimp only [GameState.afterCorr, GameState.leak] at hadm_Q
                simp [lastLeakGuessAdmissible, healedBy] at hadm_Q
                have hQ_le : esR.g.epoch Q ≤ max (esR.g.epoch .A) (esR.g.epoch .B) := by
                  cases Q <;> simp
                omega),
              .pre ⟨hpl_ac, hm.corrRootL, hm.corrRootR, hm.vp_root, hm.cache_rel,
                hm.fTable_ne, hm.table_t, hm.spL_b, hm.spR_b, hm.sp_σ_lt, hm.spL_prf_lt,
                hm.spR_prf_le, hm.spR_prng, hm.spR_corr⟩⟩⟩)
        · have hl_lt_e1 : l < esR.g.epoch P + 1 := Nat.lt_of_not_le he1_le_l
          cases hrL_opt : (esL.g.st P).root with
          | none =>
            simp only [hne_max, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
            exact LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          | some σL =>
            have hdoomedL : DoomedMain Δcka (some l)
                ({ g := esL.g.afterCorr P,
                   h := if !(decide (esR.g.epoch P < healEpoch (some l))) && esL.h.corrRoot.isNone
                        then { esL.h with corrRoot := some (esR.g.epoch P, σL) } else esL.h }, winEp) := by
              refine Or.inr (Or.inr ⟨esR.g.epoch P + 1, ?_, by simp [ltOpt, hl_lt_e1], ?_⟩)
              · dsimp only [GameState.afterCorr, GameState.leak]
                have hpl0 : postLeak (some l) esL.g = false := by rw [hpl_eq]; exact hm.pl_false
                unfold postLeak at hpl0
                have heMaxL : max (esL.g.epoch .A) (esL.g.epoch .B) = esR.g.epoch P + 1 := by
                  rw [hep_eq]; exact heMax_eq
                rw [heMaxL]
                cases hcur : esL.g.tL with
                | none => simp [maxOpt]
                | some cur =>
                  rw [hcur] at hpl0
                  simp [ltOpt] at hpl0
                  have hmax_e1 : max cur (esR.g.epoch P + 1) = esR.g.epoch P + 1 := by omega
                  simp [maxOpt, hmax_e1]
              · intro tWin hadm_win
                simp [lastLeakGuessAdmissible, healedBy] at hadm_win
                omega
            by_cases hmodL : (!(decide (esR.g.epoch P < healEpoch (some l))) && esL.h.corrRoot.isNone) = true
            · simp only [hmodL, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, StateT.run_set, simulateQ_pure]
              exact LeComp.pure_left _ _ fun _ _ => Or.inl (by simpa [hmodL] using hdoomedL)
            · simp only [hmodL, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
              exact LeComp.pure_left _ _ fun _ _ => Or.inl (by simpa [hmodL] using hdoomedL)
    · obtain ⟨σ, hresL, hresR⟩ := hm.vp_res P
      have hpl_ac : postLeak tL (esR.g.afterCorr P) = true := postLeak_leak_of_true hm.pl_true _
      let hL' : PRNGBucketAuthState T Sig K I :=
        if !(decide (esR.g.epoch P < healEpoch tL)) && esL.h.corrRoot.isNone
        then { esL.h with corrRoot := some (esR.g.epoch P, σ) } else esL.h
      let hR' : PRNGBucketAuthState T Sig K I :=
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
      have hsync_out : SyncStepMain Δcka tL t
          { g := esL.g.afterCorr P, h := hL' } spL
          { g := esR.g.afterCorr P, h := hR' } spR := by
        refine ⟨rfl, rfl, hac_er, hsync.vp_base,
          fun e' hgt => by rw [hcL_eq, hcR_eq]; exact hsync.cache_gt_max e' hgt,
          hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
          (fun h => by rw [hpl_ac] at h; cases h),
          .allResolved ⟨hpl_ac, fun Q => ?_, fun e' he' => ?_⟩⟩
        · obtain ⟨τ, h1, h2⟩ := hm.vp_res Q
          exact ⟨τ, hpresL h1, hpresR h2⟩
        · rcases hm.cache_res e' he' with ⟨hn1, hn2⟩ | ⟨Tc, rL, rR, k, τ, hc1, hc2, hr1, hr2⟩
          · exact Or.inl ⟨by rw [hcL_eq]; exact hn1, by rw [hcR_eq]; exact hn2⟩
          · exact Or.inr ⟨Tc, rL, rR, k, τ, by rw [hcL_eq]; exact hc1,
              by rw [hcR_eq]; exact hc2, hpresL hr1, hpresR hr2⟩
      rw [hresL, hresR]
      by_cases hmodL : (!(decide (esR.g.epoch P < healEpoch tL)) && esL.h.corrRoot.isNone) = true <;>
        by_cases hmodR : (!(decide (esR.g.epoch P < healEpoch tL)) && esR.h.corrRoot.isNone) = true <;>
        simp only [hmodL, hmodR, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, StateT.run_set, simulateQ_pure] <;>
        exact LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl, by
          simpa only [hL', hR', hmodL, hmodR, Bool.false_eq_true, ↓reduceIte] using hsync_out⟩)
    · rcases hm with ⟨hpl, Q_corr, eC, σC, htH_eC, hmem_corr, hcrL, hcrR,
        hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩
      have hpl_ac : postLeak tL (esR.g.afterCorr P) = true := postLeak_leak_of_true hpl _
      have hisNoneL : esL.h.corrRoot.isNone = false := by simp [hcrL]
      have hisNoneR : esR.h.corrRoot.isNone = false := by simp [hcrR]
      by_cases hP_Qc : P = Q_corr
      · subst P
        obtain ⟨σ, hresL, hresR⟩ := hres_Qc
        simp only [hresL, hresR, hisNoneL, hisNoneR,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
        refine LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl,
          ⟨rfl, rfl, hac_er, hsync.vp_base, hsync.cache_gt_max,
            hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
            (fun h => by rw [hpl_ac] at h; cases h),
            .postCorr ⟨hpl_ac, Q_corr, eC, σC, htH_eC,
              by simp [GameState.afterCorr, hmem_corr],
              hcrL, hcrR, hep_Qc, ⟨σ, hresL, hresR⟩, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩⟩⟩)
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
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
            exact LeComp.pure (Or.inl (Or.inl rfl))
          | some σ =>
            simp only [hisNoneL, hisNoneR, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
            refine LeComp.pure (Or.inr ⟨congrArg some (hreal_eq σ), rfl,
              ⟨rfl, rfl, hac_er, hsync.vp_base, hsync.cache_gt_max,
                hsync.epoch_le, hsync.epoch_sends, hsync.trans_epoch, hcomp_ac,
                (fun h => by rw [hpl_ac] at h; cases h),
                .postCorr ⟨hpl_ac, Q_corr, eC, σC, htH_eC,
                  by simp [GameState.afterCorr, hmem_corr],
                  hcrL, hcrR, hep_Qc, hres_Qc, hep_Qo, hsends_Qc, hroot_Qo, hcache_ge⟩⟩⟩)
        · have heC1_eq_t : eC - 1 = t := Decidable.of_not_not hne_t
          cases hresL_opt : resolveCorrRoot esL.h (esR.g.epoch Q_corr.other) (esL.g.st Q_corr.other).root with
          | none =>
            simp only [hpl, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
            exact LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inl rfl)
          | some σL =>
            simp only [hisNoneL, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set, simulateQ_pure]
            refine LeComp.pure_left _ _ fun _ _ => Or.inl (Or.inr (Or.inl ?_))
            intro P'
            dsimp only [GameState.afterCorr, GameState.leak]
            by_cases hP' : P' = Q_corr.other
            · subst P'
              refine ⟨esL.g.epoch Q_corr.other, List.mem_cons_self, ?_⟩
              rw [hep_eq, hep_eC1, heC1_eq_t]
              exact ltOpt_of_ge_healEpoch htLo
            · have hP'_Qc : P' = Q_corr := by
                cases P' <;> cases Q_corr <;> first | exact False.elim (hP' rfl) | rfl
              subst P'
              have hmemL : (Q_corr, eC) ∈ esL.g.corrs := by
                rw [eraseSt_corrs hsync.g_eq]; exact hmem_corr
              exact ⟨eC, List.mem_cons_of_mem _ hmemL, ltOpt_of_ge_healEpoch htH_eC⟩

/-! ### 5. Full Oracle Dispatcher `stepPMain`, `DoomedMain` Absorption, `runPMain`, and Top Step -/

private def stepPMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpec Γ T Sig SS RS M CCoins E).Range q ×
      PRNGBucketAuthEState Γ T Sig SS RS M E K I) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL m)
      Δcka qep fs.maxSkip tL false q).run st)).run sp

private theorem leComp_stepPMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hwinEp : stL.2 = stR.2)
    (hsync : SyncStepMain Δcka tL t stL.1 spL stR.1 spR) :
    LeComp (StepRelMain Δcka tL t)
      (stepPMain cka prng fs Δcka qep tL t q stL spL)
      (stepPMain cka prng fs Δcka qep tL (t + 1) q stR spR) := by
  rcases stL with ⟨esL, winEpL⟩
  rcases stR with ⟨esR, winEpR⟩
  dsimp only at hwinEp hsync
  subst hwinEp
  unfold stepPMain
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [implPRNGBucketAuthGen, pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact LeComp.sample_bind _ fun u _ => LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · exact leComp_transmit_main cka prng fs Δcka qep tL t htLo arg hsync
  · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync⟩)
  · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
    refine (leComp_deliverE_main cka prng fs Δcka qep tL t arg hsync).bind ?_
    rintro ⟨⟨outL, esL'⟩, spL'⟩ ⟨⟨outR, esR'⟩, spR'⟩ (hd | ⟨hout, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
      exact LeComp.pure (Or.inl (doomedMain_independent_winEp hd))
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)
  · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc,
      Bool.not_false, Bool.true_or, Bool.and_true]
    refine (leComp_injectE_main cka prng fs Δcka qep tL t arg hsync).bind ?_
    rintro ⟨⟨outL, esL'⟩, spL'⟩ ⟨⟨outR, esR'⟩, spR'⟩ (hd | ⟨hout, hsync'⟩)
    · simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
      exact LeComp.pure (Or.inl (doomedMain_independent_winEp hd))
    · dsimp only at hout; subst hout
      simp only [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
      rw [eraseSt_win hsync.g_eq, eraseSt_win hsync'.g_eq]
      exact LeComp.pure (Or.inr ⟨rfl, rfl, hsync'⟩)
  · exact leComp_corr_main cka prng fs Δcka qep tL t htLo P hsync

private theorem support_liftH_g_eq_main
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (x : HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    {r : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) ×
         PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (pImpl prng) ((liftH x).run es)).run sp)) :
    r.1.2.g = es.g ∧ r.1.2.abort = es.abort := by
  rw [run_liftH, simulateQ_bind, StateT.run_bind] at hr
  rw [MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨⟨⟨_, _⟩, _⟩, _, hr2⟩
  simp at hr2
  rcases hr2 with rfl
  exact ⟨rfl, rfl⟩

private theorem epMgmt_corrs_leaks_sub {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    s.corrs ⊆ s₁.corrs ∧ s.leaks ⊆ s₁.leaks := by
  unfold GameState.epMgmt at hep
  split_ifs at hep
  all_goals
    simp only [Option.some.injEq] at hep
    subst hep
  · exact ⟨List.Subset.refl _, fun _ hx => List.mem_cons_of_mem _ hx⟩
  · exact ⟨List.Subset.refl _, List.Subset.refl _⟩
  · exact ⟨List.Subset.refl _, List.Subset.refl _⟩

private theorem stepPMain_monotone
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support (stepPMain cka prng fs Δcka qep tL m q st sp),
      (st.1.abort = true → r.1.2.1.abort = true) ∧
      (r.1.2.1.abort = false →
        st.1.g.corrs ⊆ r.1.2.1.g.corrs ∧ st.1.g.leaks ⊆ r.1.2.1.g.leaks) := by
  intro r hr
  rcases st with ⟨es, winEp⟩
  unfold stepPMain at hr
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · simp [implPRNGBucketAuthGen, pImpl, StateT.run_lift, simulateQ_bind,
      simulateQ_query, map_eq_bind_pure_comp, bind_assoc] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
  · rcases arg with ⟨P, msg, r_coins⟩
    simp only [implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, pure_bind] at hr
    by_cases habw : (es.abort || es.g.win) = true
    · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
    · have hab_f : es.abort = false := by
        cases h : es.abort
        · rfl
        · simp [h] at habw
      simp only [habw, Bool.false_eq_true, ↓reduceIte] at hr
      cases hep : es.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr
        subst hr
        exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
      | some s₁ =>
        obtain ⟨hsub_c, hsub_l⟩ := epMgmt_corrs_leaks_sub hep
        simp only [hep, StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc] at hr
        rw [MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨⟨res_vs, h'⟩, sp1⟩, _, hr_rest⟩
        cases res_vs with
        | none =>
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          cases hr_rest
          exact ⟨fun _ => rfl, fun h => by simp at h⟩
        | some vc =>
          rcases vc with ⟨st', ct⟩
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
          cases hr_rest
          refine ⟨fun h => (by rw [hab_f] at h; cases h), fun _ => ⟨hsub_c, ?_⟩⟩
          dsimp only [GameState.record]
          exact hsub_l
  · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    cases hr
    exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
  · rcases arg with ⟨P, c⟩
    simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc] at hr
    rw [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨out_d, es'⟩, sp1⟩, hr_d, hr_rest⟩
    simp only [pure_bind, StateT.run_set, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
    cases hr_rest
    unfold deliverE at hr_d
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr_d
    by_cases habw : (es.abort || es.g.win) = true
    · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr_d
      cases hr_d
      exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
    · have hab_f : es.abort = false := by
        cases h : es.abort
        · rfl
        · simp [h] at habw
      simp only [habw, Bool.false_eq_true, ↓reduceIte] at hr_d
      cases htr : es.g.inTransit P.other c with
      | none =>
        simp only [htr, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hr_d
        cases hr_d
        exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
      | some rec =>
        simp only [htr, StateT.run_bind, simulateQ_bind] at hr_d
        rw [MonadAttach.mem_support_bind] at hr_d
        rcases hr_d with ⟨⟨⟨res_vr, es1⟩, sp2⟩, hr_vr, hr_d2⟩
        obtain ⟨hg1, hab1⟩ := support_liftH_g_eq_main prng _ es sp hr_vr
        dsimp only at hg1 hab1
        cases res_vr with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_d2
          cases hr_d2
          exact ⟨fun _ => rfl, fun h => by simp at h⟩
        | some opt_vr =>
          cases opt_vr with
          | none =>
            split_ifs at hr_d2 <;>
              simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_d2 <;>
              cases hr_d2 <;>
              exact ⟨fun h => (by rw [hab_f] at h; cases h),
                fun _ => by rw [hg1]; exact ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
          | some vtim =>
            rcases vtim with ⟨vp', t', i', m'⟩
            simp only [StateT.run_bind, run_commitE_main, pure_bind,
              StateT.run_modify, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hr_d2
            cases hr_d2
            refine ⟨fun h => (by rw [hab_f] at h; cases h), fun _ => ?_⟩
            split_ifs <;> exact ⟨List.Subset.refl _, List.Subset.refl _⟩
  · rcases arg with ⟨P, c⟩
    simp only [implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      simulateQ_bind, bind_assoc] at hr
    rw [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨out_i, es'⟩, sp1⟩, hr_i, hr_rest⟩
    simp only [pure_bind, StateT.run_set, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
    cases hr_rest
    unfold injectE at hr_i
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr_i
    by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !es.g.safeInj (2 + Δcka)) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr_i
      cases hr_i
      exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
    · have hab_f : es.abort = false := by
        cases h : es.abort
        · rfl
        · simp [h] at hguard
      simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind] at hr_i
      rw [MonadAttach.mem_support_bind] at hr_i
      rcases hr_i with ⟨⟨⟨res_vr, es1⟩, sp2⟩, hr_vr, hr_i2⟩
      obtain ⟨hg1, _⟩ := support_liftH_g_eq_main prng _ es sp hr_vr
      dsimp only at hg1
      cases res_vr with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_i2
        cases hr_i2
        exact ⟨fun _ => rfl, fun h => by simp at h⟩
      | some opt_vr =>
        cases opt_vr with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr_i2
          cases hr_i2
          exact ⟨fun h => (by rw [hab_f] at h; cases h),
            fun _ => by rw [hg1]; exact ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
        | some vtim =>
          rcases vtim with ⟨vp', t', i', m'⟩
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hr_i2
            cases hr_i2
            exact ⟨fun h => (by rw [hab_f] at h; cases h),
              fun _ => by rw [hg1]; exact ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
          · simp only [hqep, ↓reduceIte] at hr_i2
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_main,
                pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hr_i2
              cases hr_i2
              exact ⟨fun h => (by rw [hab_f] at h; cases h),
                fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr_i2
              split_ifs at hr_i2 <;>
                simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_i2 <;>
                cases hr_i2 <;>
                exact ⟨fun h => (by rw [hab_f] at h; cases h),
                  fun _ => by rw [hg1]; exact ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
  · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply,
      StateT.run_bind, StateT.run_get, pure_bind] at hr
    by_cases hguard : (es.abort || es.g.win || !es.g.corrAllowed P) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr
      cases hr
      exact ⟨id, fun _ => ⟨List.Subset.refl _, List.Subset.refl _⟩⟩
    · have hab_f : es.abort = false := by
        cases h : es.abort
        · rfl
        · simp [h] at hguard
      simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        simulateQ_bind, bind_assoc] at hr
      rw [MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨⟨⟨res_rv, h'⟩, sp1⟩, _, hr_rest⟩
      cases res_rv with
      | none =>
        simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
        cases hr_rest
        exact ⟨fun _ => rfl, fun h => by simp at h⟩
      | some stOut =>
        simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr_rest
        cases hr_rest
        refine ⟨fun h => (by rw [hab_f] at h; cases h), fun _ => ?_⟩
        dsimp only [GameState.afterCorr, GameState.leak]
        exact ⟨fun _ hx => List.mem_cons_of_mem _ hx, fun _ hx => List.mem_cons_of_mem _ hx⟩

private theorem stepPMain_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K)
    (hd : DoomedMain Δcka tL st) :
    ∀ r ∈ support (stepPMain cka prng fs Δcka qep tL m q st sp),
      DoomedMain Δcka tL r.1.2 := by
  intro r hr
  obtain ⟨hab_imp, hsub_imp⟩ := stepPMain_monotone cka prng fs Δcka qep tL m q st sp r hr
  by_cases hab' : r.1.2.1.abort = true
  · exact Or.inl hab'
  · have hab'_f : r.1.2.1.abort = false := Bool.eq_false_iff.mpr hab'
    obtain ⟨hsub_c, hsub_l⟩ := hsub_imp hab'_f
    rcases hd with hab0 | hcorrs0 | ⟨l, hl_mem, hlt, hlt_win⟩
    · exact Or.inl (hab_imp hab0)
    · exact Or.inr (Or.inl fun P =>
        let ⟨e, he_mem, he_lt⟩ := hcorrs0 P
        ⟨e, hsub_c he_mem, he_lt⟩)
    · exact Or.inr (Or.inr ⟨l, hsub_l hl_mem, hlt, hlt_win⟩)

private def runPMain
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL m)
      Δcka qep fs.maxSkip tL false) oa).run st)).run sp
  pure (authOutBucketMain (2 + Δcka) tL r.1.2)

private theorem runPMain_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ) (b : Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) :
    runPMain cka prng fs Δcka qep tL m (pure b) st sp =
      pure (authOutBucketMain (2 + Δcka) tL st) := by
  simp [runPMain]

private theorem runPMain_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) :
    runPMain cka prng fs Δcka qep tL m (liftM (OracleSpec.query q) >>= k) st sp =
      stepPMain cka prng fs Δcka qep tL m q st sp >>= fun r =>
        runPMain cka prng fs Δcka qep tL m (k r.1.1) r.1.2 r.2 := by
  simp [runPMain, stepPMain, simulateQ_bind, StateT.run_bind]

private theorem runPMain_doomed
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (m : ℕ)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {st : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {sp : PRFPRNG.GameState Sig I K}
    (hd : DoomedMain Δcka tL st) :
    𝒟[runPMain cka prng fs Δcka qep tL m oa st sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing st sp with
  | pure b' =>
    rw [runPMain_pure, authOutBucketMain_eq_false_of_doomedMain hd]
    simp
  | query_bind q k ih =>
    rw [runPMain_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPMain_doomed cka prng fs Δcka qep tL m q st sp hd r hr)

private theorem runPMain_le_succ
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (htLo : healEpoch tL ≤ t)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {stL stR : PRNGBucketAuthEState Γ T Sig SS RS M E K I}
    {spL spR : PRFPRNG.GameState Sig I K}
    (hwinEp : stL.2 = stR.2)
    (hsync : SyncStepMain Δcka tL t stL.1 spL stR.1 spR) :
    𝒟[runPMain cka prng fs Δcka qep tL t oa stL spL] {true} ≤
      𝒟[runPMain cka prng fs Δcka qep tL (t + 1) oa stR spR] {true} := by
  induction oa using OracleComp.inductionOn generalizing stL stR spL spR with
  | pure b' =>
    rw [runPMain_pure, runPMain_pure]
    rcases stL with ⟨esL, winEpL⟩
    rcases stR with ⟨esR, winEpR⟩
    dsimp only at hwinEp hsync
    subst hwinEp
    have hout : authOutBucketMain (2 + Δcka) tL (esL, winEpL) =
        authOutBucketMain (2 + Δcka) tL (esR, winEpL) := by
      cases winEpL with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketMain]
        rw [hsync.abortL, hsync.abortR, eraseSt_win hsync.g_eq,
          eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPMain_query_bind, runPMain_query_bind]
    refine leComp_stepPMain cka prng fs Δcka qep tL t htLo q hwinEp hsync _ _ ?_
    rintro ⟨⟨uL, stL'⟩, spL'⟩ ⟨⟨uR, stR'⟩, spR'⟩ (hd | ⟨hu, hwinEp', hsync'⟩)
    · rw [runPMain_doomed cka prng fs Δcka qep tL t (k uL) hd]
      exact zero_le
    · dsimp only at hu; subst hu
      exact ih uL hwinEp' hsync'

/-- Hop 2b (`Main` adjacent-epoch step): ideal PRNG (`b = true`) on `Main` at epoch `t` is
bounded by real PRNG (`b = false`) on `Main` at epoch `t + 1` for `healEpoch tL ≤ t < qep + 1`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridMain_le_succ_false_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (t + 1) A)] {true} := by
  have _ := htHi
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuthBucketHybridMain runPRNGAuthBucketHybridGen
    initPRNGBucketAuthHybrid
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    simulateQ_pImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  refine (leComp_rootInit_main (T := T) prng tL t lam (prng.init kr) htLo) _ _ ?_
  rintro ⟨⟨resL, hL0⟩, spL0⟩ ⟨⟨resR, hR0⟩, spR0⟩ hrel0
  rcases hrel0 with hnone |
    ⟨rL0, rR0, kVal, hresL, hresR, hr0, hcL0, hcR0, hcrL0, hcrR0, hft0, htab0,
      hbL0, hbR0, hσ0, hprfL0, hprfR0, hprng0, hcorr0⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hresL hresR
    subst hresL hresR
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind,
      pure_bind, bind_assoc]
    let pL := mkParties (T := T) (cka.initA kc) (cka.initB kc) rL0 (fs.initSender kVal) (fs.initReceiver kVal)
    let pR := mkParties (T := T) (cka.initA kc) (cka.initB kc) rR0 (fs.initSender kVal) (fs.initReceiver kVal)
    let gL : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => pL.1 | .B => pL.2, b := false }
    let gR : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => pR.1 | .B => pR.2, b := false }
    refine le_trans (le_of_eq ?_)
      (le_trans (runPMain_le_succ cka prng fs Δcka qep tL t htLo A
        (stL := ({ g := gL, h := hL0 }, none)) (stR := ({ g := gR, h := hR0 }, none))
        (spL := spL0) (spR := spR0) rfl ?_) (le_of_eq ?_))
    · unfold runPMain
      apply congrArg (fun c => 𝒟[c] {true})
      congr 1
      funext ⟨⟨bOut, esOut, winEpOut⟩, spOut⟩
      cases winEpOut <;> simp [authOutBucketMain]
    · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        .pre ⟨rfl, hcrL0, hcrR0, ?_, ?_, hft0, htab0, hbL0, hbR0,
          hσ0, hprfL0, fun _ => hprfR0,
          hprng0, hcorr0⟩⟩
      · intro P
        cases P <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      · intro e' _; rw [hcL0, hcR0]; exact ⟨rfl, rfl⟩
      · intro P; simp [gR]
      · intro P hlt; simp [gR] at hlt
      · intro r hr; cases hr
      · intro pos' hpos'; cases hpos'
      · intro _ Q hlt; simp [gR] at hlt
      · intro P; cases P <;> exact hr0
      · intro e'; rw [hcL0, hcR0]; exact Or.inl ⟨rfl, rfl⟩
    · unfold runPMain
      apply congrArg (fun c => 𝒟[c] {true})
      congr 1
      funext ⟨⟨bOut, esOut, winEpOut⟩, spOut⟩
      cases winEpOut <;> simp [authOutBucketMain]

end Hop2bMain

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bMain
