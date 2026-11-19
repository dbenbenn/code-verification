/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section ForgedTopCoupling

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

private theorem resolveCorrRoot_eq_of_syncTopRaw
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

private theorem postLeak_epMgmt_of_sendsIn_false {St Msg C : Type}
    {Δ qep : ℕ} {P : Party} {bad : Bool} {g s₁ : SM.GameState St Msg C}
    (hns : P.sendsIn (g.epoch P + 1) = false) (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold SM.GameState.epMgmt at hep; simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split at hep <;> simp at hep; exact hep.symm

private theorem isHonestHdr_eq_of_relCacheBucket [DecidableEq T]
    {hP : PRNGBucketState T Sig K I} {hL : LocalBucketState T Sig K I}
    (hc : ∀ e, RelCacheBucket (hP.cache e) (hL.cache e)) (hdr : Header T) :
    isHonestHdrPRNGBucket hP hdr = isHonestHdrLocalBucket hL hdr := by
  unfold isHonestHdrPRNGBucket isHonestHdrLocalBucket
  rcases hc hdr.1 with ⟨hcP, hcL⟩ | ⟨Tc, σp, σl, k, hcP, hcL, _⟩ <;>
    cases hdr.2 <;> simp [hcP, hcL]

private theorem transmitEBucket_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    transmitEBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) := rfl

private theorem transmitEBucket_localForged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    transmitEBucket (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) =
      transmitEBucket (hooksLocalBucket cka prng fs Δcka qep tL par) := rfl

private theorem deliverE_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    deliverE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      deliverE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) := rfl

private theorem deliverE_localForged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    deliverE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) =
      deliverE (hooksLocalBucket cka prng fs Δcka qep tL par) := rfl

private theorem injectE_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) := rfl

private theorem injectE_localForged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    injectE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) =
      injectE (hooksLocalBucket cka prng fs Δcka qep tL par) := rfl

private theorem deliverForgeE_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    deliverForgeE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t) =
      deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) := rfl

private theorem deliverForgeE_localForged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    deliverForgeE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) =
      deliverForgeE (hooksLocalBucket cka prng fs Δcka qep tL par) := rfl

private theorem leComp_transmitEBucket_forgedTop
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
        ((transmitEBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((transmitEBucket (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
          (2 + Δcka) qep arg).run esL)) := by
  rw [transmitEBucket_forged_eq, transmitEBucket_localForged_eq]
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
        fun _ s hres => resolveCorrRoot_eq_of_syncTopRaw hsync P s hres
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
          have hs₁L_eq : s₁L = esL.g := postLeak_epMgmt_of_sendsIn_false hns h2
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

private theorem leComp_deliverE_forgedTop [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (arg : Party × (Header T × E))
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) :
    AuthL11.LeComp (StepRelTopRaw prng Δcka qep tL)
      ((simulateQ (AuthL11.pImpl prng) ((deliverE
        (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1)) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl ((deliverE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rw [deliverE_forged_eq, deliverE_localForged_eq]
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
      have hσ_qep : postLeak tL esL.g = false → esL.g.epoch P = qep → sp.σ = (esL.g.st P).root := by
        intro hpl0 heq_qep
        have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
          have hA := hsync.epoch_le_qep .A; have hB := hsync.epoch_le_qep .B; cases P <;> omega
        exact ((hsync.pl_false_max hpl0).1 P hmax).symm
      simp only [hmust_eq, StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc]
      refine (leComp_vRecvBucketTop cka prng fs Δcka qep tL par (eraseSt_postLeak hsync.g_eq)
        (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
        (hsync.epoch_le_qep P) hsync.corrRoot_pl
        (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)
        (fun _ s hres => resolveCorrRoot_eq_of_syncTopRaw hsync P s hres) hσ_qep).bind ?_
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
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNGBucket, run_commitE_LocalBucket,
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

private theorem leComp_injectE_forgedTop
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
        ((injectE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((injectE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rw [injectE_forged_eq, injectE_localForged_eq]
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
    have hσ_qep : postLeak tL esL.g = false → esL.g.epoch P = qep → sp.σ = (esL.g.st P).root := by
      intro hpl0 heq_qep
      have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
        have hA := hsync.epoch_le_qep .A; have hB := hsync.epoch_le_qep .B; cases P <;> omega
      exact ((hsync.pl_false_max hpl0).1 P hmax).symm
    refine (leComp_vRecvBucketTop cka prng fs Δcka qep tL par (eraseSt_postLeak hsync.g_eq)
      (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
      (hsync.epoch_le_qep P) hsync.corrRoot_pl
      (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)
      (fun _ s hres => resolveCorrRoot_eq_of_syncTopRaw hsync P s hres) hσ_qep).bind ?_
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
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucket,
            run_commitE_LocalBucket, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
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

private theorem leComp_deliverForgeE_forgedTop
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
        ((deliverForgeE (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((deliverForgeE (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esL)) := by
  rw [deliverForgeE_forged_eq, deliverForgeE_localForged_eq]
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
        have hσ_qep : postLeak tL esL.g = false → esL.g.epoch P = qep → sp.σ = (esL.g.st P).root := by
          intro hpl0 heq_qep
          have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) := by
            have hA := hsync.epoch_le_qep .A; have hB := hsync.epoch_le_qep .B; cases P <;> omega
          exact ((hsync.pl_false_max hpl0).1 P hmax).symm
        refine (leComp_vRecvBucketTop cka prng fs Δcka qep tL par (eraseSt_postLeak hsync.g_eq)
          (hsync.vp_rel P) hsync.cache_rel hsync.fTable_lt hsync.table_top hsync.sp_b
          (hsync.epoch_le_qep P) hsync.corrRoot_pl
          (fun eC σC hcr => (hsync.corrRoot_rel eC σC hcr).2.2)
          (fun _ s hres => resolveCorrRoot_eq_of_syncTopRaw hsync P s hres) hσ_qep).bind ?_
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
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNGBucket,
                run_commitE_LocalBucket, StateT.run_pure, StateT.run_modify, pure_bind,
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

private theorem leComp_corrEPaperBucket_forgedTop
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
        ((corrEPaperBucket (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1)) P).run esP)).run sp)
      (simulateQ AuthL11.lImpl
        ((corrEPaperBucket (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par) P).run esL)) := by
  unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
    AuthL11.eraseSt_corrAllowedPaper hsync.g_eq P]
  by_cases hguard : (false || esL.g.win || !esL.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hac_er := AuthL11.eraseSt_afterCorr hsync.g_eq P
    have hvp := hsync.vp_rel P
    have hep_eq : esP.g.epoch = esL.g.epoch := AuthL11.eraseSt_epoch hsync.g_eq
    have hps_eq : realParty (esP.g.st P) (esP.g.st P).γ (esL.g.st P).root (esP.g.st P).vS (esP.g.st P).vR =
        realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
      dsimp only [realParty]
      rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq, funext hvp.vR_eq]
    have hcomp_ac := AuthL11.comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
      (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv
    simp only [StateT.run_bind, AuthL11.run_liftH, simulateQ_bind, bind_assoc,
      hooksPRNGBucketForgedHdr, hooksPRNGBucketForgedHdrGen, hooksLocalBucketForgedHdr,
      pure_bind]
    rw [hvp.tcur_P, hvp.tcur_L, hep_eq]
    by_cases hlt_abort : (!(decide (esL.g.epoch P < healEpoch tL)) ||
        !(decide (max (esL.g.epoch .A) (esL.g.epoch .B) < healEpoch tL))) = true
    · simp only [hlt_abort, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        pure_bind, abortE, StateT.run_bind, StateT.run_modify]
      exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · simp only [hlt_abort, Bool.false_eq_true, ↓reduceIte]
      cases hrP : (esP.g.st P).root with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind, abortE, StateT.run_bind,
          StateT.run_modify]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      | some σ =>
        have hσ_eq := hvp.root_eq σ hrP; subst hσ_eq
        simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_bind, StateT.run_modify]
        exact AuthL11.LeComp.pure (Or.inr ⟨congrArg some hps_eq,
          ⟨hsync.abortP, hsync.abortL, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.fTable_lt,
            hsync.table_top, hsync.sp_b, hsync.epoch_le_qep, hcomp_ac,
            hsync.trans_epoch, hsync.vp_curCka, hsync.trans_cache, hsync.epoch_le, hsync.epoch_sends,
            hsync.same_epoch_rootL, hsync.cache_rootL, hsync.cache_rootP_none,
            fun hcr => postLeak_afterCorr_mono (hsync.corrRoot_pl hcr), hsync.corrRoot_rel,
            fun Q hge his => postLeak_afterCorr_mono (hsync.root_ge_tH_pl Q hge his),
            hsync.some_mono_max, hsync.root_max, hsync.cache_max,
            fun hpl => hsync.pl_false_max (Bool.eq_false_iff.mpr fun ht => (by
              rw [postLeak_afterCorr_mono ht] at hpl; cases hpl)), hsync.lc_inv⟩⟩)

private theorem leComp_implEDFPaperBucketRaw_forgedTop
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
        (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esP)).run sp)
      (simulateQ AuthL11.lImpl ((implEDFPaperBucketRaw
        (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esL)) := by
  rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
  · simp [implEDFPaperBucketRaw, coinsE, AuthL11.pImpl, AuthL11.lImpl, StateT.run_lift,
      simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, bind_assoc]
    exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
    exact leComp_transmitEBucket_forgedTop cka prng fs Δcka qep tL par arg hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure, simulateQ_pure]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
    exact leComp_deliverE_forgedTop cka prng fs Δcka qep tL par arg hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
    exact leComp_injectE_forgedTop cka prng fs Δcka qep tL par arg hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
    exact leComp_corrEPaperBucket_forgedTop cka prng fs Δcka qep tL par P hsync
  · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
    exact leComp_deliverForgeE_forgedTop cka prng fs Δcka qep tL par df hsync

private def StepRelBucketForgedTop (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) {α : Type}
    (x : (α × (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K)
    (y : α × (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) : Prop :=
  x.1.2.1.abort = true ∨ (x.1.1 = y.1 ∧ x.1.2.2 = y.2.2 ∧ SyncTopRaw prng Δcka qep tL x.1.2.1 x.2 y.2.1)

private def stepPBucketForgedTop [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (AuthL11.pImpl prng)
    ((implEDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket q).run stP)).run sp

private def stepLBucketForgedTop [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp ((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ)) :=
  simulateQ AuthL11.lImpl
    ((implEDFPaperBucketMode (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrLocalBucket q).run stL)

private theorem leComp_stepPBucketForgedTop_stepLBucketForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncTopRaw prng Δcka qep tL stP.1 sp stL.1) :
    AuthL11.LeComp (StepRelBucketForgedTop prng Δcka qep tL)
      (stepPBucketForgedTop cka prng fs Δcka qep tL par q stP sp)
      (stepLBucketForgedTop cka prng fs Δcka qep tL par q stL) := by
  rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
  dsimp only at hwinEp hsync; subst hwinEp
  unfold stepPBucketForgedTop stepLBucketForgedTop implEDFPaperBucketMode withWinEpDFMode
  simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  refine (leComp_implEDFPaperBucketRaw_forgedTop cka prng fs Δcka qep tL par q hsync).bind ?_
  rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨hu, hsync'⟩)
  · exact AuthL11.LeComp.pure (Or.inl hab)
  · dsimp only at hu; subst hu
    refine AuthL11.LeComp.pure (Or.inr ⟨rfl, ?_, hsync'⟩)
    dsimp only
    rw [AuthL11.eraseSt_win hsync.g_eq, AuthL11.eraseSt_win hsync'.g_eq]
    revert uP
    rcases q with _ | (((((_ | _) | _) | ⟨P, c⟩) | _) | _) <;> intro uP _ <;> dsimp only
    simp only [(hsync.vp_rel P).tcur_P, (hsync.vp_rel P).tcur_L,
      isHonestHdr_eq_of_relCacheBucket hsync.cache_rel c.1]

private theorem stepPBucketForgedTop_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) (hab : stP.1.abort = true) :
    ∀ r ∈ support (stepPBucketForgedTop cka prng fs Δcka qep tL par q stP sp),
      r.1.2.1.abort = true := by
  intro r hr; rcases stP with ⟨esP, winEpP⟩; dsimp only at hab
  rcases q with n | (((((q | q) | q) | q) | P) | df)
  · simp [stepPBucketForgedTop, implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
      coinsE, AuthL11.pImpl, StateT.run_lift, simulateQ_bind, simulateQ_query,
      map_eq_bind_pure_comp, bind_assoc] at hr
    rcases hr with ⟨_, _, rfl⟩; exact hab
  · simp [stepPBucketForgedTop, implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
      transmitEBucket, hab] at hr
    rcases hr with rfl; exact hab
  · simp [stepPBucketForgedTop, implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
      challEBucket] at hr
    rcases hr with rfl; exact hab
  all_goals
    simp [stepPBucketForgedTop, implEDFPaperBucketMode, withWinEpDFMode, implEDFPaperBucketRaw,
      deliverE, injectE, corrEPaperBucket, deliverForgeE, hab] at hr
    rcases hr with rfl; exact hab

private def runPBucketForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (AuthL11.pImpl prng)
    ((simulateQ (implEDFPaperBucketMode
      (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par (qep + 1))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket) oa).run stP)).run sp
  pure (authOutBucketPaper (2 + Δcka) tL r.1.2)

private def runLBucketForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    ((simulateQ (implEDFPaperBucketMode
      (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrLocalBucket) oa).run stL)
  pure (authOutBucketPaper (2 + Δcka) tL r.2)

private theorem runPBucketForgedTop_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketForgedTop cka prng fs Δcka qep tL par (pure b) stP sp =
      pure (authOutBucketPaper (2 + Δcka) tL stP) := by simp [runPBucketForgedTop]

private theorem runLBucketForgedTop_pure
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketForgedTop cka prng fs Δcka qep tL par (pure b) stL =
      pure (authOutBucketPaper (2 + Δcka) tL stL) := by simp [runLBucketForgedTop]

private theorem runPBucketForgedTop_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runPBucketForgedTop cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stP sp =
      stepPBucketForgedTop cka prng fs Δcka qep tL par q stP sp >>= fun r =>
        runPBucketForgedTop cka prng fs Δcka qep tL par (k r.1.1) r.1.2 r.2 := by
  simp [runPBucketForgedTop, stepPBucketForgedTop, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runLBucketForgedTop_query_bind
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ) :
    runLBucketForgedTop cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stL =
      stepLBucketForgedTop cka prng fs Δcka qep tL par q stL >>= fun r =>
        runLBucketForgedTop cka prng fs Δcka qep tL par (k r.1) r.2 := by
  simp [runLBucketForgedTop, stepLBucketForgedTop, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

private theorem runPBucketForgedTop_abort
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K} (hab : stP.1.abort = true) :
    𝒟[runPBucketForgedTop cka prng fs Δcka qep tL par oa stP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stP sp with
  | pure b' =>
    rw [runPBucketForgedTop_pure]; rcases stP with ⟨esP, winEpP⟩; dsimp only at hab
    cases winEpP <;> simp [authOutBucketPaper, authOutBucket, authOut, hab]
  | query_bind q k ih =>
    rw [runPBucketForgedTop_query_bind]
    exact AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPBucketForgedTop_abort cka prng fs Δcka qep tL par q stP sp hab r hr)

private theorem runPBucketForgedTop_le_runLBucketForgedTop
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    {stL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I) × Option ℕ}
    (hwinEp : stP.2 = stL.2) (hsync : SyncTopRaw prng Δcka qep tL stP.1 sp stL.1) :
    𝒟[runPBucketForgedTop cka prng fs Δcka qep tL par oa stP sp] {true} ≤
      𝒟[runLBucketForgedTop cka prng fs Δcka qep tL par oa stL] {true} := by
  induction oa using OracleComp.inductionOn generalizing stP sp stL with
  | pure b' =>
    rw [runPBucketForgedTop_pure, runLBucketForgedTop_pure]
    rcases stP with ⟨esP, winEpP⟩; rcases stL with ⟨esL, winEpL⟩
    dsimp only at hwinEp hsync; subst hwinEp
    have hout : authOutBucketPaper (2 + Δcka) tL (esP, winEpP) =
        authOutBucketPaper (2 + Δcka) tL (esL, winEpP) := by
      cases winEpP with
      | none => rfl
      | some tWin =>
        simp only [authOutBucketPaper, authOutBucket, authOut]
        rw [hsync.abortP, hsync.abortL, AuthL11.eraseSt_win hsync.g_eq,
          AuthL11.eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin]
    rw [hout]
  | query_bind q k ih =>
    rw [runPBucketForgedTop_query_bind, runLBucketForgedTop_query_bind]
    refine leComp_stepPBucketForgedTop_stepLBucketForgedTop cka prng fs Δcka qep tL par q
      hwinEp hsync _ _ ?_
    rintro ⟨⟨uP, stP'⟩, sp'⟩ ⟨uL, stL'⟩ (hab | ⟨hu, hwinEp', hsync'⟩)
    · rw [runPBucketForgedTop_abort cka prng fs Δcka qep tL par (k uP) hab]; exact zero_le
    · dsimp only at hu; subst hu; exact ih uP hwinEp' hsync'

private theorem syncTopRaw_init_forged
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

/-- Hop-2c top step (`t = qep + 1`, `b = true`, `ForgedHdr`): the ideal PRF-PRNG world at the final
reachable epoch `qep + 1` is bounded by `localAuthDFPaperBucketForgedHdr`. -/
theorem prng_branch_true_redPRNGAuthDFPaperBucketForgedHdr_top_le_local_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (_htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par (qep + 1) A)] {true} ≤
      𝒟[localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuthDFPaperBucketForgedHdr localAuthDFPaperBucketForgedHdr
    engRunDFPaperBucketMode initPRNGBucketHybrid initLocalBucket
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
    exact runPBucketForgedTop_le_runLBucketForgedTop (stP := (_, none)) (stL := (_, none))
      cka prng fs Δcka qep tL par A rfl
      (syncTopRaw_init_forged prng Δcka qep tL (cka.initA kc) (cka.initB kc)
        (fs.initSender kL) (fs.initReceiver kL) σP σL hP0 sp0 hL0
        hσ_rel hσP_eq hsp_σ hcr0 hb0 hcP0 hlcP0 hcL0 hlcL0 hft0 htop0)

end ForgedTopCoupling

end CryptoGames.SM.Construction.DeliverForge
