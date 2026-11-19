/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG

/-!
# `DeliverForge` Lemma 11 and Theorem 8

Lifts Lemma 11 (hop H2 → FS-AEAD) to `SMCompDF` (`implEDF`) and assembles `theorem8_df`.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL11

open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
open Engine
open SM

variable {ι : Type} {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

abbrev SMSpecDF (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

abbrev SMCompDF (Γ T Sig SS RS M CCoins E : Type) :=
  AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

@[expose] def liftQ (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain) :
    (SMSpecDF Γ T Sig SS RS M CCoins E).Domain :=
  match q with
  | .inl n => .inl n
  | .inr oq => .inr (.inl oq)

@[expose] def stepPDF (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDF (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

@[expose] def stepLDF (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDF (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esL)

def runPDF (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implEDF (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runLocDF (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDF (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2)

@[expose] def runLocAtDF (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDF (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

@[expose] def localAuthDF (tL : Option ℕ) (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocDF cka prng fs Δcka qep mo A { g, h }

@[expose] def localAuthAtDF (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtDF cka prng fs Δcka qep mo j A { g, h }

@[expose] def stepLFixedDF (j : ℕ) (k_fs : K) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDF (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esL)

@[expose] def runLocAtFixedDF (j : ℕ) (k_fs : K) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDF (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

@[expose] def localAuthAtFixedDF (j : ℕ) (k_fs : K) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtFixedDF cka prng fs Δcka qep mo j k_fs A { g, h }

@[expose] def stepFDF (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) :=
  (simulateQ (implFS fs)
    ((implEDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esF)).run st

@[expose] def runFDF (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) : ProbComp Bool := do
  let r ← (simulateQ (implFS fs)
    ((simulateQ (implEDF (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esF)).run st
  pure r.2.win

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDF_pure (j : ℕ) (k_fs : K) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDF cka prng fs Δcka qep mo j k_fs (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtFixedDF, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDF_query_bind (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDF cka prng fs Δcka qep mo j k_fs (liftM (OracleSpec.query q) >>= k) esL =
      stepLFixedDF cka prng fs Δcka qep mo j k_fs q esL >>= fun r =>
        runLocAtFixedDF cka prng fs Δcka qep mo j k_fs (k r.1) r.2 := by
  simp [runLocAtFixedDF, stepLFixedDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runFDF_query_bind (j : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    runFDF cka prng fs Δcka qep mo j (liftM (OracleSpec.query q) >>= k) esF st =
      stepFDF cka prng fs Δcka qep mo j q esF st >>= fun r =>
        runFDF cka prng fs Δcka qep mo j (k r.1.1) r.1.2 r.2 := by
  simp [runFDF, stepFDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem stepPDF_abort (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) (hab : esP.abort = true) :
    ∀ r ∈ support (stepPDF cka prng fs Δcka qep mo q esP sp), r.1.2.abort = true := by
  intro r hr
  rcases q with n | (oq | ⟨P, c, c'⟩)
  · exact stepP_abort cka prng fs Δcka qep mo (.inl n) esP sp hab r hr
  · exact stepP_abort cka prng fs Δcka qep mo (.inr oq) esP sp hab r hr
  · simp only [stepPDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab

theorem leComp_deliverForgeE_PRNG_local
    (arg : Party × (Header T × E) × (Header T × E))
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((deliverForgeE (hooksPRNG cka prng fs mo) (2 + Δcka) qep mo.cfg arg).run esP)).run sp)
      (simulateQ lImpl
        ((deliverForgeE (hooksLocal cka prng fs mo) (2 + Δcka) qep mo.cfg arg).run esL)) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq]
  by_cases habw : (esL.abort || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rw [eraseSt_inTransit hsync.g_eq]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      rw [eraseSt_inTransit hsync.g_eq, eraseSt_comp hsync.g_eq]
      by_cases hguard :
          ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        have hhdr : c.1 = c'.1 := hguard.2
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c'.1.1 := by
          rw [← hhdr, ← hr_ep.2, hr_mem.2.2]
        have hc_le_other : c'.1.1 ≤ esL.g.epoch P.other := by
          rw [← hr_pos_ep, ← hr_mem.2.1]
          exact hr_ep.1
        have hσ_tStar : P.sendsIn (esL.g.epoch P + 1) = false → esL.g.epoch P + 1 = mo.tStar →
            ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = (esL.g.st P).root := by
          intro _ he1 hnot_th
          exact (hsync.root_pred (by omega) P (by omega) hnot_th).symm
        refine (leComp_vRecv_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
          hsync.sp_b hsync.table_eq hsync.corr_tH hσ_tStar).bind ?_
        rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
        rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hc1, hb1, htab1, hcorr1, hσ1⟩ |
          ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hc1, hb1, htab1, hcorr1,
            hσ1, hroot_le, hcache_e1⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none hhP1; subst hP_none hL_none hhP1
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          refine LeComp.pure ?_
          refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
            htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
            fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
            fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
            fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
          intro t'; rw [hc1]; exact hsync.cache_rel t'
        · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
          have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [hr_pos_ep]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind, hne_ep, Bool.or_false]
          by_cases hqep : decide (qep + 1 < c'.1.1) = true
          · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            refine LeComp.pure ?_
            refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
              htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 =>
                (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
            intro t'; rw [hc1]; exact hsync.cache_rel t'
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
            rw [eraseSt_trivial hsync.g_eq]
            by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNG, run_commitE_local,
                StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
              let pos : Pos := ⟨P.other, c'.1.1, i'⟩
              have hacc_er : eraseSt (esP.g.accept P vpP' pos) =
                  eraseSt (esL.g.accept P vpL' pos) :=
                eraseSt_accept hsync.g_eq P vpP' vpL' pos
              have hacc_ep_L : (esL.g.accept P vpL' pos).epoch =
                  Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) := rfl
              refine LeComp.pure (Or.inr ⟨rfl, ?_⟩)
              refine ⟨hsync.abort_eq, hacc_er, ?_, ?_, hb1, htab1, hcorr1,
                comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv,
                ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro Q
                dsimp only
                rw [hacc_ep_L]
                dsimp only [SM.GameState.accept]
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self]; exact hvp'
                · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
              · intro t'; rw [hc1]; exact hsync.cache_rel t'
              · intro r' hr'
                dsimp only at hr' ⊢
                rw [hacc_ep_L]
                simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr' ⊢
                obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
                refine ⟨?_, h2⟩
                by_cases hQ : r'.pos.sender = P
                · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
                · rw [Function.update_of_ne hQ]; exact h1
              · intro Q
                dsimp only
                rw [hacc_ep_L]
                have hle_P := hsync.epoch_le P
                have hle_other := hsync.epoch_le P.other
                cases Q <;> cases P <;>
                  simp [Party.other] at hc_le_other htle hle_P hle_other ⊢ <;> omega
              · intro Q hlt_Q
                dsimp only at hlt_Q ⊢
                rw [hacc_ep_L] at hlt_Q ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other
                    rw [Party.other_other] at this
                    omega
                  cases Q <;> cases P <;> simp [Party.other, hnew] at heq_other hlt_Q <;> omega
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  have hmax_e : max (esL.g.epoch P) c'.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
                  rw [hmax_e, Function.update_eq_self] at hlt_Q ⊢
                  exact hsync.epoch_sends Q hlt_Q
              · intro Q hQ_max hQ_lt
                dsimp only at hQ_max hQ_lt ⊢
                rw [hacc_ep_L] at hQ_max hQ_lt
                rw [hσ1]
                dsimp only [SM.GameState.accept] at hQ_max hQ_lt ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other
                    rw [Party.other_other] at this
                    omega
                  have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
                    cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
                  have hmax_new :
                      max (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .A)
                        (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .B) =
                        esL.g.epoch P + 1 := by
                    rw [hnew]
                    exact max_epoch_accept_succ (by omega) (by omega)
                  by_cases hQ : Q = P
                  · subst Q
                    simp only [Function.update_self] at hQ_lt ⊢
                    have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
                    obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
                    rw [← hmax_old] at hc_eq he1_lt
                    exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
                  · simp only [Function.update_of_ne hQ] at hQ_max hQ_lt ⊢
                    have hQ_eq_max : esL.g.epoch Q = max (esL.g.epoch .A) (esL.g.epoch .B) := by
                      rw [hmax_old, ← hmax_new, hQ_max]
                    exact hsync.root_max Q hQ_eq_max hQ_lt
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  have hmax_e : max (esL.g.epoch P) c'.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
                  rw [hmax_e, Function.update_eq_self] at hQ_max hQ_lt
                  by_cases hQ : Q = P
                  · subst Q
                    simp only [Function.update_self, hroot_le htle_e]
                    exact hsync.root_max P hQ_max hQ_lt
                  · simp only [Function.update_of_ne hQ]
                    exact hsync.root_max Q hQ_max hQ_lt
              · intro hpos Q hQ_pred hnot_th
                dsimp only at hQ_pred ⊢
                rw [hacc_ep_L] at hQ_pred
                rw [hσ1]
                dsimp only [SM.GameState.accept] at hQ_pred ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other
                    rw [Party.other_other] at this
                    omega
                  have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
                    cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
                  by_cases hQ : Q = P
                  · subst Q
                    simp only [Function.update_self] at hQ_pred ⊢
                    have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
                    obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
                    rw [← hmax_old] at hc_eq he1_lt
                    exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
                  · simp only [Function.update_of_ne hQ] at hQ_pred ⊢
                    exact hsync.root_pred hpos Q hQ_pred hnot_th
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  have hmax_e : max (esL.g.epoch P) c'.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
                  rw [hmax_e, Function.update_eq_self] at hQ_pred
                  by_cases hQ : Q = P
                  · subst Q
                    simp only [Function.update_self, hroot_le htle_e]
                    exact hsync.root_pred hpos P hQ_pred hnot_th
                  · simp only [Function.update_of_ne hQ]
                    exact hsync.root_pred hpos Q hQ_pred hnot_th
              · intro Tc σc k idx? hc_max hmax_lt
                dsimp only at hc_max hmax_lt ⊢
                rw [hacc_ep_L, hc1] at hc_max
                rw [hacc_ep_L] at hmax_lt
                rw [hσ1]
                have hmax_eq : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .A)
                    (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .B) =
                    max (esL.g.epoch .A) (esL.g.epoch .B) := by
                  cases P <;> simp [Party.other] at hc_le_other ⊢ <;> omega
                rw [hmax_eq] at hc_max hmax_lt
                exact hsync.cache_max Tc σc k idx? hc_max hmax_lt
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : (mo.cfg : SM.Config M).injectFull c'.1.1 = true
              · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                refine LeComp.pure ?_
                refine Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, hsync.vp_rel, ?_, hb1, htab1,
                  hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
                  fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
                  fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
                  fun Tc σc k idx? h1 h2 =>
                    (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
                · have hg := hsync.g_eq
                  simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
                    eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
                    eraseSt_leaks hg, eraseSt_corrs hg]
                · intro t'; rw [hc1]; exact hsync.cache_rel t'
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                refine LeComp.pure ?_
                refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
                  htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le,
                  hsync.epoch_sends,
                  fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
                  fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
                  fun Tc σc k idx? h1 h2 =>
                    (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
                intro t'; rw [hc1]; exact hsync.cache_rel t'

theorem leComp_stepPDF_stepLDF (hauth : mo.auth = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      (stepPDF cka prng fs Δcka qep mo q esP sp)
      (stepLDF cka prng fs Δcka qep mo q esL) := by
  rcases q with n | (oq | df)
  · exact leComp_stepP_stepL cka prng fs Δcka qep mo hauth (.inl n) hsync
  · exact leComp_stepP_stepL cka prng fs Δcka qep mo hauth (.inr oq) hsync
  · exact leComp_deliverForgeE_PRNG_local cka prng fs Δcka qep mo df hsync

theorem stepLDF_sessInv (hauth : mo.auth = true) {q rem : ℕ}
    (q_sm : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    (∀ t, q_sm = .inl t →
      ∀ r ∈ support (stepLDF cka prng fs Δcka qep mo (.inl t) esL),
        SessInv mo q rem r.2) ∧
    (∀ q_inr, q_sm = .inr q_inr → 0 < rem →
      ∀ r ∈ support (stepLDF cka prng fs Δcka qep mo (.inr q_inr) esL),
        SessInv mo q (rem - 1) r.2) := by
  constructor
  · intro t ht r hr
    exact (stepL_sessInv cka prng fs Δcka qep mo hauth (.inl t) esL hS).1 t rfl r hr
  · intro q_inr hq_sm hrem r hr
    rcases q_inr with oq | ⟨P, c, c'⟩
    · exact (stepL_sessInv cka prng fs Δcka qep mo hauth (.inr oq) esL hS).2 oq rfl hrem r hr
    · have hrem_mono :
          (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
          (esL.g.win = false ∧
            ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
             (0 < mo.tStar ∧ esL.h.sessions.length + (rem - 1) ≤ q))) := by
        rcases hS.bound with hwin | ⟨hnw, ⟨ht0, hle1, _⟩ | hpos⟩
        · exact Or.inl hwin
        · exact Or.inr ⟨hnw, Or.inl ⟨ht0, hle1, by omega⟩⟩
        · exact Or.inr ⟨hnw, Or.inr ⟨hpos.1, by omega⟩⟩
      have hS_noop : SessInv mo q (rem - 1) esL := ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
      simp only [stepLDF, implEDF, QueryImpl.add_apply, deliverForgeE, Mode.cfg, hauth, ↓reduceIte,
        SM.Config.auth, StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_ab_win
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_ab_win
        have hnw : esL.g.win = false := hnot_ab_win.2
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnw; cases hnw
        · split at hr
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hS_noop
          · split at hr
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact hS_noop
            · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                MonadAttach.mem_support_bind] at hr
              rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
              obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
                mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
              have hbound' :
                  (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
                  (esL.g.win = false ∧
                    ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                     (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
                refine Or.inr ⟨hnw, ?_⟩
                rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨htpos, _⟩
                · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
                · exact Or.inr ⟨htpos, by omega⟩
              have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
                  ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
                intro Tc σ k idx? hc
                rw [hcache'] at hc
                obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              cases res_vr with
              | none =>
                simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                subst hr2
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              | some res_vr' =>
                cases res_vr' with
                | none =>
                  simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr2
                  subst hr2
                  refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                  obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                  exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
                | some val =>
                  rcases val with ⟨st', t', i', m'⟩
                  obtain ⟨_, hvR_st', hlast_tStar⟩ := hvp' st' t' i' m' rfl
                  simp only  at hr2
                  split at hr2
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hr2
                    subst hr2
                    refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                    obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                    exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
                  · split at hr2
                    · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                        StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                        Set.mem_singleton_iff] at hr2
                      subst hr2
                      refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                      dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                      rw [Function.update_idem] at hq
                      exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
                    · split at hr2
                      · rename_i ht'
                        simp only [beq_iff_eq] at ht'
                        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                        subst hr2
                        obtain ⟨idx, hidx_lt, hlast_eq⟩ := hlast_tStar ht'
                        have hidx_q : idx < q := by
                          rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨_, _⟩
                          · rw [h0 ht0] at hidx_lt; omega
                          · omega
                        refine ⟨fun Q rsv hq => ?_, hc', Or.inl ⟨rfl, ⟨idx, hidx_q, hlast_eq⟩⟩⟩
                        obtain ⟨idx', hlt, heq⟩ := hS.vR_idx Q rsv hq
                        exact ⟨idx', lt_of_lt_of_le hlt hl1, heq⟩
                      · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                          Set.mem_singleton_iff] at hr2
                        subst hr2
                        refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                        obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                        exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩

theorem stepLFixedDF_eq_of_lt {j : ℕ} (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    stepLFixedDF cka prng fs Δcka qep mo j k_fs q esL =
      stepLDF cka prng fs Δcka qep mo q esL := by
  rcases q with n | (oq | ⟨P, c, c'⟩)
  · exact stepLFixed_eq_of_lt cka prng fs Δcka qep mo k_fs (.inl n) hlt
  · exact stepLFixed_eq_of_lt cka prng fs Δcka qep mo k_fs (.inr oq) hlt
  · simp only [stepLFixedDF, stepLDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [StateT.run_bind, run_liftH,
            vRecv_fixed_eq_of_lt cka prng fs mo k_fs esL.g P (esL.g.st P) c' none hlt]
          rfl

theorem mem_support_stepLDF_sessions_le
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I)
    {r : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (stepLDF cka prng fs Δcka qep mo q esL)) :
    esL.h.sessions.length ≤ r.2.h.sessions.length := by
  rcases q with n | (oq | ⟨P, c, c'⟩)
  · exact mem_support_stepL_sessions_le cka prng fs Δcka qep mo (.inl n) esL hr
  · exact mem_support_stepL_sessions_le cka prng fs Δcka qep mo (.inr oq) esL hr
  · simp only [stepLDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      · split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact le_rfl
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
          have hl := mem_support_vRecv_sessions_le cka prng fs mo hvr
          cases res_vr with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2; exact hl
          | some res_vr' =>
            cases res_vr' with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              simp only  at hr2
              split at hr2
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2; exact hl
              · split at hr2
                · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                    StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr2
                  subst hr2; exact hl
                · split at hr2
                  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                    subst hr2; exact hl
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hr2
                    subst hr2; exact hl

theorem shiftLe_stepLDF {j : ℕ}
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    ShiftLe mo j (fun r => r.2.h)
      (stepLDF cka prng fs Δcka qep mo q esL)
      (fun k_fs => stepLFixedDF cka prng fs Δcka qep mo j k_fs q esL) := by
  rcases q with n | (oq | ⟨P, c, c'⟩)
  · exact shiftLe_stepL cka prng fs Δcka qep mo (.inl n) hle hinv
  · exact shiftLe_stepL cka prng fs Δcka qep mo (.inr oq) hle hinv
  · simp only [stepLDF, stepLFixedDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · split
        · simp only [StateT.run_pure, simulateQ_pure]
          exact ShiftLe.pure mo _ hle hinv
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
            commitE, hooksLocal, hooksLocalFixed]
          refine (shiftLe_vRecv cka prng fs mo esL.g P (esL.g.st P) c' none hle hinv).post
            mo _ ?_
          intro a b hb
          rcases a with ⟨res_vr, h'⟩
          cases res_vr with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          | some res_vr' =>
            cases res_vr' with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              simp only  at hb
              split at hb
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hb
                subst hb; exact ⟨rfl, rfl⟩
              · split at hb
                · simp only [StateT.run_bind] at hb
                  subst hb; exact ⟨rfl, rfl⟩
                · split at hb
                  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
                    subst hb; exact ⟨rfl, rfl⟩
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hb
                    subst hb; exact ⟨rfl, rfl⟩

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runFDF_eq_one_of_win (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E)
    (hwin : st.win = true) :
    𝒟[runFDF cka prng fs Δcka qep mo j oa esF st] {true} = 1 := by
  unfold runFDF
  refine evalDist_bind_eq_one _ _ fun r hr => ?_
  rw [simulateQ_implFS_preserves_win fs _ st hwin r hr]
  simp

theorem stepLFixedDF_preserves_LHSDead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    ∀ r ∈ support (stepLFixedDF cka prng fs Δcka qep mo j k_fs q esL),
      LHSDead Δcka mo j r.2 := by
  intro r hr
  rcases q with n | (oq | ⟨P, c, c'⟩)
  · exact stepLFixed_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs (.inl n) esL hdead r hr
  · exact stepLFixed_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs (.inr oq) esL hdead r hr
  · rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
        StateT.run_get, pure_bind, habw, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · have hinjFull : (mo.cfg : Config M).injectFull = fun t => t == mo.tStar := by
        simp [Mode.cfg, hmo, Config.auth]
      simp only [stepLFixedDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
        StateT.run_get, pure_bind, hab, hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      · split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        · simp only [run_liftH, StateT.run_bind, simulateQ_bind, pure_bind,
            bind_assoc, MonadAttach.mem_support_bind] at hr
          obtain ⟨out, hout, hr⟩ := hr
          cases hout1 : out.1 with
          | none =>
            rw [hout1] at hr
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka mo j rfl
          | some o1 =>
            cases o1 with
            | none =>
              rw [hout1] at hr
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr
              subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
            | some val =>
              rcases val with ⟨vp', t', i', m'⟩
              rw [hout1] at hr
              simp only  at hr
              obtain ⟨hid', hR', hlast⟩ :=
                vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                  c' none esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
              split at hr
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr
                subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
              · split at hr
                · simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind, StateT.run_pure,
                    pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr
                  subst hr
                  refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
                  · by_cases hQP : Q = P
                    · subst hQP; simp [Function.update_self, hid']
                    · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
                  · unfold RWrongSession at hR ⊢
                    by_cases hRP : Party.receiverOf mo.tStar = P
                    · simp only [hRP, Function.update_self]
                      exact hR' hRP.symm
                    · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]
                      exact hR
                · simp only [hinjFull] at hr
                  by_cases ht_eq : (t' == mo.tStar) = true
                  · simp only [ht_eq, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr
                    exact LHSDead.of_win_ne Δcka mo j rfl (hlast (beq_iff_eq.mp ht_eq))
                  · simp only [ht_eq, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩

theorem evalDist_runLocAtFixedDF_eq_zero_of_dead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    𝒟[runLocAtFixedDF cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtFixedDF_pure]
    rcases hdead with ⟨_, hout⟩ | ⟨_, hwin, _, _⟩
    · simp [hout]
    · simp [authOut, hwin]
  | query_bind q k ih =>
    rw [runLocAtFixedDF_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1 r.2
        (stepLFixedDF_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs q esL hdead r hr)

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runLocAtFixedDF_eq_zero_of_not_validGuess (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = false)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    𝒟[runLocAtFixedDF cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  unfold runLocAtFixedDF
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  have h : authOut (2 + Δcka) mo.policy r.2 = false := by
    simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
  simp [h]

@[expose] def injectTailDF {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c : Header T × E) (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    match ← liftH (vRecvTail hk s P s₁ c none) with
    | none =>
      abortE
      return none
    | some none => return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' then return some RecvResult.rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial (2 + Δcka) pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₂ =>
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := s₂ }
          return some (RecvResult.accepted t' i' (some m'))
      else
        if (mo.cfg (M := M)).injectFull t' then
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := { es.g with win := true } }
        return some RecvResult.rejected).run es

@[expose] def deliverForgeTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c' : Header T × E) (r : Record M (Header T × E))
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    match ← liftH (vRecvTail hk s P s₁ c' none) with
    | none =>
      abortE
      return none
    | some none => return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' || t' != r.pos.epoch then return some RecvResult.rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial (2 + Δcka) pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₂ =>
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := s₂ }
          return some (RecvResult.accepted t' i' (some m'))
      else
        if (mo.cfg (M := M)).injectFull t' then
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := { es.g with win := true } }
        return some RecvResult.rejected).run es

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins] in
theorem deliverForgeTail_eq_injectTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c' : Header T × E) (r : Record M (Header T × E))
    (hr_ep : r.pos.epoch = c'.1.1)
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    deliverForgeTail Δcka qep mo hk P c' r s₁ es =
      injectTailDF Δcka qep mo hk P c' s₁ es := by
  dsimp only [deliverForgeTail, injectTailDF, vRecvTail]
  cases s₁.vR c'.1.1 with
  | none => rfl
  | some v =>
    simp only [StateT.run_bind, run_liftH, bind_assoc]
    congr 1
    funext x
    rcases x with ⟨res, h'⟩
    cases res with
    | none => rfl
    | some res' =>
      cases res' with
      | none => rfl
      | some val =>
        rcases val with ⟨v', i, m⟩
        have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [hr_ep]
        by_cases hqep : qep + 1 < c'.1.1 <;>
          simp only [StateT.run_pure, pure_bind, hne_ep, Bool.or_false, hqep, decide_true,
            decide_false, Bool.false_eq_true, ↓reduceIte]

omit [SampleableType KR] [SampleableType KC] in
theorem leComp_deliverForgeTail (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (P : Party) (c' : Header T × E)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hin : esL.g.inTransit P.other c' = none)
    (hsends_f : P.sendsIn c'.1.1 = false)
    (ht_le : c'.1.1 ≤ (esL.g.st P).tcur + 1)
    (s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (s₁F : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : s₁L.id = P) (hidF' : s₁F.id = P)
    (hγ' : s₁L.γ = s₁F.γ) (hroot' : s₁L.root = s₁F.root)
    (hTcurL' : s₁L.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : s₁F.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : s₁L.tcur = max (esL.g.st P).tcur c'.1.1)
    (htcurF' : s₁F.tcur = max (esF.g.st P).tcur c'.1.1)
    (hvSL' : s₁L.vS = (esL.g.st P).vS) (hvSF' : s₁F.vS = (esF.g.st P).vS)
    (hvR_other' : ∀ t', t' ≠ c'.1.1 →
      s₁L.vR t' = (esL.g.st P).vR t' ∧ s₁F.vR t' = (esF.g.st P).vR t')
    (hvR_c :
      (s₁L.vR c'.1.1 = none ∧ s₁F.vR c'.1.1 = none) ∨
      (∃ rs idx?, s₁L.vR c'.1.1 = some (rs, idx?) ∧
        s₁F.vR c'.1.1 = some (some rs) ∧ idx? ≠ some j) ∨
      (c'.1.1 = mo.tStar ∧
        s₁L.vR c'.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c'.1.1 = some none)) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        (injectTailDF Δcka qep mo (hooksLocalFixed cka prng fs mo j k_fs) P c' s₁L esL))
      ((simulateQ (implFS fs)
        (injectTailDF Δcka qep mo (hooksFS cka prng fs Δcka mo j) P c' s₁F esF)).run st) :=
  leComp_injectTail cka prng fs Δcka qep mo j k_fs hauth P c' hs hin hsends_f ht_le
    s₁L s₁F hidL' hidF' hγ' hroot' hTcurL' hTcurF' htcurL' htcurF' hvSL' hvSF' hvR_other' hvR_c

set_option maxHeartbeats 400000 in
theorem leComp_deliverForgeE (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (q : Party × (Header T × E) × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((deliverForgeE (hooksLocalFixed cka prng fs mo j k_fs) (2 + Δcka) qep mo.cfg q).run esL))
      ((simulateQ (implFS fs)
        ((deliverForgeE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q).run
          esF)).run st) := by
  rcases q with ⟨P, c, c'⟩
  unfold deliverForgeE
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte]
  have hin_c_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  have hin_c'_eq : esF.g.inTransit P.other c' = esL.g.inTransit P.other c' := by
    simp only [GameState.inTransit, hs.htrans]
  rw [hin_c_eq]
  cases hin_c : esL.g.inTransit P.other c with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | some r =>
    dsimp only
    rw [hin_c'_eq, ← hs.hcomp]
    by_cases hguard :
        ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
      rcases hguard with ⟨⟨htrans0, _⟩, hhdr⟩
      have hin : esL.g.inTransit P.other c' = none := by
        cases h : esL.g.inTransit P.other c' with
        | none => rfl
        | some _ => simp [h] at htrans0
      obtain ⟨hmem, hct, hpos_eq, _, _, _⟩ :=
        inTransit_some_props fs Δcka qep mo hs P c r hin_c
      have hr_ep : r.pos.epoch = c'.1.1 := by
        have h1 : r.pos.epoch = c.1.1 := by rw [hpos_eq]
        rw [h1, hhdr]
      have hcond_eq :
          ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) =
            ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) := by
        rw [hs.hidF P, hs.hidL P, ← hs.htcur P]
      by_cases hcondL :
          ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) = true
      · have hcondF :
            ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) = true :=
          hcond_eq.trans hcondL
        dsimp only [vRecv]
        simp only [hcondL, hcondF, ↓reduceIte, StateT.run_bind, run_liftH, StateT.run_pure,
          pure_bind, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
      · have hcondL_f :
            ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) = false :=
          Bool.eq_false_iff.mpr hcondL
        have hcondF_f :
            ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) = false :=
          hcond_eq.trans hcondL_f
        have hsends_f : P.sendsIn c'.1.1 = false := by
          have h := hcondL_f
          rw [hs.hidL P, Bool.or_eq_false_iff] at h
          exact h.1
        have ht_le : c'.1.1 ≤ (esL.g.st P).tcur + 1 := by
          have h := hcondL_f
          rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
          omega
        have hPother_s : P.other = Party.senderOf c'.1.1 := by
          have hother_sends : P.other.sendsIn c'.1.1 = true := by
            revert hsends_f
            cases P <;> cases h : Nat.beq (c'.1.1 % 2) 1 <;> simp [Party.other, Party.sendsIn]
          exact eq_senderOf_of_sendsIn hother_sends
        have hP_recv : P = Party.receiverOf c'.1.1 := by
          unfold Party.receiverOf
          rw [← hPother_s]
          cases P <;> rfl
        by_cases heq : c'.1.1 = (esL.g.st P).tcur + 1
        · have heqF : c'.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          cases hTn : c'.1.2 with
          | none =>
            have hvL : vRecv (hooksLocalFixed cka prng fs mo j k_fs) esL.g P (esL.g.st P) c' none =
                pure (some none) := by
              simp [vRecv, heq, hTn]
            have hvF : vRecv (hooksFS cka prng fs Δcka mo j) esF.g P (esF.g.st P) c' none =
                pure (some none) := by
              simp [vRecv, heqF, hTn]
            simp only [hvL, hvF, run_liftH, StateT.run_bind, StateT.run_pure, pure_bind,
              simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
          | some Tc =>
            have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
              esL.g P (esL.g.st P) c' none Tc hcondL_f heq hTn
            have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
              esF.g P (esF.g.st P) c' none Tc hcondF_f heqF hTn
            simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind]
            rw [← hs.hγ P, ← hs.hroot P]
            refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c'.1.1
              (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
            intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
            rw [hr_st]
            rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
              ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
            · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE,
                simulateQ_pure]
              exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j _))
            · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
                syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
                  (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
            · simp only [hL_some, hF_some]
              have hs₁ : SyncLFS fs Δcka qep mo j k_fs
                  { esL with h := rL.2 } { esF with h := rF.1.2 } st := by
                refine syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs
                  hr_cL ?_ hr_ex hr_cnt hr_tr hr_sc
                intro h1 h2
                rcases h_origin with ⟨_, _, _, hsess⟩ | ⟨_, hnot, _, _⟩
                · exact hsess
                · exact absurd ⟨h1, h2⟩ hnot
              let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
                { esL.g.st P with
                  tcur := c'.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                  vR := Function.update (esL.g.st P).vR c'.1.1 (some (fs.initReceiver kL, idx?)) }
              let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
                { esF.g.st P with
                  tcur := c'.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                  vR := Function.update (esF.g.st P).vR c'.1.1
                    (some (if ext then none else some (fs.initReceiver kF))) }
              have hvR_c :
                  (s₁L.vR c'.1.1 = none ∧ s₁F.vR c'.1.1 = none) ∨
                  (∃ rs idx₀, s₁L.vR c'.1.1 = some (rs, idx₀) ∧
                    s₁F.vR c'.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
                  (c'.1.1 = mo.tStar ∧
                    s₁L.vR c'.1.1 = some (st.receiverState, some j) ∧
                    s₁F.vR c'.1.1 = some none) := by
                by_cases hj : idx? = some j
                · obtain ⟨hkL, ht_star⟩ := h_eq_j hj
                  right; right
                  have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                    rw [← ht_star, ← hP_recv]; omega
                  have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                    (hs.hvR_target_lt hlt_tstar).2.2
                  have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
                  refine ⟨ht_star, ?_, ?_⟩
                  · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
                · right; left
                  have hkL : kL = kF := h_ne_j hj
                  have hext_false : ext = false := by
                    rw [hext_eq, beq_eq_false_iff_ne]; exact hj
                  refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
                  · dsimp only [s₁L]; rw [Function.update_self]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
              have htailL := deliverForgeTail_eq_injectTail Δcka qep mo
                (hooksLocalFixed cka prng fs mo j k_fs) P c' r hr_ep s₁L { esL with h := rL.2 }
              have htailF := deliverForgeTail_eq_injectTail Δcka qep mo
                (hooksFS cka prng fs Δcka mo j) P c' r hr_ep s₁F { esF with h := rF.1.2 }
              convert leComp_deliverForgeTail cka prng fs Δcka qep mo j k_fs hauth P c' hs₁ hin
                hsends_f ht_le s₁L s₁F (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
                (by dsimp only [s₁L]; omega)
                (by dsimp only [s₁F]; have := hs.htcur P; omega)
                rfl rfl
                (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                                by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
                hvR_c using 1
              · rw [← htailL]
                dsimp only [deliverForgeTail, s₁L]
                simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                  simulateQ_pure]
                congr 1
              · rw [← htailF]
                dsimp only [deliverForgeTail, s₁F]
                simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]
                congr 1
        · have heqF : c'.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          have ht_le_cur : c'.1.1 ≤ (esL.g.st P).tcur := by omega
          have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
            esL.g P (esL.g.st P) c' none hcondL_f heq
          have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
            esF.g P (esF.g.st P) c' none hcondF_f heqF
          have hvR_c :
              ((esL.g.st P).vR c'.1.1 = none ∧ (esF.g.st P).vR c'.1.1 = none) ∨
              (∃ rs idx₀, (esL.g.st P).vR c'.1.1 = some (rs, idx₀) ∧
                (esF.g.st P).vR c'.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c'.1.1 = mo.tStar ∧
                (esL.g.st P).vR c'.1.1 = some (st.receiverState, some j) ∧
                (esF.g.st P).vR c'.1.1 = some none) := by
            by_cases ht_star : c'.1.1 = mo.tStar
            · right; right
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
                rw [← hP_tstar, ← ht_star]; exact ht_le_cur
              obtain ⟨_, h1, h2⟩ := hs.hvR_target_ge hge
              exact ⟨ht_star, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
            · rcases hs.hvR_other P c'.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
          have htailL := deliverForgeTail_eq_injectTail Δcka qep mo
            (hooksLocalFixed cka prng fs mo j k_fs) P c' r hr_ep (esL.g.st P) esL
          have htailF := deliverForgeTail_eq_injectTail Δcka qep mo
            (hooksFS cka prng fs Δcka mo j) P c' r hr_ep (esF.g.st P) esF
          convert leComp_deliverForgeTail cka prng fs Δcka qep mo j k_fs hauth P c' hs hin
            hsends_f ht_le (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P)
            (hs.hroot P) rfl rfl (by omega) (by have := hs.htcur P; omega) rfl rfl
            (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
          · rw [← htailL]
            dsimp only [deliverForgeTail]
            simp only [hvRecvL, StateT.run_bind]
            congr 2
          · rw [← htailF]
            dsimp only [deliverForgeTail]
            simp only [hvRecvF, StateT.run_bind]
            congr 3

theorem leComp_stepLFixedDF_stepFDF (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (stepLFixedDF cka prng fs Δcka qep mo j k_fs q esL)
      (stepFDF cka prng fs Δcka qep mo j q esF st) := by
  rcases q with n | (oq | df)
  · exact leComp_stepLFixed_stepF cka prng fs Δcka qep mo j k_fs hauth hvg (.inl n) hs
  · exact leComp_stepLFixed_stepF cka prng fs Δcka qep mo j k_fs hauth hvg (.inr oq) hs
  · unfold stepLFixedDF stepFDF implEDF; dsimp only [QueryImpl.add_apply]
    exact leComp_deliverForgeE cka prng fs Δcka qep mo j k_fs hauth df hs

theorem runLocAtFixedDF_le_runFDF (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    𝒟[runLocAtFixedDF cka prng fs Δcka qep mo j k_fs oa esL] {true} ≤
      𝒟[runFDF cka prng fs Δcka qep mo j oa esF st] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL esF st with
  | pure b' =>
    have hwinL := hs.hwinL
    have hout : (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) = false := by
      simp [authOut, hwinL]
    simp only [runLocAtFixedDF, simulateQ_pure, StateT.run_pure, pure_bind, hout]
    have hzero : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
    rw [hzero]
    exact zero_le
  | query_bind q k ih =>
    rw [runLocAtFixedDF_query_bind, runFDF_query_bind]
    refine leComp_stepLFixedDF_stepFDF cka prng fs Δcka qep mo j k_fs hauth hvg q hs
      (fun rL => runLocAtFixedDF cka prng fs Δcka qep mo j k_fs (k rL.1) rL.2)
      (fun rF => runFDF cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2) ?_
    intro rL rF hrel
    rcases hrel with hdead | hwin | ⟨heq_ans, hs'⟩
    · rw [evalDist_runLocAtFixedDF_eq_zero_of_dead cka prng fs Δcka qep mo hauth j k_fs
        (k rL.1) rL.2 hdead]
      exact zero_le
    · rw [evalDist_runFDF_eq_one_of_win cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2 hwin]
      exact prob_le_one
    · rw [heq_ans]
      exact ih rF.1.1 hs'

@[expose] def runFSDF (j : ℕ) (b : Bool) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  engRunDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initFS cka prng fs lam mo j) {} b A

theorem localAuthAtFixedDF_le_runFSDF (j : ℕ) (k_fs : K) (b_fs : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtFixedDF cka prng fs lam Δcka qep j k_fs tL t A] {true} ≤
      𝒟[(simulateQ (implFS fs) (runFSDF cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A)).run
          (FSAEAD.initState fs k_fs b_fs) >>= fun z => pure z.2.win] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · unfold localAuthAtFixedDF runFSDF engRunDF
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine leComp_init cka prng fs lam Δcka qep ⟨true, tL, t⟩ j k_fs b_fs _ _ ?_
    intro rL rF ⟨vAL, vBL, vAF, vBF, hrL1, hrF1, hrel⟩
    rcases rL with ⟨vsL, hL⟩
    rcases rF with ⟨⟨vsF, hF⟩, stF⟩
    dsimp only at hrL1 hrF1 ⊢
    subst hrL1 hrF1
    dsimp only at hrel ⊢
    rcases hrel with hdead | hs
    · exact le_of_eq_of_le
        (evalDist_runLocAtFixedDF_eq_zero_of_dead cka prng fs Δcka qep ⟨true, tL, t⟩ rfl j k_fs
          A _ hdead)
        zero_le
    · refine le_trans
        (runLocAtFixedDF_le_runFDF cka prng fs Δcka qep ⟨true, tL, t⟩ j k_fs rfl hvg A hs) ?_
      refine le_of_eq (congrArg (fun p => 𝒟[p] {true}) ?_)
      simp only [runFDF, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero : 𝒟[localAuthAtFixedDF cka prng fs lam Δcka qep j k_fs tL t A] {true} = 0 := by
      unfold localAuthAtFixedDF
      refine evalDist_bind_eq_zero _ _ fun r hr => ?_
      rcases r with ⟨vs, h⟩
      cases vs with
      | none => simp
      | some vp =>
        rcases vp with ⟨vA, vB⟩
        exact evalDist_runLocAtFixedDF_eq_zero_of_not_validGuess cka prng fs Δcka qep ⟨true, tL, t⟩
          j k_fs hvg_f A _
    rw [hzero]
    exact zero_le

end CryptoGames.SM.Construction.AuthL11

namespace CryptoGames.SM.Construction.DeliverForge

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

theorem lemma9_df (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGuessedAdvantage (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDF cka prng fs lam Δcka qep tL t A)] {true} :=
  AuthL9DF.lemma9_df cka prng fs lam Δcka qep hc tL t A

theorem lemma10_df (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDF cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuthDF cka prng fs lam Δcka qep tL t A)] {true} :=
  AuthL10DF.lemma10_df cka prng fs lam Δcka qep hc tL t A

end CryptoGames.SM.Construction.DeliverForge

