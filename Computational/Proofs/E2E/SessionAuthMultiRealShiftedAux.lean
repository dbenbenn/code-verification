/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthRouter -- proof-setup: allow-public-import

import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
/-!
# Session-Index `0` Invariants for `B1` (`ShiftedDir2Paper`)

Proves that when `mo.auth = false` and `2 ≤ t`, both the post-PRNG local game
`localAuthDFShiftedDir2Paper` and the Stage-2 multi-session reduction
`redFSAuthDFShiftedDir2PaperMulti` register at most one FS-AEAD session (index `0`, created
at most once when `Party.senderOf t` enters epoch `t`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiRealShiftedAux

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (GameState Pos Record RecvResult healedBy)
open _root_.CryptoGames.SM.Engine (EState Hooks VP abortE challE commitE deliverE
  deliverForgeEGen injectEGen liftH transmitE vRecv vSend)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiSpec FSMultiState Header Mode
  PartyState hooksFSMulti initFSMultiRaw liftFSMulti lookupMultiF mkParties regSessMulti
  regSessOptMulti rootFSMulti sampleT)
open _root_.CryptoGames.SM.Construction.AuthL11 (EStateL LState SMCompDF SMSpecDF hooksLocal
  initLocal lImpl mem_support_regSessOf mem_support_rootL run_liftH
  simulateQ_lImpl_run_lift_sampleT)
open _root_.CryptoGames.SM.Construction.DeliverForge (MakesAtMostQueriesDF
  SchemeAdversaryDF afterCorrShifted corrEShiftedPaper deliverForgeEB1
  implEDFShiftedB1 implEDFShiftedPaperGen injectEB1 localAuthAtDFShiftedDir2Paper
  localAuthDFShiftedDir2Paper localAuthDFShiftedDir2Paper_le_sum_localAuthAtDFShiftedDir2Paper
  moAuth runLocAtDFShiftedDir2Paper)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec sessOffRange)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedDir2PaperMulti redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper)

/-! ## 1. Local `H2` Session-Index `0` Invariant (`localAuthDFShiftedDir2Paper_le_at_zero`) -/

private theorem party_eq_senderOf_of_party_sendsIn (P : Party) (ep : ℕ)
    (hs : P.sendsIn ep = true) :
    P = Party.senderOf ep := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at hs ⊢ <;> omega

private theorem epMgmt_st_eq {St Msg C : Type} {g s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool} (hep : g.epMgmt Δ qep P bad = some s₁) : s₁.st = g.st := by
  unfold GameState.epMgmt at hep
  split at hep
  · split at hep
    · cases hep
    · injection hep with hep; subst hep; cases bad && !g.safeCh Δ P <;> simp [GameState.leak]
  · split at hep
    · cases hep
    · injection hep with hep; subst hep; rfl
private structure Dir2SessZeroL {Γ T Sig SS RS M E K I : Type} (t : ℕ)
    (esL : EStateL Γ T Sig SS RS M E K I) : Prop where
  id_eq : ∀ P, (esL.g.st P).id = P
  sess_le : esL.h.sessions.length ≤
    if t ≤ (esL.g.st (Party.senderOf t)).tcur ∨ esL.abort = true then 1 else 0
  cache_zero : ∀ t' Tc σc kc idx, esL.h.cache t' = some (Tc, σc, kc, some idx) → idx = 0
  vR_zero : ∀ P t' rs idx, (esL.g.st P).vR t' = some (rs, some idx) → idx = 0
  last_zero : ∀ idx, esL.h.lastIdx = some idx → idx = 0
private theorem dir2SessZeroL_init {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) {l t : ℕ} (ht2 : 2 ≤ t)
    {vA vB : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {h : LState T Sig K I}
    (hx : (some (vA, vB), h) ∈ support (simulateQ lImpl ((initLocal cka prng fs lam ⟨false, some (l - 1), t⟩).run {}))) :
    Dir2SessZeroL (M := M) (E := Header T × E) t
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } := by
  have ht0 : (⟨false, some (l - 1), t⟩ : Mode).tStar ≠ 0 := by dsimp; omega
  simp only [initLocal, StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨⟨kr, s1⟩, ⟨_, _, hs1⟩, ⟨kc, s2⟩, ⟨_, _, hs2⟩,
    ⟨⟨σ, k, sid⟩, s3⟩, hroot, ⟨idx?, s4⟩, hreg, hpure⟩
  injection hs1 with _ hs1; subst hs1; injection hs2 with _ hs2; subst hs2; simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hpure
  injection hpure with hvAB hh; injection hvAB with hvAB; injection hvAB with hvA hvB; subst hvA hvB hh; obtain ⟨hl_r, hc_r, hlast_r, _, hsid_r2⟩ := mem_support_rootL prng ⟨false, some (l - 1), t⟩ hroot
  obtain ⟨hnone_reg, _⟩ := mem_support_regSessOf hreg; obtain ⟨hidx_none, hs4⟩ := hnone_reg (hsid_r2 ht0.symm)
  refine ⟨fun P => by cases P <;> rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hs4, hl_r]; exact Nat.zero_le _
  · intro t' Tc σc kc idx hc; rw [hs4, hc_r] at hc; cases hc
  · intro Q t' rs idx hv; subst hidx_none
    cases Q <;> simp at hv
  · intro idx hlast; rw [hs4, hlast_r] at hlast; cases hlast
private theorem mem_support_vRecv_sessZeroL {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) {l t : ℕ} (esL : EStateL Γ T Sig SS RS M E K I) (hZ : Dir2SessZeroL t esL)
    (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E))) {out : Option (Option (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × ℕ × ℕ × M))} {h' : LState T Sig K I}
    (hr : (out, h') ∈ support (simulateQ lImpl ((vRecv (hooksLocal cka prng fs ⟨false, some (l - 1), t⟩) esL.g P (esL.g.st P) c rec).run esL.h))) : h'.sessions = esL.h.sessions ∧ h'.cache = esL.h.cache ∧
    (∀ idx, h'.lastIdx = some idx → idx = 0) ∧ (∀ st' t' i' m', out = some (some (st', t', i', m')) → st'.id = (esL.g.st P).id ∧ (esL.g.st P).tcur ≤ st'.tcur ∧ ∀ ep rs idx, st'.vR ep = some (rs, some idx) → idx = 0) := by
  unfold vRecv at hr; dsimp only at hr
  split at hr
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
  · split at hr
    · rename_i _ hteq
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
      | some Tn =>
        simp only [hc2, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨⟨res_sr, s_sr⟩, hsr, h2⟩; have hsr_spec : s_sr = esL.h ∧ ∀ γ' σ' rs, res_sr = some (some (γ', σ', rs)) →
              ∀ idx, rs.2 = some idx → idx = 0 := by
          unfold hooksLocal at hsr; dsimp only at hsr; simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hsr
          cases hcache : esL.h.cache c.1.1 with
          | none =>
            simp only [hcache, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hsr; rcases hsr with ⟨rfl, rfl⟩
            exact ⟨rfl, fun _ _ _ h => by cases h⟩
          | some quad =>
            rcases quad with ⟨Tc, σc, kc, idx?⟩
            by_cases hT : Tc = Tn
            · simp only [hcache, hT, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hsr; rcases hsr with ⟨rfl, rfl⟩
              refine ⟨rfl, fun _ _ rs hout idx hrs => ?_⟩
              injection hout with hout; injection hout with hout; have hrs_eq := (Prod.mk.inj (Prod.mk.inj hout).2).2; rw [← hrs_eq] at hrs; dsimp only at hrs; rw [hrs] at hcache; exact hZ.cache_zero c.1.1 Tc σc kc idx hcache
            · simp only [hcache, hT, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hsr; rcases hsr with ⟨rfl, rfl⟩
              exact ⟨rfl, fun _ _ _ h => by cases h⟩
        rcases hsr_spec with ⟨rfl, hrs_zero⟩
        rcases res_sr with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2; rcases h2 with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
        · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2; rcases h2 with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
        · simp only [pure_bind, Function.update_self, hooksLocal] at h2
          cases hfs : fs.receive rs.1 c.1 c.2 with
          | none =>
            simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2; rcases h2 with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
          | some val =>
            rcases val with ⟨rs', i0, m0⟩; simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2; rcases h2 with ⟨rfl, rfl⟩
            refine ⟨rfl, rfl, fun idx hli => hrs_zero γ' σ' rs rfl idx hli,
              fun st' t' i' m' hout => ?_⟩
            injection hout with hout; injection hout with hout; rcases hout with ⟨rfl, rfl, rfl, rfl⟩
            refine ⟨rfl, by dsimp only; omega, fun ep rs0 idx hv => ?_⟩
            by_cases hep : ep = c.1.1
            · subst ep; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hv; exact hrs_zero γ' σ' rs rfl idx hv.2
            · simp only [Function.update_of_ne hep] at hv; exact hZ.vR_zero P ep rs0 idx hv
    · simp only [pure_bind] at hr
      cases hvR : (esL.g.st P).vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
      | some rsv =>
        simp only [hvR, hooksLocal] at hr
        cases hfs : fs.receive rsv.1 c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, hZ.last_zero, fun _ _ _ _ h => by cases h⟩
        | some val =>
          rcases val with ⟨rs', i0, m0⟩; simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨rfl, rfl⟩
          refine ⟨rfl, rfl, fun idx hli => ?_, fun st' t' i' m' hout => ?_⟩
          · dsimp only at hli; rcases rsv with ⟨rs0, idx0⟩; subst hli; exact hZ.vR_zero P c.1.1 rs0 idx hvR
          · injection hout with hout; injection hout with hout; rcases hout with ⟨rfl, rfl, rfl, rfl⟩
            refine ⟨rfl, le_rfl, fun ep rs0 idx hv => ?_⟩
            by_cases hep : ep = c.1.1
            · subst ep; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hv; rcases rsv with ⟨rs1, idx1⟩; dsimp only at hv; rw [hv.2] at hvR; exact hZ.vR_zero P c.1.1 rs1 idx hvR
            · simp only [Function.update_of_ne hep] at hv; exact hZ.vR_zero P ep rs0 idx hv
private theorem dir2SessZeroL_accept {Γ T Sig SS RS M E K I : Type} {t : ℕ}
    (esL : EStateL Γ T Sig SS RS M E K I) (hZ : Dir2SessZeroL t esL)
    (h' : LState T Sig K I)
    (hs1 : h'.sessions = esL.h.sessions) (hc1 : h'.cache = esL.h.cache)
    (hlast1 : ∀ idx, h'.lastIdx = some idx → idx = 0)
    (P : Party) (st' : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) (pos : Pos)
    (hid' : st'.id = (esL.g.st P).id) (htcur' : (esL.g.st P).tcur ≤ st'.tcur)
    (hvR' : ∀ ep rs idx, st'.vR ep = some (rs, some idx) → idx = 0)
    (bad : Bool) :
    let s₁ := esL.g.accept P st' pos
    let s₂ := { s₁ with st := Function.update s₁.st P st' }
    Dir2SessZeroL t { esL with g := if bad then { s₂ with win := true } else s₂, h := h' } := by
  have hst_eq : ∀ Q, ((if bad then
          { (esL.g.accept P st' pos) with
              st := Function.update (esL.g.accept P st' pos).st P st', win := true }
        else
          { (esL.g.accept P st' pos) with
              st := Function.update (esL.g.accept P st' pos).st P st' }).st Q) =
      Function.update esL.g.st P st' Q := by
    intro Q; cases bad <;> simp [GameState.accept, GameState.delete, Function.update_idem]
  refine ⟨fun Q => ?_, ?_, fun ep Tc σc kc idx hc => hZ.cache_zero ep Tc σc kc idx (hc1 ▸ hc),
    fun Q ep rs idx hv => ?_, hlast1⟩
  · rw [hst_eq Q]
    by_cases hQ : Q = P
    · subst hQ; simp [Function.update_self, hid', hZ.id_eq]
    · simp [Function.update_of_ne hQ, hZ.id_eq]
  · dsimp only; rw [hs1, hst_eq (Party.senderOf t)]; refine hZ.sess_le.trans ?_
    by_cases hPs : Party.senderOf t = P
    · rw [hPs] at *; rw [Function.update_self]; cases esL.abort
      · simp only [Bool.false_eq_true, or_false]; split <;> split <;> omega
      · simp
    · rw [Function.update_of_ne hPs]
  · dsimp only at hv; rw [hst_eq Q] at hv
    by_cases hQ : Q = P
    · subst hQ; simp only [Function.update_self] at hv; exact hvR' ep rs idx hv
    · simp only [Function.update_of_ne hQ] at hv; exact hZ.vR_zero Q ep rs idx hv
private theorem stepLDFShiftedDir2Paper_preserves_sessZeroL {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) {qep l t : ℕ}
    (x : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain) (esL : EStateL Γ T Sig SS RS M E K I) (hZ : Dir2SessZeroL t esL) {r : (SMSpecDF Γ T Sig SS RS M CCoins E).Range x × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (simulateQ lImpl ((implEDFShiftedB1 l (hooksLocal cka prng fs ⟨false, some (l - 1), t⟩) 2 qep fs.maxSkip t (moAuth ⟨false, some (l - 1), t⟩).cfg (moAuth ⟨false, some (l - 1), t⟩).policy x).run esL))) :
    Dir2SessZeroL t r.2 := by
  let mo : Mode := ⟨false, some (l - 1), t⟩
  have hZ_abort : ∀ (h' : LState T Sig K I), h'.sessions = esL.h.sessions → h'.cache = esL.h.cache → (∀ idx, h'.lastIdx = some idx → idx = 0) →
      Dir2SessZeroL t { esL with h := h', abort := true } := by
    intro h' hs1 hc1 hl1
    refine ⟨hZ.id_eq, ?_, fun ep Tc σc kc idx hc => hZ.cache_zero ep Tc σc kc idx (hc1 ▸ hc),
      hZ.vR_zero, hl1⟩
    dsimp only; rw [hs1]; simp only [or_true, ↓reduceIte]
    exact hZ.sess_le.trans (by split <;> omega)
  have hZ_win : ∀ (h' : LState T Sig K I) (w : Bool), h'.sessions = esL.h.sessions → h'.cache = esL.h.cache → (∀ idx, h'.lastIdx = some idx → idx = 0) →
      Dir2SessZeroL t { esL with g := if w then { esL.g with win := true } else esL.g, h := h' } := by
    intro h' w hs1 hc1 hl1
    cases w <;>
      exact ⟨hZ.id_eq, by dsimp only; rw [hs1]; exact hZ.sess_le,
        fun ep Tc σc kc idx hc => hZ.cache_zero ep Tc σc kc idx (hc1 ▸ hc), hZ.vR_zero, hl1⟩
  rcases x with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, _root_.CryptoGames.SM.Engine.coinsE] at hr; unfold StateT.lift at hr
    simp only [StateT.run, simulateQ_bind, MonadAttach.mem_support_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; rcases hr with ⟨_, _, rfl⟩; exact hZ
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, transmitE, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · rename_i hnot_ab; simp only [Bool.or_eq_true, not_or] at hnot_ab; have hab : esL.abort = false := Bool.eq_false_iff.mpr hnot_ab.1
      cases hep : esL.g.epMgmt 2 qep P rc.isSome with
      | none => simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
      | some s₁ =>
        have hst1 : s₁.st = esL.g.st := epMgmt_st_eq hep; simp only [hep] at hr
        split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ_abort esL.h rfl rfl hZ.last_zero
        · simp only [pure_bind, StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨⟨s1_opt, h4⟩, hstart, hfin⟩; unfold vSend hooksLocal at hstart; dsimp only at hstart
          by_cases hsend : ((s₁.st P).id.sendsIn ((s₁.st P).tcur + 1)) = true
          · have hsendP : P.sendsIn ((esL.g.st P).tcur + 1) = true := by
              simpa [hst1, hZ.id_eq P] using hsend
            have hP : P = Party.senderOf ((esL.g.st P).tcur + 1) := party_eq_senderOf_of_party_sendsIn P _ hsendP; rw [hst1] at hsend; simp only [hst1, hsend, ↓reduceIte] at hstart
            have hstart_c : ∃ (coins : CCoins) (σ1 : Sig) (k1 : K) (sid : Option I)
                (h2 : LState T Sig K I) (idx1 : Option ℕ) (h3 : LState T Sig K I),
                ((σ1, k1, sid), h2) ∈ support (simulateQ lImpl ((_root_.CryptoGames.SM.Construction.AuthL11.rootL prng mo ((esL.g.st P).tcur + 1) (cka.send (esL.g.st P).γ coins).2.2 (esL.g.st P).root).run esL.h)) ∧
                (idx1, h3) ∈ support (simulateQ lImpl ((_root_.CryptoGames.SM.Construction.AuthL11.regSessOf sid).run h2)) ∧
                s1_opt = some (
                  { id := (esL.g.st P).id, root := σ1, vS := some ((fs.send (fs.initSender k1) ((esL.g.st P).tcur + 1, some (cka.send (esL.g.st P).γ coins).2.1) m).1, idx1),
                    vR := (esL.g.st P).vR, γ := (cka.send (esL.g.st P).γ coins).1,
                    curCkaMsg := some (cka.send (esL.g.st P).γ coins).2.1,
                    tcur := (esL.g.st P).tcur + 1 },
                  ((esL.g.st P).tcur + 1, some (cka.send (esL.g.st P).γ coins).2.1),
                  (fs.send (fs.initSender k1) ((esL.g.st P).tcur + 1, some (cka.send (esL.g.st P).γ coins).2.1) m).2) ∧
                h4 = { h3 with cache := Function.update h3.cache ((esL.g.st P).tcur + 1)
                                  (some ((cka.send (esL.g.st P).γ coins).2.1, σ1, k1, idx1)) } := by
              cases rc with
              | none =>
                simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_lImpl_run_lift_sampleT, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hstart
                rcases hstart with ⟨coins, _, ⟨⟨σ1, k1, sid⟩, h2⟩, hroot,
                  ⟨idx1, h3⟩, hreg, rfl, rfl⟩
                exact ⟨coins, σ1, k1, sid, h2, idx1, h3, hroot, hreg, rfl, rfl⟩
              | some coins =>
                simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hstart
                rcases hstart with ⟨⟨⟨σ1, k1, sid⟩, h2⟩, hroot, ⟨idx1, h3⟩, hreg, rfl, rfl⟩; exact ⟨coins, σ1, k1, sid, h2, idx1, h3, hroot, hreg, rfl, rfl⟩
            rcases hstart_c with ⟨coins, σ1, k1, sid, h2, idx1, h3, hroot, hreg, rfl, rfl⟩; obtain ⟨hl_r, hc_r, hlast_r, _, hsid_ne⟩ := mem_support_rootL prng mo hroot; obtain ⟨hnone_reg, hsome_reg⟩ := mem_support_regSessOf hreg
            simp only [StateT.run_modify, StateT.run_pure, StateT.run_bind, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hfin; subst hfin
            rcases sid with _ | Ik
            · obtain ⟨hidx_n, hh3⟩ := hnone_reg rfl; subst hidx_n hh3
              refine ⟨fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, Function.update_self, hst1, hZ.id_eq]
                  · simp [GameState.record, Function.update_of_ne hQ, hst1, hZ.id_eq],
                ?_, ?_, ?_, fun i hi => hZ.last_zero i (by simpa [hlast_r] using hi)⟩
              · simp only [GameState.record, hl_r, hst1]; refine hZ.sess_le.trans ?_
                by_cases hPs : Party.senderOf t = P
                · rw [hPs, Function.update_self]; dsimp only; cases esL.abort
                  · simp only [Bool.false_eq_true, or_false]; split <;> split <;> omega
                  · simp
                · rw [Function.update_of_ne hPs]
              · intro ep Tc0 σc0 kc0 idx0 hc0
                by_cases hep0 : ep = (esL.g.st P).tcur + 1
                · subst hep0; simp at hc0
                · simp only [Function.update_of_ne hep0, hc_r] at hc0; exact hZ.cache_zero ep Tc0 σc0 kc0 idx0 hc0
              · intro Q ep rs0 idx0 hv0; simp only [GameState.record, hst1] at hv0
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self] at hv0; exact hZ.vR_zero P ep rs0 idx0 hv0
                · simp only [Function.update_of_ne hQ] at hv0; exact hZ.vR_zero Q ep rs0 idx0 hv0
            · have ht_eq : (esL.g.st P).tcur + 1 = t :=
                Decidable.byContradiction fun hne => by have := hsid_ne hne; simp at this
              have hP_s : P = Party.senderOf t := by rw [ht_eq] at hP; exact hP
              have hlen0 : esL.h.sessions.length = 0 := by
                have := hZ.sess_le
                have hlt : ¬ (t ≤ (esL.g.st (Party.senderOf t)).tcur) := by rw [← hP_s]; omega
                simp [hlt, hab] at this; simp [this]
              obtain ⟨⟨j0, hj0_lt, hidx_s⟩, _, hh3_le, hh3_cache, hh3_last⟩ := hsome_reg Ik rfl
              have hh3_1 : h3.sessions.length ≤ 1 := by rw [hl_r, hlen0] at hh3_le; omega
              have hj0 : j0 = 0 := by omega
              subst hj0 hidx_s
              refine ⟨fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, Function.update_self, hst1, hZ.id_eq]
                  · simp [GameState.record, Function.update_of_ne hQ, hst1, hZ.id_eq],
                ?_, ?_, ?_, fun i hi => hZ.last_zero i (by simpa [hh3_last, hlast_r] using hi)⟩
              · have htcur_new : t ≤ (esL.g.st P).tcur + 1 := by omega
                simp only [GameState.record, hst1, ← hP_s, Function.update_self, htcur_new, true_or, ↓reduceIte]; exact hh3_1
              · intro ep Tc0 σc0 kc0 idx0 hc0
                by_cases hep0 : ep = (esL.g.st P).tcur + 1
                · subst hep0; simp only [Function.update_self] at hc0; injection hc0 with hc0; exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hc0).2).2).2.symm |> Option.some.inj
                · simp only [Function.update_of_ne hep0, hh3_cache, hc_r] at hc0; exact hZ.cache_zero ep Tc0 σc0 kc0 idx0 hc0
              · intro Q ep rs0 idx0 hv0; simp only [GameState.record, hst1] at hv0
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self] at hv0; exact hZ.vR_zero P ep rs0 idx0 hv0
                · simp only [Function.update_of_ne hQ] at hv0; exact hZ.vR_zero Q ep rs0 idx0 hv0
          · rw [hst1] at hsend; simp only [hst1, hsend, pure_bind] at hstart
            cases hvs : (esL.g.st P).vS with
            | none =>
              simp only [hvs] at hstart; rcases hstart with ⟨rfl, rfl⟩; simp only [StateT.run_pure, StateT.run_bind, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hfin; subst hfin
              refine ⟨fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, hst1, hZ.id_eq]
                  · simp [GameState.record, hst1, hZ.id_eq],
                by simp only [GameState.record, hst1, Function.update_eq_self]; exact hZ.sess_le,
                hZ.cache_zero,
                fun Q ep rs0 idx0 hv0 => by
                  simp only [GameState.record, hst1, Function.update_eq_self] at hv0; exact hZ.vR_zero Q ep rs0 idx0 hv0,
                hZ.last_zero⟩
            | some ssv =>
              simp only [hvs] at hstart; rcases hstart with ⟨rfl, rfl⟩; simp only [StateT.run_pure, StateT.run_bind, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hfin; subst hfin
              refine ⟨fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, Function.update_self, hst1, hZ.id_eq]
                  · simp [GameState.record, Function.update_of_ne hQ, hst1, hZ.id_eq],
                by
                  simp only [GameState.record, hst1]
                  by_cases hPs : Party.senderOf t = P
                  · rw [hPs, Function.update_self]; simpa [← hPs] using hZ.sess_le
                  · simpa [Function.update_of_ne hPs] using hZ.sess_le,
                hZ.cache_zero,
                fun Q ep rs0 idx0 hv0 => by
                  simp only [GameState.record, hst1] at hv0
                  by_cases hQ : Q = P
                  · subst Q; simp only [Function.update_self] at hv0; exact hZ.vR_zero P ep rs0 idx0 hv0
                  · simp only [Function.update_of_ne hQ] at hv0; exact hZ.vR_zero Q ep rs0 idx0 hv0,
                hZ.last_zero⟩
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, challE, moAuth, Mode.cfg, _root_.CryptoGames.SM.Config.auth, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · cases hep : esL.g.epMgmt 2 qep P rc.isSome <;>
        (simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ)
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, deliverE, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · cases hit : esL.g.inTransit P.other c with
      | none => simp only [hit, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
      | some rec =>
        simp only [hit, StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨⟨out, h1⟩, hv, htail⟩
        obtain ⟨hs1, hc1, hl1, hout⟩ := mem_support_vRecv_sessZeroL cka prng fs esL hZ P c (some rec) hv
        rcases out with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_abort h1 hs1 hc1 hl1
        · dsimp only at htail; split at htail
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 true hs1 hc1 hl1
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
        · obtain ⟨hid', htcur', hvR'⟩ := hout st' t' i' m' rfl
          simp only [commitE, hooksLocal, run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail
          exact dir2SessZeroL_accept esL hZ h1 hs1 hc1 hl1 P st' rec.pos hid' htcur' hvR' _
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, injectEB1, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨⟨out, h1⟩, hv, htail⟩
      obtain ⟨hs1, hc1, hl1, hout⟩ := mem_support_vRecv_sessZeroL cka prng fs esL hZ P c none hv
      rcases out with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_abort h1 hs1 hc1 hl1
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
      · obtain ⟨hid', htcur', hvR'⟩ := hout st' t' i' m' rfl; simp only [] at htail
        split at htail
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
        · split at htail
          · simp only [commitE, hooksLocal, run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail
            exact dir2SessZeroL_accept esL hZ h1 hs1 hc1 hl1 P st' ⟨P.other, t', i'⟩ hid' htcur' hvR' false
          · split at htail
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 true hs1 hc1 hl1
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · split at hr
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ_abort esL.h rfl rfl hZ.last_zero
      · simp only [hooksLocal, run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr
        have hst_corr : (afterCorrShifted l esL.g P).st = esL.g.st := by
          unfold afterCorrShifted; split <;> rfl
        exact ⟨fun Q => by rw [hst_corr]; exact hZ.id_eq Q,
          by dsimp only; rw [hst_corr]; exact hZ.sess_le,
          hZ.cache_zero,
          fun Q ep rs idx hv => by dsimp only at hv; rw [hst_corr] at hv; exact hZ.vR_zero Q ep rs idx hv,
          hZ.last_zero⟩
  · simp only [implEDFShiftedB1, QueryImpl.add_apply, deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
    · cases hit : esL.g.inTransit P.other c with
      | none => simp only [hit, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
      | some rec =>
        simp only [hit] at hr
        split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨⟨out, h1⟩, hv, htail⟩
          obtain ⟨hs1, hc1, hl1, hout⟩ := mem_support_vRecv_sessZeroL cka prng fs esL hZ P c' none hv
          rcases out with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_abort h1 hs1 hc1 hl1
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
          · obtain ⟨hid', htcur', hvR'⟩ := hout st' t' i' m' rfl; simp only [] at htail
            split at htail
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
            · split at htail
              · simp only [commitE, hooksLocal, run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail
                exact dir2SessZeroL_accept esL hZ h1 hs1 hc1 hl1 P st' ⟨P.other, t', i'⟩ hid' htcur' hvR' false
              · split at htail
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 true hs1 hc1 hl1
                · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at htail; subst htail; exact hZ_win h1 false hs1 hc1 hl1
private theorem dir2SessZeroL_run {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) {qep l t : ℕ} {α : Type} (oa : SMCompDF Γ T Sig SS RS M CCoins E α)
    (esL : EStateL Γ T Sig SS RS M E K I) (hZ : Dir2SessZeroL t esL) {r : α × EStateL Γ T Sig SS RS M E K I} (hr : r ∈ support (simulateQ lImpl
    ((simulateQ (implEDFShiftedB1 l (hooksLocal cka prng fs ⟨false, some (l - 1), t⟩) 2 qep fs.maxSkip t (moAuth ⟨false, some (l - 1), t⟩).cfg (moAuth ⟨false, some (l - 1), t⟩).policy) oa).run esL))) : Dir2SessZeroL t r.2 := by
  induction oa using OracleComp.inductionOn generalizing esL r with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hZ
  | query_bind x k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hr; rcases hr with ⟨⟨u, esL'⟩, hu, hr⟩
    exact ih u esL' (stepLDFShiftedDir2Paper_preserves_sessZeroL cka prng fs x esL hZ hu) hr
private theorem evalDist_localAuthAtDFShiftedDir2Paper_eq_zero_of_ne_zero {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) {qep l t : ℕ} (ht2 : 2 ≤ t) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (i : ℕ) (hi : i ≠ 0) : 𝒟[localAuthAtDFShiftedDir2Paper cka prng fs lam 0 qep i l (some (l - 1)) t A] {true} = 0 := by
  unfold localAuthAtDFShiftedDir2Paper runLocAtDFShiftedDir2Paper
  refine _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun r hes0 => ?_
  rcases r with ⟨_ | ⟨vA, vB⟩, h⟩
  · simp
  · refine _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun r' hesf => ?_
    have hZ0 := dir2SessZeroL_init (M := M) (E := E) cka prng fs lam ht2 hes0; have hZf := dir2SessZeroL_run cka prng fs A _
      ⟨hZ0.1, hZ0.2, hZ0.3, hZ0.4, hZ0.5⟩ hesf
    cases hlast : r'.2.h.lastIdx with
    | none => simp
    | some idx => have h0 := hZf.last_zero idx hlast; subst h0; simp [hi.symm]

/-- In `B1` (`localAuthDFShiftedDir2Paper` with `2 ≤ t`), every winning forged delivery hits
session index `0`, so the union bound over `q` collapses to `j = 0`. -/
theorem localAuthDFShiftedDir2Paper_le_at_zero
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q qep l t : ℕ) (ht2 : 2 ≤ t)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[localAuthDFShiftedDir2Paper cka prng fs lam 0 qep l (some (l - 1)) t A] {true} ≤
      𝒟[localAuthAtDFShiftedDir2Paper cka prng fs lam 0 qep 0 l (some (l - 1)) t A] {true} := by
  refine (localAuthDFShiftedDir2Paper_le_sum_localAuthAtDFShiftedDir2Paper cka prng fs lam 0 qep
    l (some (l - 1)) t q A hq).trans ?_
  by_cases hq0 : q = 0
  · subst hq0; simp
  · rw [Finset.sum_eq_single 0]
    · intro j _ hj0
      exact evalDist_localAuthAtDFShiftedDir2Paper_eq_zero_of_ne_zero cka prng fs lam ht2 A j hj0
    · intro h0; exact False.elim (h0 (Finset.mem_range.mpr (Nat.pos_of_ne_zero hq0)))

/-! ## 2. Multi-Session `sessOffRange 1` Bound (`redFSAuthDFShiftedDir2PaperMulti_offRange_one`) -/

private inductive AllSessLt (M_sess : ℕ) {SS RS T M E : Type} :
    {α : Type} →
      OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α →
      Prop where
  | pure {α : Type} (a : α) : AllSessLt M_sess (pure a)
  | coin {α : Type} (n : ℕ)
      (k : Fin (n + 1) →
        OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) :
      (∀ u, AllSessLt M_sess (k u)) →
      AllSessLt M_sess
        (liftM (OracleSpec.query
          (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
          (.inl n)) >>= k)
  | sess {α : Type} (s : ℕ) (hs : s < M_sess)
      (q_fs : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
      (k : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Range q_fs →
        OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) :
      (∀ u, AllSessLt M_sess (k u)) →
      AllSessLt M_sess
        (liftM (OracleSpec.query
          (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
          (.inr ⟨s, q_fs⟩)) >>= k)

private theorem AllSessLt.bind_support {M_sess : ℕ} {SS RS T M E α β : Type} {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    {k : α → OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) β} (hoa : AllSessLt M_sess oa) (hk : ∀ a ∈ support oa, AllSessLt M_sess (k a)) : AllSessLt M_sess (oa >>= k) := by
  induction hoa with
  | pure a => rw [pure_bind]; exact hk a (by simp)
  | coin n r _ ih =>
    rw [bind_assoc]
    exact .coin n _ fun u => ih u fun a ha => hk a (by rw [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)
  | sess s hs q_fs r _ ih =>
    let r' : (unifSpec + multiSessSpec
        (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Range (.inr ⟨s, q_fs⟩) → _ := r
    have hk' : ∀ a ∈ support (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inr ⟨s, q_fs⟩)) >>= r'), AllSessLt M_sess (k a) := hk
    change AllSessLt M_sess ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inr ⟨s, q_fs⟩)) >>= r') >>= k)
    rw [bind_assoc]
    exact .sess s hs q_fs _ fun u => ih u fun a ha =>
      let u' : (unifSpec + multiSessSpec
        (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Range (.inr ⟨s, q_fs⟩) := u
      hk' a (by rw [mem_support_bind_iff]; exact ⟨u', mem_support_query _ u', ha⟩)
private theorem AllSessLt.map {M_sess : ℕ} {SS RS T M E α β : Type} (f : α → β) {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α} (hoa : AllSessLt M_sess oa) :
    AllSessLt M_sess (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact hoa.bind_support fun a _ => .pure (f a)
set_option synthInstance.maxHeartbeats 200000 in
private theorem AllSessLt.liftProbComp {M_sess : ℕ} {SS RS T M E α : Type} (c : ProbComp α) : AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess (liftM c :
    OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) := by
  induction c using OracleComp.inductionOn with
  | pure a => simpa using AllSessLt.pure a
  | query_bind n r ih =>
    change AllSessLt M_sess (simulateQ _ (liftM (query n) >>= r))
    simp only [simulateQ_bind, simulateQ_query]; exact .coin n _ fun u => ih u
private theorem AllSessLt.to_isQueryBoundP {M_sess : ℕ} {SS RS T M E α : Type} {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α} (hoa : AllSessLt M_sess oa) :
    oa.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0 := by
  induction hoa with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | coin n k _ ih =>
    have hnp : ¬ (sessOffRange M_sess ((.inl n : (unifSpec + multiSessSpec
        (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain)) = true) := by simp [sessOffRange]
    rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl hnp, fun u => by simpa [hnp] using ih u⟩
  | sess s hs q_fs k _ ih =>
    let k' : (unifSpec + multiSessSpec
        (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Range (.inr ⟨s, q_fs⟩) → _ := k
    change (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
        (.inr ⟨s, q_fs⟩)) >>= k').IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0
    have hnp : ¬ (sessOffRange M_sess (.inr ⟨s, q_fs⟩) = true) := by simp [sessOffRange, Nat.not_le.mpr hs]
    rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl hnp, fun u => by simpa [hnp] using ih u⟩
private theorem liftFSMulti_allSessLt {T RSt K I SS RS M E α : Type} {M_sess sIdx : ℕ} (hs : sIdx < M_sess) (h : FSMultiState T RSt K I E) (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    AllSessLt M_sess ((liftFSMulti (T := T) sIdx x).run h) := by
  unfold liftFSMulti StateT.lift
  refine AllSessLt.bind_support ?_ fun a _ => .pure (a, h)
  induction x using OracleComp.inductionOn with
  | pure a => simpa using AllSessLt.pure a
  | query_bind t r ih =>
    rw [simulateQ_query_bind]; rcases t with n | qfs
    · exact .coin n _ fun u => ih u
    · exact .sess sIdx hs qfs _ fun u => ih u
private def AllSpec (M_sess : ℕ) {SS RS T M E α : Type} (Post : α → Prop) (oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) : Prop :=
  AllSessLt M_sess oa ∧ ∀ z ∈ support oa, Post z
private theorem AllSpec.pure {M_sess : ℕ} {SS RS T M E α : Type} {Post : α → Prop} {a : α} (ha : Post a) : AllSpec (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess Post (Pure.pure a) :=
  ⟨.pure a, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; exact hz ▸ ha⟩
private theorem AllSpec.bind {M_sess : ℕ} {SS RS T M E α β : Type} {Mid : α → Prop} {Post : β → Prop} {mx : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    {f : α → OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) β} (h : AllSpec M_sess Mid mx) (hf : ∀ a, Mid a → AllSpec M_sess Post (f a)) : AllSpec M_sess Post (mx >>= f) :=
  ⟨h.1.bind_support fun a ha => (hf a (h.2 a ha)).1, fun z hz => by
    rw [mem_support_bind_iff] at hz; obtain ⟨a, ha, hz⟩ := hz; exact (hf a (h.2 a ha)).2 z hz⟩
private theorem AllSpec.map {M_sess : ℕ} {SS RS T M E α β : Type} {Mid : α → Prop} {Post : β → Prop} {mx : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    {g : α → β} (h : AllSpec M_sess Mid mx) (hg : ∀ a, Mid a → Post (g a)) : AllSpec M_sess Post (g <$> mx) := by
  rw [map_eq_bind_pure_comp]; exact h.bind fun a ha => .pure (hg a ha)
private theorem sampleT_allSpec {M_sess : ℕ} {SS RS T M E : Type} (α : Type) [SampleableType α] : AllSpec (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess (fun _ => True) (sampleT α) :=
  ⟨AllSessLt.liftProbComp ($ᵗ α : ProbComp α), fun _ _ => trivial⟩
private theorem lift_sampleT_allSpec {M_sess : ℕ} {SS RS T M E HS : Type} (α : Type) [SampleableType α] (h : HS) : AllSpec (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
    (fun z => z.2 = h) ((StateT.lift (sampleT α)).run h) := by
  rw [StateT.run_lift]; exact (sampleT_allSpec α).bind fun _ _ => .pure rfl
private theorem liftFSMulti_allSpec {T RSt K I SS RS M E α : Type} {M_sess sIdx : ℕ} (hs : sIdx < M_sess) (h : FSMultiState T RSt K I E) (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    AllSpec M_sess (fun z => z.2 = h) ((liftFSMulti (T := T) sIdx x).run h) := by
  refine ⟨liftFSMulti_allSessLt hs h x, ?_⟩
  unfold liftFSMulti; rw [StateT.run_lift]; intro z hz; rw [mem_support_bind_iff] at hz; obtain ⟨_, _, hz⟩ := hz; simp only [support_pure, Set.mem_singleton_iff] at hz; exact congrArg Prod.snd hz
private theorem lookupMultiF_allSessLt {T RSt K I SS RS M E : Type} [DecidableEq I] [SampleableType K] {M_sess : ℕ} (Ik : I) (h : FSMultiState T RSt K I E) : AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
    ((lookupMultiF Ik).run h) ∧ ∀ z ∈ support ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h), z.2.sessions = h.sessions ∧ z.2.cache = h.cache := by
  change AllSpec M_sess (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache) ((lookupMultiF Ik).run h)
  unfold lookupMultiF; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some _ => simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_allSpec K h).bind fun ⟨_, h1⟩ hh1 => by
      rw [hh1]; simp only [StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure ⟨rfl, rfl⟩
private theorem regSessMulti_spec {T RSt K I SS RS M E : Type} [DecidableEq I] {M_sess : ℕ} (Ik : I) (h : FSMultiState T RSt K I E) : AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess ((regSessMulti Ik).run h) ∧
    ∀ z ∈ support ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h), z.1 < z.2.sessions.length ∧ z.2.sessions.length ≤ h.sessions.length + 1 ∧ z.2.cache = h.cache := by
  change AllSpec M_sess
    (fun z => z.1 < z.2.sessions.length ∧ z.2.sessions.length ≤ h.sessions.length + 1 ∧ z.2.cache = h.cache)
    ((regSessMulti Ik).run h)
  unfold regSessMulti; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hmem
  · simp only [StateT.run_pure]; exact AllSpec.pure ⟨List.idxOf_lt_length_of_mem hmem, Nat.le_succ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    exact AllSpec.pure ⟨by simp, by simp, rfl⟩
private theorem regSessOptMulti_spec {T RSt K I SS RS M E : Type} [DecidableEq I] {M_sess : ℕ} (sid : Option I) (h : FSMultiState T RSt K I E) : AllSpec (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
    (fun z => (∀ sIdx, z.1 = some sIdx → ∃ I0, sid = some I0 ∧ sIdx < z.2.sessions.length) ∧ (sid = none → z.1 = none ∧ z.2.sessions = h.sessions) ∧ z.2.sessions.length ≤ h.sessions.length + 1 ∧ z.2.cache = h.cache)
    ((regSessOptMulti sid).run h) := by
  cases sid with
  | none =>
    simp only [regSessOptMulti, StateT.run_pure]
    exact AllSpec.pure ⟨(fun _ hs => by cases hs), fun _ => ⟨rfl, rfl⟩, Nat.le_succ _, rfl⟩
  | some Ik =>
    simp only [regSessOptMulti, StateT.run_map]
    exact AllSpec.map (regSessMulti_spec Ik h) fun z ⟨hlt, hle, hca⟩ =>
      ⟨(fun sIdx hs => by injection hs with hs'; subst hs'; exact ⟨Ik, rfl, hlt⟩),
       (fun hno => by cases hno), hle, hca⟩
private structure Dir2SessZeroM {Γ T RSt SS RS K I M E : Type} (t : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) : Prop where
  id_eq : ∀ P, (es.g.st P).id = P
  sess_le : es.h.sessions.length ≤
    if t ≤ (es.g.st (Party.senderOf t)).tcur ∨ es.abort = true then 1 else 0
  vS_zero : ∀ P sIdx, (es.g.st P).vS = some (.inr sIdx) → sIdx = 0
  vR_zero : ∀ P ep sIdx, (es.g.st P).vR ep = some (.inr sIdx) → sIdx = 0
  cache_zero : ∀ ep Tc σc kc sIdx, es.h.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0
private theorem rootFSMulti_dir2_spec {KR RSt I K T SS RS M E : Type} [DecidableEq I] [SampleableType I] [SampleableType K] (prng : PRFPRNG KR RSt I K) (l t ep : ℕ) (Ik : I) (σ : RSt) (h : FSMultiState T RSt K I E) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) 1 ((rootFSMulti prng ⟨false, some (l - 1), t⟩ ep Ik σ).run h) ∧ ∀ z ∈ support ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng ⟨false, some (l - 1), t⟩ ep Ik σ).run h), z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧ (∀ I0, z.1.2.2 = some I0 → ep = t) ∧ (ep ≠ t → z.1.2.2 = none) := by
  change AllSpec 1 (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
    (∀ I0, z.1.2.2 = some I0 → ep = t) ∧ (ep ≠ t → z.1.2.2 = none))
    ((rootFSMulti prng ⟨false, some (l - 1), t⟩ ep Ik σ).run h)
  unfold rootFSMulti; split_ifs with hlt heq hheal hheal2
  · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, (fun _ hs => by cases hs), fun _ => rfl⟩
  · simp only [StateT.run_bind]
    refine (lift_sampleT_allSpec I h).bind fun ⟨_, h1⟩ hh1 => ?_
    rw [hh1]; refine (lift_sampleT_allSpec K h).bind fun ⟨_, h2⟩ hh2 => ?_
    rw [hh2]; simp only [StateT.run_pure]
    exact AllSpec.pure ⟨rfl, rfl, fun _ _ => heq, fun hne => False.elim (hne heq)⟩
  · simp only [StateT.run_bind]
    exact AllSpec.bind (lookupMultiF_allSessLt Ik h) fun ⟨_, h1⟩ ⟨hse, hca⟩ => by
      simp only [StateT.run_pure]; exact AllSpec.pure ⟨hse, hca, fun _ _ => heq, fun hne => False.elim (hne heq)⟩
  · simp only [StateT.run_bind]
    exact (lift_sampleT_allSpec I h).bind fun ⟨_, h1⟩ hh1 => by
      rw [hh1]; simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, (fun _ hs => by cases hs), fun _ => rfl⟩
  · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, (fun _ hs => by cases hs), fun _ => rfl⟩
private theorem fsRecv_hooksFSMulti_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) {l t : ℕ} (la : Bool) (g : GameState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E))
    (P : Party) (ep : ℕ) (rsv : RS ⊕ ℕ) (hrsv : ∀ sIdx, rsv = .inr sIdx → sIdx = 0) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E))) (h : FSMultiState T RSt K I E) :
    AllSessLt 1 (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).fsRecv g P ep rsv hdr e rec).run h) ∧ ∀ z ∈ support (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).fsRecv
    g P ep rsv hdr e rec).run h), z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧ ∀ rsv' i' m', z.1 = some (some (rsv', i', m')) → ∀ sIdx, rsv' = .inr sIdx → sIdx = 0 := by
  change AllSpec 1 (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
      ∀ rsv' i' m', z.1 = some (some (rsv', i', m')) → ∀ sIdx, rsv' = .inr sIdx → sIdx = 0)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).fsRecv g P ep rsv hdr e rec).run h)
  dsimp only [hooksFSMulti]; cases rsv with
  | inl rs =>
    simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
      cases hfr : fs.receive rs hdr e with
      | none => simp [hfr] at hs
      | some o =>
        simp only [hfr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, _, _⟩; simp at hv⟩
  | inr sIdx =>
    have hs0 : sIdx = 0 := hrsv sIdx rfl; subst hs0; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hc : ((((h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isNone &&
        !(healedBy g.tL (2 + 0) ep) && !((h.book 0).getD {}).sCorr) = true
    · simp only [hc, ↓reduceIte]; by_cases hla : la = true
      · simp only [hla, Bool.not_false, ↓reduceIte, StateT.run_pure]
        exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_allSpec Nat.zero_lt_one h _).bind fun ⟨cRes, h0⟩ hh0 => ?_
        rw [hh0]; cases cRes with
        | none =>
          simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
          exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        | some _ =>
          simp only [StateT.run_bind, StateT.run_modify, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
          (by_cases hm : (((h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isSome = true <;>
            simp only [hm, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]) <;>
          (refine (liftFSMulti_allSpec Nat.zero_lt_one _ _).bind fun ⟨res, h2⟩ hh2 => ?_
           rw [hh2]; rcases res with _ | (_ | ⟨i, mo'⟩)
           · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
           · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
           · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
             · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
               exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
             · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases mo' with _ | m
               · rcases rec with _ | rec0 <;> simp only [StateT.run_pure]
                 · exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
                 · exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ _ ⟨rfl, _, _⟩ _ ⟨⟩; rfl⟩
               · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ _ ⟨rfl, _, _⟩ _ ⟨⟩; rfl⟩)
    · simp only [hc, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
      (by_cases hm : (((h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isSome = true <;>
        simp only [hm, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]) <;>
      (refine (liftFSMulti_allSpec Nat.zero_lt_one _ _).bind fun ⟨res, h2⟩ hh2 => ?_
       rw [hh2]; rcases res with _ | (_ | ⟨i, mo'⟩)
       · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
       · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
       · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
         · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
           exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
         · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases mo' with _ | m
           · rcases rec with _ | rec0 <;> simp only [StateT.run_pure]
             · exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
             · exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ _ ⟨rfl, _, _⟩ _ ⟨⟩; rfl⟩
           · simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ _ ⟨rfl, _, _⟩ _ ⟨⟩; rfl⟩)
section Dir2StepHelpers
variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) {qep l t : ℕ} (la : Bool)
private theorem epMgmt_st_eqM {St Msg C : Type} (g s₁ : GameState St Msg C) (Δ qep' : ℕ) (P : Party) (bad : Bool) (h : g.epMgmt Δ qep' P bad = some s₁) : s₁.st = g.st := by
  unfold GameState.epMgmt GameState.leak at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> cases h <;> rfl
private theorem liftH_allSpec {HS Γv T' Sv SSv RSv M' E' α SS' RS' : Type} {Post : α × HS → Prop} {x : _root_.CryptoGames.SM.Engine.HM (FSMultiSpec SS' RS' T' M' E') HS α} {es : EState (VP Γv T' Sv SSv RSv) M' (Header T' × E') HS}
    (hx : AllSpec (SS := SS') (RS := RS') (T := T') (M := M') (E := E') 1 Post (x.run es.h)) : AllSpec (SS := SS') (RS := RS') (T := T') (M := M') (E := E') 1
    (fun z => Post (z.1, z.2.h) ∧ z.2.g = es.g ∧ z.2.abort = es.abort) ((liftH x).run es) := by
  unfold liftH; exact hx.bind fun ⟨a, h'⟩ hp => AllSpec.pure ⟨hp, rfl, rfl⟩
private theorem Dir2SessZeroM.len_le_one {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)} (hZ : Dir2SessZeroM t es) : es.h.sessions.length ≤ 1 := by
  have h := hZ.sess_le; split_ifs at h <;> omega
private theorem dir2SessZeroM_abort {es es1 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)} (hZ : Dir2SessZeroM t es) (hg : es1.g = es.g) (hlen : es1.h.sessions.length ≤ 1)
    (hca : ∀ ep Tc σc kc sIdx, es1.h.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0) : Dir2SessZeroM t { es1 with abort := true } :=
  ⟨hg ▸ hZ.id_eq, by simpa using hlen, hg ▸ hZ.vS_zero, hg ▸ hZ.vR_zero, hca⟩
private theorem dir2SessZeroM_same_st {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)} (hZ : Dir2SessZeroM t es) (hst : es'.g.st = es.g.st) (hab : es'.abort = es.abort)
    (hse : es'.h.sessions = es.h.sessions) (hca : es'.h.cache = es.h.cache) : Dir2SessZeroM t es' :=
  { id_eq := fun P => by rw [hst]; exact hZ.id_eq P
    sess_le := by rw [hse, hst, hab]; exact hZ.sess_le
    vS_zero := fun P sIdx hv => by rw [hst] at hv; exact hZ.vS_zero P sIdx hv
    vR_zero := fun P ep sIdx hv => by rw [hst] at hv; exact hZ.vR_zero P ep sIdx hv
    cache_zero := fun ep Tc σc kc sIdx hc => by rw [hca] at hc; exact hZ.cache_zero ep Tc σc kc sIdx hc }
private theorem sess_le_of_tcur_mono
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hZ : Dir2SessZeroM t es) (P : Party) (st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (htcur : (es.g.st P).tcur ≤ st'.tcur) :
    es.h.sessions.length ≤
      if t ≤ (Function.update es.g.st P st' (Party.senderOf t)).tcur ∨ es.abort = true then 1 else 0 := by
  have hle_sender : (es.g.st (Party.senderOf t)).tcur ≤
      (Function.update es.g.st P st' (Party.senderOf t)).tcur := by
    by_cases hSP : Party.senderOf t = P
    · rw [hSP, Function.update_self]; exact htcur
    · rw [Function.update_of_ne hSP]
  refine hZ.sess_le.trans ?_; split_ifs with h1 h2
  · exact le_rfl
  · exfalso; rcases h1 with ht0 | hab
    · exact h2 (Or.inl (ht0.trans hle_sender))
    · exact h2 (Or.inr hab)
  · exact Nat.zero_le _
  · exact le_rfl
private theorem dir2SessZeroM_update_party
    {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hZ : Dir2SessZeroM t es) (P : Party) (st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hst : es'.g.st = Function.update es.g.st P st') (hab : es'.abort = es.abort) (hid : st'.id = P)
    (hvS : ∀ sIdx, st'.vS = some (.inr sIdx) → sIdx = 0)
    (hvR : ∀ ep sIdx, st'.vR ep = some (.inr sIdx) → sIdx = 0)
    (hca : ∀ ep Tc σc kc sIdx, es'.h.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0)
    (hsess : es'.h.sessions.length ≤
      if t ≤ (Function.update es.g.st P st' (Party.senderOf t)).tcur ∨ es.abort = true then 1 else 0) :
    Dir2SessZeroM t es' :=
  { id_eq := fun Q => by
      rw [hst]; by_cases hQP : Q = P
      · subst hQP; simpa [Function.update_self] using hid
      · simpa [Function.update_of_ne hQP] using hZ.id_eq Q
    sess_le := by rw [hst, hab]; exact hsess
    vS_zero := fun Q sIdx hv => by
      rw [hst] at hv; by_cases hQP : Q = P
      · subst hQP; simp only [Function.update_self] at hv; exact hvS sIdx hv
      · simp only [Function.update_of_ne hQP] at hv; exact hZ.vS_zero Q sIdx hv
    vR_zero := fun Q ep sIdx hv => by
      rw [hst] at hv; by_cases hQP : Q = P
      · subst hQP; simp only [Function.update_self] at hv; exact hvR ep sIdx hv
      · simp only [Function.update_of_ne hQP] at hv; exact hZ.vR_zero Q ep sIdx hv
    cache_zero := hca }
private theorem startSend_some_dir2_spec (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (coins : CCoins) (h : FSMultiState T RSt K I E) (hlen : h.sessions.length ≤ 1)
    (hca0 : ∀ ep' Tc σc kc sIdx, h.cache ep' = some (Tc, σc, kc, some sIdx) → sIdx = 0) (hep_t : ep = t → h.sessions.length = 0) : AllSpec 1 (fun z => z.2.sessions.length ≤ 1 ∧ (ep ≠ t → z.2.sessions = h.sessions) ∧
    (∀ ep' Tc σc kc sIdx, z.2.cache ep' = some (Tc, σc, kc, some sIdx) → sIdx = 0) ∧ ∀ γ' T' σ' ssv, z.1 = some (γ', T', σ', ssv) → ∀ sIdx, ssv = .inr sIdx → sIdx = 0)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).startSend ctx P ep γ σ (some coins)).run h) := by
  dsimp only [hooksFSMulti]; rw [StateT.run_bind, StateT.run_pure, pure_bind]; simp only [StateT.run_bind]; refine AllSpec.bind (rootFSMulti_dir2_spec prng l t ep (cka.send γ coins).2.2 σ h)
    fun ⟨⟨σ', k0, sid⟩, h1⟩ ⟨hse1, hca1, hsid_some, hsid_ne⟩ => ?_
  refine (regSessOptMulti_spec sid h1).bind fun ⟨optIdx, h2⟩ ⟨hopt_some, hopt_none, hle2, hca2⟩ => ?_
  dsimp only at hse1 hca1 hsid_some hsid_ne hopt_some hopt_none hle2 hca2 ⊢; simp only [StateT.run_modify, StateT.run_pure, pure_bind]
  have hlen2 : h2.sessions.length ≤ 1 := by
    by_cases het : ep = t
    · have hz0 : h1.sessions.length = 0 := by rw [hse1]; exact hep_t het
      omega
    · rw [(hopt_none (hsid_ne het)).2, hse1]; exact hlen
  have hopt_zero : ∀ sIdx, optIdx = some sIdx → sIdx = 0 := by
    intro sIdx hopt; rcases hopt_some sIdx hopt with ⟨I0, hsidI, hlt⟩
    have hz0 : h1.sessions.length = 0 := by rw [hse1]; exact hep_t (hsid_some I0 hsidI)
    omega
  refine AllSpec.pure ⟨hlen2, fun hne => by rw [(hopt_none (hsid_ne hne)).2, hse1], ?_, ?_⟩
  · intro ep' Tc σc kc sIdx hent; by_cases heq : ep' = ep
    · subst heq; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hent; exact hopt_zero sIdx hent.2.2.2
    · simp only [Function.update_of_ne heq, hca2, hca1] at hent; exact hca0 ep' Tc σc kc sIdx hent
  · intro _ _ _ ssv hsome sIdx hssv; simp only [Option.some.injEq, Prod.mk.injEq] at hsome; rcases hsome with ⟨_, _, _, rfl⟩
    cases hopt : optIdx with
    | none => simp [hopt] at hssv
    | some idx0 => simp only [hopt, Sum.inr.injEq] at hssv; subst hssv; exact hopt_zero idx0 hopt
private theorem startSend_dir2_spec (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins) (h : FSMultiState T RSt K I E) (hlen : h.sessions.length ≤ 1)
    (hca0 : ∀ ep' Tc σc kc sIdx, h.cache ep' = some (Tc, σc, kc, some sIdx) → sIdx = 0) (hep_t : ep = t → h.sessions.length = 0) : AllSpec 1 (fun z => z.2.sessions.length ≤ 1 ∧ (ep ≠ t → z.2.sessions = h.sessions) ∧
    (∀ ep' Tc σc kc sIdx, z.2.cache ep' = some (Tc, σc, kc, some sIdx) → sIdx = 0) ∧ ∀ γ' T' σ' ssv, z.1 = some (γ', T', σ', ssv) → ∀ sIdx, ssv = .inr sIdx → sIdx = 0)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).startSend ctx P ep γ σ r).run h) := by
  cases r with
  | some coins => exact startSend_some_dir2_spec (l := l) cka prng fs la ctx P ep γ σ coins h hlen hca0 hep_t
  | none =>
    dsimp only [hooksFSMulti]; simp only [StateT.run_bind]
    refine (lift_sampleT_allSpec CCoins h).bind fun ⟨coins, h0⟩ hh0 => ?_
    rw [hh0]; exact startSend_some_dir2_spec (l := l) cka prng fs la ctx P ep γ σ coins h hlen hca0 hep_t
private theorem fsSend_dir2_spec (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (ep : ℕ) (ssv : SS ⊕ ℕ) (hssv : ∀ sIdx, ssv = .inr sIdx → sIdx = 0)
    (hdr : Header T) (m : M) (pair : Option (M × M)) (h : FSMultiState T RSt K I E) : AllSpec 1 (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧ ∀ v' e, z.1 = some (v', e) → ∀ sIdx, v' = .inr sIdx → sIdx = 0)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).fsSend ctx P ep ssv hdr m pair).run h) := by
  dsimp only [hooksFSMulti]; cases ssv with
  | inl ss =>
    simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _⟩; simp at hv⟩
  | inr sIdx =>
    have hs0 : sIdx = 0 := hssv sIdx rfl; subst hs0; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hc : (!(ctx.safeCh (2 + 0) P) && !((h.book 0).getD {}).sCorr) = true
    · simp only [hc, ↓reduceIte]; by_cases hla : la = true
      · simp only [hla, Bool.not_false, ↓reduceIte, StateT.run_pure]
        exact AllSpec.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_allSpec Nat.zero_lt_one h _).bind fun ⟨cRes, h0⟩ hh0 => ?_
        rw [hh0]; cases cRes with
        | none =>
          simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
          exact AllSpec.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
        | some _ =>
          simp only [StateT.run_bind, StateT.run_modify, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
          (rcases pair with _ | ⟨m₀, m₁⟩) <;>
          (simp only [StateT.run_bind]
           refine (liftFSMulti_allSpec Nat.zero_lt_one _ _).bind fun ⟨e?, h2⟩ hh2 => ?_
           rw [hh2]; cases e? with
           | none => simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
           | some e =>
             simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
             exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ ⟨rfl, rfl⟩ _ ⟨⟩; rfl⟩)
    · simp only [hc, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
      (rcases pair with _ | ⟨m₀, m₁⟩) <;>
      (simp only [StateT.run_bind]
       refine (liftFSMulti_allSpec Nat.zero_lt_one _ _).bind fun ⟨e?, h2⟩ hh2 => ?_
       rw [hh2]; cases e? with
       | none => simp only [StateT.run_pure]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
       | some e =>
         simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
         exact AllSpec.pure ⟨rfl, rfl, by rintro _ _ ⟨rfl, rfl⟩ _ ⟨⟩; rfl⟩)
private theorem startRecv_dir2_spec (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (Tn : T) (h : FSMultiState T RSt K I E)
    (hca0 : ∀ ep' Tc σc kc sIdx, h.cache ep' = some (Tc, σc, kc, some sIdx) → sIdx = 0) : AllSpec 1 (fun z => z.2 = h ∧ ∀ γ' σ' rsv, z.1 = some (some (γ', σ', rsv)) → ∀ sIdx, rsv = .inr sIdx → sIdx = 0)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).startRecv ctx P ep γ σ Tn).run h) := by
  dsimp only [hooksFSMulti]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hca : h.cache ep with _ | ⟨Tc, σc, k0, optIdx⟩
  · simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, StateT.run_pure]
    exact AllSpec.pure ⟨rfl, fun _ _ _ hs => by cases hs⟩
  · by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte, StateT.run_pure]
      refine AllSpec.pure ⟨rfl, fun _ _ rsv hs sIdx hrsv => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨_, _, rfl⟩
      cases hopt : optIdx with
      | none => simp [hopt] at hrsv
      | some idx0 => simp only [hopt, Sum.inr.injEq] at hrsv; subst hrsv; exact hca0 ep Tc σc k0 idx0 (hopt ▸ hca)
    · simp only [hTc, Bool.false_eq_true, Bool.false_and, ↓reduceIte, StateT.run_pure]
      exact AllSpec.pure ⟨rfl, fun _ _ _ hs => by cases hs⟩
private theorem reveal_dir2_spec (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hvS : ∀ sIdx, vp.vS = some (.inr sIdx) → sIdx = 0) (h : FSMultiState T RSt K I E) : AllSpec 1 (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
    (((hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la).reveal ctx P vp).run h) := by
  dsimp only [hooksFSMulti]; rcases hvs_eq : vp.vS with _ | (ss | sIdx)
  · dsimp only; split_ifs <;> exact AllSpec.pure ⟨rfl, rfl⟩
  · dsimp only; split_ifs <;> exact AllSpec.pure ⟨rfl, rfl⟩
  · have hs0 : sIdx = 0 := hvS sIdx hvs_eq; subst hs0; dsimp only
    cases la with
    | true => exact AllSpec.pure ⟨rfl, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine (liftFSMulti_allSpec Nat.zero_lt_one h _).bind fun ⟨res, h1⟩ hh1 => ?_
      dsimp only at hh1; subst h1; cases res with
      | none => dsimp only; exact AllSpec.pure ⟨rfl, rfl⟩
      | some _ => dsimp only; split_ifs <;> exact AllSpec.pure ⟨rfl, rfl⟩
private theorem vSend_dir2_spec
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hZ : Dir2SessZeroM t es) (habort : es.abort = false)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (hs_eq : s = es.g.st P)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) :
    AllSpec 1 (fun z => z.2.sessions.length ≤ 1 ∧
        (∀ ep Tc σc kc sIdx, z.2.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0) ∧
        ∀ st' c, z.1 = some (st', c) → st'.id = P ∧ (∀ sIdx, st'.vS = some (.inr sIdx) → sIdx = 0) ∧ (∀ ep sIdx, st'.vR ep = some (.inr sIdx) → sIdx = 0) ∧ z.2.sessions.length ≤
            if t ≤ (Function.update es.g.st P st' (Party.senderOf t)).tcur ∨ es.abort = true then 1 else 0)
      ((vSend (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) ctx P s m pair r).run es.h) := by
  unfold vSend; have hid_s : s.id = P := hs_eq ▸ hZ.id_eq P; have hvS_s : ∀ sIdx, s.vS = some (.inr sIdx) → sIdx = 0 := hs_eq ▸ hZ.vS_zero P; have hvR_s : ∀ ep sIdx, s.vR ep = some (.inr sIdx) → sIdx = 0 := hs_eq ▸ hZ.vR_zero P
  cases hsend : s.id.sendsIn (s.tcur + 1) with
  | true =>
    simp only [↓reduceIte, StateT.run_bind]; have hP_ep : P = Party.senderOf (s.tcur + 1) := party_eq_senderOf_of_party_sendsIn P (s.tcur + 1) (hid_s ▸ hsend)
    have hep_t : s.tcur + 1 = t → es.h.sessions.length = 0 := by
      intro het; have hP_t : P = Party.senderOf t := het ▸ hP_ep
      have htcur_lt : ¬ (t ≤ (es.g.st (Party.senderOf t)).tcur) := by rw [← hP_t, ← hs_eq]; omega
      have hle := hZ.sess_le; simp only [htcur_lt, habort, Bool.false_eq_true, or_self, ↓reduceIte] at hle; omega
    refine (startSend_dir2_spec cka prng fs la ctx P (s.tcur + 1) s.γ s.root r es.h
      hZ.len_le_one hZ.cache_zero hep_t).bind fun ⟨o, h1⟩ ⟨hlen1, hse_ne, hca1, hss⟩ => ?_
    dsimp only at hlen1 hse_ne hca1 hss ⊢; rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]; exact AllSpec.pure ⟨hlen1, hca1, fun _ _ hc => by cases hc⟩
    · simp only [pure_bind, StateT.run_bind]
      refine (fsSend_dir2_spec cka prng fs la ctx P (s.tcur + 1) ss
        (fun sIdx hv_eq => hss γ' T' σ' ss rfl sIdx hv_eq) (s.tcur + 1, some T') m pair h1).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      dsimp only at hse2 hca2 hv_eq ⊢
      have hca2' : ∀ ep Tc σc kc sIdx, h2.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0 :=
        fun ep Tc σc kc sIdx hc => hca1 ep Tc σc kc sIdx (hca2 ▸ hc)
      rcases res with _ | ⟨v', e⟩
      · exact AllSpec.pure ⟨hse2 ▸ hlen1, hca2', fun _ _ hc => by cases hc⟩
      · refine AllSpec.pure ?_; dsimp only; refine ⟨hse2 ▸ hlen1, hca2', fun st' _ hc => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, _⟩
        refine ⟨hid_s, fun sIdx hv' => ?_, hvR_s, ?_⟩
        · simp only [Option.some.injEq] at hv'; exact hv_eq v' e rfl sIdx hv'
        · by_cases het : s.tcur + 1 = t
          · have hP_t : P = Party.senderOf t := het ▸ hP_ep; rw [← hP_t, Function.update_self]; dsimp only
            have ht_ok : t ≤ s.tcur + 1 := by omega
            simp only [ht_ok, true_or, ↓reduceIte, hse2]; exact hlen1
          · rw [hse2, hse_ne het]; exact sess_le_of_tcur_mono hZ P _ (by rw [← hs_eq]; exact Nat.le_succ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; rcases hv : s.vS with _ | v
    · exact AllSpec.pure ⟨hZ.len_le_one, hZ.cache_zero, fun st' _ hc => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, _⟩
        exact ⟨hid_s, hvS_s, hvR_s, sess_le_of_tcur_mono hZ P s (by rw [hs_eq])⟩⟩
    · simp only [StateT.run_bind]
      refine (fsSend_dir2_spec cka prng fs la ctx P s.tcur v
        (fun sIdx hv_eq => hvS_s sIdx (hv ▸ hv_eq ▸ rfl)) (s.tcur, s.curCkaMsg) m pair es.h).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      dsimp only at hse2 hca2 hv_eq ⊢
      have hca2' : ∀ ep Tc σc kc sIdx, h2.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0 :=
        fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca2 ▸ hc)
      rcases res with _ | ⟨v', e⟩
      · exact AllSpec.pure ⟨hse2 ▸ hZ.len_le_one, hca2', fun _ _ hc => by cases hc⟩
      · refine AllSpec.pure ?_; dsimp only; refine ⟨hse2 ▸ hZ.len_le_one, hca2', fun st' _ hc => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, _⟩
        refine ⟨hid_s, fun sIdx hv' => ?_, hvR_s, ?_⟩
        · simp only [Option.some.injEq] at hv'; exact hv_eq v' e rfl sIdx hv'
        · rw [hse2]; exact sess_le_of_tcur_mono hZ P _ (by rw [← hs_eq])
private theorem vRecv_dir2_spec (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    AllSpec 1 (fun z => z.2.sessions = es.h.sessions ∧ z.2.cache = es.h.cache ∧ ∀ st' t' i' m', z.1 = some (some (st', t', i', m')) → st'.id = P ∧ (es.g.st P).tcur ≤ st'.tcur ∧ (∀ sIdx, st'.vS = some (.inr sIdx) → sIdx = 0) ∧
    (∀ ep sIdx, st'.vR ep = some (.inr sIdx) → sIdx = 0)) ((vRecv (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) es.g P (es.g.st P) c rec).run es.h) := by
  unfold vRecv; dsimp only
  by_cases hguard : ((es.g.st P).id.sendsIn c.1.1 || decide ((es.g.st P).tcur + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ _ hc => by cases hc⟩
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]; by_cases hnew : c.1.1 = (es.g.st P).tcur + 1
    · simp only [hnew, ↓reduceIte]; rcases c.1.2 with _ | Tn
      · simp only [pure_bind]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ _ hc => by cases hc⟩
      · simp only [StateT.run_bind]
        refine (startRecv_dir2_spec cka prng fs la es.g P ((es.g.st P).tcur + 1)
          (es.g.st P).γ (es.g.st P).root Tn es.h hZ.cache_zero).bind fun ⟨o, h1⟩ ⟨hh1, hrs⟩ => ?_
        dsimp only at hh1 hrs ⊢; rw [hh1]; rcases o with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ _ hc => by cases hc⟩
        · simp only [pure_bind]; exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ _ hc => by cases hc⟩
        · simp only [pure_bind, Function.update_self, StateT.run_bind]
          refine AllSpec.bind (fsRecv_hooksFSMulti_spec (l := l) (t := t) cka prng fs la es.g P
            ((es.g.st P).tcur + 1) rs (fun sIdx hr => hrs γ' σ' rs rfl sIdx hr) c.1 c.2 rec es.h)
            fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
          dsimp only at hse2 hca2 hv_eq ⊢; rcases res with _ | (_ | ⟨v', i', m'⟩)
          · exact AllSpec.pure ⟨hse2, hca2, fun _ _ _ _ hc => by cases hc⟩
          · exact AllSpec.pure ⟨hse2, hca2, fun _ _ _ _ hc => by cases hc⟩
          · refine AllSpec.pure ?_; dsimp only; refine ⟨hse2, hca2, fun st' _ _ _ hc => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, _, _, _⟩
            refine ⟨hZ.id_eq P, Nat.le_succ _, hZ.vS_zero P, fun ep sIdx hr => ?_⟩
            simp only [Function.update_idem] at hr; by_cases heq : ep = (es.g.st P).tcur + 1
            · subst heq; simp only [Function.update_self, Option.some.injEq] at hr; exact hv_eq v' i' m' rfl sIdx hr
            · simp only [Function.update_of_ne heq] at hr; exact hZ.vR_zero P ep sIdx hr
    · simp only [hnew, ↓reduceIte, pure_bind]; rcases hv : (es.g.st P).vR c.1.1 with _ | v
      · exact AllSpec.pure ⟨rfl, rfl, fun _ _ _ _ hc => by cases hc⟩
      · simp only [StateT.run_bind]
        refine AllSpec.bind (fsRecv_hooksFSMulti_spec cka prng fs la es.g P c.1.1 v
          (fun sIdx hr => hZ.vR_zero P c.1.1 sIdx (hv ▸ hr ▸ rfl)) c.1 c.2 rec es.h)
          fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
        dsimp only at hse2 hca2 hv_eq ⊢; rcases res with _ | (_ | ⟨v', i', m'⟩)
        · exact AllSpec.pure ⟨hse2, hca2, fun _ _ _ _ hc => by cases hc⟩
        · exact AllSpec.pure ⟨hse2, hca2, fun _ _ _ _ hc => by cases hc⟩
        · refine AllSpec.pure ?_; dsimp only; refine ⟨hse2, hca2, fun st' _ _ _ hc => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, _, _, _⟩
          refine ⟨hZ.id_eq P, le_rfl, hZ.vS_zero P, fun ep sIdx hr => ?_⟩
          by_cases heq : ep = c.1.1
          · subst heq; simp only [Function.update_self, Option.some.injEq] at hr; exact hv_eq v' i' m' rfl sIdx hr
          · simp only [Function.update_of_ne heq] at hr; exact hZ.vR_zero P ep sIdx hr
private theorem commitE_dir2_spec (s : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) : AllSpec 1 (fun z => z.2 = es ∧ ∀ s₁, z.1 = some s₁ → s₁.st = Function.update s.st P new)
    ((commitE (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) s P old new pos).run es) := by
  cases es; unfold commitE liftH
  simp only [hooksFSMulti, StateT.run_bind, StateT.run_pure, pure_bind]
  refine AllSpec.pure ⟨rfl, fun s₁ hs1 => ?_⟩
  injection hs1 with hs1'; subst hs1'; simp [GameState.accept, GameState.delete, Function.update_idem]
private theorem transmitE_dir2_spec (π : _root_.CryptoGames.SM.Engine.Policy) (q : Party × M × Option CCoins) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) :
    AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((transmitE (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep π q).run es) := by
  rcases q with ⟨P, m, r⟩; unfold transmitE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have habort : es.abort = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard; exact hguard.1
    cases hep : es.g.epMgmt 2 qep P r.isSome with
    | none => simp only [StateT.run_pure]; exact AllSpec.pure hZ
    | some s₁ =>
      dsimp only; have hst1 : s₁.st = es.g.st := epMgmt_st_eqM es.g s₁ 2 qep P r.isSome hep
      by_cases hdoom : π.leakDoom es.g s₁ = true
      · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ rfl hZ.len_le_one hZ.cache_zero)
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]; refine (liftH_allSpec (vSend_dir2_spec cka prng fs la es hZ habort s₁ P (s₁.st P) (congrFun hst1 P) m none r)).bind
          fun ⟨res, es1⟩ ⟨⟨hlen1, hca1, hst'⟩, hg1, hab1⟩ => ?_
        rcases res with _ | ⟨st', c⟩
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 hlen1 hca1)
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; rcases hst' st' c rfl with ⟨hid', hvS', hvR', hsess'⟩
          exact AllSpec.pure (dir2SessZeroM_update_party hZ P st' (by dsimp only [GameState.record]; rw [hst1]) hab1 hid' hvS' hvR' hca1 hsess')
private theorem challE_dir2_spec (cfg : _root_.CryptoGames.SM.Config M) (π : _root_.CryptoGames.SM.Engine.Policy) (q : Party × M × M × Option CCoins)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) : AllSpec 1 (fun z => Dir2SessZeroM t z.2)
    ((challE (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep cfg π q).run es) := by
  rcases q with ⟨P, m₀, m₁, r⟩; unfold challE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have habort : es.abort = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard; exact hguard.1
    cases hep : es.g.epMgmt 2 qep P r.isSome with
    | none => simp only [StateT.run_pure]; exact AllSpec.pure hZ
    | some s₁ =>
      dsimp only; have hst1 : s₁.st = es.g.st := epMgmt_st_eqM es.g s₁ 2 qep P r.isSome hep
      by_cases hsafe : (!(s₁.safeCh 2 P) || !(cfg.challAllowedIn (s₁.epoch P))) = true
      · simp only [hsafe, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
      · simp only [hsafe, Bool.false_eq_true, ↓reduceIte]
        by_cases hdoom : π.leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ rfl hZ.len_le_one hZ.cache_zero)
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          let mChosen := (cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)
          refine (liftH_allSpec (vSend_dir2_spec cka prng fs la es hZ habort s₁ P (s₁.st P) (congrFun hst1 P) mChosen (some (m₀, m₁)) r)).bind
            fun ⟨res, es1⟩ ⟨⟨hlen1, hca1, hst'⟩, hg1, hab1⟩ => ?_
          rcases res with _ | ⟨st', c⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 hlen1 hca1)
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; rcases hst' st' c rfl with ⟨hid', hvS', hvR', hsess'⟩
            exact AllSpec.pure (dir2SessZeroM_update_party hZ P st' (by dsimp only [GameState.record]; rw [hst1]) hab1 hid' hvS' hvR' hca1 hsess')
private theorem deliverE_dir2_spec (cfg : _root_.CryptoGames.SM.Config M) (q : Party × (Header T × E)) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) :
    AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((deliverE (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) fs.maxSkip cfg q).run es) := by
  rcases q with ⟨P, c⟩; unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]; cases es.g.inTransit P.other c with
    | none => simp only [StateT.run_pure]; exact AllSpec.pure hZ
    | some r =>
      simp only [StateT.run_bind]; refine (liftH_allSpec (vRecv_dir2_spec cka prng fs la es hZ P c (some r))).bind
        fun ⟨res, es1⟩ ⟨⟨hse1, hca1, hst'⟩, hg1, hab1⟩ => ?_
      have hca1' : ∀ ep Tc σc kc sIdx, es1.h.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0 :=
        fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca1 ▸ hc)
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 (hse1 ▸ hZ.len_le_one) hca1')
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_same_st hZ (by dsimp only; exact congrArg GameState.st hg1) hab1 hse1 hca1)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure (dir2SessZeroM_same_st hZ (congrArg GameState.st hg1) hab1 hse1 hca1)
      · simp only [StateT.run_bind]; rcases hst' st' t' i' m' rfl with ⟨hid', htcur', hvS', hvR'⟩; refine (commitE_dir2_spec cka prng fs la es.g P (es.g.st P) st' r.pos es1).bind
          fun ⟨s₁?, es2⟩ ⟨hes2, hs1_st⟩ => ?_
        rw [hes2]; rcases s₁? with _ | s₁
        · simp only [StateT.run_pure]; exact AllSpec.pure (dir2SessZeroM_same_st hZ (congrArg GameState.st hg1) hab1 hse1 hca1)
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact AllSpec.pure (dir2SessZeroM_update_party hZ P st' (by dsimp only; split_ifs <;> exact hs1_st s₁ rfl) hab1 hid' hvS' hvR' hca1' (hse1 ▸ sess_le_of_tcur_mono hZ P st' htcur'))
private theorem vRecv_forged_tail_dir2_spec
    (cfg : _root_.CryptoGames.SM.Config M) (P : Party)
    (es es1 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hZ : Dir2SessZeroM t es) (hse1 : es1.h.sessions = es.h.sessions) (hca1 : es1.h.cache = es.h.cache)
    (hg1 : es1.g = es.g) (hab1 : es1.abort = es.abort)
    (st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (t' i' : ℕ) (m' : M)
    (hid' : st'.id = P) (htcur' : (es.g.st P).tcur ≤ st'.tcur)
    (hvS' : ∀ sIdx, st'.vS = some (.inr sIdx) → sIdx = 0)
    (hvR' : ∀ ep sIdx, st'.vR ep = some (.inr sIdx) → sIdx = 0) :
    AllSpec 1 (fun z => Dir2SessZeroM t z.2)
      (((if _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g ⟨P.other, t', i'⟩ then do
          match ← commitE (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la)
              es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ with
          | none => pure none
          | some s₁ => modify fun es => { es with g := s₁ }; pure (some (RecvResult.accepted t' i' (some m')))
        else if cfg.injectFull t' then do
          modify fun es => { es with g := { es.g with win := true } }; pure (some RecvResult.rejected)
        else pure (some RecvResult.rejected)) :
        _root_.CryptoGames.SM.Engine.EM (FSMultiSpec SS RS T M E)
          Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E (FSMultiState T RSt K I E) (Option (RecvResult M))).run es1) := by
  have hsame : Dir2SessZeroM t es1 := dir2SessZeroM_same_st hZ (congrArg GameState.st hg1) hab1 hse1 hca1
  have hca1' : ∀ ep Tc σc kc sIdx, es1.h.cache ep = some (Tc, σc, kc, some sIdx) → sIdx = 0 :=
    fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca1 ▸ hc)
  by_cases htriv : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g ⟨P.other, t', i'⟩ = true
  · simp only [htriv, ↓reduceIte, StateT.run_bind]; refine (commitE_dir2_spec cka prng fs la es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ es1).bind
      fun ⟨s₁?, es2⟩ ⟨hes2, hs1_st⟩ => ?_
    rw [hes2]; rcases s₁? with _ | s₁
    · simp only [StateT.run_pure]; exact AllSpec.pure hsame
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_update_party hZ P st' (hs1_st s₁ rfl) hab1 hid' hvS' hvR' hca1' (hse1 ▸ sess_le_of_tcur_mono hZ P st' htcur'))
  · simp only [htriv, Bool.false_eq_true, ↓reduceIte]; by_cases hfull : cfg.injectFull t' = true
    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_same_st hZ (by dsimp only; exact congrArg GameState.st hg1) hab1 hse1 hca1)
    · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hsame
private theorem injectEB1_dir2_spec (cfg : _root_.CryptoGames.SM.Config M) (q : Party × (Header T × E)) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) :
    AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((injectEB1 (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) qep t cfg q).run es) := by
  rcases q with ⟨P, c⟩; unfold injectEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]; refine (liftH_allSpec (vRecv_dir2_spec cka prng fs la es hZ P c none)).bind
      fun ⟨res, es1⟩ ⟨⟨hse1, hca1, hst'⟩, hg1, hab1⟩ => ?_
    have hsame : Dir2SessZeroM t es1 := dir2SessZeroM_same_st hZ (congrArg GameState.st hg1) hab1 hse1 hca1
    rcases res with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 (hse1 ▸ hZ.len_le_one)
        (fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca1 ▸ hc)))
    · simp only [StateT.run_pure]; exact AllSpec.pure hsame
    · by_cases hrej : qep + 1 < t'
      · simp only [hrej, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hsame
      · simp only [hrej, ↓reduceIte]; rcases hst' st' t' i' m' rfl with ⟨hid', htcur', hvS', hvR'⟩; exact vRecv_forged_tail_dir2_spec (l := l) cka prng fs la cfg P es es1 hZ hse1 hca1 hg1 hab1
          st' t' i' m' hid' htcur' hvS' hvR'
private theorem corrEShiftedPaper_dir2_spec (π : _root_.CryptoGames.SM.Engine.Policy) (P : Party) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) :
    AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((corrEShiftedPaper l (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) π P).run es) := by
  unfold corrEShiftedPaper; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_abort hZ rfl hZ.len_le_one hZ.cache_zero)
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine (liftH_allSpec (reveal_dir2_spec cka prng fs la es.g P (es.g.st P)
        (hZ.vS_zero P) es.h)).bind fun ⟨stOpt, es1⟩ ⟨⟨hse1, hca1⟩, hg1, hab1⟩ => ?_
      rcases stOpt with _ | st
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 (hse1 ▸ hZ.len_le_one)
          (fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca1 ▸ hc)))
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact AllSpec.pure (dir2SessZeroM_same_st hZ rfl hab1 hse1 hca1)
private theorem deliverForgeEB1_dir2_spec (cfg : _root_.CryptoGames.SM.Config M) (q : Party × (Header T × E) × (Header T × E)) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hZ : Dir2SessZeroM t es) : AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((deliverForgeEB1 (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) qep t cfg q).run es) := by
  rcases q with ⟨P, c, c'⟩; unfold deliverForgeEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.abort || es.g.win) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]; cases es.g.inTransit P.other c with
    | none => simp only [StateT.run_pure]; exact AllSpec.pure hZ
    | some r =>
      dsimp only
      by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || (c.1 != c'.1)) = true
      · simp only [hchk, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hZ
      · simp only [hchk, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]; refine (liftH_allSpec (vRecv_dir2_spec cka prng fs la es hZ P c' none)).bind
          fun ⟨res, es1⟩ ⟨⟨hse1, hca1, hst'⟩, hg1, hab1⟩ => ?_
        have hsame : Dir2SessZeroM t es1 := dir2SessZeroM_same_st hZ (congrArg GameState.st hg1) hab1 hse1 hca1
        rcases res with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact AllSpec.pure (dir2SessZeroM_abort hZ hg1 (hse1 ▸ hZ.len_le_one)
            (fun ep Tc σc kc sIdx hc => hZ.cache_zero ep Tc σc kc sIdx (hca1 ▸ hc)))
        · simp only [StateT.run_pure]; exact AllSpec.pure hsame
        · by_cases hrej : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
          · simp only [hrej, ↓reduceIte, StateT.run_pure]; exact AllSpec.pure hsame
          · simp only [hrej, Bool.false_eq_true, ↓reduceIte]; rcases hst' st' t' i' m' rfl with ⟨hid', htcur', hvS', hvR'⟩; exact vRecv_forged_tail_dir2_spec (l := l) cka prng fs la cfg P es es1 hZ hse1 hca1 hg1 hab1
              st' t' i' m' hid' htcur' hvS' hvR'
private theorem coinsE_dir2_spec (u : unifSpec.Domain) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) : AllSpec 1 (fun z => Dir2SessZeroM t z.2)
    ((_root_.CryptoGames.SM.Engine.coinsE (tspec := FSMultiSpec SS RS T M E) u).run es) := by
  unfold _root_.CryptoGames.SM.Engine.coinsE; rw [StateT.run_lift]
  refine ⟨.coin u _ fun a => .pure (a, es), fun z hz => ?_⟩
  rw [mem_support_bind_iff] at hz; rcases hz with ⟨_, _, hz⟩; simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hZ
end Dir2StepHelpers
private theorem stepM_dir2_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) {qep l t : ℕ} (la : Bool) (x : (SMSpecDF Γ T RSt SS RS M CCoins E).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) : AllSessLt 1 ((implEDFShiftedPaperGen true l
    (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep fs.maxSkip t (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy x).run es) ∧ ∀ z ∈ support ((implEDFShiftedPaperGen true l
    (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep fs.maxSkip t (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy x).run es), Dir2SessZeroM t z.2 := by
  change AllSpec 1 (fun z => Dir2SessZeroM t z.2) ((implEDFShiftedPaperGen true l
    (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep fs.maxSkip t
    (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy x).run es)
  rcases x with u | (((((q1 | q2) | q3) | q4) | q5) | q6)
  · exact coinsE_dir2_spec u es hZ
  · exact transmitE_dir2_spec cka prng fs la _ q1 es hZ
  · exact challE_dir2_spec cka prng fs la _ _ q2 es hZ
  · exact deliverE_dir2_spec cka prng fs la _ q3 es hZ
  · exact injectEB1_dir2_spec cka prng fs la _ q4 es hZ
  · exact corrEShiftedPaper_dir2_spec cka prng fs la _ q5 es hZ
  · exact deliverForgeEB1_dir2_spec cka prng fs la _ q6 es hZ
private theorem runM_dir2_allSessLt {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) {qep l t : ℕ} (la : Bool) {α : Type} (oa : SMCompDF Γ T RSt SS RS M CCoins E α)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) (hZ : Dir2SessZeroM t es) : AllSessLt 1 ((simulateQ (implEDFShiftedPaperGen true l
    (hooksFSMulti cka prng fs 0 ⟨false, some (l - 1), t⟩ false la) 2 qep fs.maxSkip t (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy) oa).run es) := by
  induction oa using OracleComp.inductionOn generalizing es with
  | pure a => simp only [simulateQ_pure, StateT.run_pure]; exact .pure _
  | query_bind x k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]; obtain ⟨ha, hpres⟩ := stepM_dir2_spec cka prng fs la x es hZ
    exact ha.bind_support fun ⟨u, es'⟩ hz => ih u es' (hpres _ hz)
private theorem initFSMultiRaw_dir2_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) {l t : ℕ} (ht2 : 2 ≤ t) : AllSpec 1 (fun es₀ => Dir2SessZeroM (M := M) (E := E) t es₀)
    (initFSMultiRaw cka prng fs lam ⟨false, some (l - 1), t⟩ false) := by
  unfold initFSMultiRaw
  refine (sampleT_allSpec KR).bind fun kr _ => ?_
  refine (sampleT_allSpec KC).bind fun kc _ => ?_
  refine AllSpec.bind (rootFSMulti_dir2_spec prng l t 0 lam (prng.init kr) {})
    fun ⟨⟨σ, k0, sid⟩, h₁⟩ ⟨hse1, hca1, _, hsid_ne⟩ => ?_
  have hsid_none : sid = none := hsid_ne (by omega); subst hsid_none
  refine (regSessOptMulti_spec none h₁).bind fun ⟨optIdx, h₂⟩ ⟨_, hopt_none, _, hca2⟩ => ?_
  rcases hopt_none rfl with ⟨rfl, hse2⟩; refine AllSpec.pure
    { id_eq := fun P => by cases P <;> rfl
      sess_le := by dsimp only; rw [hse2, hse1]; exact Nat.zero_le _
      vS_zero := fun P sIdx hv => by cases P <;> simp [mkParties] at hv
      vR_zero := fun P ep sIdx hv => by cases P <;> simp [mkParties] at hv
      cache_zero := fun ep Tc σc kc sIdx hc => by dsimp only at hc; rw [hca2, hca1] at hc; cases hc }

/-- `redFSAuthDFShiftedDir2PaperMulti` (`B1`, `2 ≤ t`) never queries any multi-session index `≥ 1`. -/
theorem redFSAuthDFShiftedDir2PaperMulti_offRange_one
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    {qep l t : ℕ} (ht2 : 2 ≤ t) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    (redFSAuthDFShiftedDir2PaperMulti cka prng fs lam qep l t la A).IsQueryBoundP
      (fun u => sessOffRange 1 u = true) 0 := by
  unfold redFSAuthDFShiftedDir2PaperMulti redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper; rw [bind_assoc]; apply AllSessLt.to_isQueryBoundP
  have hInit := initFSMultiRaw_dir2_spec (M := M) (E := E) cka prng fs lam (l := l) ht2
  exact hInit.1.bind_support fun es₀ hes₀ =>
    (runM_dir2_allSessLt cka prng fs la A es₀ (hInit.2 es₀ hes₀)).bind_support fun _ _ => .pure _

end

end Computational.Proofs.E2E.SessionAuthMultiRealShiftedAux
