/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c3 -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c4
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB3 -- proof-setup: allow-public-import
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game

/-!
# `Auth` hybrid hop `G3 → G3.5`: freeze-on-win simulation coupling

Couples `pqxdhAuthSendLatchedStageImpl` between `.g3_5` and `.g3` via freeze-on-win induction
and projects the frozen `.g3` bad event to `runAuthFgLatchedSim`.
-/

public section

set_option autoImplicit false
open Classical SignalPqxdh SignalPqxdh.Security OracleSpec OracleComp MeasureTheory
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Freeze-on-win equivalence -/

theorem finalizeAuthKosk_of_hasWonAuth {S : Setup} (P : Primitives)
    (secb b' : Bool) (hst : AuthHybridState S)
    (hWon : hst.base.hasWonAuth = true) :
    finalizeAuthKosk S P secb b' hst =
      (if isAuthG3Abort P hst then $ᵗ Bool else pure true) := by
  unfold finalizeAuthKosk
  simp [hWon]

/-! ## Frozen `.g3` simulation induction -/

/-- `.g3` `AuthSendLatchedState` oracle frozen once `s.hyb.base.hasWonAuth = true`. -/
@[expose] def pqxdhAuthSendLatchedFrozenG3Impl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthSendLatchedState S) ProbComp) :=
  freezeImpl (fun s : AuthSendLatchedState S => s.hyb.base.hasWonAuth)
    (fun _ => .noneResp) (pqxdhAuthSendLatchedStageImpl .g3 S P)

theorem pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_true
    {S : Setup} (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hWon : s.hyb.base.hasWonAuth = true) :
    (pqxdhAuthSendLatchedFrozenG3Impl S P q).run s = pure (.noneResp, s) := by
  simp [pqxdhAuthSendLatchedFrozenG3Impl, freezeImpl, StateT.run_bind, StateT.run_get, hWon]

/-! ## `AuthSendWinGuardedCoupledInv` query dispatcher -/

theorem relProbUpToBad_liftSendLatched_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    {s35 s3 : AuthSendLatchedState S} (hEqLatched : s35.respEkCollLatched = s3.respEkCollLatched)
    {m5 m6 : ProbComp (AuthResponse × AuthAdvLatchedState S)}
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg) m5 m6) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg || y3.2.respEkCollLatched)
      (m5 >>= fun p => pure (p.1, { s35 with toAuthAdvLatchedState := p.2 }))
      (m6 >>= fun p => pure (p.1, { s3 with toAuthAdvLatchedState := p.2 })) := by
  have hRel : ∀ x y : AuthResponse × AuthAdvLatchedState S,
      (x.1 = y.1 ∧ AuthFullG3G3_5CoupledInv P x.2 y.2) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) →
      (x.1 = y.1 ∧
        AuthSendWinGuardedCoupledInv P
          { s35 with toAuthAdvLatchedState := x.2 }
          { s3 with toAuthAdvLatchedState := y.2 }) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) := by
    intro x y hR; rcases hR with ⟨hEq, hFull'⟩ | hAb
    · exact Or.inl ⟨hEq, authWinGuardedG3G3_5CoupledInv_of_full P hFull', hEqLatched⟩
    · exact Or.inr hAb
  have hBad : ∀ y : AuthResponse × AuthAdvLatchedState S,
      badAuthFgAnyLatchedMono P maxRo y.2.toFg = true →
      (badAuthFgAnyLatchedMono P maxRo y.2.toFg || s3.respEkCollLatched) = true :=
    fun _ hb => Bool.or_eq_true_iff.mpr (Or.inl hb)
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.1
      (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
      (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 }))
      (fun x => hw5 _) (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.2
      (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 }))
      (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
      (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))

theorem relProbUpToBad_wrapSendLatched_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    {s35 s3 : AuthSendLatchedState S} (hFull : AuthFullG3G3_5CoupledInv P
      s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState)
    (hEqLatched : s35.respEkCollLatched = s3.respEkCollLatched)
    {m5 m6 : ProbComp (AuthResponse × AuthAdvLatchedState S)}
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3.toAuthAdvLatchedState y3.2 false) m5 m6) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg || y3.2.respEkCollLatched)
      (m5 >>= fun p => pure (wrapSendLatched P s35 p))
      (m6 >>= fun p => pure (wrapSendLatched P s3 p)) := by
  have hRel : ∀ x y : AuthResponse × AuthAdvLatchedState S,
      (x.1 = y.1 ∧ AuthFullG3G3_5CoupledInv P x.2 y.2) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) →
      ((wrapSendLatched P s35 x).1 = (wrapSendLatched P s3 y).1 ∧
        AuthSendWinGuardedCoupledInv P (wrapSendLatched P s35 x).2 (wrapSendLatched P s3 y).2) ∨
        (isAuthG3Abort P (wrapSendLatched P s35 x).2.hyb = true ∧
          isAuthG3Abort P (wrapSendLatched P s3 y).2.hyb = true) := by
    intro x y hR; rcases hR with ⟨hEq, hFull'⟩ | hAb
    · exact Or.inl ⟨hEq, authWinGuardedG3G3_5CoupledInv_of_full P hFull',
        latchRespEkCollSendStep_eq_of_agree P hFull.1.1 hFull'.1.1 hEqLatched⟩
    · exact Or.inr hAb
  have hBad : ∀ y : AuthResponse × AuthAdvLatchedState S,
      (badAuthFgAnyLatchedMono P maxRo y.2.toFg ||
        latchRespEkCollSendStep P s3.toAuthAdvLatchedState y.2 false) = true →
      (badAuthFgAnyLatchedMono P maxRo (wrapSendLatched P s3 y).2.toFg ||
        (wrapSendLatched P s3 y).2.respEkCollLatched) = true := by
    intro y hb; dsimp only [wrapSendLatched]
    rcases Bool.or_eq_true_iff.mp hb with hb1 | hb2
    · exact Bool.or_eq_true_iff.mpr (Or.inl hb1)
    · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
      unfold latchRespEkCollSendStep at hb2 ⊢; rw [Bool.false_or] at hb2
      exact Bool.or_eq_true_iff.mpr (Or.inr hb2)
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.1 (fun x => w5 (wrapSendLatched P s35 x)) (fun y => w6 (wrapSendLatched P s3 y))
      (fun x => hw5 _) (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.2 (fun y => w6 (wrapSendLatched P s3 y)) (fun x => w5 (wrapSendLatched P s35 x))
      (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))

theorem fgAuthStepCoupling_nonRo_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    (q : AuthQuery S) (hq : isAuthNonRoQuery q = true)
    (s35 s3 : AuthAdvLatchedState S) (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3)) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv', authRecvOriginInv_of_nonRo_query P q s3 hq hFull.2 hy3⟩
  · exact Or.inr hAb

/-! ## Freeze-on-win projection to `runAuthFgLatchedSim` -/

/-- Clears the `hasWonAuth` bit in `AuthState S`. -/
@[expose] def clearAuthWon {S : Setup} (st : AuthState S) : AuthState S :=
  { st with hasWonAuth := false }

@[simp]
theorem clearAuthWon_of_hasWonAuth_false {S : Setup} (st : AuthState S)
    (hWon : st.hasWonAuth = false) :
    clearAuthWon st = st := by
  cases st; dsimp only at hWon; subst hWon; rfl

/-- Projects `AuthSendLatchedState S` to `AuthFgCutoffState S` with `hasWonAuth := false`. -/
@[expose] def projSendToFg {S : Setup} (s : AuthSendLatchedState S) : AuthFgCutoffState S :=
  { s.toFg with base := clearAuthWon s.toFg.base }

@[simp]
theorem projSendToFg_empty (S : Setup) (secb : Bool) :
    projSendToFg (AuthSendLatchedState.empty S secb) = AuthFgCutoffState.empty S secb := rfl

@[simp]
theorem badAuthFgAnyLatchedMono_projSendToFg {S : Setup} (P : Primitives) (maxRo : ℕ)
    (s : AuthSendLatchedState S) :
    badAuthFgAnyLatchedMono P maxRo (projSendToFg s) = badAuthFgAnyLatchedMono P maxRo s.toFg := rfl

theorem map_base_pqxdhAuthHybridKoskImpl_g3_eq_mkG3Hybrid (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) :
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid hst.base) := by
  rw [map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q hst,
      map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (mkG3Hybrid hst.base)]

@[expose] def clearHybWon {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with base := clearAuthWon hst.base }

theorem commutesProj_clearHybWon_recvOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = false) :
    CommutesProj clearHybWon (mkG3Hybrid st)
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvOPK k j o msg))
      (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvOPK k j o msg)) := by
  have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
    simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
  have hPure : CommutesProj clearHybWon (mkG3Hybrid st)
      (pure AuthResponse.noneResp) (pure AuthResponse.noneResp) := by
    unfold CommutesProj; simp [hId, StateT.run_pure, Prod.map]
  unfold pqxdhAuthHybridKoskImpl
  apply CommutesProj.get_bind; dsimp only
  rw [hId]; dsimp only [mkG3Hybrid]
  simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  cases st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hPure
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hPure
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact hPure
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only
        refine CommutesProj.ite _ _ _ hPure ?_
        refine CommutesProj.ite _ _ _ hPure ?_
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact hPure
        | some ss =>
          dsimp only
          refine CommutesProj.set_bind clearHybWon (mkG3Hybrid st) _ _
            (by simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon]) ?_
          apply CommutesProj.liftM_bind; intro opt
          cases opt with
          | none =>
            unfold CommutesProj
            simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon, StateT.run_pure, Prod.map]
          | some tup =>
            rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
            cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
            | none =>
              exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                (CommutesProj.pure _ _ _)
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩; dsimp only
              cases (!senderEntry.corrupted) <;>
                exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                  (CommutesProj.pure _ _ _)

theorem commutesProj_clearHybWon_recvNoOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = false) :
    CommutesProj clearHybWon (mkG3Hybrid st)
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvNoOPK k j l msg))
      (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvNoOPK k j l msg)) := by
  have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
    simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
  have hPure : CommutesProj clearHybWon (mkG3Hybrid st)
      (pure AuthResponse.noneResp) (pure AuthResponse.noneResp) := by
    unfold CommutesProj; simp [hId, StateT.run_pure, Prod.map]
  unfold pqxdhAuthHybridKoskImpl
  apply CommutesProj.get_bind; dsimp only
  rw [hId]; dsimp only [mkG3Hybrid]
  simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  cases st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hPure
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hPure
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      refine CommutesProj.ite _ _ _ hPure ?_
      cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => exact hPure
      | some ss =>
        dsimp only
        refine CommutesProj.set_bind clearHybWon (mkG3Hybrid st) _ _
          (by simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon]) ?_
        apply CommutesProj.liftM_bind; intro opt
        cases opt with
        | none =>
          unfold CommutesProj
          simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon, StateT.run_pure, Prod.map]
        | some tup =>
          rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
          cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
          | none =>
            exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
              (CommutesProj.pure _ _ _)
          | some sp =>
            rcases sp with ⟨_, senderEntry⟩; dsimp only
            cases (!senderEntry.corrupted) <;>
              exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                (CommutesProj.pure _ _ _)

private theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S)
    (hWon : st.hasWonAuth = false)
    (hEq : (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st))
    (hPres : PreservesAt AuthState.hasWonAuth st
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q)) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st) := by
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id
      (fun h : AuthHybridState S => clearAuthWon h.base)) =
      fun a => Prod.map id clearAuthWon (Prod.map id AuthHybridState.base a) := by
    funext ⟨r, h⟩; rfl
  rw [hEq, hComp, ← Functor.map_map, ← hEq,
      map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (mkG3Hybrid st)]
  have hFr : (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run
        (mkG3Hybrid st).base =
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run st := by
    simp [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get, hWon]
  rw [hFr]
  have hIdOnSupp : ∀ {α : Type} (mx : ProbComp α) (f : α → α),
      (∀ x ∈ support mx, f x = x) → f <$> mx = mx := by
    intro α mx f hf
    induction mx using OracleComp.inductionOn with
    | pure a => simp [hf a (by simp)]
    | query_bind i k ih =>
      rw [map_eq_bind_pure_comp, bind_assoc]; simp only [← map_eq_bind_pure_comp]
      congr 1; funext u
      exact ih u (fun x hx => hf x (by
        rw [MonadAttach.mem_support_bind]
        exact ⟨u, by simp, hx⟩))
  refine hIdOnSupp _ _ (fun x hx => ?_)
  rcases x with ⟨r, s'⟩
  simp [Prod.map, clearAuthWon_of_hasWonAuth_false s' ((hPres (r, s') hx).trans hWon)]

theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_mkG3Hybrid (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S) (hWon : st.hasWonAuth = false) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP
      (.sendOPK u i bundle m0 m1) st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl
      simp [StateT.run_bind, StateT.run_get, mkG3Hybrid, hWon]
    · intro x hx
      unfold pqxdhAuthWithProvImpl at hx; dsimp only at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨_, rfl⟩; rfl
      · exact runAuthSendWithProv_pres_hasWonAuth S P (checkBundleProvenanceExact P)
          _ u bundle m0 m1 st x hx
  | sendNoOPK u i bundle m0 m1 =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP
      (.sendNoOPK u i bundle m0 m1) st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl
      simp [StateT.run_bind, StateT.run_get, mkG3Hybrid, hWon]
    · intro x hx
      unfold pqxdhAuthWithProvImpl at hx; dsimp only at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨_, rfl⟩; rfl
      · exact runAuthSendWithProv_pres_hasWonAuth S P (checkBundleProvenanceExact P)
          _ u bundle m0 m1 st x hx
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP _ st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl
      simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        mkG3Hybrid, hWon]
    · unfold pqxdhAuthWithProvImpl pqxdhAuthImpl; dsimp only; prove_preserves_at
  | recvOPK k j o msg =>
    have hC := commutesProj_clearHybWon_recvOPK S P k j o msg st hWon
    unfold CommutesProj at hC
    have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
      simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
    rw [hId] at hC
    have hMap := congrArg (Prod.map id AuthHybridState.base <$> ·) hC.symm
    rw [Functor.map_map] at hMap
    exact hMap
  | recvNoOPK k j l msg =>
    have hC := commutesProj_clearHybWon_recvNoOPK S P k j l msg st hWon
    unfold CommutesProj at hC
    have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
      simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
    rw [hId] at hC
    have hMap := congrArg (Prod.map id AuthHybridState.base <$> ·) hC.symm
    rw [Functor.map_map] at hMap
    exact hMap

theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) (hWon : hst.base.hasWonAuth = false) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) := by
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id
      (fun h : AuthHybridState S => clearAuthWon h.base)) =
      fun a => Prod.map id clearAuthWon (Prod.map id AuthHybridState.base a) := by
    funext ⟨r, h⟩; rfl
  rw [hComp, ← Functor.map_map,
      map_base_pqxdhAuthHybridKoskImpl_g3_eq_mkG3Hybrid S P hP q hst,
      Functor.map_map, ← hComp]
  exact map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_mkG3Hybrid S P hP q hst.base hWon

@[expose] def projAdvToFg {S : Setup} (s : AuthAdvLatchedState S) : AuthFgCutoffState S :=
  { s.toFg with base := clearAuthWon s.hyb.base }

private theorem map_hyb_to_base_g3 {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (q : AuthQuery S)
    (hst : AuthHybridState S) (hWon : hst.base.hasWonAuth = false)
    (f : AuthState S → AuthFgCutoffState S) :
    ((pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst >>= fun p =>
      pure (p.1, f (clearAuthWon p.2.base))) =
    ((pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) >>= fun p =>
      pure (p.1, f p.2.base)) := by
  have h1 : ((pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst >>= fun p =>
      pure (p.1, f (clearAuthWon p.2.base))) =
      Prod.map id f <$> (Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
        (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
  have h2 : ((pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) >>= fun p =>
      pure (p.1, f p.2.base)) =
      Prod.map id f <$> (Prod.map id AuthHybridState.base <$>
        (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
  rw [h1, h2, map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3 S P hP q hst hWon]

theorem evalDist_outer_bind_abs_sub_le_three {β : Type}
    (mx : ProbComp β)
    (f5 f6 fBad : β → ProbComp Bool)
    (hle : ∀ b,
      𝒟[f5 b] {true} ≤ 𝒟[f6 b] {true} + 𝒟[fBad b] {true} ∧
      𝒟[f6 b] {true} ≤ 𝒟[f5 b] {true} + 𝒟[fBad b] {true}) :
    |(𝒟[mx >>= f5] {true}).toReal - (𝒟[mx >>= f6] {true}).toReal| ≤
      (𝒟[mx >>= fBad] {true}).toReal := by
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  have hEq : ∀ (f : β → ProbComp Bool),
      𝒟[mx >>= f] {true} = probExpect mx (fun b => 𝒟[f b] {true}) := by
    intro f; unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have h1 : 𝒟[mx >>= f5] {true} ≤ 𝒟[mx >>= f6] {true} + 𝒟[mx >>= fBad] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).1)
  have h2 : 𝒟[mx >>= f6] {true} ≤ 𝒟[mx >>= f5] {true} + 𝒟[mx >>= fBad] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).2)
  have hfin5 : 𝒟[mx >>= f5] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hfin6 : 𝒟[mx >>= f6] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hfinBad : 𝒟[mx >>= fBad] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinBad⟩)).mpr h1
  have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinBad⟩)).mpr h2
  rw [ENNReal.toReal_add hfin6 hfinBad] at h1r
  rw [ENNReal.toReal_add hfin5 hfinBad] at h2r
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end Proofs.SignalPqxdh.Security
