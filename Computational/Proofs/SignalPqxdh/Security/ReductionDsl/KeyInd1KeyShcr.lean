/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrWire -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrEval
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreHol
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrBranch
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Costed `ReductionDsl` One-Key `KemShCr` Program and Advantage Equivalence

**Checked by Lean.** Defines the two-stage `ReductionDsl` program `shcrKeyInd1KeyProg` for the
one-key `KemShCr` reduction `shcrReductionKeyInd1Key` and proves its syntactic cost, query, and
block-size bounds together with exact `KemShCr` advantage agreement.
-/

public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp RoKem

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

/-! ## One-key `initPrin` branch and `shcrKeyInd1KeyProg` -/

/-- One-key `initPrin u` handler reusing a single 32-byte scalar for both X25519 keys. -/
@[expose] def initPrin1KeyB (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs rNone (v st))) <|
  bindV sBytes32 fun s0 => bindV (qX25519Base (v s0)) fun ik =>
  .ret (rs (rInitPrin (v ik) (v ik)) (stUpd (v st) (prin := .cons
    (.pair (v u) (peMk (v s0) (v ik) (v s0) (v ik) (.bool false))) (stPrin (v st)))))

@[expose, reducible] def keyIndQueryRestTy : PT :=
  .sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat bundleT)) (.sum (.prod .nat (.prod .nat bundleT))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum sidT (.sum (B 192) (.sum .unit (.sum sidT (.sum (B 32) (.prod .nat .nat))))))))))))

@[expose] def shcrPostTailC (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (q : Var (keyIndQueryRestTy :: Δ) keyIndQueryRestTy) :
    Comp pqxdhOps pqPrimIface (keyIndQueryRestTy :: Δ) SCS :=
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => testB K g sid) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB true K g sec) fun q =>
  caseSumV (v q) (fun _ => onBase s fun g => revealDhB true K g) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => revealB K g sid) fun q =>
  caseSumV (v q) (fun sk => onBase s fun g => registerB g sk) fun x =>
  onBase s fun g => revealSpkB K g x

@[expose] def shcr1KeyPostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrin1KeyB K g u) (shcrPostTailC S K s)

theorem shcrPostC_eq_tail (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    shcrPostC (Δ := Δ) S K s q =
      caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u) (shcrPostTailC S K s) :=
  rfl

@[expose] def shcr1KeyPreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcr1KeyPostC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (.fst (.snd (v d)))) (.pair (v d) (v s))))

/-- Two-stage `ReductionDsl` program for `shcrReductionKeyInd1KeyCore S b` with extraction bound `Q` and state-list bound `K`. -/
@[expose] def shcrKeyInd1KeyProg (S : Setup) (Q K : Nat) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init := (shcrKeyIndProg S Q K).init
  handlePre := shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  chDone := .ret (scTPk (.var .zero))
  resume := shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero
  handlePost := shcr1KeyPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero

abbrev shcrKeyInd1KeyDslProg (S : Setup) (b : QueryBudget) :=
  shcrKeyInd1KeyProg S b.q_total (keyIndLoopBound b)

/-! ## Syntactic cost, query, and block-size bounds -/

theorem initPrin1KeyB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).cost ≤ (initPrinB (Δ := Δ) K st u).cost := by
  simp only [initPrin1KeyB, initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stUpd, stMk, peMk, rs, rNone, rInitPrin,
    cost_sBytes32, cost_qX25519Base, cost_qSigPkGen, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

theorem initPrin1KeyB_queries_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).queries primW primWS ≤
      (initPrinB (Δ := Δ) K st u).queries primW primWS := by
  simp [initPrin1KeyB, initPrinB, bindV, Comp.queries]

theorem caseSumV_cost_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).cost ≤ (l₂ .zero).cost) :
    (caseSumV e l₁ r).cost ≤ (caseSumV e l₂ r).cost := by
  dsimp only [caseSumV, Comp.cost]
  omega

theorem caseSumV_queries_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).queries primW primWS ≤ (l₂ .zero).queries primW primWS) :
    (caseSumV e l₁ r).queries primW primWS ≤ (caseSumV e l₂ r).queries primW primWS := by
  dsimp only [caseSumV, Comp.queries]
  omega

private theorem securityStepCostBudget_le_legacy (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  refine (security_stepCostBudget_le S b).trans ?_
  unfold stepCostBudget _root_.SignalPqxdh.LegacyCosted.stepCostBudget
  have hEq : 2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 =
      (2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) +
        2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot) +
      (2 ^ 16 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot) +
        63488 * S.N_dh ^ 2 + 130816 * S.N_dh * S.N_sess_tot + 65536 * S.N_sess_tot ^ 2) := by ring
  rw [hEq]
  exact Nat.le_add_right _ _

theorem initPrin1KeyB_size_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).size ≤ (initPrinB (Δ := Δ) K st u).size := by
  simp only [initPrin1KeyB, initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stUpd, stMk, peMk, rs, rNone, rInitPrin,
    sBytes32, qX25519Base, qSigPkGen, v, Comp.size, Expr.size]
  omega

theorem caseSumV_size_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).size ≤ (l₂ .zero).size) :
    (caseSumV e l₁ r).size ≤ (caseSumV e l₂ r).size := by
  dsimp only [caseSumV, Comp.size]
  omega

@[simp] private theorem sh_partnerC_size {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV, qPow8, getDBytes, optBytesEq, eLet2, eLet, eCaseOpt,
    eqB, litB, v, Comp.size, Expr.size]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
    Ops.sum, Sum.elim_inl]

/-! ## Branch evaluation and invariant preservation -/

theorem initPrin1KeyB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (env : Env Δ) (s : KeyIndState S)
    (hs : env.get (Ext.wk st) = keyIndStateToVal s) (hB : KeyIndListsBounded s K)
    (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (initPrin1KeyB K st uV).eval env =
      encRS <$> (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u)).run s := by
  unfold initPrin1KeyB
  core_simp [hs, hu, List.take_of_length_le, hB.principals_le]
  simp only [pqxdhKeyIndImpl1KeyRoPrim]
  by_cases h : (s.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]
  · simp [h, encRS, keyIndRespToVal, keyIndRenc, liftM, sampleScalar32]

theorem pqxdhKeyIndImpl1KeyRoPrim_hol (S : Setup) (n : Nat) (q : KeyIndQuery S)
    (s : KeyIndState S) (hB : KeyIndListsBounded s n) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 (n + 1))
      ((pqxdhKeyIndImpl1KeyRoPrim S q).run s) := by
  cases q with
  | initPrin u =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hB
    simp only [pqxdhKeyIndImpl1KeyRoPrim]
    khol_simp
    split
    · exact HoldsOnLeaves.pure (by khol_leaf)
    · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ => ?_
      khol_simp
      exact HoldsOnLeaves.pure (by khol_leaf)
  | _ =>
    simpa [pqxdhKeyIndImpl1KeyRoPrim, StateT.run_bind, StateT.run_get, pure_bind] using
      pqxdhKeyIndImplPrim_hol true S n _ s hB

theorem pqxdhKeyIndShCrPrimImpl1Key_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhKeyIndShCrPrimImpl1Key true S q).run h) := by
  cases q with
  | initPrin u =>
    simp only [pqxdhKeyIndShCrPrimImpl1Key, liftShCrBasePrim, StateT.run]
    exact HoldsOnLeaves.bind (pqxdhKeyIndImpl1KeyRoPrim_hol S n (.initPrin u) h.base hI.bnd)
      fun p hp => HoldsOnLeaves.pure ⟨hp, hI.tpk, hI.tsk⟩
  | _ =>
    simpa [pqxdhKeyIndShCrPrimImpl1Key] using pqxdhKeyIndShCrPrimImpl_inv S pk sk n _ h hI

theorem shcr1KeyPostC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q)
    (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyPostC S K sV qV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h := by
  cases q with
  | initPrin u =>
    have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
    unfold shcr1KeyPostC pqxdhKeyIndShCrPrimImpl1Key
    simp only [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    refine Eq.trans (b := encSCS sIdx chosen <$>
        (liftShCrBasePrim (S := S) (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u))).run h) ?_ rfl
    exact onBase_eval S _ _ h sIdx chosen (by simpa [Ext.step_wk', Env.get_succ'] using hs) _ _
      (initPrin1KeyB_eval S K _ _ h.base rfl hK _ u rfl)
  | _ =>
    have hEq : (shcr1KeyPostC S K sV qV).eval env = (shcrPostC S K sV qV).eval env := by
      rw [shcrPostC_eq_tail]
      unfold shcr1KeyPostC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcrPostC_eval S K n sV qV env _ h sIdx chosen hs hq hB hn]
    rfl

/-! ## Stage 1 and Stage 2 simulation -/

@[expose] def stepMid1Key (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    OracleComp PrimBaseSpec
      ((KeyIndResponse × KeyIndShCrState S) ⊕ (Bytes × (PauseMid S × KeyIndShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h

theorem shcr1KeyPreC_eval (S : Setup) (K n : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S)
    (sIdx : ℕ) (chosen : Bytes) (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
        (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      Sum.map (encSCS sIdx chosen) (Prod.map id (Prod.map encPause (shcrStToVal · sIdx chosen))) <$>
        stepMid1Key S sIdx q h := by
  have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
  unfold shcr1KeyPreC
  simp only [bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ h sIdx chosen rfl hK _ q rfl]
  simp only [stepMid1Key, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcr1KeyPostC_eval S K n _ _ _ q h sIdx chosen rfl rfl hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, k, e⟩ := d
    simp [Expr.eval, v, encPause, shcrStToVal, preKeyBundleToVal]

theorem stepUntilShCr1Key_eq (S : Setup) (sIdx : ℕ) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    stepUntilShCrFuelKeyInd1KeyPrim S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid1Key S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid1Key S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelKeyInd1KeyPrim S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
    dsimp only
    rw [tryPauseMid_shallow, bind_map_left]
    simp only [stepMid1Key, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | d
    · simp only [Option.map_none, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [Option.map_some, pure_bind]
      rfl

theorem runWithFuelShCr1Key_eq (S : Setup) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    runWithFuelKeyInd1KeyShCrPrim S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) mx fuel h := by
  have := runWithFuelPrim_char false (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) id
    (fun mx fuel h => runWithFuelKeyInd1KeyShCrPrim S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind]) mx fuel h
  rw [this, id_map]

theorem stepMid1Key_inv (S : Setup) (sIdx : ℕ) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid1Key S sIdx q h) := by
  unfold stepMid1Key
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhKeyIndShCrPrimImpl1Key_inv S pk sk n q h hI) fun _ hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩

@[expose] def midRun1Key (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (ℕ × (Option Bytes ×
      RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :=
  if S.N_spk_tot * S.N_send_tot = 0 then do
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1Key S 0) A.run b.q_total
      (initSh S secb 0 pk sk)
    pure (0, r)
  else do
    let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
    let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
    let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
    pure (sIdx, r)

@[expose] def midAdv1Key (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) : KemShCrAdv where
  State := Bytes × Bytes × ℕ × (Option Bytes ×
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))
  choosePk := fun pk sk => (fun x => (chosenOf pk x.2.2, (pk, sk, x))) <$> midRun1Key S b A pk sk
  findCollision := fun st => findCollisionKeyInd1KeyPrim S b (toShallow st)
  q_prim := primQueryBudget S b

theorem kemShCrExp_mid1Key_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : KeyIndAdversary S) :
    KemShCr P (shcrReductionKeyInd1KeyCore S b A) = KemShCr P (midAdv1Key S b A) := by
  refine SignalPqxdh.Security.ReductionDsl.AuthHs.kemShCr_eq_of_choosePk_spk_send
    P S (shcrReductionKeyInd1KeyCore S b A) (midAdv1Key S b A) toShallow
    (fun bIdx sIdx pk sk => do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk)
      pure (chosenOf pk r.2, (pk, sk, sIdx, r))) ?_ ?_ (fun _ _ _ => rfl)
  · intro pk sk
    simp only [shcrReductionKeyInd1KeyCore, choosePkKeyInd1KeyPrimAt, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr1Key_eq, bind_map_left]
    refine bind_congr fun r => ?_
    obtain ⟨c, st⟩ := r
    rcases st with ⟨a, h⟩ | ⟨q, d, h, k⟩ <;> rfl
  · intro pk sk
    simp only [midAdv1Key, midRun1Key]
    split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

@[expose] def stepPreD1Key (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec ((KeyIndResponse × shcrStTy.denote) ⊕
      (Bytes × (pauseTy.denote × shcrStTy.denote))) :=
  (shcrKeyInd1KeyProg S Q K).handlePre.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote ⊕ (Bytes × (pauseTy.denote × shcrStTy.denote))) => match x with
    | .inl (rVal, st') => pure (.inl (valToKeyIndResp rVal, st'))
    | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))

theorem stepPreD1Key_eq (S : Setup) (Q K K' : ℕ) (sIdx : ℕ) (pk sk : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk K' h) (hK : K' + 1 ≤ K) :
    stepPreD1Key S Q K q (shcrStToVal h sIdx pk) =
      Sum.map (Prod.map id (shcrStToVal · sIdx pk))
        (Prod.map id (Prod.map encPause (shcrStToVal · sIdx pk))) <$> stepMid1Key S sIdx q h := by
  unfold stepPreD1Key
  have hpre : (shcrKeyInd1KeyProg S Q K).handlePre.eval
      (.cons (shcrStToVal h sIdx pk) (.cons (keyIndQueryToVal q) .nil)) = _ :=
    shcr1KeyPreC_eval S K K' q h sIdx pk hI.bnd hK
  rw [hpre, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h'⟩ | ⟨c, d, h'⟩
  · have hr : valToKeyIndResp (keyIndRespToVal r) = r := keyIndRdec_keyIndRenc r
    simp only [Function.comp_apply, Sum.map_inl, encSCS, Prod.map, id]
    erw [pure_bind]
    simp only [hr]
  · rfl

theorem eval1_1Key_unfold (S : Setup) (Q K : ℕ) (A : KeyIndAdversary S) (pk sk : Bytes)
    (fuel : ℕ) :
    (shcrKeyInd1KeyProg S Q K).eval1 (fun _ => A.run) (pk, sk) fuel false =
    (do
      let (_, st0) ← (shcrKeyInd1KeyProg S Q K).init.eval (.cons (pk, sk) .nil)
      let r : Option Bytes × RedProg2State (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote ←
          stepUntilPauseFuel false (stepPreD1Key S Q K) A.run fuel st0
      match r with
      | (_, .done aOut stFinal) => do
        let v ← (shcrKeyInd1KeyProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
        pure (v, .done aOut stFinal)
      | (c?, .paused gq p stPaused c) =>
        let ch1 := c?.getD pk
        pure (ch1, .paused gq ch1 p stPaused c) :
      OracleComp PrimBaseSpec (Bytes × Mid (keyIndSpec S) Bool pauseTy.denote
        shcrStTy.denote Bytes)) := by
  unfold TwoStageCostedReduction.eval1
  refine bind_congr (m := OracleComp PrimBaseSpec) fun ast0 => ?_
  rcases ast0 with ⟨a, st0⟩
  dsimp only
  rw [GRed2_run1_eq_stepUntilPauseFuel (shcrKeyInd1KeyProg S Q K) false pk A.run fuel st0,
    bind_map_left]
  refine bind_congr2 ?_ fun r => ?_
  · congr 1; funext q st; unfold stepPreD1Key
    refine bind_congr fun x => ?_
    rcases x with ⟨_, _⟩ | ⟨_, _, _⟩ <;> rfl
  rcases r with ⟨c?, ⟨aOut, stFinal⟩ | ⟨gq, p, stPaused, c⟩⟩ <;> rfl

theorem stepRun1Key_bounded (S : Setup) (Q K Ks sIdx : ℕ) (pk sk : Bytes) (A : KeyIndAdversary S)
    (h0 : KeyIndShCrState S) (hI0 : ShInv pk sk 0 h0)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) Ks)
    (hK : Ks + 1 ≤ K) :
    HoldsOnLeaves (Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) Ks)
        (stepUntilPauseFuel false (stepMid1Key S sIdx) A.run Ks h0) ∧
      stepUntilPauseFuel false (stepPreD1Key S Q K) A.run Ks (shcrStToVal h0 sIdx pk) =
        Prod.map id (RedProg2State.mapSt encPause (shcrStToVal · sIdx pk)) <$>
          stepUntilPauseFuel false (stepMid1Key S sIdx) A.run Ks h0 :=
  stepUntilPauseFuel_map_boundedC false encPause (shcrStToVal · sIdx pk)
    (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) (fun hnm hI => ShInv.mono hnm hI)
    (stepMid1Key S sIdx) (stepPreD1Key S Q K) Ks
    (fun _ q st hn hI => stepPreD1Key_eq S Q K _ sIdx pk sk q st hI (by omega))
    (fun n q st hI => stepMid1Key_inv S sIdx pk sk n q st hI) A.run Ks hA Ks 0 h0 hI0 (by omega)

theorem midRun1Key_inv (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total) :
    HoldsOnLeaves
      (fun x => Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total x.2)
      (midRun1Key S b A pk sk) := by
  unfold midRun1Key
  split_ifs
  · refine HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1Key_bounded S b.q_total (b.q_total + 1) b.q_total 0 pk sk A
      (initSh S secb 0 pk sk) (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr
  · refine HoldsOnLeaves.bind_const _ fun uIdx => HoldsOnLeaves.bind_const _ fun jIdx =>
      HoldsOnLeaves.bind_const _ fun sIdx => HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1Key_bounded S b.q_total (b.q_total + 1) b.q_total sIdx pk sk A
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
      (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr

theorem shcr1KeyInit_eval (S : Setup) (Q K : ℕ) (pk sk : Bytes) :
    (shcrKeyInd1KeyProg S Q K).init.eval (.cons (pk, sk) .nil) =
      if S.N_spk_tot * S.N_send_tot = 0 then (do
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb 0 pk sk) 0 pk))
      else (do
        let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
        let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb (uIdx * S.N_recv + jIdx) pk sk) sIdx pk)) :=
  shcrInit_eval S Q K pk sk

theorem eval1_1Key_eq (S : Setup) (Q K : ℕ) (b : QueryBudget) (A : KeyIndAdversary S)
    (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    (shcrKeyInd1KeyProg S Q K).eval1 (fun _ => A.run) (pk, sk) b.q_total false =
    (fun x => (chosenOf pk x.2.2, encMid pk x)) <$> midRun1Key S b A pk sk := by
  have hBody : ∀ bIdx sIdx secb,
      (stepUntilPauseFuel false (stepPreD1Key S Q K) A.run b.q_total
        (shcrStToVal (initSh S secb bIdx pk sk) sIdx pk) >>= fun r =>
        match r with
        | (_, .done aOut stFinal) => do
          let v ← (shcrKeyInd1KeyProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
          pure (v, .done aOut stFinal)
        | (c?, .paused gq p stPaused c) =>
          let ch1 := c?.getD pk
          pure (ch1, .paused gq ch1 p stPaused c)) =
      (stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk) >>= fun r =>
        pure (chosenOf pk r.2, encMid pk (sIdx, r))) := by
    intro bIdx sIdx secb
    obtain ⟨hInv, hEq⟩ := stepRun1Key_bounded S Q K b.q_total sIdx pk sk A
      (initSh S secb bIdx pk sk) (initSh_inv _ _ _ _ _) hA hK
    erw [hEq, bind_map_left]
    refine hInv.bind_congr _ _ fun r hr => ?_
    obtain ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ := r
    · obtain ⟨rfl, hI⟩ := hr
      simp [shcrKeyInd1KeyProg, Comp.eval, Expr.eval, shcrStToVal, chosenOf, encMid,
        RedProg2State.mapSt, hI.tpk]
    · obtain ⟨rfl, -⟩ := hr
      rfl
  rw [eval1_1Key_unfold, shcr1KeyInit_eval]
  unfold midRun1Key
  split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · refine bind_congr fun secb => hBody 0 0 secb
  · refine bind_congr fun uIdx => bind_congr fun jIdx => bind_congr fun sIdx =>
      bind_congr fun secb => hBody (uIdx * S.N_recv + jIdx) sIdx secb

/-! ## DSL adversary, semantic bounds, and advantage equality -/

@[expose] def shcrKeyInd1KeyDslAdvK (S : Setup) (b : QueryBudget) (K : ℕ) (A : KeyIndAdversary S) :
    KemShCrAdv where
  State := Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes
  choosePk := fun pk sk =>
    (shcrKeyInd1KeyProg S b.q_total K).eval1 (fun _ => A.run) (pk, sk) b.q_total false
  findCollision := fun st ss ct =>
    (shcrKeyInd1KeyProg S b.q_total K).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

/-- `KemShCr` adversary obtained by running `shcrKeyInd1KeyDslProg S b`. -/
@[expose] def shcrKeyInd1KeyDslAdv (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrAdv :=
  shcrKeyInd1KeyDslAdvK S b (keyIndLoopBound b) A.1

@[expose] def stepPostD1Key (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec (KeyIndResponse × shcrStTy.denote) :=
  (shcrKeyInd1KeyProg S Q K).handlePost.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote) => pure (valToKeyIndResp x.1, x.2)

theorem stepPostD1Key_eq (S : Setup) (Q K Ks sIdx : ℕ) (pk sk chosen : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk Ks h) (hK : Ks + 1 ≤ K) :
    stepPostD1Key S Q K q (shcrStToVal h sIdx chosen) =
      Prod.map id (shcrStToVal · sIdx chosen) <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h := by
  unfold stepPostD1Key
  have hpost : (shcrKeyInd1KeyProg S Q K).handlePost.eval
      (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h :=
    shcr1KeyPostC_eval S K Ks (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero _ q h sIdx chosen rfl rfl hI.bnd hK
  rw [hpost, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  have hr : valToKeyIndResp (keyIndRespToVal x.1) = x.1 := keyIndRdec_keyIndRenc x.1
  simp only [Function.comp_apply, encSCS, Prod.map, id]
  erw [pure_bind]
  simp only [hr]

theorem eval2_1Key_done (S : Setup) (Q K fuel : ℕ) (a : Bool) (st : shcrStTy.denote)
    (ss ct : Bytes) :
    (shcrKeyInd1KeyProg S Q K).eval2 (.done a st) (ss, ct) fuel false =
    (shcrKeyIndProg S Q K).finish.eval (.cons st (.cons a (.cons (ss, ct) .nil))) := by
  simp only [TwoStageCostedReduction.eval2, pure_bind]; rfl

theorem eval2_1Key_paused (S : Setup) (Q K fuel : ℕ) (q : KeyIndQuery S) (ch : Bytes)
    (p : pauseTy.denote) (st : shcrStTy.denote)
    (k : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool)
    (ss ct : Bytes) :
    (shcrKeyInd1KeyProg S Q K).eval2 (.paused q ch p st k) (ss, ct) fuel false =
    ((shcrKeyIndProg S Q K).resume.eval (.cons st (.cons p (.cons (ss, ct) .nil))) >>=
      fun (x : SCS.denote) => runWithFuelPrim false (stepPostD1Key S Q K)
        (k (valToKeyIndResp x.1)) fuel x.2 >>= fun (y : Bool × shcrStTy.denote) =>
      (shcrKeyIndProg S Q K).finish.eval (.cons y.2 (.cons y.1 (.cons (ss, ct) .nil)))) := by
  simp only [TwoStageCostedReduction.eval2]
  refine bind_congr fun x => ?_
  rw [runFuel_pqPrimIface_eq_runWithFuelPrim]
  rfl

theorem kemShCrExp_dsl1Key_mid (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    kemShCrExp P (shcrKeyInd1KeyDslAdvK S b K A) = kemShCrExp P (midAdv1Key S b A) := by
  refine kemShCrExp_congr P (midAdv1Key S b A) (shcrKeyInd1KeyDslAdvK S b K A)
    (fun st => Stage1InvC (ShInv st.1 st.2.1) (fun d : PauseMid S => d.2.1.pqspkB)
      b.q_total st.2.2.2)
    (fun st => encMid st.1 st.2.2) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrKeyInd1KeyDslAdvK, midAdv1Key]
    rw [eval1_1Key_eq S b.q_total K b A pk sk hA hK, Functor.map_map]
  · intro pk sk
    simp only [midAdv1Key]
    exact HoldsOnLeaves.map _ (midRun1Key_inv S b A pk sk hA) fun _ hx => hx
  · rintro ⟨pk, sk, sIdx, c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ ⟨_, hI⟩ ss ct
    · have hI' : ShInv pk sk b.q_total h := hI
      show (shcrKeyInd1KeyProg S b.q_total K).eval2
          (.done a (shcrStToVal h sIdx pk)) (ss, ct) b.q_total false =
        findCollisionKeyInd1KeyPrim S b (pk, sk, pk, .inl (a, h)) ss ct
      erw [eval2_1Key_done, shcrFinish_eval]
      simp only [findCollisionKeyInd1KeyPrim, pure_bind, hI'.tpk, hI'.tsk]
    · obtain ⟨n, r, hIn, hnr, hk⟩ := hI
      show (shcrKeyInd1KeyProg S b.q_total K).eval2
          (.paused q d.2.1.pqspkB (encPause d) (shcrStToVal h sIdx pk) k) (ss, ct) b.q_total
          false =
        findCollisionKeyInd1KeyPrim S b (pk, sk, d.2.1.pqspkB, .inr (toPaused h k d)) ss ct
      erw [eval2_1Key_paused, shcrResume_eval S _ K d h sIdx pk ss ct (hIn.bnd.mono (by omega))]
      erw [bind_map_left]
      simp only [findCollisionKeyInd1KeyPrim, resumePausedKeyInd1KeyPrim, toPaused, bind_assoc]
      refine (postKem_inv S pk sk n d h hIn ss ct).bind_congr _ _ fun p hp => ?_
      obtain ⟨resp, h'⟩ := p
      have hr : valToKeyIndResp (keyIndRespToVal resp) = resp := keyIndRdec_keyIndRenc resp
      dsimp only [encSCS]
      rw [hr]
      obtain ⟨hInvR, hEqR⟩ := runWithFuelPrim_map_bounded false (shcrStToVal · sIdx d.2.1.pqspkB)
        (fun n h => ShInv pk sk n h) (fun hnm hI => ShInv.mono hnm hI)
        (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) (stepPostD1Key S b.q_total K)
        b.q_total (fun q st hI => stepPostD1Key_eq S b.q_total K b.q_total sIdx pk sk _ q st hI hK)
        (fun n q st hI => pqxdhKeyIndShCrPrimImpl1Key_inv S pk sk n q st hI) (k resp) r (hk resp)
        b.q_total (n + 1) h' hp (by omega)
      rw [hEqR, bind_map_left, runWithFuelShCr1Key_eq]
      refine hInvR.bind_congr _ _ fun y hy => ?_
      obtain ⟨a, hf⟩ := y
      dsimp only [Prod.map, id]
      erw [shcrFinish_eval]
      rw [hy.tpk, hy.tsk]

theorem kemShCrExp_shcrKeyInd1KeyDslAdvK_of_queryBound (P : Primitives) (S : Setup) (b : QueryBudget)
    (K : ℕ) (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyInd1KeyDslAdvK S b K A) =
      KemShCr P (shcrReductionKeyInd1KeyCore S b A) := by
  have hDslMid : KemShCr P (shcrKeyInd1KeyDslAdvK S b K A) = KemShCr P (midAdv1Key S b A) := by
    unfold KemShCr
    rw [kemShCrExp_dsl1Key_mid P S b K A hA hK]
  rw [hDslMid, ← kemShCrExp_mid1Key_core]

theorem kemShCrExp_shcrKeyInd1KeyDslAdvK (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : BoundedAdv (KeyIndAdversary S) b) (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyInd1KeyDslAdvK S b K A.1) =
      KemShCr P (shcrReductionKeyInd1Key S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    have h := A.2.2.2.2.1
    convert h using 1; funext q; cases q <;> rfl
  exact kemShCrExp_shcrKeyInd1KeyDslAdvK_of_queryBound P S b K A.1 hA hK

theorem kemShCrExp_shcrKeyInd1KeyDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyDslAdv S b A) = KemShCr P (shcrReductionKeyInd1Key S b A) :=
  kemShCrExp_shcrKeyInd1KeyDslAdvK P S b (keyIndLoopBound b) A (by
    change b.q_total + 1 ≤ 2 * b.q_total + 1; omega)

/-- Exact `KemShCr` advantage equality between `shcrKeyInd1KeyDslAdv` and `shcrReductionKeyInd1Key`. -/
theorem KemShCr_shcrKeyInd1KeyDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyDslAdv S b A) = KemShCr P (shcrReductionKeyInd1Key S b A) :=
  kemShCrExp_shcrKeyInd1KeyDslAdv P S b A

end SignalPqxdh.Security.ReductionDsl.KeyInd
