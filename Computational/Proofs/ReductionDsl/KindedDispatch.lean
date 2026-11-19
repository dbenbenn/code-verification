/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.KindedCost
public import Computational.Proofs.ReductionDsl.KindedQueries -- proof-setup: allow-public-import

/-!
# Per-Query-Kind Dispatch and `CostBoundedByKind` Assembly

Defines the multi-step pure dispatch relation `DispatchesTo` for `ReductionDsl` handlers, tracking
exact dispatch cost while preserving `queriesAt` and `eval`. Provides combinators assembling
one-stage and two-stage `CostBoundedByKind` and `QueriesBoundedByKind` from per-arm bounds.
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (
  Sig Ty Var Expr Comp Env Ops Samplers Iface GameCodec
  CostedReduction TwoStageCostedReduction
)

namespace Computational.Proofs.ReductionDsl.KindedDispatch

section PointwiseSteps

variable {S : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem pureEval?_ret {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) (ρ : Env Γ) :
    (Comp.ret e : Comp O I Γ t).pureEval? ρ = some (e.eval ρ) :=
  rfl

theorem pureEval?_bind_ret {Γ : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    ((Comp.ret e).bind k).pureEval? ρ = k.pureEval? (.cons (e.eval ρ) ρ) :=
  rfl

theorem costAt_bind_of_pureEval?_le {Γ : List (Ty S)} {t u : Ty S}
    (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) {x : t.denote} {cc ck : ℕ}
    (hp : c.pureEval? ρ = some x) (hc : c.costAt ρ ≤ cc) (hk : k.costAt (.cons x ρ) ≤ ck) :
    (c.bind k).costAt ρ ≤ ck + (cc + 1) := by
  have h := Comp.costAt_bind_of_pureEval? c k ρ hp
  omega

theorem costAt_bind_le_cost_right {Γ : List (Ty S)} {t u : Ty S}
    (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) {cc : ℕ}
    (hc : c.costAt ρ ≤ cc) :
    (c.bind k).costAt ρ ≤ cc + k.cost + 1 := by
  simp only [Comp.costAt]
  rcases c.pureEval? ρ with _ | x <;> dsimp only
  · omega
  · have hk := k.costAt_le_cost (.cons x ρ)
    omega

theorem costAt_caseOpt_none {Γ : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ (.opt t)) (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u)
    (ρ : Env Γ) (he : e.eval ρ = none) :
    (Comp.caseOpt e n s).costAt ρ = e.costAt ρ + n.costAt ρ + 1 := by
  simp [Comp.costAt, he]

theorem costAt_caseOpt_some {Γ : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ (.opt t)) (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u)
    (ρ : Env Γ) {x : t.denote} (he : e.eval ρ = some x) :
    (Comp.caseOpt e n s).costAt ρ = e.costAt ρ + s.costAt (.cons x ρ) + 1 := by
  simp [Comp.costAt, he]

end PointwiseSteps

section DispatchSpine

variable {S : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}
  {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}

/-- Multi-step pure dispatch relation from `(c, ρ)` to `(arm, ρ')` with exact step cost `d`. -/
inductive DispatchesTo :
    ∀ {Γ Δ : List (Ty S)} {u : Ty S},
      Comp O I Γ u → Env Γ → ℕ → Comp O I Δ u → Env Δ → Prop where
  | refl {Γ : List (Ty S)} {u : Ty S} (arm : Comp O I Γ u) (ρ : Env Γ) :
      DispatchesTo arm ρ 0 arm ρ
  | caseSum_inl {Γ Δ : List (Ty S)} {t₁ t₂ u : Ty S}
      {e : Expr O Γ (.sum t₁ t₂)} {l : Comp O I (t₁ :: Γ) u} {r : Comp O I (t₂ :: Γ) u}
      {ρ : Env Γ} {x : t₁.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (he : e.eval ρ = .inl x)
      (h : DispatchesTo l (.cons x ρ) d arm ρ') :
      DispatchesTo (.caseSum e l r) ρ (d + e.costAt ρ + 1) arm ρ'
  | caseSum_inr {Γ Δ : List (Ty S)} {t₁ t₂ u : Ty S}
      {e : Expr O Γ (.sum t₁ t₂)} {l : Comp O I (t₁ :: Γ) u} {r : Comp O I (t₂ :: Γ) u}
      {ρ : Env Γ} {y : t₂.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (he : e.eval ρ = .inr y)
      (h : DispatchesTo r (.cons y ρ) d arm ρ') :
      DispatchesTo (.caseSum e l r) ρ (d + e.costAt ρ + 1) arm ρ'
  | ite_true {Γ Δ : List (Ty S)} {u : Ty S}
      {b : Expr O Γ .bool} {c₁ c₂ : Comp O I Γ u}
      {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (hb : b.eval ρ = true)
      (h : DispatchesTo c₁ ρ d arm ρ') :
      DispatchesTo (.ite b c₁ c₂) ρ (d + b.costAt ρ + 1) arm ρ'
  | ite_false {Γ Δ : List (Ty S)} {u : Ty S}
      {b : Expr O Γ .bool} {c₁ c₂ : Comp O I Γ u}
      {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (hb : b.eval ρ = false)
      (h : DispatchesTo c₂ ρ d arm ρ') :
      DispatchesTo (.ite b c₁ c₂) ρ (d + b.costAt ρ + 1) arm ρ'
  | caseOpt_none {Γ Δ : List (Ty S)} {t u : Ty S}
      {e : Expr O Γ (.opt t)} {n : Comp O I Γ u} {s : Comp O I (t :: Γ) u}
      {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (he : e.eval ρ = none)
      (h : DispatchesTo n ρ d arm ρ') :
      DispatchesTo (.caseOpt e n s) ρ (d + e.costAt ρ + 1) arm ρ'
  | caseOpt_some {Γ Δ : List (Ty S)} {t u : Ty S}
      {e : Expr O Γ (.opt t)} {n : Comp O I Γ u} {s : Comp O I (t :: Γ) u}
      {ρ : Env Γ} {x : t.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (he : e.eval ρ = some x)
      (h : DispatchesTo s (.cons x ρ) d arm ρ') :
      DispatchesTo (.caseOpt e n s) ρ (d + e.costAt ρ + 1) arm ρ'
  | bind_pure {Γ Δ : List (Ty S)} {t u : Ty S}
      {c : Comp O I Γ t} {k : Comp O I (t :: Γ) u}
      {ρ : Env Γ} {x : t.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
      (hc : c.pureEval? ρ = some x)
      (h : DispatchesTo k (.cons x ρ) d arm ρ') :
      DispatchesTo (.bind c k) ρ (d + c.costAt ρ + 1) arm ρ'

theorem DispatchesTo.letV {Γ Δ : List (Ty S)} {t u : Ty S}
    {e : Expr O Γ t} {k : Comp O I (t :: Γ) u}
    {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo k (.cons (e.eval ρ) ρ) d arm ρ') :
    DispatchesTo ((Comp.ret e).bind k) ρ (d + (e.costAt ρ + 1) + 1) arm ρ' :=
  DispatchesTo.bind_pure (pureEval?_ret e ρ) h

theorem DispatchesTo.letV_var {Γ Δ : List (Ty S)} {t u : Ty S}
    {v : Var Γ t} {k : Comp O I (t :: Γ) u}
    {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo k (.cons (ρ.get v) ρ) d arm ρ') :
    DispatchesTo ((Comp.ret (.var v)).bind k) ρ (d + 3) arm ρ' :=
  DispatchesTo.letV (e := .var v) h

theorem DispatchesTo.caseSum_var_inl {Γ Δ : List (Ty S)} {t₁ t₂ u : Ty S}
    {v : Var Γ (.sum t₁ t₂)} {l : Comp O I (t₁ :: Γ) u} {r : Comp O I (t₂ :: Γ) u}
    {ρ : Env Γ} {x : t₁.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (hv : ρ.get v = .inl x)
    (h : DispatchesTo l (.cons x ρ) d arm ρ') :
    DispatchesTo (.caseSum (.var v) l r) ρ (d + 2) arm ρ' :=
  DispatchesTo.caseSum_inl (e := .var v) hv h

theorem DispatchesTo.caseSum_var_inr {Γ Δ : List (Ty S)} {t₁ t₂ u : Ty S}
    {v : Var Γ (.sum t₁ t₂)} {l : Comp O I (t₁ :: Γ) u} {r : Comp O I (t₂ :: Γ) u}
    {ρ : Env Γ} {y : t₂.denote} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (hv : ρ.get v = .inr y)
    (h : DispatchesTo r (.cons y ρ) d arm ρ') :
    DispatchesTo (.caseSum (.var v) l r) ρ (d + 2) arm ρ' :=
  DispatchesTo.caseSum_inr (e := .var v) hv h

theorem costAt_eq_of_dispatchesTo {Γ Δ : List (Ty S)} {u : Ty S}
    {c : Comp O I Γ u} {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo c ρ d arm ρ') :
    c.costAt ρ = arm.costAt ρ' + d := by
  induction h with
  | refl => omega
  | caseSum_inl he _ ih =>
    rw [Comp.costAt_caseSum_inl _ _ _ _ he, ih]; omega
  | caseSum_inr he _ ih =>
    rw [Comp.costAt_caseSum_inr _ _ _ _ he, ih]; omega
  | ite_true hb _ ih =>
    simp only [Comp.costAt, hb, ite_true, ih]; omega
  | ite_false hb _ ih =>
    simp only [Comp.costAt, hb, Bool.false_eq_true, ite_false, ih]; omega
  | caseOpt_none he _ ih =>
    rw [costAt_caseOpt_none _ _ _ _ he, ih]; omega
  | caseOpt_some he _ ih =>
    rw [costAt_caseOpt_some _ _ _ _ he, ih]; omega
  | bind_pure hc _ ih =>
    rw [Comp.costAt_bind_of_pureEval? _ _ _ hc, ih]; omega

theorem costAt_le_arm_cost_of_dispatchesTo {Γ Δ : List (Ty S)} {u : Ty S}
    {c : Comp O I Γ u} {ρ : Env Γ} {d cDisp : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo c ρ d arm ρ') (hd : d ≤ cDisp) :
    c.costAt ρ ≤ arm.cost + cDisp := by
  have hEq := costAt_eq_of_dispatchesTo h
  have hArm := arm.costAt_le_cost ρ'
  omega

theorem queriesAt_eq_of_dispatchesTo (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List (Ty S)} {u : Ty S}
    {c : Comp O I Γ u} {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo c ρ d arm ρ') :
    c.queriesAt w ws ρ = arm.queriesAt w ws ρ' := by
  induction h with
  | refl => rfl
  | caseSum_inl he _ ih =>
    rw [Comp.queriesAt_caseSum_inl w ws _ _ _ _ he, ih]
  | caseSum_inr he _ ih =>
    rw [Comp.queriesAt_caseSum_inr w ws _ _ _ _ he, ih]
  | ite_true hb _ ih =>
    simp only [Comp.queriesAt, hb, ite_true, ih]
  | ite_false hb _ ih =>
    simp only [Comp.queriesAt, hb, Bool.false_eq_true, ite_false, ih]
  | caseOpt_none he _ ih =>
    simp only [Comp.queriesAt, he, ih]
  | caseOpt_some he _ ih =>
    simp only [Comp.queriesAt, he, ih]
  | bind_pure hc _ ih =>
    have h0 := Comp.queriesAt_eq_zero_of_pureEval? w ws _ _ hc
    simp only [Comp.queriesAt, hc, h0, zero_add, ih]

theorem queriesAt_le_arm_queries_of_dispatchesTo (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List (Ty S)} {u : Ty S}
    {c : Comp O I Γ u} {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo c ρ d arm ρ') :
    c.queriesAt w ws ρ ≤ arm.queries w ws := by
  rw [queriesAt_eq_of_dispatchesTo w ws h]
  exact arm.queriesAt_le_queries w ws ρ'

theorem eval_eq_of_dispatchesTo {Γ Δ : List (Ty S)} {u : Ty S}
    {c : Comp O I Γ u} {ρ : Env Γ} {d : ℕ} {arm : Comp O I Δ u} {ρ' : Env Δ}
    (h : DispatchesTo c ρ d arm ρ') :
    c.eval ρ = arm.eval ρ' := by
  induction h with
  | refl => rfl
  | caseSum_inl he _ ih => simp only [Comp.eval, he, ih]
  | caseSum_inr he _ ih => simp only [Comp.eval, he, ih]
  | ite_true hb _ ih => simp only [Comp.eval, hb, ite_true, ih]
  | ite_false hb _ ih => simp only [Comp.eval, hb, Bool.false_eq_true, ite_false, ih]
  | caseOpt_none he _ ih => simp only [Comp.eval, he, ih]
  | caseOpt_some he _ ih => simp only [Comp.eval, he, ih]
  | bind_pure hc _ ih =>
    rw [Comp.eval, Comp.eval_eq_pure_of_pureEval? _ _ hc, pure_bind, ih]

/-- Bounds `R.handle.costAt` by `arm.cost + cDisp` when `R.handle` dispatches to `arm` in cost at
most `cDisp`. -/
theorem handle_costAt_le_of_dispatchesTo
    (R : CostedReduction O I G C rIn aIn aOut out)
    (s : R.σ.denote) (t : κ) {Δ : List (Ty S)}
    {d cDisp : ℕ} {arm : Comp O I Δ (.prod C.R R.σ)} {ρ' : Env Δ}
    (hDisp : DispatchesTo R.handle (.cons s (.cons (C.qenc t) .nil)) d arm ρ')
    (hd : d ≤ cDisp) :
    R.handle.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ arm.cost + cDisp :=
  costAt_le_arm_cost_of_dispatchesTo hDisp hd

end DispatchSpine

section Assembly

variable {S : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}
  {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}

/-- Assembles `CostedReduction.CostBoundedByKind` from per-kind handler cost bounds and total
cost. -/
theorem costBoundedByKind_of_armCosts
    (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (kind : κ → Fin n) (hCost qKind : Fin n → ℕ) {B : ℕ}
    (hArm : ∀ (s : R.σ.denote) (t : κ),
      R.handle.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t))
    (hTot :
      R.init.cost +
        (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum +
        R.finish.cost ≤ B) :
    R.CostBoundedByKind kind qKind B :=
  ⟨hCost, hArm, hTot⟩

/-- Assembles `TwoStageCostedReduction.CostBoundedByKind` from stage-1 and stage-2 per-kind handler
cost bounds. -/
theorem twoStageCostBoundedByKind_of_armCosts
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) (hCost qKind : Fin n → ℕ) {B : ℕ}
    (hPre : ∀ (s : R.σ.denote) (t : κ),
      R.handlePre.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t))
    (hPost : ∀ (s : R.σ.denote) (t : κ),
      R.handlePost.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t))
    (hTot :
      R.init.cost +
        (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum +
        max R.chDone.cost R.resume.cost + R.finish.cost ≤ B) :
    R.CostBoundedByKind kind qKind B :=
  ⟨hCost, fun s t => ⟨hPre s t, hPost s t⟩, hTot⟩

theorem list_ofFn_fin2_sum (f : Fin 2 → ℕ) : (List.ofFn f).sum = f 0 + f 1 := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil, add_zero]
  rfl

theorem costBoundedByKind_fin2_of_armCosts
    (R : CostedReduction O I G C rIn aIn aOut out)
    (kind : κ → Fin 2) (qKind : Fin 2 → ℕ) {c0 c1 B : ℕ}
    (h0 : ∀ (s : R.σ.denote) (t : κ), kind t = 0 →
      R.handle.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c0)
    (h1 : ∀ (s : R.σ.denote) (t : κ), kind t = 1 →
      R.handle.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c1)
    (hTot :
      R.init.cost +
        qKind 0 * max I.uCost (c0 + C.codecCost) +
        qKind 1 * max I.uCost (c1 + C.codecCost) +
        R.finish.cost ≤ B) :
    R.CostBoundedByKind kind qKind B := by
  let hCost : Fin 2 → ℕ := fun i => if i.val = 0 then c0 else c1
  refine costBoundedByKind_of_armCosts R kind hCost qKind (fun s t => ?_) ?_
  · rcases hkt : kind t with ⟨_ | _ | k, hk⟩
    · exact h0 s t (by ext; simp [hkt])
    · exact h1 s t (by ext; simp [hkt])
    · omega
  · have h0v : hCost 0 = c0 := rfl
    have h1v : hCost 1 = c1 := rfl
    rw [list_ofFn_fin2_sum, h0v, h1v]
    omega

theorem twoStageCostBoundedByKind_fin2_of_armCosts
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (kind : κ → Fin 2) (qKind : Fin 2 → ℕ) {c0 c1 B : ℕ}
    (hPre0 : ∀ (s : R.σ.denote) (t : κ), kind t = 0 →
      R.handlePre.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c0)
    (hPost0 : ∀ (s : R.σ.denote) (t : κ), kind t = 0 →
      R.handlePost.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c0)
    (hPre1 : ∀ (s : R.σ.denote) (t : κ), kind t = 1 →
      R.handlePre.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c1)
    (hPost1 : ∀ (s : R.σ.denote) (t : κ), kind t = 1 →
      R.handlePost.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ c1)
    (hTot :
      R.init.cost +
        qKind 0 * max I.uCost (c0 + C.codecCost) +
        qKind 1 * max I.uCost (c1 + C.codecCost) +
        max R.chDone.cost R.resume.cost + R.finish.cost ≤ B) :
    R.CostBoundedByKind kind qKind B := by
  let hCost : Fin 2 → ℕ := fun i => if i.val = 0 then c0 else c1
  refine twoStageCostBoundedByKind_of_armCosts R kind hCost qKind
    (fun s t => ?_) (fun s t => ?_) ?_
  · rcases hkt : kind t with ⟨_ | _ | k, hk⟩
    · exact hPre0 s t (by ext; simp [hkt])
    · exact hPre1 s t (by ext; simp [hkt])
    · omega
  · rcases hkt : kind t with ⟨_ | _ | k, hk⟩
    · exact hPost0 s t (by ext; simp [hkt])
    · exact hPost1 s t (by ext; simp [hkt])
    · omega
  · have h0v : hCost 0 = c0 := rfl
    have h1v : hCost 1 = c1 := rfl
    rw [list_ofFn_fin2_sum, h0v, h1v]
    omega

end Assembly

namespace ToyTests

@[expose] def toySig : Sig where
  Base := Empty
  den := Empty.elim
  sz := fun b => b.elim

@[expose] def toyOps : Ops toySig where
  Op := Empty
  dom := Empty.elim
  cod := Empty.elim
  eval := fun o => o.elim
  cost := Empty.elim

@[expose] def toyTargetSpec : OracleSpec Empty := fun i => i.elim

@[expose] def toyIface : Iface toySig toyTargetSpec where
  fwdU := fun _ => pure 0
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun g => g.elim
  dec := fun g => g.elim
  qCost := Empty.elim
  smp := Samplers.empty

@[expose] def ToyQuery : Type := Unit ⊕ ℕ

@[expose] def toyGameSpec : OracleSpec ToyQuery := fun _ => ℕ

@[expose] def toyKind : ToyQuery → Fin 2
  | .inl () => 0
  | .inr _ => 1

@[expose] def toyCodec : GameCodec toySig toyGameSpec where
  Q := .sum .unit .nat
  R := .nat
  qenc := id
  rdec := fun _ n => n
  codecCost := 4

@[expose] def toyHeavyArm :
    Comp toyOps toyIface [.unit, .sum .unit .nat, .nat, .sum .unit .nat] (.prod .nat .nat) :=
  .bind (.iter 100 (.nat 0) (.ret .v0)) (.ret (.pair .v0 .v3))

@[expose] def toyFastArm :
    Comp toyOps toyIface [.nat, .sum .unit .nat, .nat, .sum .unit .nat] (.prod .nat .nat) :=
  .ret (.pair .v0 .v2)

@[expose] def toy1StageRed :
    CostedReduction toyOps toyIface toyGameSpec toyCodec .unit .unit .bool .nat where
  σ := .nat
  init := .ret (.pair .unit (.nat 0))
  handle := (Comp.ret .v1).bind (.caseSum .v0 toyHeavyArm toyFastArm)
  finish := .ret .v0

@[expose] def toyHeavyPreArm :
    Comp toyOps toyIface [.unit, .sum .unit .nat, .nat, .sum .unit .nat]
      (.sum (.prod .nat .nat) (.prod .unit (.prod .unit .nat))) :=
  .bind (.iter 100 (.nat 0) (.ret .v0)) (.ret (.inl (.pair .v0 .v3)))

@[expose] def toyFastPreArm :
    Comp toyOps toyIface [.nat, .sum .unit .nat, .nat, .sum .unit .nat]
      (.sum (.prod .nat .nat) (.prod .unit (.prod .unit .nat))) :=
  .ret (.inl (.pair .v0 .v2))

@[expose] def toy2StageRed :
    TwoStageCostedReduction toyOps toyIface toyGameSpec toyCodec
      .unit .unit .bool .unit .bool .nat where
  σ := .nat
  π := .unit
  init := .ret (.pair .unit (.nat 0))
  handlePre := (Comp.ret .v1).bind (.caseSum .v0 toyHeavyPreArm toyFastPreArm)
  chDone := .ret .unit
  resume := .ret (.pair (.nat 0) .v0)
  handlePost := (Comp.ret .v1).bind (.caseSum .v0 toyHeavyArm toyFastArm)
  finish := .ret .v0

@[expose] def toyCounts : Fin 2 → ℕ := fun i => if i.val = 0 then 1 else 1000

theorem toy1Stage_handle_costAt_ro (s x : ℕ) :
    toy1StageRed.handle.costAt (.cons s (.cons (toyCodec.qenc (Sum.inr x)) .nil)) ≤ 9 :=
  handle_costAt_le_of_dispatchesTo toy1StageRed s (Sum.inr x)
    (DispatchesTo.letV_var (DispatchesTo.caseSum_var_inr rfl (DispatchesTo.refl _ _)))
    (cDisp := 5) le_rfl

end ToyTests

end Computational.Proofs.ReductionDsl.KindedDispatch
