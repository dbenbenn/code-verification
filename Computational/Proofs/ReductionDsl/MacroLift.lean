/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound

/-!
# Monadic Macro Compiler for `ReductionDsl`

Compiles `ReductionDsl` expressions, computations, and one- or two-stage `CostedReduction` programs
from an abstract operation table `O₁` and interface `I₁` into target tables `O₂` and `I₂`,
threading a read-only auxiliary context `aux : auxT.denote`. Establishes query, static cost, AST
size, and `OracleComp` evaluation bounds, together with length-guarded `GRedBounded` and
`GTwoStageBounded` wrappers (`guardRed`, `guardTwoStageRed`).-/

public section

set_option autoImplicit false

/-! ## Variable renaming on `Expr` and `Comp` -/

namespace ReductionDsl

open OracleSpec OracleComp

@[expose] def liftRen {S : Sig} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {a : Ty S} :
    ∀ ⦃u⦄, Var (a :: Γ) u → Var (a :: Δ) u
  | _, .zero => .zero
  | _, .succ v => .succ (ξ v)

theorem get_liftRen {S : Sig} {Γ Δ : List (Ty S)} {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u}
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v)
    {a : Ty S} (x : a.denote) ⦃u : Ty S⦄ (v : Var (a :: Γ) u) :
    (Env.cons x ρ₂).get (liftRen ξ v) = (Env.cons x ρ₁).get v := by
  cases v with
  | zero => rfl
  | succ v => exact hξ v

@[expose] def Expr.renameM {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} : Expr O Γ t → Expr O Δ t
  | .var v => .var (ξ v)
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .sub a b => .sub (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .mulK k a => .mulK k (Expr.renameM ξ a)
  | .divK k a => .divK k (Expr.renameM ξ a)
  | .modK k a => .modK k (Expr.renameM ξ a)
  | .lt a b => .lt (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .eqN a b => .eqN (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .not a => .not (Expr.renameM ξ a)
  | .and a b => .and (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .ite c a b => .ite (Expr.renameM ξ c) (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .pair a b => .pair (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .fst a => .fst (Expr.renameM ξ a)
  | .snd a => .snd (Expr.renameM ξ a)
  | .inl a => .inl (Expr.renameM ξ a)
  | .inr a => .inr (Expr.renameM ξ a)
  | .none => .none
  | .some a => .some (Expr.renameM ξ a)
  | .caseOpt e n s =>
    .caseOpt (Expr.renameM ξ e) (Expr.renameM ξ n) (Expr.renameM (liftRen ξ) s)
  | .caseSum e l r =>
    .caseSum (Expr.renameM ξ e) (Expr.renameM (liftRen ξ) l) (Expr.renameM (liftRen ξ) r)
  | .letE e b => .letE (Expr.renameM ξ e) (Expr.renameM (liftRen ξ) b)
  | .op o a => .op o (Expr.renameM ξ a)
  | .nil => .nil
  | .cons x l => .cons (Expr.renameM ξ x) (Expr.renameM ξ l)
  | .len l => .len (Expr.renameM ξ l)
  | .take n l => .take (Expr.renameM ξ n) (Expr.renameM ξ l)
  | .appendL K a b => .appendL K (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .findB K l p => .findB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) p)
  | .anyB K l p => .anyB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) p)
  | .mapB K l f => .mapB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) f)
  | .foldrB K l z f =>
    .foldrB K (Expr.renameM ξ l) (Expr.renameM ξ z) (Expr.renameM (liftRen (liftRen ξ)) f)
  | .tconst a => .tconst (Expr.renameM ξ a)
  | .tget m i => .tget (Expr.renameM ξ m) (Expr.renameM ξ i)
  | .tset m i a => .tset (Expr.renameM ξ m) (Expr.renameM ξ i) (Expr.renameM ξ a)

@[simp] theorem Expr.renameM_cost {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).cost = e.cost := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.cost, *]

theorem Expr.one_le_size {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.size := by
  cases e with
  | nat n => exact one_le_bits n
  | mulK k _ | divK k _ | modK k _ =>
    have := one_le_bits k
    simp only [Expr.size]
    omega
  | _ =>
    simp only [Expr.size]
    omega

@[simp] theorem Expr.renameM_size {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).size = e.size := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.size, *]

/-- Bit-length-independent AST node count (every constructor and literal counts `1`). -/
@[expose, simp] def Expr.nodes {S : Sig} {O : Ops S} : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 1
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .letE a b | _, _, .appendL _ a b | _, _, .findB _ a b
  | _, _, .anyB _ a b | _, _, .mapB _ a b | _, _, .tget a b => a.nodes + b.nodes + 1
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a | _, _, .op _ a => a.nodes + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b
  | _, _, .foldrB _ c a b | _, _, .tset c a b => c.nodes + a.nodes + b.nodes + 1

@[simp] theorem Expr.renameM_nodes {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).nodes = e.nodes := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.nodes, *]

theorem Expr.renameM_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u} {t : Ty S} (e : Expr O Γ t)
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v) :
    (Expr.renameM ξ e).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Δ with
  | var v => exact hξ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | sub _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | mulK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | divK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | modK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | lt _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | eqN _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | not _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | and _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | ite _ _ _ ihc iha ihb => simp [Expr.renameM, Expr.eval, ihc hξ, iha hξ, ihb hξ]
  | pair _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | fst _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | snd _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | inl _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | inr _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | some _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    cases e.eval ρ₁ with
    | none => exact ihn hξ
    | some x => exact ihs (get_liftRen hξ x)
  | caseSum e l r ihe ihl ihr =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen hξ x)
    | inr y => exact ihr (get_liftRen hξ y)
  | letE e b ihe ihb =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    exact ihb (get_liftRen hξ (e.eval ρ₁))
  | op _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | cons _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | len _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | take _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | appendL _ _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | findB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihp (get_liftRen hξ x)
  | anyB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihp (get_liftRen hξ x)
  | mapB K l f ihl ihf =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihf (get_liftRen hξ x)
  | foldrB K l z f ihl ihz ihf =>
    simp only [Expr.renameM, Expr.eval, ihl hξ, ihz hξ]
    congr 1; funext x acc; exact ihf (get_liftRen (get_liftRen hξ acc) x)
  | tconst _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | tget _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ, ih3 hξ]

@[expose] def Comp.renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} :
    Comp O I Γ t → Comp O I Δ t
  | .ret e => .ret (Expr.renameM ξ e)
  | .bind c k => .bind (Comp.renameM ξ c) (Comp.renameM (liftRen ξ) k)
  | .ite b c d => .ite (Expr.renameM ξ b) (Comp.renameM ξ c) (Comp.renameM ξ d)
  | .caseOpt e n s =>
    .caseOpt (Expr.renameM ξ e) (Comp.renameM ξ n) (Comp.renameM (liftRen ξ) s)
  | .caseSum e l r =>
    .caseSum (Expr.renameM ξ e) (Comp.renameM (liftRen ξ) l) (Comp.renameM (liftRen ξ) r)
  | .sample s e => .sample s (Expr.renameM ξ e)
  | .query g e => .query g (Expr.renameM ξ e)
  | .iter n e body => .iter n (Expr.renameM ξ e) (Comp.renameM (liftRen ξ) body)
  | .findM K l p => .findM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p)
  | .anyM K l p => .anyM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p)
  | .mapM K l f => .mapM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p) (Expr.renameM (liftRen ξ) mk)
  | .foldM K l z f =>
    .foldM K (Expr.renameM ξ l) (Expr.renameM ξ z) (Comp.renameM (liftRen (liftRen ξ)) f)

@[simp] theorem Comp.renameM_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).cost = c.cost := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.cost, Expr.renameM_cost, *]

@[simp] theorem Comp.renameM_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).size = c.size := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.size, Expr.renameM_size, *]

@[expose, simp] def Comp.nodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e | _, _, .sample _ e | _, _, .query _ e => e.nodes + 1
  | _, _, .bind c k => c.nodes + k.nodes + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    b.nodes + c.nodes + d.nodes + 1
  | _, _, .iter _ e body | _, _, .findM _ e body | _, _, .anyM _ e body | _, _, .mapM _ e body =>
    e.nodes + body.nodes + 1
  | _, _, .consumeFirstM _ l p mk => l.nodes + p.nodes + mk.nodes + 1
  | _, _, .foldM _ l z f => l.nodes + z.nodes + f.nodes + 1

@[simp] theorem Comp.renameM_nodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).nodes = c.nodes := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.nodes, Expr.renameM_nodes, *]

@[expose, simp] def CostedReduction.nodes {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) : ℕ :=
  R.init.nodes + R.handle.nodes + R.finish.nodes

@[simp] theorem Comp.renameM_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (Comp.renameM ξ c).queries w ws = c.queries w ws := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.queries, *]

private theorem iterM_congr {m : Type → Type} [Monad m] {α : Type}
    {f g : α → m α} (h : ∀ a, f a = g a) :
    ∀ (n : ℕ) (a : α), iterM f n a = iterM g n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, h a]
    exact bind_congr fun b => iterM_congr h n b

private theorem findML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, findML p xs = findML q xs
  | [] => rfl
  | x :: xs => by simp only [findML, h x, findML_congr h xs]

private theorem anyML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, anyML p xs = anyML q xs
  | [] => rfl
  | x :: xs => by simp only [anyML, h x, anyML_congr h xs]

private theorem mapML_congr {m : Type → Type} [Monad m] {α β : Type}
    {f g : α → m β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, mapML f xs = mapML g xs
  | [] => rfl
  | x :: xs => by simp only [mapML, h x, mapML_congr h xs]

private theorem consumeFirstML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} {mk₁ mk₂ : α → α}
    (hp : ∀ x, p x = q x) (hm : ∀ x, mk₁ x = mk₂ x) :
    ∀ xs : List α, consumeFirstML p mk₁ xs = consumeFirstML q mk₂ xs
  | [] => rfl
  | x :: xs => by simp only [consumeFirstML, hp x, hm x, consumeFirstML_congr hp hm xs]

private theorem foldML_congr {m : Type → Type} [Monad m] {α β : Type}
    {f g : α → β → m β} (h : ∀ x b, f x b = g x b) :
    ∀ (b : β) (xs : List α), foldML f b xs = foldML g b xs
  | _, [] => rfl
  | b, x :: xs => by
    simp only [foldML, h x b]
    exact bind_congr fun b' => foldML_congr h b' xs

theorem Comp.renameM_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u}
    {t : Ty S} (c : Comp O I Γ t) {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v) :
    (Comp.renameM ξ c).eval ρ₂ = c.eval ρ₁ := by
  induction c generalizing Δ with
  | ret e => simp [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
  | bind c k ihc ihk =>
    simp only [Comp.renameM, Comp.eval, ihc hξ]
    exact bind_congr fun x => ihk (get_liftRen hξ x)
  | ite b c d ihc ihd =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval b hξ]
    split_ifs <;> [exact ihc hξ; exact ihd hξ]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    cases e.eval ρ₁ with
    | none => exact ihn hξ
    | some x => exact ihs (get_liftRen hξ x)
  | caseSum e l r ihl ihr =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen hξ x)
    | inr y => exact ihr (get_liftRen hξ y)
  | sample s e =>
    simp only [Comp.renameM, Comp.eval]
    rw [Expr.renameM_eval e hξ]
  | query g e =>
    simp only [Comp.renameM, Comp.eval]
    rw [Expr.renameM_eval e hξ]
  | iter n e body ihb =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    exact iterM_congr (fun a => ihb (get_liftRen hξ a)) n (e.eval ρ₁)
  | findM K l p ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact findML_congr (fun x => ihp (get_liftRen hξ x)) _
  | anyM K l p ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact anyML_congr (fun x => ihp (get_liftRen hξ x)) _
  | mapM K l f ihf =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact mapML_congr (fun x => ihf (get_liftRen hξ x)) _
  | consumeFirstM K l p mk ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact consumeFirstML_congr (fun x => ihp (get_liftRen hξ x))
      (fun x => Expr.renameM_eval mk (get_liftRen hξ x)) _
  | foldM K l z f ihf =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ, Expr.renameM_eval z hξ]
    exact foldML_congr (fun x acc => ihf (get_liftRen (get_liftRen hξ acc) x)) _ _

@[expose, reducible] def Comp.wk1 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I Γ t) : Comp O I (a :: Γ) t :=
  Comp.renameM (fun ⦃_⦄ v => .succ v) c

@[expose, reducible] def Comp.wk2 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I Γ t) : Comp O I (a :: b :: Γ) t :=
  Comp.renameM (fun ⦃_⦄ v => .succ (.succ v)) c

theorem Comp.wk1_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I Γ t) (x : a.denote) (ρ : Env Γ) :
    (Comp.wk1 c).eval (.cons x ρ) = c.eval ρ :=
  Comp.renameM_eval c (fun ⦃_⦄ _ => rfl)

@[expose, reducible] def Expr.wkClosed {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O [] t) : Expr O Γ t :=
  Expr.renameM (fun ⦃_⦄ v => by cases v) e

@[expose, reducible] def Expr.wkTop1 {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a t : Ty S}
    (e : Expr O [a] t) : Expr O (a :: Γ) t :=
  Expr.renameM (fun ⦃_⦄ v => match v with | .zero => .zero | .succ w => nomatch w) e

theorem Expr.wkTop1_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a t : Ty S}
    (e : Expr O [a] t) (x : a.denote) (ρ : Env Γ) :
    (Expr.wkTop1 e).eval (.cons x ρ) = e.eval (.cons x .nil) :=
  Expr.renameM_eval e fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

@[expose, reducible] def Comp.wkTop2 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I [a, b] t) :
    Comp O I (a :: b :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ w) => nomatch w) c

theorem Comp.wkTop2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I [a, b] t)
    (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (Comp.wkTop2 c).eval (.cons x (.cons y ρ)) = c.eval (.cons x (.cons y .nil)) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w =>
      cases w with
      | zero => rfl
      | succ u => nomatch u

@[expose, reducible] def Comp.wkTop3 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d t : Ty S} (c : Comp O I [a, b, d] t) :
    Comp O I (a :: b :: d :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ .zero) => .succ (.succ .zero)
      | .succ (.succ (.succ w)) => nomatch w) c

theorem Comp.wkTop3_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d t : Ty S} (c : Comp O I [a, b, d] t)
    (x : a.denote) (y : b.denote) (z : d.denote) (ρ : Env Γ) :
    (Comp.wkTop3 c).eval (.cons x (.cons y (.cons z ρ))) =
      c.eval (.cons x (.cons y (.cons z .nil))) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w =>
      cases w with
      | zero => rfl
      | succ u =>
        cases u with
        | zero => rfl
        | succ q => nomatch q

@[expose, reducible] def Comp.wkTop4 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d g t : Ty S} (c : Comp O I [a, b, d, g] t) :
    Comp O I (a :: b :: d :: g :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ .zero) => .succ (.succ .zero)
      | .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
      | .succ (.succ (.succ (.succ w))) => nomatch w) c

theorem Comp.wkTop4_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d g t : Ty S} (c : Comp O I [a, b, d, g] t)
    (x : a.denote) (y : b.denote) (z : d.denote) (w : g.denote) (ρ : Env Γ) :
    (Comp.wkTop4 c).eval (.cons x (.cons y (.cons z (.cons w ρ)))) =
      c.eval (.cons x (.cons y (.cons z (.cons w .nil)))) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ v1 =>
      cases v1 with
      | zero => rfl
      | succ v2 =>
        cases v2 with
        | zero => rfl
        | succ v3 =>
          cases v3 with
          | zero => rfl
          | succ v4 => nomatch v4

end ReductionDsl

namespace Computational.Proofs.ReductionDsl.MacroLift

open OracleSpec OracleComp
open _root_.ReductionDsl
open _root_.CryptoVerification.LibsignalSession (GRedBounded GTwoStageBounded evalTwoStage1)
open _root_.CryptoVerification.E2E.Costed (gRedBounded_of_bounds)

/-! ## Sort-to-type substitution and auxiliary-rooted environments -/

section Subst

@[expose, reducible] def mapTy {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) : Ty S₁ → Ty S₂
  | .base b => f b
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .opt t => .opt (mapTy f t)
  | .prod t u => .prod (mapTy f t) (mapTy f u)
  | .sum t u => .sum (mapTy f t) (mapTy f u)
  | .list t => .list (mapTy f t)
  | .tbl t => .tbl (mapTy f t)

@[expose] def toVal {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂)
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) :
    (t : Ty S₁) → t.denote → (mapTy f t).denote
  | .base b, x => toDen b x
  | .unit, x => x
  | .bool, x => x
  | .nat, x => x
  | .opt t, x => x.map (toVal f toDen t)
  | .prod t u, x => (toVal f toDen t x.1, toVal f toDen u x.2)
  | .sum t u, x => Sum.map (toVal f toDen t) (toVal f toDen u) x
  | .list t, x => x.map (toVal f toDen t)
  | .tbl t, m => fun i => toVal f toDen t (m i)

/-- Translated context `Γ.map (mapTy f) ++ [auxT]`, definitionally commuting with `cons`. -/
@[expose, reducible] def mapCtx {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    List (Ty S₁) → List (Ty S₂)
  | [] => [auxT]
  | t :: Γ => mapTy f t :: mapCtx f auxT Γ

@[expose] def mapVarAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Var Γ t → Var (mapCtx f auxT Γ) (mapTy f t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (mapVarAux f auxT v)

@[expose] def auxVar {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    (Γ : List (Ty S₁)) → Var (mapCtx f auxT Γ) auxT
  | [] => .zero
  | _ :: Γ => .succ (auxVar f auxT Γ)

@[expose] def mapEnvAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote) :
    {Γ : List (Ty S₁)} → Env Γ → Env (mapCtx f auxT Γ)
  | _, .nil => .cons aux .nil
  | _, .cons x ρ => .cons (toVal f toDen _ x) (mapEnvAux f toDen aux ρ)

theorem get_mapEnvAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} {t : Ty S₁} (ρ : Env Γ) (v : Var Γ t) :
    (mapEnvAux f toDen aux ρ).get (mapVarAux f auxT v) = toVal f toDen t (ρ.get v) := by
  induction v with
  | zero => cases ρ; rfl
  | succ v ih =>
    cases ρ with
    | cons _ ρ => exact ih ρ

theorem get_auxVar {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote) :
    ∀ {Γ : List (Ty S₁)} (ρ : Env Γ),
      (mapEnvAux f toDen aux ρ).get (auxVar f auxT Γ) = aux
  | _, .nil => rfl
  | _, .cons _ ρ => get_auxVar f toDen aux ρ

@[expose] def callMacroAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    Comp O₂ I₂ (a :: mapCtx f auxT Γ) b :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (auxVar f auxT Γ))
    c

@[simp] theorem callMacroAux_cost {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    (callMacroAux f auxT Γ c).cost = c.cost :=
  Comp.renameM_cost _ c

@[simp] theorem callMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    (callMacroAux f auxT Γ c).size = c.size :=
  Comp.renameM_size _ c

@[simp] theorem callMacroAux_queries {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b)
    (w : I₂.Tag → ℕ) (ws : I₂.smp.Samp → ℕ) :
    (callMacroAux f auxT Γ c).queries w ws = c.queries w ws :=
  Comp.renameM_queries _ c w ws

theorem callMacroAux_eval {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} (ρ : Env Γ) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₂ : Iface S₂ T} {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) (x : a.denote) :
    (callMacroAux f auxT Γ c).eval (.cons x (mapEnvAux f toDen aux ρ)) =
      c.eval (.cons x (.cons aux .nil)) := by
  refine Comp.renameM_eval c ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => exact get_auxVar f toDen aux ρ
    | succ v => nomatch v

end Subst

/-! ## Monadic macro compiler -/

/-- Target `Comp O₂ I₂` macros implementing each operator, sampler, and query tag of `(O₁, I₁)`
with access to `(arg, aux)`. -/
structure MacroBundle (S₁ S₂ : Sig) (O₁ : Ops S₁) (O₂ : Ops S₂)
    {ι : Type} {T : OracleSpec ι} (I₁ : Iface S₁ T) (I₂ : Iface S₂ T)
    (auxT : Ty S₂) where
  fSort : S₁.Base → Ty S₂
  opMacro : (o : O₁.Op) → Comp O₂ I₂ [mapTy fSort (O₁.dom o), auxT] (mapTy fSort (O₁.cod o))
  sampMacro : (s : I₁.smp.Samp) →
    Comp O₂ I₂ [mapTy fSort (I₁.smp.sDom s), auxT] (mapTy fSort (I₁.smp.sTy s))
  queryMacro : (g : I₁.Tag) →
    Comp O₂ I₂ [mapTy fSort (I₁.dom g), auxT] (mapTy fSort (I₁.cod g))

section Compile

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}

@[expose] def compileExpr (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .var v => .ret (.var (mapVarAux M.fSort auxT v))
  | _, _, .unit => .ret .unit
  | _, _, .bool b => .ret (.bool b)
  | _, _, .nat n => .ret (.nat n)
  | _, _, .add a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.add (.var (.succ .zero)) (.var .zero))))
  | _, _, .sub a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.sub (.var (.succ .zero)) (.var .zero))))
  | _, _, .mulK k a => .bind (compileExpr M a) (.ret (.mulK k (.var .zero)))
  | _, _, .divK k a => .bind (compileExpr M a) (.ret (.divK k (.var .zero)))
  | _, _, .modK k a => .bind (compileExpr M a) (.ret (.modK k (.var .zero)))
  | _, _, .lt a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.lt (.var (.succ .zero)) (.var .zero))))
  | _, _, .eqN a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.eqN (.var (.succ .zero)) (.var .zero))))
  | _, _, .not a => .bind (compileExpr M a) (.ret (.not (.var .zero)))
  | _, _, .and a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.and (.var (.succ .zero)) (.var .zero))))
  | _, _, .ite c a b =>
    .bind (compileExpr M c)
      (.ite (.var .zero) ((compileExpr M a).wk1) ((compileExpr M b).wk1))
  | _, _, .pair a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.pair (.var (.succ .zero)) (.var .zero))))
  | _, _, .fst a => .bind (compileExpr M a) (.ret (.fst (.var .zero)))
  | _, _, .snd a => .bind (compileExpr M a) (.ret (.snd (.var .zero)))
  | _, _, .inl a => .bind (compileExpr M a) (.ret (.inl (.var .zero)))
  | _, _, .inr a => .bind (compileExpr M a) (.ret (.inr (.var .zero)))
  | _, _, .none => .ret .none
  | _, _, .some a => .bind (compileExpr M a) (.ret (.some (.var .zero)))
  | _, _, .caseOpt e n s =>
    .bind (compileExpr M e)
      (.caseOpt (.var .zero) ((compileExpr M n).wk1)
        ((compileExpr M s).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .caseSum e l r =>
    .bind (compileExpr M e)
      (.caseSum (.var .zero)
        ((compileExpr M l).renameM (liftRen (fun ⦃_⦄ v => .succ v)))
        ((compileExpr M r).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .letE e b => .bind (compileExpr M e) (compileExpr M b)
  | Γ, _, .op o a =>
    .bind (compileExpr M a) (callMacroAux M.fSort auxT Γ (M.opMacro o))
  | _, _, .nil => .ret .nil
  | _, _, .cons x l =>
    .bind (compileExpr M x)
      (.bind ((compileExpr M l).wk1) (.ret (.cons (.var (.succ .zero)) (.var .zero))))
  | _, _, .len l => .bind (compileExpr M l) (.ret (.len (.var .zero)))
  | _, _, .take n l =>
    .bind (compileExpr M n)
      (.bind ((compileExpr M l).wk1) (.ret (.take (.var (.succ .zero)) (.var .zero))))
  | _, _, .appendL K a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.appendL K (.var (.succ .zero)) (.var .zero))))
  | _, _, .findB K l p =>
    .bind (compileExpr M l)
      (.findM K (.var .zero) ((compileExpr M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .anyB K l p =>
    .bind (compileExpr M l)
      (.anyM K (.var .zero) ((compileExpr M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .mapB K l f =>
    .bind (compileExpr M l)
      (.mapM K (.var .zero) ((compileExpr M f).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .foldrB K l z f =>
    .bind (compileExpr M l)
      (.bind (.foldM K (.var .zero) .nil (.ret (.cons (.var .zero) (.var (.succ .zero)))))
        (.bind ((compileExpr M z).wk2)
          (.foldM K (.var (.succ .zero)) (.var .zero)
            ((compileExpr M f).renameM
              (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ (.succ v)))))))))
  | _, _, .tconst a => .bind (compileExpr M a) (.ret (.tconst (.var .zero)))
  | _, _, .tget m i =>
    .bind (compileExpr M m)
      (.bind ((compileExpr M i).wk1) (.ret (.tget (.var (.succ .zero)) (.var .zero))))
  | _, _, .tset m i a =>
    .bind (compileExpr M m)
      (.bind ((compileExpr M i).wk1)
        (.bind ((compileExpr M a).wk2)
          (.ret (.tset (.var (.succ (.succ .zero))) (.var (.succ .zero)) (.var .zero)))))

@[expose] def compileComp (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .ret e => compileExpr M e
  | _, _, .bind c k => .bind (compileComp M c) (compileComp M k)
  | _, _, .ite b c d =>
    .bind (compileExpr M b)
      (.ite (.var .zero) ((compileComp M c).wk1) ((compileComp M d).wk1))
  | _, _, .caseOpt e n s =>
    .bind (compileExpr M e)
      (.caseOpt (.var .zero) ((compileComp M n).wk1)
        ((compileComp M s).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .caseSum e l r =>
    .bind (compileExpr M e)
      (.caseSum (.var .zero)
        ((compileComp M l).renameM (liftRen (fun ⦃_⦄ v => .succ v)))
        ((compileComp M r).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | Γ, _, .sample s e =>
    .bind (compileExpr M e) (callMacroAux M.fSort auxT Γ (M.sampMacro s))
  | Γ, _, .query g e =>
    .bind (compileExpr M e) (callMacroAux M.fSort auxT Γ (M.queryMacro g))
  | _, _, .iter n e body =>
    .bind (compileExpr M e)
      (.iter n (.var .zero) ((compileComp M body).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .findM K l p =>
    .bind (compileExpr M l)
      (.findM K (.var .zero) ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .anyM K l p =>
    .bind (compileExpr M l)
      (.anyM K (.var .zero) ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .mapM K l f =>
    .bind (compileExpr M l)
      (.mapM K (.var .zero) ((compileComp M f).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .consumeFirstM K l p mk =>
    .bind (compileExpr M l)
      (.bind
        (.foldM K (.var .zero) (.pair (.bool false) .nil)
          (.ite (.fst (.var (.succ .zero)))
            (.ret (.pair (.bool true) (.cons (.var .zero) (.snd (.var (.succ .zero))))))
            (.bind
              ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ (.succ v))))
              (.ite (.var .zero)
                (.bind
                  ((compileExpr M mk).renameM
                    (fun ⦃_⦄ v => match v with
                      | .zero => .succ .zero
                      | .succ w => .succ (.succ (.succ (.succ w)))))
                  (.ret (.pair (.bool true)
                    (.cons (.var .zero) (.snd (.var (.succ (.succ (.succ .zero)))))))))
                (.ret (.pair (.bool false)
                  (.cons (.var (.succ .zero)) (.snd (.var (.succ (.succ .zero)))))))))))
        (.bind
          (.foldM K (.snd (.var .zero)) .nil (.ret (.cons (.var .zero) (.var (.succ .zero)))))
          (.ret (.pair (.fst (.var (.succ .zero))) (.var .zero)))))
  | _, _, .foldM K l z f =>
    .bind (compileExpr M l)
      (.bind ((compileExpr M z).wk1)
        (.foldM K (.var (.succ .zero)) (.var .zero)
          ((compileComp M f).renameM (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ v)))))))

theorem compileExpr_queries (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compileExpr M e).queries w₂ ws₂ = 0 := by
  induction e with
  | op o a iha => simp only [compileExpr, callMacroAux_queries, Comp.queries, iha, hOpQ, add_zero]
  | _ => simp only [compileExpr, Comp.wk1, Comp.renameM_queries, Comp.queries,
      add_zero, Nat.max_zero, mul_zero, *]

theorem compileComp_queries_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compileComp M c).queries w₂ ws₂ ≤ c.queries w₁ ws₁ := by
  induction c with
  | ret e => simp [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e]
  | bind c k ihc ihk =>
    simp only [compileComp, Comp.queries]
    omega
  | ite b c d ihc ihd =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ b,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihc ihd
  | caseOpt e n s ihn ihs =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihn ihs
  | caseSum e l r ihl ihr =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihl ihr
  | sample s e =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      callMacroAux_queries, zero_add]
    exact hSampQ s
  | query g e =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      callMacroAux_queries, zero_add]
    exact hQueryQ g
  | iter n e body ihb =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left n ihb
  | findM K l p ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihp
  | anyM K l p ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihp
  | mapM K l f ihf =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihf
  | consumeFirstM K l p mk ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      compileExpr_queries M w₂ ws₂ hOpQ mk, Comp.renameM_queries, zero_add, add_zero,
      Nat.max_zero, Nat.zero_max, mul_zero]
    exact Nat.mul_le_mul_left K ihp
  | foldM K l z f ihf =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      compileExpr_queries M w₂ ws₂ hOpQ z, Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihf

/-! ### Evaluation agreement -/

private theorem iterM_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (f₁ : α → m α) (f₂ : β → m β)
    (hf : ∀ a, f₂ (g a) = g <$> f₁ a) :
    ∀ (n : ℕ) (a : α), iterM f₂ n (g a) = g <$> iterM f₁ n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact bind_congr fun a' => iterM_map_hom g f₁ f₂ hf n a'

private theorem findML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, findML p₂ (xs.map g) = Option.map g <$> findML p₁ xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    refine bind_congr fun b => ?_
    cases b with
    | true => simp
    | false => exact findML_map_hom g p₁ p₂ hp xs

private theorem anyML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, anyML p₂ (xs.map g) = anyML p₁ xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    refine bind_congr fun b => ?_
    cases b with
    | true => rfl
    | false => exact anyML_map_hom g p₁ p₂ hp xs

private theorem mapML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → m β₁) (f₂ : α₂ → m β₂)
    (hf : ∀ x, f₂ (g x) = h <$> f₁ x) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = List.map h <$> mapML f₁ xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    refine bind_congr fun y => ?_
    rw [mapML_map_hom g h f₁ f₂ hf xs, bind_map_left]
    simp

private theorem foldML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → m β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x b, f₂ (g x) (h b) = h <$> f₁ x b) :
    ∀ (b : β₁) (xs : List α₁), foldML f₂ (h b) (xs.map g) = h <$> foldML f₁ b xs
  | b, [] => by simp [foldML]
  | b, x :: xs => by
    simp only [List.map_cons, foldML, hf x b, bind_map_left, map_bind]
    exact bind_congr fun b' => foldML_map_hom g h f₁ f₂ hf b' xs

end Compile

/-! ## Reduction compiler and length-guarded wrappers -/

section CompileRed

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
  {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
  {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}

/-- Adapter expressions reshaping source/target reduction boundary types and game codecs. -/
structure RedAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ out₁ : Ty S₁) (rIn₂ aIn₂ aOut₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

private theorem simulateQ_state_hom
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁, (impl₂ q).run (proj s₁) = Prod.map id proj <$> (impl₁ q).run s₁)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s₁ : σ₁,
      (simulateQ impl₂ oa).run (proj s₁) = Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s₁
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s₁
    simp only [simulateQ_query_bind, StateT.run_bind]
    change
      (do let p ← (impl₂ q).run (proj s₁); (simulateQ impl₂ (mx p.1)).run p.2) =
        Prod.map id proj <$>
          (do let p ← (impl₁ q).run s₁; (simulateQ impl₁ (mx p.1)).run p.2)
    rw [hStep q s₁, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

@[expose] def dummyRed {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    CostedReduction O I G C rIn aIn aOut out where
  σ := .unit
  init := .ret (.pair (Expr.wkClosed dfltAIn) .unit)
  handle := .ret (.pair (Expr.wkClosed dfltR) .unit)
  finish := .ret (Expr.wkClosed dfltOut)

@[simp] theorem dummyRed_totalQueries {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).totalQueries
      w ws q = 0 := by
  simp [CostedReduction.totalQueries, dummyRed, Comp.queries]

theorem dummyRed_totalCost {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) (q : ℕ) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).totalCost q =
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 3 + C.codecCost) + (dfltOut.cost + 1) := by
  simp [CostedReduction.totalCost, dummyRed, Expr.wkClosed, Comp.cost, Expr.cost]

theorem dummyRed_size {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).size =
      (dfltAIn.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) := by
  simp [CostedReduction.size, dummyRed, Expr.wkClosed, Comp.size, Expr.size]

/-- Guard `realR` behind proposition `P` (`[Decidable P]`), falling back to `dummyRed` when `¬ P`. -/
@[expose] def guardRed (P : Prop) [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    CostedReduction O I G C rIn aIn aOut out :=
  if P then realR else dummyRed dfltAIn dfltR dfltOut

@[simp] theorem guardRed_pos {P : Prop} [Decidable P] (hP : P)
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    guardRed P realR dfltAIn dfltR dfltOut = realR := by
  simp [guardRed, hP]

theorem guardRed_gRedBounded {P : Prop} [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCostPos : P → realR.totalCost q ≤ costBudget)
    (hCostNeg :
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 3 + C.codecCost) + (dfltOut.cost + 1) ≤
        costBudget)
    (hSizePos : P → realR.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hSizeNeg :
      (dfltAIn.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) ≤ reductionSizeBudget)
    (hQueriesPos : P → realR.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRedBounded (guardRed P realR dfltAIn dfltR dfltOut) wTag wSamp q qOut costBudget := by
  unfold guardRed
  split_ifs with hP
  · exact gRedBounded_of_bounds realR wTag wSamp q qOut costBudget
      (hCostPos hP) (hSizePos hP) (hQueriesPos hP) hO hS
  · apply gRedBounded_of_bounds
    · rw [dummyRed_totalCost]; exact hCostNeg
    · rw [dummyRed_size]; exact Nat.le_trans hSizeNeg (Nat.le_add_right _ _)
    · rw [dummyRed_totalQueries]; exact Nat.zero_le qOut
    · exact hO
    · exact hS

private theorem comp_one_le_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ c.cost := by
  cases c with
  | sample _ a | query _ a =>
    have := CryptoVerification.E2E.Costed.Expr.one_le_cost a
    simp only [Comp.cost]; omega
  | _ =>
    simp only [Comp.cost]; omega

/-- Construct `GTwoStageBounded` from static cost, AST size, query, and size-honesty bounds. -/
theorem gTwoStageBounded_of_bounds {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GTwoStageBounded R wTag wSamp q qOut costBudget := by
  refine ⟨hCost, hSize, hQueries,
    CryptoVerification.E2E.Costed.costedOpsSizeHonest_of_opsSizeHonest hO,
    CryptoVerification.E2E.Costed.costedSampSizeHonest_of_sampSizeHonest hS,
    fun B hA A hfit x hx dflt => ?_⟩
  let widthB := 2 * (costBudget + 2 * q + 1) * (B + 1)
  have hWidthRing : widthB = (2 * costBudget + 4 * q + 2) * B + (2 * costBudget + 4 * q + 2) := by
    dsimp only [widthB]; ring
  have hA' : ∀ v : aOut.denote, aOut.Fits B v :=
    fun v => (CryptoVerification.E2E.Costed.costedFits_iff_fits B aOut v).1 (hA v)
  have hx' : rIn.Fits B x := (CryptoVerification.E2E.Costed.costedFits_iff_fits B rIn x).1 hx
  have hnq : R.nq q ≤ costBudget :=
    le_trans (CryptoVerification.E2E.Costed.TwoStageCostedReduction.nq_le_totalCost R q) hCost
  have hInitOne : 1 ≤ R.init.cost := comp_one_le_cost R.init
  have hFinOne : 1 ≤ R.finish.cost := comp_one_le_cost R.finish
  have hBudgetGe2 : 2 ≤ costBudget := by
    have := hCost
    dsimp only [TwoStageCostedReduction.totalCost] at this
    omega
  have hPreCost :
      q * R.handlePre.cost ≤
        q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q
      (le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
  have hPostCost :
      q * R.handlePost.cost ≤
        q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q
      (le_trans (le_trans (le_max_right _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
  have hResCost : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
  have hPreNq : q * R.handlePre.nq ≤ q * max R.handlePre.nq R.handlePost.nq :=
    Nat.mul_le_mul_left q (le_max_left _ _)
  have hPostNq : q * R.handlePost.nq ≤ q * max R.handlePre.nq R.handlePost.nq :=
    Nat.mul_le_mul_left q (le_max_right _ _)
  have hResNq : R.resume.nq ≤ max R.chDone.nq R.resume.nq := le_max_right _ _
  have hSumCost :
      R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost + R.finish.cost ≤
        2 * costBudget := by
    have := hCost
    dsimp only [TwoStageCostedReduction.totalCost] at this
    omega
  have hSumNq1 : R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq ≤ costBudget := by
    have := hnq
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq]
      at hPreNq hResNq this ⊢
    omega
  have hSumNqPost : q * R.handlePost.nq ≤ costBudget := by
    have := hnq
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq]
      at hPostNq this ⊢
    omega
  have hCoeffB :
      R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq + q * R.handlePost.nq +
        2 * q + 3 ≤ 2 * costBudget + 4 * q + 2 := by
    cases q with
    | zero => simp only [Nat.zero_mul, mul_zero, add_zero] at hSumNq1 ⊢; omega
    | succ _ => omega
  dsimp only
  intro cm hcm
  obtain ⟨hChFits, hMidFits⟩ := R.fits_eval1_when hO hS B B B hA' A hfit q B x hx' dflt cm hcm
  have hB1_le :
      B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) ≤
        widthB := by
    have hL :
        B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) =
          (R.init.nq + q * R.handlePre.nq + q + 1) * B + (R.init.cost + q * R.handlePre.cost) := by
      ring
    have hMul := Nat.mul_le_mul_right B (show R.init.nq + q * R.handlePre.nq + q + 1 ≤
      2 * costBudget + 4 * q + 2 by omega)
    omega
  refine ⟨?_, ?_, fun y hy z hz => ?_⟩
  · refine (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB ch cm.1).2
      (Ty.fits_mono ?_ ch cm.1 hChFits)
    have hL :
        B + B + q * B + R.totalCost q + R.nq q * B = (R.nq q + q + 2) * B + R.totalCost q := by
      ring
    have hMul := Nat.mul_le_mul_right B (show R.nq q + q + 2 ≤ 2 * costBudget + 4 * q + 2 by omega)
    omega
  · cases hcm2 : cm.2 with
    | done a s =>
      rw [hcm2] at hMidFits
      exact (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.σ s).2
        (Ty.fits_mono hB1_le R.σ s hMidFits)
    | paused t c p s k =>
      rw [hcm2] at hMidFits
      exact ⟨(CryptoVerification.E2E.Costed.costedFits_iff_fits widthB ch c).2
          (Ty.fits_mono hB1_le ch c hMidFits.1),
        (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.π p).2
          (Ty.fits_mono hB1_le R.π p hMidFits.2.1),
        (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.σ s).2
          (Ty.fits_mono hB1_le R.σ s hMidFits.2.2.1)⟩
  · have hy' : rIn2.Fits B y := (CryptoVerification.E2E.Costed.costedFits_iff_fits B rIn2 y).1 hy
    have hz' := R.fits_eval2_when hO hS B B B hA' cm.2 _ hMidFits y B hy' q dflt z hz
    refine (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB out z).2
      (Ty.fits_mono ?_ out z hz')
    have hL :
        B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) +
          B + B + q * B + (R.resume.cost + q * R.handlePost.cost + R.finish.cost) +
          (R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B =
          (R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq + q * R.handlePost.nq +
            2 * q + 3) * B +
          (R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost +
            R.finish.cost) := by
      ring
    have hMul := Nat.mul_le_mul_right B hCoeffB
    omega

/-- Adapter expressions reshaping source/target two-stage reduction boundary types and game codecs. -/
structure TwoStageRedAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁)
    (rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptCh : Expr O₂ [mapTy fSort ch₁] ch₂
  adaptRIn2 : Expr O₂ [rIn2₂] (mapTy fSort rIn2₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

/-- Compile `R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁` into
`TwoStageCostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂` with state
`.prod (mapTy M.fSort R.σ) auxT` and pause payload `mapTy M.fSort R.π`. -/
@[expose] def compileTwoStageRed (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁) :
    TwoStageCostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ where
  σ := .prod (mapTy M.fSort R.σ) auxT
  π := mapTy M.fSort R.π
  init :=
    .bind (.ret A.splitIn)
      (.bind (.ret (.snd (.var .zero)))
        (.bind (.ret (.fst (.var (.succ .zero))))
          (.bind
            (Comp.wkTop2 (compileComp M R.init))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptAIn))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ .zero)))))))))
  handlePre :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.handlePre))
            (.ret
              (.caseSum (.var .zero)
                (.inl
                  (.pair
                    (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                    (.pair (.snd (.var .zero))
                      (.var (.succ (.succ (.succ (.succ .zero))))))))
                (.inr
                  (.pair
                    (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptCh))
                    (.pair (.fst (.snd (.var .zero)))
                      (.pair (.snd (.snd (.var .zero)))
                        (.var (.succ (.succ (.succ (.succ .zero))))))))))))))
  chDone :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptAOut)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.chDone))
            (.ret
              (.letE (.var .zero) (Expr.wkTop1 A.adaptCh))))))
  resume :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptRIn2)))
        (.bind (.ret (.var (.succ (.succ (.succ .zero)))))
          (.bind (.ret (.fst (.var (.succ (.succ (.succ .zero))))))
            (.bind
              (Comp.wkTop4 (compileComp M R.resume))
              (.ret
                (.pair
                  (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                  (.pair (.snd (.var .zero))
                    (.var (.succ (.succ (.succ (.succ .zero))))))))))))
  handlePost :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.handlePost))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ (.succ .zero))))))))))
  finish :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptRIn2)))
        (.bind
          (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptAOut)))
          (.bind (.ret (.fst (.var (.succ (.succ (.succ .zero))))))
            (.bind
              (Comp.wkTop4 (compileComp M R.finish))
              (.ret
                (.letE (.var .zero) (Expr.wkTop1 A.adaptOut)))))))

theorem compileTwoStageRed_totalQueries_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    (q : ℕ) :
    (compileTwoStageRed M A R).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  have hi := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.init
  have hpre := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.handlePre
  have hpost := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.handlePost
  have hch := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.chDone
  have hres := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.resume
  have hf := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.finish
  have hmaxH : max ((compileComp M R.handlePre).queries w₂ ws₂)
      ((compileComp M R.handlePost).queries w₂ ws₂) ≤
      max (R.handlePre.queries w₁ ws₁) (R.handlePost.queries w₁ ws₁) :=
    max_le_max hpre hpost
  have hmul := Nat.mul_le_mul_left q hmaxH
  have hmaxC : max ((compileComp M R.chDone).queries w₂ ws₂)
      ((compileComp M R.resume).queries w₂ ws₂) ≤
      max (R.chDone.queries w₁ ws₁) (R.resume.queries w₁ ws₁) :=
    max_le_max hch hres
  simp only [TwoStageCostedReduction.totalQueries, compileTwoStageRed, Comp.queries,
    Comp.renameM_queries, zero_add, add_zero]
  omega

@[expose] def dummyTwoStageRed {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out where
  σ := .unit
  π := .unit
  init := .ret (.pair (Expr.wkClosed dfltAIn) .unit)
  handlePre := .ret (.inl (.pair (Expr.wkClosed dfltR) .unit))
  chDone := .ret (Expr.wkClosed dfltCh)
  resume := .ret (.pair (Expr.wkClosed dfltR) .unit)
  handlePost := .ret (.pair (Expr.wkClosed dfltR) .unit)
  finish := .ret (Expr.wkClosed dfltOut)

@[simp] theorem dummyTwoStageRed_totalQueries {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).totalQueries w ws q = 0 := by
  simp [TwoStageCostedReduction.totalQueries, dummyTwoStageRed, Comp.queries]

theorem dummyTwoStageRed_totalCost {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) (q : ℕ) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).totalCost q =
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 4 + C.codecCost) +
        max (dfltCh.cost + 1) (dfltR.cost + 3) + (dfltOut.cost + 1) := by
  have hmax : max (dfltR.cost + 4) (dfltR.cost + 3) = dfltR.cost + 4 := by omega
  simp only [TwoStageCostedReduction.totalCost, dummyTwoStageRed, Expr.wkClosed, Comp.cost,
    Expr.cost, Expr.renameM_cost]
  rw [show dfltR.cost + 1 + 1 + 1 + 1 = dfltR.cost + 4 by omega,
    show dfltR.cost + 1 + 1 + 1 = dfltR.cost + 3 by omega, hmax]

theorem dummyTwoStageRed_size {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).size =
      (dfltAIn.size + 3) + (dfltR.size + 4) + (dfltCh.size + 1) +
        (dfltR.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) := by
  simp [TwoStageCostedReduction.size, dummyTwoStageRed, Expr.wkClosed, Comp.size, Expr.size]

/-- Guard `realR` behind proposition `P` (`[Decidable P]`), falling back to `dummyTwoStageRed`
when `¬ P`. -/
@[expose] def guardTwoStageRed (P : Prop) [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out :=
  if P then realR else dummyTwoStageRed dfltAIn dfltR dfltCh dfltOut

@[simp] theorem guardTwoStageRed_pos {P : Prop} [Decidable P] (hP : P)
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    guardTwoStageRed P realR dfltAIn dfltR dfltCh dfltOut = realR := by
  simp [guardTwoStageRed, hP]

theorem guardTwoStageRed_gTwoStageBounded {P : Prop} [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCostPos : P → realR.totalCost q ≤ costBudget)
    (hCostNeg :
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 4 + C.codecCost) +
        max (dfltCh.cost + 1) (dfltR.cost + 3) + (dfltOut.cost + 1) ≤ costBudget)
    (hSizePos : P → realR.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hSizeNeg :
      (dfltAIn.size + 3) + (dfltR.size + 4) + (dfltCh.size + 1) +
        (dfltR.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) ≤ reductionSizeBudget)
    (hQueriesPos : P → realR.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GTwoStageBounded (guardTwoStageRed P realR dfltAIn dfltR dfltCh dfltOut)
      wTag wSamp q qOut costBudget := by
  unfold guardTwoStageRed
  split_ifs with hP
  · exact gTwoStageBounded_of_bounds realR wTag wSamp q qOut costBudget
      (hCostPos hP) (hSizePos hP) (hQueriesPos hP) hO hS
  · apply gTwoStageBounded_of_bounds
    · rw [dummyTwoStageRed_totalCost]; exact hCostNeg
    · rw [dummyTwoStageRed_size]; exact Nat.le_trans hSizeNeg (Nat.le_add_right _ _)
    · rw [dummyTwoStageRed_totalQueries]; exact Nat.zero_le qOut
    · exact hO
    · exact hS

end CompileRed

/-! ## Retagging ASTs across `Ops` tables -/

section RetagOps

def retagExpr {S : Sig} {O₀ O₁ : Ops S}
    (fOp : O₀.Op → O₁.Op)
    (hDom : ∀ o, O₀.dom o = O₁.dom (fOp o))
    (hCod : ∀ o, O₀.cod o = O₁.cod (fOp o)) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O₀ Γ t → Expr O₁ Γ t
  | _, _, .var v => .var v
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .sub a b => .sub (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .mulK k a => .mulK k (retagExpr fOp hDom hCod a)
  | _, _, .divK k a => .divK k (retagExpr fOp hDom hCod a)
  | _, _, .modK k a => .modK k (retagExpr fOp hDom hCod a)
  | _, _, .lt a b => .lt (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .eqN a b => .eqN (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .not a => .not (retagExpr fOp hDom hCod a)
  | _, _, .and a b => .and (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .ite c a b =>
    .ite (retagExpr fOp hDom hCod c) (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .pair a b => .pair (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .fst a => .fst (retagExpr fOp hDom hCod a)
  | _, _, .snd a => .snd (retagExpr fOp hDom hCod a)
  | _, _, .inl a => .inl (retagExpr fOp hDom hCod a)
  | _, _, .inr a => .inr (retagExpr fOp hDom hCod a)
  | _, _, .none => .none
  | _, _, .some a => .some (retagExpr fOp hDom hCod a)
  | _, _, .caseOpt e n s =>
    .caseOpt (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod n) (retagExpr fOp hDom hCod s)
  | _, _, .caseSum e l r =>
    .caseSum (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod r)
  | _, _, .letE e b => .letE (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod b)
  | _, _, .op o a => hCod o ▸ .op (fOp o) (hDom o ▸ retagExpr fOp hDom hCod a)
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (retagExpr fOp hDom hCod x) (retagExpr fOp hDom hCod l)
  | _, _, .len l => .len (retagExpr fOp hDom hCod l)
  | _, _, .take n l => .take (retagExpr fOp hDom hCod n) (retagExpr fOp hDom hCod l)
  | _, _, .appendL K a b =>
    .appendL K (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .findB K l p => .findB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod p)
  | _, _, .anyB K l p => .anyB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod p)
  | _, _, .mapB K l f => .mapB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod f)
  | _, _, .foldrB K l z f =>
    .foldrB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod z) (retagExpr fOp hDom hCod f)
  | _, _, .tconst a => .tconst (retagExpr fOp hDom hCod a)
  | _, _, .tget m i => .tget (retagExpr fOp hDom hCod m) (retagExpr fOp hDom hCod i)
  | _, _, .tset m i a =>
    .tset (retagExpr fOp hDom hCod m) (retagExpr fOp hDom hCod i) (retagExpr fOp hDom hCod a)

end RetagOps

end Computational.Proofs.ReductionDsl.MacroLift
