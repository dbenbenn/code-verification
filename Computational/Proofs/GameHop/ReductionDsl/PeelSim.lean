/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Monadic Peeling and Bounded List-Loop Lemmas for `ReductionDsl`

Congruence lemmas peeling monadic binds and branches across `F <$> ·`, removing non-truncating
`List.take K` bounds, and commuting `ReductionDsl` monadic list loops with value encodings.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.GameHop.ReductionDsl.PeelSim

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Env Ops Expr iterM findML anyML mapML consumeFirstML foldML)

section MonadPeel

theorem peel_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  simp only [bind_map_left, map_bind, hg]

theorem peel_bind_same {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  rw [map_bind]
  exact congrArg _ (funext hg)

theorem peel_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem peel_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type}
    (F : γ → δ) {a : δ} {a' : γ} (h : a = F a') :
    (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem peel_pure_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x : m α} {y : α} {g : α → m δ} {z : γ}
    (hx : x = pure y) (hg : g y = pure (F z)) :
    x >>= g = F <$> pure z := by
  rw [hx, pure_bind, hg, map_pure]

theorem ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Prop} [Decidable c]
    (x y : m α) (f : α → m β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

end MonadPeel

section BoundedLoops

variable {S : Sig} {O : Ops S}

theorem take_map_of_le {α β : Type} {K : ℕ} (f : α → β) (l : List α) (h : l.length ≤ K) :
    List.take K (l.map f) = l.map f :=
  List.take_of_length_le (by simpa using h)

theorem findML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (p : β → m Bool) (p' : α → m Bool)
    (hp : ∀ a, p (enc a) = p' a) :
    ∀ xs : List α, findML p (xs.map enc) = Option.map enc <$> findML p' xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    refine congrArg _ (funext fun b => ?_)
    cases b
    · simpa using findML_map enc p p' hp xs
    · simp

theorem anyML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (p : β → m Bool) (p' : α → m Bool)
    (hp : ∀ a, p (enc a) = p' a) :
    ∀ xs : List α, anyML p (xs.map enc) = anyML p' xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    refine congrArg _ (funext fun b => ?_)
    cases b
    · exact anyML_map enc p p' hp xs
    · rfl

theorem foldML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α α' β β' : Type}
    (enc₁ : α → α') (enc₂ : β → β') (f : α' → β' → m β') (f' : α → β → m β)
    (hf : ∀ a acc, f (enc₁ a) (enc₂ acc) = enc₂ <$> f' a acc) :
    ∀ (acc : β) (xs : List α), foldML f (enc₂ acc) (xs.map enc₁) = enc₂ <$> foldML f' acc xs
  | acc, [] => by simp [foldML]
  | acc, x :: xs => by
    simp only [List.map_cons, foldML, hf x acc, bind_map_left, map_bind]
    exact congrArg _ (funext fun acc' => foldML_map enc₁ enc₂ f f' hf acc' xs)

end BoundedLoops

end Computational.Proofs.GameHop.ReductionDsl.PeelSim
