/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.GameHop.Rnd
import Computational.Proofs.GameHop.StateSim
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import PolyFun.Control.Monad.Support
public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.OracleSpec
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Lazy-vs-Eager Sampling, `CacheLens`, `SlotM`, and Association Caches

Post-hoc state-completion equivalences (`evalDistEq_simulateQ_run'_of_complete`), `Option V` slot
lenses (`CacheLens`), single-slot and one-time lazy monads (`SlotM`, `LazyOnce`), and list-backed
lazy random caches (`evalCache`, `CacheEquiv`).
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.GameHop.Swap

open OracleSpec OracleComp
open Computational.Proofs.GameHop.Rnd (evalDistEq_bind_right_of_mem_support evalDist_bind_congr_of_mem_support)

section PostHocCompletion

variable {κ : Type} {spec : OracleSpec.{0, 0} κ}



end PostHocCompletion

section CacheLens

/-- Lens focusing an `Option V` lazy slot inside an ambient state `S`. -/
structure CacheLens (S V : Type) where
  get : S → Option V
  put : S → Option V → S
  get_put : ∀ s o, get (put s o) = o
  put_get : ∀ s, put s (get s) = s
  put_put : ∀ s o₁ o₂, put (put s o₁) o₂ = put s o₂

namespace CacheLens

variable {S V : Type}

@[expose] def fill (L : CacheLens S V) (samp : ProbComp V) (s : S) : ProbComp S :=
  match L.get s with
  | some _ => pure s
  | none => (fun v => L.put s (some v)) <$> samp

@[simp]
theorem fill_of_some (L : CacheLens S V) (samp : ProbComp V) {s : S} {v : V}
    (h : L.get s = some v) :
    L.fill samp s = pure s := by
  simp [fill, h]

@[simp]
theorem fill_of_none (L : CacheLens S V) (samp : ProbComp V) {s : S}
    (h : L.get s = none) :
    L.fill samp s = ((fun v => L.put s (some v)) <$> samp) := by
  simp [fill, h]


end CacheLens

end CacheLens

section SlotM

/-- Single-slot lazy sampling monad over `ProbComp`. -/
abbrev SlotM (κ : Type) := StateT (Option κ) ProbComp

namespace SlotM

variable {κ : Type}

@[expose] def fill1 {α : Type} (samp : ProbComp κ) (r : α × Option κ) : ProbComp (α × Option κ) :=
  match r.2 with
  | some _ => pure r
  | none => do
    let k ← samp
    pure (r.1, some k)

@[simp]
theorem fill1_some {α : Type} (samp : ProbComp κ) (a : α) (k : κ) :
    fill1 samp (a, some k) = pure (a, some k) := rfl

@[simp]
theorem fill1_none {α : Type} (samp : ProbComp κ) (a : α) :
    fill1 samp (a, none) = (do let k ← samp; pure (a, some k)) := rfl

theorem bind_fill1_of_keep {α γ : Type} (samp : ProbComp κ) (k : κ)
    (mx : ProbComp (α × Option κ)) (g : α × Option κ → ProbComp γ)
    (hkeep : ∀ y ∈ support mx, y.2 = some k) :
    (mx >>= fun y => fill1 samp y >>= g) = mx >>= g := by
  refine bind_congr_of_forall_mem_support mx fun y hy => ?_
  rcases y with ⟨a, o⟩
  have ho : o = some k := hkeep (a, o) hy
  subst ho
  simp [fill1]

/-- Lazy read-or-sample operation on `SlotM κ`. -/
@[expose] def getSlot (samp : ProbComp κ) : SlotM κ κ :=
  StateT.mk fun o => match o with
    | some k => pure (k, some k)
    | none => do
      let k ← samp
      pure (k, some k)

@[simp]
theorem getSlot_run_some (samp : ProbComp κ) (k : κ) :
    (getSlot samp).run (some k) = pure (k, some k) := rfl

@[simp]
theorem getSlot_run_none (samp : ProbComp κ) :
    (getSlot samp).run none = (do let k ← samp; pure (k, some k)) := rfl

/-- Well-behaved lazy slot computation: never overwrites an initialized slot and commutes with
`fill1 samp`. -/
structure SlotComp (samp : ProbComp κ) {α : Type} (mx : SlotM κ α) : Prop where
  keep : ∀ (k : κ) (y : α × Option κ), y ∈ support (mx.run (some k)) → y.2 = some k
  comm : ∀ {β : Type} [MeasurableSpace β] (g : α × Option κ → ProbComp β),
    𝒟[samp >>= fun k => mx.run (some k) >>= g] =
      𝒟[mx.run none >>= fill1 samp >>= g]

theorem SlotComp.of_eq {samp : ProbComp κ} {α : Type} {mx₁ mx₂ : SlotM κ α}
    (heq : mx₁ = mx₂) (h : SlotComp samp mx₂) : SlotComp samp mx₁ :=
  heq ▸ h

theorem SlotComp.pure (samp : ProbComp κ) {α : Type} (x : α) :
    SlotComp samp (Pure.pure x : SlotM κ α) where
  keep k y hy := by
    simp [StateT.run_pure] at hy
    subst hy; rfl
  comm g := by
    simp [StateT.run_pure, fill1]

theorem SlotComp.liftComp (samp : ProbComp κ) {α : Type} (c : ProbComp α) :
    SlotComp samp (liftM c : SlotM κ α) where
  keep k y hy := by
    simp only [StateT.run_monadLift, monadLift_self, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨_, _, rfl⟩ := hy
    rfl
  comm g := by
    simp only [StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, fill1]
    exact OracleComp.evalDist_bind_bind_swap samp c (fun k x => g (x, some k))

theorem SlotComp.getSlot (samp : ProbComp κ) :
    SlotComp samp (getSlot samp) where
  keep k y hy := by
    simp [getSlot_run_some] at hy
    subst hy; rfl
  comm g := by
    simp [getSlot_run_some, getSlot_run_none, fill1]

theorem SlotComp.bind {samp : ProbComp κ} {α β : Type}
    {mx : SlotM κ α} {mf : α → SlotM κ β}
    (hx : SlotComp samp mx) (hf : ∀ a, SlotComp samp (mf a)) :
    SlotComp samp (mx >>= mf) where
  keep k y hy := by
    rw [StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hz2 : z.2 = some k := hx.keep k z hz
    rw [hz2] at hy
    exact (hf z.1).keep k y hy
  comm g := by
    simp only [StateT.run_bind, bind_assoc]
    rw [hx.comm (fun z => (mf z.1).run z.2 >>= g)]
    simp only [bind_assoc]
    refine evalDist_bind_congr_of_mem_support _ _ _ fun z _ => ?_
    rcases z with ⟨a, _ | k⟩
    · simp only [fill1_none, bind_assoc, pure_bind]
      simpa only [bind_assoc] using (hf a).comm g
    · simp only [fill1_some, pure_bind]
      rw [bind_fill1_of_keep samp k ((mf a).run (some k)) g ((hf a).keep k)]

theorem SlotComp.map {samp : ProbComp κ} {α β : Type} (f : α → β)
    {mx : SlotM κ α} (hx : SlotComp samp mx) :
    SlotComp samp (f <$> mx) := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind fun a => SlotComp.pure samp (f a)

theorem SlotComp.ite {samp : ProbComp κ} {α : Type} (c : Prop) [Decidable c]
    {t e : SlotM κ α} (ht : c → SlotComp samp t) (he : ¬ c → SlotComp samp e) :
    SlotComp samp (if c then t else e) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact ht hc
  · simp only [hc, ↓reduceIte]; exact he hc

theorem SlotComp.eager_eq_lazy_run' {samp : ProbComp κ} {α β : Type} [MeasurableSpace β]
    {mx : SlotM κ α} (h : SlotComp samp mx) (g : α → ProbComp β) :
    𝒟[samp >>= fun k => mx.run' (some k) >>= g] =
      𝒟[mx.run' none >>= g] := by
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  rw [h.comm (fun y => g y.1), bind_assoc]
  refine evalDist_bind_congr_of_mem_support _ _ _ fun y _ => ?_
  rcases y with ⟨a, _ | k⟩
  · simp only [fill1_none, bind_assoc, pure_bind]
    exact evalDist_bind_const samp (g a)
  · simp only [fill1_some, pure_bind]


end SlotM

end SlotM

section LazyOnce

/-- Three-state one-time key slot: uninitialized, pre-sampled ready, or already consumed. -/
inductive LazyOnce (κ : Type) : Type where
  | uninit
  | ready (k : κ)
  | consumed
  deriving DecidableEq

namespace LazyOnce

@[expose] def consume {κ : Type} (samp : ProbComp κ) : StateT (LazyOnce κ) ProbComp (Option κ) :=
  StateT.mk fun st => match st with
    | .uninit => do
      let k ← samp
      pure (some k, .consumed)
    | .ready k => pure (some k, .consumed)
    | .consumed => pure (none, .consumed)

@[expose] def fillOnce {κ : Type} (samp : ProbComp κ) : LazyOnce κ → ProbComp (LazyOnce κ)
  | .uninit => .ready <$> samp
  | .ready k => pure (.ready k)
  | .consumed => pure .consumed

theorem evalDistEq_consume_comm {κ : Type} (samp : ProbComp κ) (st : LazyOnce κ) :
    (do let st' ← fillOnce samp st; (consume samp).run st') =ᵈ
      (do let z ← (consume samp).run st; let st' ← fillOnce samp z.2; pure (z.1, st')) := by
  cases st with
  | uninit =>
    simp only [fillOnce, consume, StateT.run_mk, bind_map_left, pure_bind, bind_assoc]
    exact EvalDistEq.rfl
  | ready k =>
    simp only [fillOnce, consume, StateT.run_mk, pure_bind]
    exact EvalDistEq.rfl
  | consumed =>
    simp only [fillOnce, consume, StateT.run_mk, pure_bind]
    exact EvalDistEq.rfl

end LazyOnce

end LazyOnce

section AssocCache

/-- Lazy random association-cache lookup and insertion over `samp : ProbComp V`. -/
@[expose] def evalCache {K V : Type} [BEq K] (samp : ProbComp V) (cache : List (K × V)) (k : K) :
    ProbComp (V × List (K × V)) :=
  match cache.find? (fun p => p.1 == k) with
  | some (_, v) => pure (v, cache)
  | none => do
    let v ← samp
    pure (v, (k, v) :: cache)

/-- Lookup equivalence on association caches: `find?` returns the same value for every key. -/
@[expose] def CacheEquiv {K V : Type} [BEq K] (c₁ c₂ : List (K × V)) : Prop :=
  ∀ k : K, (c₁.find? (fun p => p.1 == k)).map Prod.snd =
           (c₂.find? (fun p => p.1 == k)).map Prod.snd

namespace CacheEquiv

theorem refl {K V : Type} [BEq K] (c : List (K × V)) : CacheEquiv c c :=
  fun _ => rfl

theorem symm {K V : Type} [BEq K] {c₁ c₂ : List (K × V)} (h : CacheEquiv c₁ c₂) :
    CacheEquiv c₂ c₁ :=
  fun k => (h k).symm

theorem trans {K V : Type} [BEq K] {c₁ c₂ c₃ : List (K × V)}
    (h₁₂ : CacheEquiv c₁ c₂) (h₂₃ : CacheEquiv c₂ c₃) : CacheEquiv c₁ c₃ :=
  fun k => (h₁₂ k).trans (h₂₃ k)

theorem cons {K V : Type} [BEq K] {c₁ c₂ : List (K × V)}
    (h : CacheEquiv c₁ c₂) (k : K) (v : V) :
    CacheEquiv ((k, v) :: c₁) ((k, v) :: c₂) := by
  intro q
  simp only [List.find?_cons]
  cases k == q
  · exact h q
  · rfl

theorem swap_cons {K V : Type} [BEq K] [LawfulBEq K]
    (c : List (K × V)) (k₁ k₂ : K) (v₁ v₂ : V) (hne : (k₁ == k₂) = false) :
    CacheEquiv ((k₁, v₁) :: (k₂, v₂) :: c) ((k₂, v₂) :: (k₁, v₁) :: c) := by
  intro q
  simp only [List.find?_cons]
  by_cases h1 : (k₁ == q) = true
  · have hEq1 : k₁ = q := beq_iff_eq.mp h1
    subst hEq1
    have h2 : (k₂ == k₁) = false := by
      rw [beq_eq_false_iff_ne]
      intro hEq2
      exact Bool.noConfusion (hne.symm.trans (beq_iff_eq.mpr hEq2.symm))
    simp [h2]
  · have h1F : (k₁ == q) = false := Bool.eq_false_iff.mpr h1
    simp [h1F]

end CacheEquiv

theorem evalDist_evalCache_congr {K V β : Type} [BEq K] [MeasurableSpace β]
    (samp : ProbComp V) {c₁ c₂ : List (K × V)} (hEq : CacheEquiv c₁ c₂) (k : K)
    (f₁ f₂ : V × List (K × V) → ProbComp β)
    (hf : ∀ v c₁' c₂', CacheEquiv c₁' c₂' → 𝒟[f₁ (v, c₁')] = 𝒟[f₂ (v, c₂')]) :
    𝒟[evalCache samp c₁ k >>= f₁] = 𝒟[evalCache samp c₂ k >>= f₂] := by
  unfold evalCache
  have hk := hEq k
  cases h1 : c₁.find? (fun p => p.1 == k) with
  | none =>
    rw [h1, Option.map_none] at hk
    cases h2 : c₂.find? (fun p => p.1 == k) with
    | none =>
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr_of_mem_support samp _ _ fun v _ => ?_
      exact hf v ((k, v) :: c₁) ((k, v) :: c₂) (hEq.cons k v)
    | some p₂ =>
      rw [h2, Option.map_some] at hk
      nomatch hk
  | some p₁ =>
    rcases p₁ with ⟨x₁, v₁⟩
    rw [h1, Option.map_some] at hk
    cases h2 : c₂.find? (fun p => p.1 == k) with
    | none =>
      rw [h2, Option.map_none] at hk
      nomatch hk
    | some p₂ =>
      rcases p₂ with ⟨x₂, v₂⟩
      rw [h2, Option.map_some] at hk
      injection hk with hv
      subst hv
      simp only [pure_bind]
      exact hf v₁ c₁ c₂ hEq

theorem evalDist_evalCache_idem {K V β : Type} [BEq K] [LawfulBEq K] [MeasurableSpace β]
    (samp : ProbComp V) (c : List (K × V)) (k : K)
    (f : V × List (K × V) → ProbComp β) :
    𝒟[evalCache samp c k >>= fun p => evalCache samp p.2 k >>= f] =
      𝒟[evalCache samp c k >>= f] := by
  unfold evalCache
  cases h1 : c.find? (fun p => p.1 == k) with
  | some p =>
    rcases p with ⟨x, v⟩
    simp [h1]
  | none =>
    simp only [bind_assoc, pure_bind, List.find?_cons, beq_self_eq_true]

/-- Lookups on keys `k₁` and `k₂` commute up to `CacheEquiv` in distribution. -/
theorem evalDist_evalCache_comm {K V β : Type} [BEq K] [LawfulBEq K] [MeasurableSpace β]
    (samp : ProbComp V) (c : List (K × V)) (k₁ k₂ : K)
    (f₁ f₂ : V → V → List (K × V) → ProbComp β)
    (hf : ∀ v₁ v₂ c₁ c₂, CacheEquiv c₁ c₂ → 𝒟[f₁ v₁ v₂ c₁] = 𝒟[f₂ v₁ v₂ c₂]) :
    𝒟[evalCache samp c k₁ >>= fun p₁ => evalCache samp p₁.2 k₂ >>= fun p₂ => f₁ p₁.1 p₂.1 p₂.2] =
      𝒟[evalCache samp c k₂ >>= fun p₂ => evalCache samp p₂.2 k₁ >>= fun p₁ => f₂ p₁.1 p₂.1 p₁.2] := by
  by_cases hEqK : (k₁ == k₂) = true
  · have hk : k₁ = k₂ := beq_iff_eq.mp hEqK
    subst hk
    unfold evalCache
    cases h1 : c.find? (fun p => p.1 == k₁) with
    | some p =>
      rcases p with ⟨x, v⟩
      simp only [pure_bind, h1]
      exact hf v v c c (CacheEquiv.refl c)
    | none =>
      simp only [bind_assoc, pure_bind, List.find?_cons, beq_self_eq_true]
      exact evalDist_bind_congr_of_mem_support samp _ _ fun v _ =>
        hf v v ((k₁, v) :: c) ((k₁, v) :: c) (CacheEquiv.refl _)
  · have hne : (k₁ == k₂) = false := Bool.eq_false_iff.mpr hEqK
    have hne' : (k₂ == k₁) = false := by
      rw [beq_eq_false_iff_ne] at hne ⊢
      exact Ne.symm hne
    unfold evalCache
    cases h1 : c.find? (fun p => p.1 == k₁) with
    | some p₁ =>
      rcases p₁ with ⟨x₁, v₁⟩
      cases h2 : c.find? (fun p => p.1 == k₂) with
      | some p₂ =>
        rcases p₂ with ⟨x₂, v₂⟩
        simp only [pure_bind, h1, h2]
        exact hf v₁ v₂ c c (CacheEquiv.refl c)
      | none =>
        simp only [pure_bind, bind_assoc, h2, List.find?_cons, hne', h1]
        exact evalDist_bind_congr_of_mem_support samp _ _ fun v₂ _ =>
          hf v₁ v₂ ((k₂, v₂) :: c) ((k₂, v₂) :: c) (CacheEquiv.refl _)
    | none =>
      cases h2 : c.find? (fun p => p.1 == k₂) with
      | some p₂ =>
        rcases p₂ with ⟨x₂, v₂⟩
        simp only [pure_bind, bind_assoc, List.find?_cons, hne, h2, h1]
        exact evalDist_bind_congr_of_mem_support samp _ _ fun v₁ _ =>
          hf v₁ v₂ ((k₁, v₁) :: c) ((k₁, v₁) :: c) (CacheEquiv.refl _)
      | none =>
        simp only [bind_assoc, pure_bind, List.find?_cons, hne, hne', h1, h2]
        rw [OracleComp.evalDist_bind_bind_swap samp samp]
        refine evalDist_bind_congr_of_mem_support samp _ _ fun v₂ _ => ?_
        refine evalDist_bind_congr_of_mem_support samp _ _ fun v₁ _ => ?_
        exact hf v₁ v₂ ((k₂, v₂) :: (k₁, v₁) :: c) ((k₁, v₁) :: (k₂, v₂) :: c)
          (CacheEquiv.swap_cons c k₂ k₁ v₂ v₁ hne')

end AssocCache

end Computational.Proofs.GameHop.Swap
