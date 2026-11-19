/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
import ProofLib.SepLogic
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WPp

/-!
# Enforced Pool Byte-Slice Bound (`PoolSliceBound`) and `FitsEnvCap` Combinators

Lightweight interface without `Mallocng` or `cliElfBytes` imports so `Main/Proofs/M5*` modules
keep small import cones. Concrete `mallocng`, `fine`, and `withFds` instances live in
`PoolSliceBoundInst.lean`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBound

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget SeqEnv fitsEvents_append rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (WriteStdoutEnv writeStdoutEnv_init1024)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)

/-! ## 1. `SepWPp` Memory-Satisfaction Witness Helper -/

theorem sepWPp_with_mem_sat {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : (∃ R : SepProp, s.mem ⊨ P ∗ R) → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => h ⟨R, hm⟩ R hm hL

/-! ## 2. `PoolSliceBound` Typeclass -/

/-- Enforced budget pools (`lim.enforced = true`) bound any live writable byte slice `buf ↦ₛ bs`
    (`bs.length ≤ 2 ^ 64`) by `lim.physCap` whenever `lim.staticBytes + M.footprint st ≤ lim.physCap`. -/
class PoolSliceBound {M : AllocCostModel} (A : RustCliAllocBudget M) : Prop where
  slice_len_le :
    ∀ {lim : BudgetLimits} {st : M.σ} {s : State} {buf : BitVec 64}
      {bs : List (BitVec 8)} {R : SepProp},
      lim.enforced = true →
      lim.staticBytes + M.footprint st ≤ lim.physCap →
      bs.length ≤ 2 ^ 64 →
      (s.mem ⊨ (buf ↦ₛ bs) ∗ A.pool lim st s ∗ R) →
      bs.length ≤ lim.physCap

theorem PoolSliceBound.slice_len_le_of_entails {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolSliceBound A]
    {lim : BudgetLimits} {st : M.σ} {s : State} {buf : BitVec 64} {bs : List (BitVec 8)}
    {P F : SepProp}
    (henf : lim.enforced = true)
    (hcap : lim.staticBytes + M.footprint st ≤ lim.physCap)
    (hbs64 : bs.length ≤ 2 ^ 64)
    (hP : P ⊢ (buf ↦ₛ bs) ∗ A.pool lim st s ∗ F)
    (hsat : ∃ R : SepProp, s.mem ⊨ P ∗ R) :
    bs.length ≤ lim.physCap := by
  rcases hsat with ⟨R, hm⟩
  have hm' : s.mem ⊨ (buf ↦ₛ bs) ∗ A.pool lim st s ∗ (F ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left hP) hm
    simpa only [sepConj_assoc] using h1
  exact PoolSliceBound.slice_len_le (A := A) henf hcap hbs64 hm'

/-! ## 3. `FitsEnvCap`: Envelope Admissibility Paired with Physical-RAM Cap -/

/-- `FitsEnv M lim st E` paired with the post-envelope physical-RAM cap
    `∀ evs, E evs → lim.staticBytes + M.footprint (M.stepEvents evs st) ≤ lim.physCap`. -/
@[expose] def FitsEnvCap (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (E : List AllocEvent → Prop) : Prop :=
  FitsEnv M lim st E ∧
    ∀ evs, E evs → lim.staticBytes + M.footprint (M.stepEvents evs st) ≤ lim.physCap

namespace FitsEnvCap

theorem fitsEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (h : FitsEnvCap M lim st E) :
    FitsEnv M lim st E :=
  h.1

theorem cap_of_mem {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : FitsEnvCap M lim st E) (hevs : E evs) :
    lim.staticBytes + M.footprint (M.stepEvents evs st) ≤ lim.physCap :=
  h.2 evs hevs

theorem cap_of_nil {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (h : FitsEnvCap M lim st E) (hnil : E []) :
    lim.staticBytes + M.footprint st ≤ lim.physCap :=
  h.2 [] hnil

theorem mono {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop}
    (hsub : ∀ evs, E₁ evs → E₂ evs)
    (h : FitsEnvCap M lim st E₂) :
    FitsEnvCap M lim st E₁ :=
  ⟨h.1.mono hsub, fun evs he1 => h.2 evs (hsub evs he1)⟩

theorem seq_left {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop}
    (h : FitsEnvCap M lim st (SeqEnv E₁ E₂)) :
    FitsEnvCap M lim st E₁ :=
  h.mono fun _ h1 => Or.inl h1

theorem seq_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} {evs₁ : List AllocEvent}
    (h : FitsEnvCap M lim st (SeqEnv E₁ E₂)) (h1 : E₁ evs₁) :
    FitsEnvCap M lim (M.stepEvents evs₁ st) E₂ := by
  refine ⟨h.1.seq_right h1, fun evs₂ h2 => ?_⟩
  rw [← M.stepEvents_append evs₁ evs₂ st]
  exact h.2 (evs₁ ++ evs₂) (Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩)

theorem iterSeq_head {α : Type} {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Step : α → List AllocEvent → Prop} {x : α} {xs : List α}
    (h : FitsEnvCap M lim st (IterSeqEnv Step (x :: xs))) :
    FitsEnvCap M lim st (Step x) :=
  h.seq_left

theorem iterSeq_tail {α : Type} {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Step : α → List AllocEvent → Prop} {x : α} {xs : List α} {evs₁ : List AllocEvent}
    (h : FitsEnvCap M lim st (IterSeqEnv Step (x :: xs))) (h1 : Step x evs₁) :
    FitsEnvCap M lim (M.stepEvents evs₁ st) (IterSeqEnv Step xs) :=
  h.seq_right h1

theorem concat_left_of_wit {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} {evs₂ : List AllocEvent}
    (h : FitsEnvCap M lim st (ConcatEnv E₁ E₂)) (h2 : E₂ evs₂) :
    FitsEnvCap M lim st E₁ := by
  refine ⟨fun evs₁ h1 =>
      ((fitsEvents_append M lim evs₁ evs₂ st).mp (h.1 (evs₁ ++ evs₂) ⟨evs₁, evs₂, rfl, h1, h2⟩)).1,
    fun evs₁ h1 => ?_⟩
  have hcap := h.2 (evs₁ ++ evs₂) ⟨evs₁, evs₂, rfl, h1, h2⟩
  rw [M.stepEvents_append evs₁ evs₂ st] at hcap
  have hmono := M.footprint_mono_events evs₂ (M.stepEvents evs₁ st)
  omega

theorem concat_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} {evs₁ : List AllocEvent}
    (h : FitsEnvCap M lim st (ConcatEnv E₁ E₂)) (h1 : E₁ evs₁) :
    FitsEnvCap M lim (M.stepEvents evs₁ st) E₂ := by
  refine ⟨fun evs₂ h2 =>
      ((fitsEvents_append M lim evs₁ evs₂ st).mp (h.1 (evs₁ ++ evs₂) ⟨evs₁, evs₂, rfl, h1, h2⟩)).2,
    fun evs₂ h2 => ?_⟩
  rw [← M.stepEvents_append evs₁ evs₂ st]
  exact h.2 (evs₁ ++ evs₂) ⟨evs₁, evs₂, rfl, h1, h2⟩

/-- Extract `FitsEnvCap M lim st E` and `lim.enforced = true` (when `E` is inhabited) from any
    `FitsEnv` whose continuation starts with `WriteStdoutEnv` (which contains `rustAllocEvents 1024 1`). -/
theorem of_seq_writeStdout {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E E_tail : List AllocEvent → Prop}
    (h : FitsEnv M lim st (SeqEnv E (SeqEnv WriteStdoutEnv E_tail))) :
    FitsEnvCap M lim st E ∧ (∀ evs, E evs → lim.enforced = true) := by
  have halloc : rustAllocEvents 1024 1 = [.alloc 1024] := by decide
  have hcap_enf : ∀ evs, E evs →
      lim.staticBytes + M.footprint (M.stepEvents evs st) ≤ lim.physCap ∧ lim.enforced = true := by
    intro evs hevs
    have hmem : SeqEnv E (SeqEnv WriteStdoutEnv E_tail) (evs ++ rustAllocEvents 1024 1) :=
      Or.inr ⟨evs, rustAllocEvents 1024 1, rfl, hevs, Or.inl writeStdoutEnv_init1024⟩
    have hfe := ((fitsEvents_append M lim evs (rustAllocEvents 1024 1) st).mp (h _ hmem)).2
    rw [halloc] at hfe
    rcases hfe.1.2 with ⟨henf, hram, _⟩
    exact ⟨by omega, henf⟩
  exact ⟨⟨h.seq_left, fun evs hevs => (hcap_enf evs hevs).1⟩, fun evs hevs => (hcap_enf evs hevs).2⟩

end FitsEnvCap

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBound
