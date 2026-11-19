/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import

/-!
# Sequential `PhaseCreditSpec` Combinators for W4 Outer `process_prekey`

`GeneratedLean`-free `PhaseCreditSpec` combinators in binary execution order for W4 `decrypt_prekey` /
`process_prekey`: trailing `FreeOnlyEvs` suffixes, optional conditional steps, 3-way and 4-way arm
dispatch, boxed store-future steps, `StringCloneEnv` / `SignalProtocolError` allocations, and
Stage P1, Stage P4, and `SlotW4` pipelines.
-/

public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers

set_option autoImplicit false

open CryptoVerification.LibsignalSessionRepr (VecGhost)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel SeqEnv FreeOnlyEvs
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (StringCloneEnv stringCloneEvents stringCloneEvents_eq_of_env)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec FreeOnlyAlign16Evs)

/-! ## 1. Trailing `FreeOnlyEvs`, Optional Steps, and Multi-Arm Dispatch -/

theorem phaseCreditSpec_seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l (max p l) r := by
  exact (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Optional binary step `if cond then E else (· = [])`. -/
theorem phaseCreditSpec_ite_nil {M : AllocCostModel} [HasFineReallocCredit M]
    (cond : Bool) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : cond = true → PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (if cond then E else (· = [])) c l p r := by
  cases hcond : cond
  · simpa [hcond] using (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · simpa [hcond] using h hcond

/-- 4-arm disjunction combinator (`Untrusted | PathA | PathB | PathC`). -/
theorem phaseCreditSpec_or4 {M : AllocCostModel} [HasFineReallocCredit M]
    {E E₁ E₂ E₃ E₄ : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄ : Nat}
    (himp : ∀ evs, E evs → E₁ evs ∨ E₂ evs ∨ E₃ evs ∨ E₄ evs)
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂)
    (h₃ : PhaseCreditSpec M E₃ c₃ l₃ p₃ r₃)
    (h₄ : PhaseCreditSpec M E₄ c₄ l₄ p₄ r₄) :
    PhaseCreditSpec M E
      (max (max c₁ c₂) (max c₃ c₄))
      (max (max l₁ l₂) (max l₃ l₄))
      (max (max p₁ p₂) (max p₃ p₄))
      (max (max r₁ r₂) (max r₃ r₄)) := by
  refine PhaseCreditSpec.or_of_imp ?_ (h₁.or h₂) (h₃.or h₄)
  intro evs hevs
  rcases himp evs hevs with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## 2. Boxed Store-Future Steps (`BoxAlloc → Poll → BoxDealloc`) -/

/-- Boxed store-future allocation predicate. -/
@[expose] def BoxPtrAllocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  ∃ boxPtr : BitVec 64, boxPtr ≠ 0#64 ∧ evs = rustAllocEvents boxSize 8

/-- Boxed store-future deallocation predicate. -/
@[expose] def BoxPtrDeallocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  evs = rustDeallocEvents boxSize 8

theorem boxPtrAllocEnv_events {boxSize : Nat} {evs : List AllocEvent}
    (h : BoxPtrAllocEnv boxSize evs) : evs = rustAllocEvents boxSize 8 := by
  rcases h with ⟨_, _, rfl⟩
  rfl

/-! ## 3. `StringCloneEnv` and `192`-Byte `SignalProtocolError` Allocation -/

theorem stringClone_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) :
    PhaseCreditSpec M (StringCloneEnv g)
      (2 * maxLen + 9539) (maxLen + 8195) (maxLen + 8195) maxLen := by
  by_cases hz : g.bytes.length = 0
  · refine (PhaseCreditSpec.of_eq_nil (M := M) ?_).mono
      (by omega) (by omega) (by omega) (by omega)
    intro evs hevs
    rw [stringCloneEvents_eq_of_env hevs]
    simp [stringCloneEvents, hz]
  · have hEq : ∀ evs, StringCloneEnv g evs → evs = rustAllocEvents g.bytes.length 1 := by
      intro evs hevs
      rw [stringCloneEvents_eq_of_env hevs]
      simp [stringCloneEvents, hz]
    exact (PhaseCreditSpec.of_imp hEq
      (PhaseCreditSpec.rustAlloc_aff (req := g.bytes.length) (al := 1) hM (by decide))).mono
      (by omega) (by omega) (by omega) hlen

theorem stringClone_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) (hsmall : maxLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (StringCloneEnv g) (2 * maxLen + 9539) 0 0 maxLen := by
  by_cases hz : g.bytes.length = 0
  · refine (PhaseCreditSpec.of_eq_nil (M := M) ?_).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (by omega)
    intro evs hevs
    rw [stringCloneEvents_eq_of_env hevs]
    simp [stringCloneEvents, hz]
  · have hEq : ∀ evs, StringCloneEnv g evs → evs = rustAllocEvents g.bytes.length 1 := by
      intro evs hevs
      rw [stringCloneEvents_eq_of_env hevs]
      simp [stringCloneEvents, hz]
    have hle : g.bytes.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hlen hsmall
    exact (PhaseCreditSpec.of_imp hEq
      (PhaseCreditSpec.rustAlloc_small_any (req := g.bytes.length) (al := 1) hM (by decide) hle)).mono
      (Nat.le_trans (hM.smallAlloc_le hle) (by omega)) (Nat.le_refl _) (Nat.le_refl _) hlen

theorem alloc192_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ErrEv : List AllocEvent → Prop}
    (hErr : ∀ evs, ErrEv evs → evs = rustAllocEvents 192 8) :
    PhaseCreditSpec M ErrEv 9923 8387 8387 192 := by
  exact (PhaseCreditSpec.of_imp hErr
    (PhaseCreditSpec.rustAlloc_aff (req := 192) (al := 8) hM (by decide))).mono
    (by omega) (by omega) (by omega) (Nat.le_refl _)

theorem alloc192_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ErrEv : List AllocEvent → Prop}
    (hErr : ∀ evs, ErrEv evs → evs = rustAllocEvents 192 8)
    (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M ErrEv 9923 0 0 192 := by
  exact (PhaseCreditSpec.of_imp hErr
    (PhaseCreditSpec.rustAlloc_small_any (req := 192) (al := 8) hM (by decide) hsmall)).mono
    (Nat.le_trans (hM.smallAlloc_le hsmall) (by omega))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-! ## 4. Stage P1, Stage P4, and `SlotW4` Sequential Pipelines -/

end LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
