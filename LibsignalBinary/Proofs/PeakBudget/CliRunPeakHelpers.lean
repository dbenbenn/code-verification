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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget -- proof-setup: allow-public-import

/-!
# CLI `signal_session::run` Envelope Composition Helpers

Sequential `PhaseCreditSpec` combinators for `signal_session::run`: `FreeOnlyEvs` epilogue and
early-reject absorption, `cliConcat2Events` framing bounds, temporary `align = 1` byte-buffer
allocation/deallocation cancellation (`Δlive` cancellation across bundle reads), and multi-stage
`R0 → Arm → J` dispatch composition.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers

open CryptoVerification.SignalSession.Cli.RunProofs (kemPkDeserialize kemPkLen)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
  (cliConcat2Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)

/-! ## `FreeOnlyEvs` Epilogue and Early-Reject Disjunction Absorption -/

/-- Sequential composition of two `FreeOnlyEvs` phases (e.g., `dropSpeOwned` followed by
`dropStores` in `RejectKPlacedEnv`) remains `FreeOnlyEvs`. -/
theorem freeOnlyEvs_of_seqEnv {E₁ E₂ : List AllocEvent → Prop}
    (h₁ : ∀ evs, E₁ evs → FreeOnlyEvs evs)
    (h₂ : ∀ evs, E₂ evs → FreeOnlyEvs evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    FreeOnlyEvs evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact h₁ evs hE1
  · intro ev hev
    rcases List.mem_append.mp hev with hm1 | hm2
    · exact h₁ evs₁ hE1 ev hm1
    · exact h₂ evs₂ hE2 ev hm2

/-- Appending a `FreeOnlyEvs` cleanup phase (such as `dropSignalMessage`, `dropPreKeyMsg`,
`dropSpeOwned`, or `J`'s `dropStores`) in `SeqEnv` order preserves `(c, l, p, r)` whenever `l ≤ p`. -/
theorem phaseCredit_seq_freeOnly_right {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E E_free : List AllocEvent → Prop} {c l p r : Nat}
    (hE : PhaseCreditSpec M E c l p r)
    (hfree : ∀ evs, E_free evs → FreeOnlyEvs evs)
    (hlp : l ≤ p) :
    PhaseCreditSpec M (SeqEnv E E_free) c l p r := by
  have hf : PhaseCreditSpec M E_free 0 0 0 0 :=
    PhaseCreditSpec.of_freeOnlyEvs_hyps hM hfree
  exact (hE.seq hf).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCredit_seq_freeOnly_left {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E_free E : List AllocEvent → Prop} {c l p r : Nat}
    (hfree : ∀ evs, E_free evs → FreeOnlyEvs evs)
    (hE : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E_free E) c l p r := by
  have hf : PhaseCreditSpec M E_free 0 0 0 0 :=
    PhaseCreditSpec.of_freeOnlyEvs_hyps hM hfree
  exact (hf.seq hE).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCredit_or_freeOnly_left {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E_free E : List AllocEvent → Prop} {c l p r : Nat}
    (hfree : ∀ evs, E_free evs → FreeOnlyEvs evs)
    (hE : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (fun evs => E_free evs ∨ E evs) c l p r := by
  have hf : PhaseCreditSpec M E_free 0 0 0 0 :=
    PhaseCreditSpec.of_freeOnlyEvs_hyps hM hfree
  exact (hf.or hE).mono (by omega) (by omega) (by omega) (by omega)

/-! ## `cliConcat2Events` Fine-Credit Bounds -/

/-! ## Temporary `align = 1` Byte-Slice Allocation Cancellation -/

@[expose] def allocBytes1OfLen (n : Nat) : List AllocEvent :=
  if n = 0 then [] else rustAllocEvents n 1

@[expose] def deallocBytes1OfLen (n : Nat) : List AllocEvent :=
  if n = 0 then [] else rustDeallocEvents n 1

theorem allocBytes1Events_eq_allocBytes1OfLen (bs : List (BitVec 8)) :
    allocBytes1Events bs = allocBytes1OfLen bs.length :=
  rfl

/-- Unconditional affine fine-credit bound for `allocBytes1OfLen n` (`n ≤ cap`), valid for both
small and `sc = 63` large byte allocations. -/
theorem phaseCredit_allocBytes1OfLen_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n cap : Nat} (hle : n ≤ cap) :
    PhaseCreditSpec M (· = allocBytes1OfLen n)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  unfold allocBytes1OfLen
  by_cases hz : n = 0
  · simp only [hz, ↓reduceIte]
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · simp only [hz, ↓reduceIte]
    exact (PhaseCreditSpec.rustAlloc_aff hM (by decide)).mono
      (by omega) (by omega) (by omega) hle

/-- Exact-order `allocBytes1OfLen n → E_body → deallocBytes1OfLen n` fine-credit cancellation:
cancels `n + 8195` out of post-deallocation `Δlive` (`Δlive = l_b`), while accounting for the
transient buffer inside `Δcum` and `Δpeak`, uniformly across `n = 0`, small `n`, and `sc = 63`
large `n ≤ cap`. -/
theorem phaseCredit_tempBytes1BodyFree_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n cap : Nat} {E_body : List AllocEvent → Prop}
    {c_b l_b p_b r_b : Nat}
    (hle : n ≤ cap)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = allocBytes1OfLen n) E_body) (· = deallocBytes1OfLen n))
      (2 * cap + 9539 + c_b) l_b (cap + 8195 + p_b) (max cap r_b) := by
  unfold allocBytes1OfLen deallocBytes1OfLen
  by_cases hz : n = 0
  · simp only [hz, ↓reduceIte]
    have hbody' :
        PhaseCreditSpec M
          (ConcatEnv (ConcatEnv (· = []) E_body) (· = []))
          c_b l_b p_b r_b :=
      hbody.of_imp fun evs h => by
        have h1 := ConcatEnv.nil_right_iff.mp h
        exact ConcatEnv.nil_left_iff.mp h1
    exact hbody'.mono (by omega) (Nat.le_refl l_b) (by omega) (by omega)
  · simp only [hz, ↓reduceIte]
    exact (PhaseCreditSpec.tempAllocBodyFree_aff hM (by decide) hbody).mono
      (by omega) (Nat.le_refl l_b) (by omega) (by omega)

theorem phaseCredit_tempAllocBytes1BodyFree_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {bs : List (BitVec 8)} {cap : Nat}
    {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hle : bs.length ≤ cap)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = allocBytes1Events bs) E_body) (· = deallocBytes1OfLen bs.length))
      (2 * cap + 9539 + c_b) l_b (cap + 8195 + p_b) (max cap r_b) :=
  phaseCredit_tempBytes1BodyFree_le hM hle hbody

/-! ## Multi-Stage Arm and `R0 → Arm → J` Composition -/

/-- Top-level `signal_session::run` envelope composition `SeqEnv E_R0 (SeqEnv E_arm E_J)` in exact
binary call order (`R0 → Arm → J`), absorbing the `FreeOnlyEvs` join epilogue `E_J` whenever
`l_a ≤ p_a`. -/
theorem phaseCredit_runDispatch {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {E_R0 E_arm E_J : List AllocEvent → Prop}
    {c₀ l₀ p₀ r₀ c_a l_a p_a r_a : Nat}
    (hR0 : PhaseCreditSpec M E_R0 c₀ l₀ p₀ r₀)
    (harm : PhaseCreditSpec M E_arm c_a l_a p_a r_a)
    (hJ : ∀ evs, E_J evs → FreeOnlyEvs evs)
    (hlp_a : l_a ≤ p_a) :
    PhaseCreditSpec M (SeqEnv E_R0 (SeqEnv E_arm E_J))
      (c₀ + c_a) (l₀ + l_a) (max p₀ (l₀ + p_a)) (max r₀ r_a) :=
  hR0.seq (phaseCredit_seq_freeOnly_right hM harm hJ hlp_a)

end LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
