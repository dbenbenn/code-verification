/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `PhaseCreditSpec`, `PhaseGroupSpec`, & `FitsEnv` Peak-Budget Bridges for Formatting Envelopes (`HooksDehook.CliFmtPeakCreditBridges`)

Untrusted (`Role::Proof`) `SeqCreditKit` and `GroupCreditKit` bounds for every `CliIoFmt`
formatting allocation envelope (`CliFmtWriteEnv`, `CliFormatInnerEnv`, `MsgDeserErrEnv`):

1. **`NonFreeBound` (`≤ 3` non-free allocator events) & Generic `PhaseGroupSpec` (`9 * FineScale`):**
   Every formatting trace performs at most `3` small allocations/reallocations (`NonFreeBound E 3`),
   giving `PhaseGroupSpec M E (9 * FineScale)` for any `[HasFineGroupCredit M]`.
2. **Parametric `ModelHyps M` & Concrete `fineCostModel` `PhaseCreditSpec`s:**
   - Unconditional `(hM : ModelHyps M)`: `PhaseCreditSpec M E 31017 25785 25785 400`
     (`29097 25185 25185 80` for `CliFmtWriteEnv`; `30537 25545 25545 320` for
     `CliFormatInnerEnv` / `MsgDeserErrEnv`).
   - Small-threshold `(hM : ModelHyps M) (hsm : r ≤ smallMaxReq M)` and `fineCostModel`:
     `Δlive = 0`, `Δpeak = 0` (`CliFmtWriteEnv`: `Δcum = 29,097`, `maxReq = 80`;
     `CliFormatInnerEnv` & `MsgDeserErrEnv`: `Δcum = 30,537`, `maxReq = 320`; unified `31,017 / 400`).
3. **End-to-End `FitsEnv` Non-Vacuity under `nonVacLimits` (`1 GiB` RAM cap).**
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtPeakCreditBridges

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq fineDynIvsOfCum fineMaxGroupsOfCum
   fineMaxMetaAreasOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (CliBufShape fmtWriteKnownEvents formatInnerKnownEvents startCliBufShape stringGrowStepEvents)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof (FmtWriteAddrEnv)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
  (FormatInnerAddrEnv FormatInnerAnyU32Env FormatInnerAnyU8Env FormatInnerFromStrEnv
   FormatInnerShortLitEnv FormatInnerSingleEnv formatInnerKnownEvents_zero_singleton)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec nonFreeCount nonFreeCount_append
   nonFreeCount_rustAllocEvents nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fineCostModel_smallAff fitsEnv_fineCostModel_of_phaseCredit nonVacLimits)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFmtWriteEnv CliFormatInnerEnv FormatInnerPrefixedEnv MsgDeserErrEnv
   cliFmtWriteEnv_iff cliFormatInnerEnv_iff formatInnerAnyU8Env_eq_alloc8 msgDeserErrEnv_iff)
open VerifiedLibraries.RustStd (stringGrowCap)

/-! ## 1. Single `String` Growth Step & `CliBufShape.append` Algebra -/

private theorem req_align_rustAlloc_le {req maxReq : Nat} (hreq : req ≤ maxReq) :
    ∀ ev ∈ rustAllocEvents req 1, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

private theorem req_align_rustRealloc_le {oldCap newCap maxReq : Nat}
    (hpos : 1 ≤ newCap) (hnew : newCap ≤ maxReq) :
    ∀ ev ∈ rustReallocEvents oldCap newCap 1, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  have hcond : (1 : Nat) ≤ 16 ∧ 1 ≤ newCap := ⟨by decide, hpos⟩
  simp only [hcond, and_self, ↓reduceIte]
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨hnew, by simp [eventStepAlign]⟩

private theorem nonFree_req_stringGrowStepEvents {oldCap newCap maxReq : Nat}
    (hpos : 1 ≤ newCap) (hnew : newCap ≤ maxReq) :
    nonFreeCount (stringGrowStepEvents oldCap newCap) = 1 ∧
      ∀ ev ∈ stringGrowStepEvents oldCap newCap,
        eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold stringGrowStepEvents
  by_cases h0 : oldCap = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨nonFreeCount_rustAllocEvents newCap 1, req_align_rustAlloc_le hnew⟩
  · simp only [h0, ↓reduceIte]
    exact ⟨nonFreeCount_rustReallocEvents oldCap newCap 1, req_align_rustRealloc_le hpos hnew⟩

/-- `PhaseCreditSpec` for a single small `String` growth step (`oldCap = 0` → `alloc(newCap, 1)`;
    `oldCap > 0` → `realloc(oldCap, newCap, 1)`). -/
theorem phaseCreditSpec_stringGrowStepEvents {oldCap newCap maxReq : Nat}
    (hold : oldCap ≤ 135167) (hpos : 1 ≤ newCap) (hnew : newCap ≤ maxReq)
    (hmax : maxReq ≤ 135167) :
    PhaseCreditSpec fineCostModel (· = stringGrowStepEvents oldCap newCap)
      (2 * maxReq + 9539) 0 0 maxReq := by
  unfold stringGrowStepEvents
  have hnew_sm : newCap ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  by_cases h0 : oldCap = 0
  · simp only [h0, ↓reduceIte]
    have haff := (fineCostModel_smallAff newCap hnew_sm).1
    exact (PhaseCreditSpec.rustAlloc_small fineCostModel (req := newCap) (al := 1)
      (by decide) (by omega) hnew_sm).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew
  · simp only [h0, ↓reduceIte]
    have hold_sm : oldCap ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    have haff := (fineCostModel_smallAff newCap hnew_sm).2
    exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel
      (old := oldCap) (new := newCap) (al := 1)
      (by decide) hpos (by omega) hold_sm (by omega) hnew_sm).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew

/-- Per-append delta event list emitted by `CliBufShape.append`. -/
@[expose] def cliBufAppendStepEvs (len cap n : Nat) : List AllocEvent :=
  if len + n ≤ cap then []
  else stringGrowStepEvents cap (stringGrowCap cap len n)

private theorem cliBufShape_append_decomp (sh : CliBufShape) (n : Nat) :
    (sh.append n).evs = sh.evs ++ cliBufAppendStepEvs sh.len sh.cap.toNat n ∧
      (sh.append n).len = sh.len + n ∧
      (sh.len + n + 2 * sh.cap.toNat + 8 < 2 ^ 64 →
        (sh.append n).cap.toNat ≤ max (max (2 * sh.cap.toNat) (sh.len + n)) 8) := by
  unfold CliBufShape.append cliBufAppendStepEvs
  by_cases hle : sh.len + n ≤ sh.cap.toNat
  · simp only [hle, ↓reduceIte, List.append_nil]
    exact ⟨trivial, trivial, fun _ => by omega⟩
  · simp only [hle, ↓reduceIte]
    refine ⟨trivial, trivial, fun hlt => ?_⟩
    have hgrow_eq : stringGrowCap sh.cap.toNat sh.len n =
        max (max (2 * sh.cap.toNat) (sh.len + n)) 8 := by
      unfold stringGrowCap; omega
    have hmod : (BitVec.ofNat 64 (stringGrowCap sh.cap.toNat sh.len n)).toNat =
        stringGrowCap sh.cap.toNat sh.len n := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by rw [hgrow_eq]; omega)
    rw [hmod, hgrow_eq]

private theorem nonFree_req_cliBufAppendStepEvs {len cap n maxReq : Nat}
    (hgrow : max (max (2 * cap) (len + n)) 8 ≤ maxReq) :
    nonFreeCount (cliBufAppendStepEvs len cap n) ≤ 1 ∧
      ∀ ev ∈ cliBufAppendStepEvs len cap n,
        eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold cliBufAppendStepEvs
  by_cases hle : len + n ≤ cap
  · simp only [hle, ↓reduceIte]
    exact ⟨Nat.zero_le 1, fun _ h => nomatch h⟩
  · simp only [hle, ↓reduceIte]
    have hgrow_eq : stringGrowCap cap len n = max (max (2 * cap) (len + n)) 8 := by
      unfold stringGrowCap; omega
    obtain ⟨hnf, hrq⟩ := nonFree_req_stringGrowStepEvents (oldCap := cap)
      (newCap := stringGrowCap cap len n) (maxReq := maxReq)
      (by rw [hgrow_eq]; omega) (by rw [hgrow_eq]; exact hgrow)
    exact ⟨Nat.le_of_eq hnf, hrq⟩

private theorem startCliBufShape_props {cap0 maxReq : Nat}
    (hcap0 : cap0 ≤ maxReq) (hlt : cap0 < 2 ^ 64) :
    let sh0 := startCliBufShape cap0
    sh0.len = 0 ∧ sh0.cap.toNat = cap0 ∧
      nonFreeCount sh0.evs ≤ 1 ∧
      ∀ ev ∈ sh0.evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold startCliBufShape
  dsimp only
  have hmod : (BitVec.ofNat 64 cap0).toNat = cap0 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  refine ⟨rfl, hmod, ?_, ?_⟩
  · split
    · exact Nat.zero_le 1
    · exact Nat.le_of_eq (nonFreeCount_rustAllocEvents cap0 1)
  · split
    · intro _ h; nomatch h
    · exact req_align_rustAlloc_le hcap0

/-! ## 2. Generic `NonFreeBound + maxReq` → `PhaseCreditSpec` Bridges under `ModelHyps M` -/

private theorem stepEvents_nonFree_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {r : Nat} (hsm : r ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st0 : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ r ∧ eventStepAlign ev ≤ 16) →
      let stf := M.stepEvents evs st0
      HasFineReallocCredit.cumSmall stf ≤
        HasFineReallocCredit.cumSmall st0 + nonFreeCount evs * (2 * r + 9539) ∧
      HasFineReallocCredit.liveLarge stf ≤ HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge stf ≤ HasFineReallocCredit.peakLarge st0
  | [], st0, _ => by
    simp only [AllocCostModel.stepEvents_nil, nonFreeCount, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: tl, st0, hreq => by
    rw [AllocCostModel.stepEvents_cons]
    have hhead := hreq ev List.mem_cons_self
    have htail : ∀ e ∈ tl, eventStepReq e ≤ r ∧ eventStepAlign e ≤ 16 :=
      fun e he => hreq e (List.mem_cons_of_mem _ he)
    cases ev with
    | free al sz =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_nonFree_small hM hsm tl (M.step (.free al sz) st0) htail
      simp only [nonFreeCount]
      omega
    | alloc req =>
      have hreq_r : req ≤ r := hhead.1
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq_r hsm
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_alloc_small_any st0 hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_nonFree_small hM hsm tl (M.step (.alloc req) st0) htail
      simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | aligned al req =>
      have hreq_r : req ≤ r := hhead.1
      have hal : al ≤ 16 := hhead.2
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq_r hsm
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_aligned_small_any st0 hal hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_nonFree_small hM hsm tl (M.step (.aligned al req) st0) htail
      simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | realloc al old newSz =>
      have hreq_r : newSz ≤ r := hhead.1
      have hal : al ≤ 16 := hhead.2
      have hnew_le : newSz ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq_r hsm
      have hsr := hM.smallRealloc_le hnew_le
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_nonFree_small hM hsm tl (M.step (.realloc al old newSz) st0) htail
      by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_realloc_small_small_any st0 hal hold_le hnew_le
        simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
        omega
      · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
        obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_realloc_large_small_any st0 hal hold_gt hnew_le
        simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
        omega

private theorem stepEvents_nonFree_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (r : Nat) :
    ∀ (evs : List AllocEvent) (st0 : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ r ∧ eventStepAlign ev ≤ 16) →
      let stf := M.stepEvents evs st0
      HasFineReallocCredit.cumSmall stf ≤
        HasFineReallocCredit.cumSmall st0 + nonFreeCount evs * (2 * r + 9539) ∧
      HasFineReallocCredit.liveLarge stf ≤
        HasFineReallocCredit.liveLarge st0 + nonFreeCount evs * (r + 8195) ∧
      HasFineReallocCredit.peakLarge stf ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + nonFreeCount evs * (r + 8195))
  | [], st0, _ => by
    simp only [AllocCostModel.stepEvents_nil, nonFreeCount, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | ev :: tl, st0, hreq => by
    rw [AllocCostModel.stepEvents_cons]
    have hhead := hreq ev List.mem_cons_self
    have htail : ∀ e ∈ tl, eventStepReq e ≤ r ∧ eventStepAlign e ≤ 16 :=
      fun e he => hreq e (List.mem_cons_of_mem _ he)
    cases ev with
    | free al sz =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_nonFree_any hM r tl (M.step (.free al sz) st0) htail
      simp only [nonFreeCount]
      omega
    | alloc req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff (ev := .alloc req) st0 hhead.1 hhead.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_nonFree_any hM r tl (M.step (.alloc req) st0) htail
      simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | aligned al req =>
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff (ev := .aligned al req) st0 hhead.1 hhead.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_nonFree_any hM r tl (M.step (.aligned al req) st0) htail
      simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega
    | realloc al old newSz =>
      obtain ⟨hc₁, hl₁, hp₁⟩ :=
        hM.step_nonFree_aff (ev := .realloc al old newSz) st0 hhead.1 hhead.2
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_nonFree_any hM r tl (M.step (.realloc al old newSz) st0) htail
      simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
      omega

private theorem phaseCreditSpec_of_nonFree_small {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {k r : Nat}
    (hM : ModelHyps M) (hsm : r ≤ HasFineReallocCredit.smallMaxReq M)
    (hOps : NonFreeBound Env k)
    (hReq : ∀ evs, Env evs → ∀ ev ∈ evs, eventStepReq ev ≤ r ∧ eventStepAlign ev ≤ 16) :
    PhaseCreditSpec M Env (k * (2 * r + 9539)) 0 0 r where
  req_align := hReq
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_nonFree_small hM hsm evs st0 (hReq evs hE)
    have hmul := Nat.mul_le_mul_right (2 * r + 9539) (hOps evs hE)
    omega

private theorem phaseCreditSpec_of_nonFree_any {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {k r : Nat}
    (hM : ModelHyps M)
    (hOps : NonFreeBound Env k)
    (hReq : ∀ evs, Env evs → ∀ ev ∈ evs, eventStepReq ev ≤ r ∧ eventStepAlign ev ≤ 16) :
    PhaseCreditSpec M Env (k * (2 * r + 9539)) (k * (r + 8195)) (k * (r + 8195)) r where
  req_align := hReq
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_nonFree_any hM r evs st0 (hReq evs hE)
    have hmulC := Nat.mul_le_mul_right (2 * r + 9539) (hOps evs hE)
    have hmulL := Nat.mul_le_mul_right (r + 8195) (hOps evs hE)
    omega

/-! ## 3. Structural Event Bounds (`NonFreeBound` & `maxReq`) for Formatting Envelopes -/

private theorem addrEnv_ops_req {nameLen devDigits : Nat}
    (hn : nameLen ≤ 40) (hd1 : 1 ≤ devDigits) (hd2 : devDigits ≤ 10)
    {evs : List AllocEvent} (hEnv : FormatInnerAddrEnv nameLen devDigits evs) :
    nonFreeCount evs ≤ 3 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 80 ∧ eventStepAlign ev ≤ 16 := by
  have _ := hd1
  set sh0 : CliBufShape := startCliBufShape 0
  have hsh0_evs : sh0.evs = [] := rfl
  have hsh0_len : sh0.len = 0 := rfl
  have hsh0_cap : sh0.cap.toNat = 0 := by decide
  obtain ⟨he1, hl1, hc1_imp⟩ := cliBufShape_append_decomp sh0 nameLen
  set sh1 : CliBufShape := sh0.append nameLen
  have hc1 : sh1.cap.toNat ≤ 40 := by
    have h := hc1_imp (by rw [hsh0_len, hsh0_cap]; omega)
    rw [hsh0_len, hsh0_cap] at h; omega
  obtain ⟨he2, hl2, hc2_imp⟩ := cliBufShape_append_decomp sh1 1
  set sh2 : CliBufShape := sh1.append 1
  have hc2 : sh2.cap.toNat ≤ 80 := by
    have h := hc2_imp (by rw [hl1, hsh0_len]; omega)
    rw [hl1, hsh0_len] at h; omega
  obtain ⟨he3, _, _⟩ := cliBufShape_append_decomp sh2 devDigits
  set sh3 : CliBufShape := sh2.append devDigits
  have hg1 : max (max (2 * sh0.cap.toNat) (sh0.len + nameLen)) 8 ≤ 80 := by
    rw [hsh0_cap, hsh0_len]; omega
  have hg2 : max (max (2 * sh1.cap.toNat) (sh1.len + 1)) 8 ≤ 80 := by
    rw [hl1, hsh0_len]; omega
  unfold FormatInnerAddrEnv formatInnerKnownEvents CliBufShape.run List.foldl at hEnv
  change evs = sh3.evs at hEnv
  obtain ⟨hn1, hr1⟩ := nonFree_req_cliBufAppendStepEvs hg1
  obtain ⟨hn2, hr2⟩ := nonFree_req_cliBufAppendStepEvs hg2
  have hstep3 : nonFreeCount (cliBufAppendStepEvs sh2.len sh2.cap.toNat devDigits) ≤ 1 ∧
      ∀ ev ∈ cliBufAppendStepEvs sh2.len sh2.cap.toNat devDigits,
        eventStepReq ev ≤ 80 ∧ eventStepAlign ev ≤ 16 := by
    by_cases hfit3 : sh2.len + devDigits ≤ sh2.cap.toNat
    · unfold cliBufAppendStepEvs; simp only [hfit3, ↓reduceIte]
      exact ⟨Nat.zero_le 1, fun _ h => nomatch h⟩
    · -- If `sh2.len + devDigits > sh2.cap.toNat`, then `sh2.cap.toNat < nameLen + 1 + 10 ≤ 51`,
      -- wait: even simpler, if `11 ≤ nameLen`, `sh1.cap.toNat` is AT LEAST `nameLen`!
      -- Let's prove `sh2.cap.toNat ≤ 20` when `¬ (sh2.len + devDigits ≤ sh2.cap.toNat)`!
      have hcap2_le20 : sh2.cap.toNat ≤ 20 := by
        -- Compute `sh1.cap.toNat` directly!
        have hc1_exact : sh1.cap.toNat = max nameLen 8 ∨ (nameLen = 0 ∧ sh1.cap.toNat = 0) := by
          unfold sh1 sh0 startCliBufShape CliBufShape.append
          dsimp only
          by_cases hn0 : nameLen = 0
          · right; simp [hn0]
          · left
            have hle0 : ¬ (0 + nameLen ≤ (0#64).toNat) := by
              change ¬ (0 + nameLen ≤ 0); omega
            simp only [hle0, ↓reduceIte]
            have hg : stringGrowCap (0#64).toNat 0 nameLen = max nameLen 8 := by
              change stringGrowCap 0 0 nameLen = max nameLen 8
              unfold stringGrowCap; omega
            rw [hg, BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by omega)
        have hc2_exact : sh2.cap.toNat = 8 ∨ (8 ≤ nameLen ∧ sh2.cap.toNat = 2 * nameLen) := by
          unfold sh2 CliBufShape.append
          rcases hc1_exact with hc1_ge | ⟨rfl, hc1_0⟩
          · by_cases hn8 : nameLen < 8
            · have h1 : sh1.cap.toNat = 8 := by omega
              have hle1 : sh1.len + 1 ≤ sh1.cap.toNat := by rw [hl1, hsh0_len, h1]; omega
              simp only [hle1, ↓reduceIte]; left; exact h1
            · have h1 : sh1.cap.toNat = nameLen := by omega
              have hle1 : ¬ (sh1.len + 1 ≤ sh1.cap.toNat) := by rw [hl1, hsh0_len, h1]; omega
              simp only [hle1, ↓reduceIte]
              right; refine ⟨by omega, ?_⟩
              have hg : stringGrowCap sh1.cap.toNat sh1.len 1 = 2 * nameLen := by
                rw [h1, hl1, hsh0_len]; unfold stringGrowCap; omega
              rw [hg, BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt (by omega)
          · have hle1 : ¬ (sh1.len + 1 ≤ sh1.cap.toNat) := by rw [hl1, hsh0_len, hc1_0]; omega
            simp only [hle1, ↓reduceIte]; left
            have hg : stringGrowCap sh1.cap.toNat sh1.len 1 = 8 := by
              rw [hc1_0, hl1, hsh0_len]; unfold stringGrowCap; omega
            rw [hg, BitVec.toNat_ofNat]
        rw [hl2, hl1, hsh0_len] at hfit3
        rcases hc2_exact with h8 | ⟨hge8, h2n⟩ <;> omega
      exact nonFree_req_cliBufAppendStepEvs
        (by rw [hl2, hl1, hsh0_len]; omega)
  obtain ⟨hn3, hr3⟩ := hstep3
  rw [hEnv, he3, he2, he1, hsh0_evs, List.nil_append]
  refine ⟨?_, ?_⟩
  · rw [nonFreeCount_append, nonFreeCount_append]; omega
  · intro ev hev
    rcases List.mem_append.mp hev with he12 | he3'
    · rcases List.mem_append.mp he12 with he1' | he2'
      · exact hr1 ev he1'
      · exact hr2 ev he2'
    · exact hr3 ev he3'

private theorem prefixedEnv_ops_req {evs : List AllocEvent} (hEnv : FormatInnerPrefixedEnv evs) :
    nonFreeCount evs ≤ 3 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 320 ∧ eventStepAlign ev ≤ 16 := by
  rcases hEnv with ⟨cap0, n0, hcap0, hn0, rest, hlen, hsum, rfl⟩
  obtain ⟨hl0, hc0, hnf0, hrq0⟩ := startCliBufShape_props (cap0 := cap0) (maxReq := 320)
    (by omega) (by omega)
  set sh0 := startCliBufShape cap0
  obtain ⟨he1, hl1, _⟩ := cliBufShape_append_decomp sh0 n0
  set sh1 := sh0.append n0
  have hfit0 : sh0.len + n0 ≤ sh0.cap.toNat := by rw [hl0, hc0]; omega
  have hstep1_nil : cliBufAppendStepEvs sh0.len sh0.cap.toNat n0 = [] := by
    unfold cliBufAppendStepEvs; simp [hfit0]
  have he1_eq : sh1.evs = sh0.evs := by rw [he1, hstep1_nil, List.append_nil]
  have hc1_eq : sh1.cap.toNat = cap0 := by
    have hsh1 : sh1.cap = sh0.cap := by unfold sh1 CliBufShape.append; simp [hfit0]
    rw [hsh1, hc0]
  unfold formatInnerKnownEvents CliBufShape.run
  rcases rest with _ | ⟨r1, _ | ⟨r2, _ | _⟩⟩
  · dsimp only [List.foldl]
    change nonFreeCount sh1.evs ≤ 3 ∧ _
    rw [he1_eq]
    exact ⟨by omega, hrq0⟩
  · simp only [List.sum_cons, List.sum_nil] at hsum
    dsimp only [List.foldl]
    obtain ⟨he2, _, _⟩ := cliBufShape_append_decomp sh1 r1
    obtain ⟨hn2, hr2⟩ := nonFree_req_cliBufAppendStepEvs
      (len := sh1.len) (cap := sh1.cap.toNat) (n := r1) (maxReq := 320)
      (by rw [hc1_eq, hl1, hl0]; omega)
    change nonFreeCount (sh1.append r1).evs ≤ 3 ∧ _
    rw [he2, he1_eq]
    refine ⟨by rw [nonFreeCount_append]; omega, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with h0 | h2
    · exact hrq0 ev h0
    · exact hr2 ev h2
  · simp only [List.sum_cons, List.sum_nil] at hsum
    dsimp only [List.foldl]
    obtain ⟨he2, hl2, hc2_imp⟩ := cliBufShape_append_decomp sh1 r1
    set sh2 := sh1.append r1
    have hc2 : sh2.cap.toNat ≤ 160 := by
      have h := hc2_imp (by rw [hc1_eq, hl1, hl0]; omega)
      rw [hc1_eq, hl1, hl0] at h; omega
    obtain ⟨hn2, hr2⟩ := nonFree_req_cliBufAppendStepEvs
      (len := sh1.len) (cap := sh1.cap.toNat) (n := r1) (maxReq := 320)
      (by rw [hc1_eq, hl1, hl0]; omega)
    obtain ⟨he3, _, _⟩ := cliBufShape_append_decomp sh2 r2
    obtain ⟨hn3, hr3⟩ := nonFree_req_cliBufAppendStepEvs
      (len := sh2.len) (cap := sh2.cap.toNat) (n := r2) (maxReq := 320)
      (by rw [hl2, hl1, hl0]; omega)
    change nonFreeCount (sh2.append r2).evs ≤ 3 ∧ _
    rw [he3, he2, he1_eq]
    refine ⟨by rw [nonFreeCount_append, nonFreeCount_append]; omega, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with h02 | h3
    · rcases List.mem_append.mp h02 with h0 | h2
      · exact hrq0 ev h0
      · exact hr2 ev h2
    · exact hr3 ev h3
  · simp only [List.length_cons] at hlen; omega

private theorem cliFmtWriteEnv_ops_req {evs : List AllocEvent} (hEnv : CliFmtWriteEnv evs) :
    nonFreeCount evs ≤ 3 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 80 ∧ eventStepAlign ev ≤ 16 := by
  rw [cliFmtWriteEnv_iff] at hEnv
  rcases hEnv with rfl | ⟨nameLen, devDigits, hn, hd1, hd2, hAddr⟩
  · exact ⟨Nat.zero_le 3, fun _ h => nomatch h⟩
  · exact addrEnv_ops_req hn hd1 hd2 hAddr

private theorem cliFormatInnerEnv_ops_req {evs : List AllocEvent} (hEnv : CliFormatInnerEnv evs) :
    nonFreeCount evs ≤ 3 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 320 ∧ eventStepAlign ev ≤ 16 := by
  rw [cliFormatInnerEnv_iff] at hEnv
  rcases hEnv with rfl | hu8 | hu32 | ⟨n, hn, hfs⟩ | ⟨n, h1, h2, hsl⟩ |
      ⟨n, hn, hsg⟩ | ⟨nameLen, devDigits, hn, hd1, hd2, hAddr⟩ | hPref
  · exact ⟨Nat.zero_le 3, fun _ h => nomatch h⟩
  · rw [formatInnerAnyU8Env_eq_alloc8 hu8]
    refine ⟨by decide, fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev; subst hev; exact ⟨by decide, by decide⟩
  · rcases hu32 with ⟨dLen, hlo, hhi, hSingle⟩
    unfold FormatInnerSingleEnv at hSingle
    rw [formatInnerKnownEvents_zero_singleton] at hSingle
    have hne : dLen ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hSingle
    rw [hSingle]
    exact ⟨by rw [nonFreeCount_rustAllocEvents]; decide, req_align_rustAlloc_le (by omega)⟩
  · unfold FormatInnerFromStrEnv at hfs
    rw [hfs]
    split
    · exact ⟨Nat.zero_le 3, fun _ h => nomatch h⟩
    · exact ⟨by rw [nonFreeCount_rustAllocEvents]; decide, req_align_rustAlloc_le (by omega)⟩
  · have heq : formatInnerKnownEvents (2 * n) [n] = rustAllocEvents (2 * n) 1 := by
      unfold formatInnerKnownEvents startCliBufShape CliBufShape.run List.foldl CliBufShape.append
      have h2n_ne : 2 * n ≠ 0 := by omega
      have hcap : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hle : n ≤ 2 * n := by omega
      simp [h2n_ne, hcap, hle]
    unfold FormatInnerShortLitEnv at hsl
    rw [hsl, heq]
    exact ⟨by rw [nonFreeCount_rustAllocEvents]; decide, req_align_rustAlloc_le (by omega)⟩
  · unfold FormatInnerSingleEnv at hsg
    rw [formatInnerKnownEvents_zero_singleton] at hsg
    rw [hsg]
    split
    · exact ⟨Nat.zero_le 3, fun _ h => nomatch h⟩
    · exact ⟨by rw [nonFreeCount_rustAllocEvents]; decide, req_align_rustAlloc_le (by omega)⟩
  · obtain ⟨hnf, hrq⟩ := addrEnv_ops_req hn hd1 hd2 hAddr
    exact ⟨hnf, fun ev hev => ⟨Nat.le_trans (hrq ev hev).1 (by decide), (hrq ev hev).2⟩⟩
  · exact prefixedEnv_ops_req hPref

theorem nonFreeBound_cliFmtWriteEnv : NonFreeBound CliFmtWriteEnv 3 :=
  fun _ h => (cliFmtWriteEnv_ops_req h).1

theorem nonFreeBound_cliFormatInnerEnv : NonFreeBound CliFormatInnerEnv 3 :=
  fun _ h => (cliFormatInnerEnv_ops_req h).1

theorem nonFreeBound_msgDeserErrEnv : NonFreeBound MsgDeserErrEnv 3 := by
  refine (nonFreeBound_cliFormatInnerEnv.concat NonFreeBound.freeOnly).of_imp ?_
  intro evs h
  exact (msgDeserErrEnv_iff.mp h)

/-- Every event in `MsgDeserErrEnv evs` has `eventStepReq ev ≤ 320` and `eventStepAlign ev ≤ 16`. -/
theorem msgDeserErrEnv_req_align {evs : List AllocEvent} (h : MsgDeserErrEnv evs) :
    ∀ ev ∈ evs, eventStepReq ev ≤ 320 ∧ eventStepAlign ev ≤ 16 := by
  rcases msgDeserErrEnv_iff.mp h with ⟨evs₁, evs₂, rfl, h1, h2⟩
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · exact (cliFormatInnerEnv_ops_req h1).2 ev hm1
  · obtain ⟨al, sz, rfl⟩ := h2 ev hm2
    exact ⟨by simp [eventStepReq], by simp [eventStepAlign]⟩

/-! ## 4. Generic `PhaseGroupSpec` Bounds (`HasFineGroupCredit M`) -/

theorem phaseGroupSpec_cliFmtWriteEnv (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M CliFmtWriteEnv (9 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M nonFreeBound_cliFmtWriteEnv).mono (by decide)

theorem phaseGroupSpec_cliFormatInnerEnv (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M CliFormatInnerEnv (9 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M nonFreeBound_cliFormatInnerEnv).mono (by decide)

theorem phaseGroupSpec_msgDeserErrEnv (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M MsgDeserErrEnv (9 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M nonFreeBound_msgDeserErrEnv).mono (by decide)

/-! ## 5. Parametric `ModelHyps M` & Concrete `fineCostModel` `PhaseCreditSpec` Bounds -/

/-- Unconditional `(hM : ModelHyps M)` `PhaseCreditSpec` for `CliFmtWriteEnv` (`maxReq = 80`). -/
theorem phaseCreditSpec_cliFmtWriteEnv_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M CliFmtWriteEnv 29097 24825 24825 80 :=
  (phaseCreditSpec_of_nonFree_any hM nonFreeBound_cliFmtWriteEnv
    (fun _ h => (cliFmtWriteEnv_ops_req h).2)).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Small-threshold `(hM : ModelHyps M)` `PhaseCreditSpec` for `CliFmtWriteEnv`
    (`Δcum = 29,097`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 80`). -/
theorem phaseCreditSpec_cliFmtWriteEnv_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm : 80 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M CliFmtWriteEnv 29097 0 0 80 :=
  (phaseCreditSpec_of_nonFree_small hM hsm nonFreeBound_cliFmtWriteEnv
    (fun _ h => (cliFmtWriteEnv_ops_req h).2)).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Unconditional `(hM : ModelHyps M)` `PhaseCreditSpec` for `CliFormatInnerEnv` (`maxReq = 320`). -/
theorem phaseCreditSpec_cliFormatInnerEnv_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M CliFormatInnerEnv 30537 25545 25545 320 :=
  (phaseCreditSpec_of_nonFree_any hM nonFreeBound_cliFormatInnerEnv
    (fun _ h => (cliFormatInnerEnv_ops_req h).2)).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Small-threshold `(hM : ModelHyps M)` `PhaseCreditSpec` for `CliFormatInnerEnv`
    (`Δcum = 30,537`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 320`). -/
theorem phaseCreditSpec_cliFormatInnerEnv_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm : 320 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M CliFormatInnerEnv 30537 0 0 320 :=
  (phaseCreditSpec_of_nonFree_small hM hsm nonFreeBound_cliFormatInnerEnv
    (fun _ h => (cliFormatInnerEnv_ops_req h).2)).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Unconditional `(hM : ModelHyps M)` `PhaseCreditSpec` for `MsgDeserErrEnv` (`maxReq = 320`). -/
theorem phaseCreditSpec_msgDeserErrEnv_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M MsgDeserErrEnv 30537 25545 25545 320 :=
  ((phaseCreditSpec_cliFormatInnerEnv_any hM).concat
    (PhaseCreditSpec.freeOnly_of_hyps hM)).congr_mono
    (fun _ h => msgDeserErrEnv_iff.mp h) (by decide) (by decide) (by decide) (by decide)

/-- Small-threshold `(hM : ModelHyps M)` `PhaseCreditSpec` for `MsgDeserErrEnv`
    (`Δcum = 30,537`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 320`). -/
theorem phaseCreditSpec_msgDeserErrEnv_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm : 320 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M MsgDeserErrEnv 30537 0 0 320 :=
  ((phaseCreditSpec_cliFormatInnerEnv_small hM hsm).concat
    (PhaseCreditSpec.freeOnly_of_hyps hM)).congr_mono
    (fun _ h => msgDeserErrEnv_iff.mp h) (by decide) (by decide) (by decide) (by decide)

/-- `FormatInnerAnyU8Env` (`[.alloc 8]`): `Δcum = 9,555`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 8`. -/
theorem phaseCreditSpec_formatInnerAnyU8Env :
    PhaseCreditSpec fineCostModel FormatInnerAnyU8Env 9555 0 0 8 := by
  have hsm : 8 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have haff := (fineCostModel_smallAff 8 hsm).1
  have halloc := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 8) (al := 1)
    (by decide) (by decide) hsm).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8)
  refine halloc.of_imp fun evs h => ?_
  rw [formatInnerAnyU8Env_eq_alloc8 h]
  rfl

/-- Concrete `fineCostModel` `PhaseCreditSpec` for `CliFmtWriteEnv` (`maxReq = 80`). -/
theorem phaseCreditSpec_cliFmtWriteEnv_80 :
    PhaseCreditSpec fineCostModel CliFmtWriteEnv 29097 0 0 80 :=
  phaseCreditSpec_cliFmtWriteEnv_small fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide)

/-- Unified `CliFmtWriteEnv` `PhaseCreditSpec` on `fineCostModel`:
    `Δcum = 31,017`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 400`. -/
theorem phaseCreditSpec_cliFmtWriteEnv :
    PhaseCreditSpec fineCostModel CliFmtWriteEnv 31017 0 0 400 :=
  phaseCreditSpec_cliFmtWriteEnv_80.mono (by decide) (by decide) (by decide) (by decide)

/-- Concrete `fineCostModel` `PhaseCreditSpec` for `CliFormatInnerEnv` (`maxReq = 320`). -/
theorem phaseCreditSpec_cliFormatInnerEnv_320 :
    PhaseCreditSpec fineCostModel CliFormatInnerEnv 30537 0 0 320 :=
  phaseCreditSpec_cliFormatInnerEnv_small fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide)

/-- Unified `CliFormatInnerEnv` `PhaseCreditSpec` on `fineCostModel`:
    `Δcum = 31,017`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 400`. -/
theorem phaseCreditSpec_cliFormatInnerEnv :
    PhaseCreditSpec fineCostModel CliFormatInnerEnv 31017 0 0 400 :=
  phaseCreditSpec_cliFormatInnerEnv_320.mono (by decide) (by decide) (by decide) (by decide)

/-- Concrete `fineCostModel` `PhaseCreditSpec` for `MsgDeserErrEnv` (`maxReq = 320`). -/
theorem phaseCreditSpec_msgDeserErrEnv_320 :
    PhaseCreditSpec fineCostModel MsgDeserErrEnv 30537 0 0 320 :=
  phaseCreditSpec_msgDeserErrEnv_small fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide)

/-- Unified `MsgDeserErrEnv` `PhaseCreditSpec` on `fineCostModel`:
    `Δcum = 31,017`, `Δlive = 0`, `Δpeak = 0`, `maxReq = 400`. -/
theorem phaseCreditSpec_msgDeserErrEnv :
    PhaseCreditSpec fineCostModel MsgDeserErrEnv 31017 0 0 400 :=
  phaseCreditSpec_msgDeserErrEnv_320.mono (by decide) (by decide) (by decide) (by decide)

/-! ## 6. Non-Vacuity `FitsEnv` Witnesses under `nonVacLimits` (`1 GiB`) -/

/-- `CliFormatInnerEnv` fits in `nonVacLimits` (`1 GiB` RAM cap) from `fineCostModel.init`. -/
theorem cliFormatInnerEnv_fitsEnv_nonVac :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init CliFormatInnerEnv :=
  fitsEnv_fineCostModel_of_phaseCredit phaseCreditSpec_cliFormatInnerEnv
    (Nat.le_refl 0) rfl (by decide) (by decide)

/-- `CliFmtWriteEnv` fits in `nonVacLimits` (`1 GiB` RAM cap) from `fineCostModel.init`. -/
theorem cliFmtWriteEnv_fitsEnv_nonVac :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init CliFmtWriteEnv :=
  fitsEnv_fineCostModel_of_phaseCredit phaseCreditSpec_cliFmtWriteEnv
    (Nat.le_refl 0) rfl (by decide) (by decide)

/-- `MsgDeserErrEnv` fits in `nonVacLimits` (`1 GiB` RAM cap) from `fineCostModel.init`. -/
theorem msgDeserErrEnv_fitsEnv_nonVac :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init MsgDeserErrEnv :=
  fitsEnv_fineCostModel_of_phaseCredit phaseCreditSpec_msgDeserErrEnv
    (Nat.le_refl 0) rfl (by decide) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtPeakCreditBridges
