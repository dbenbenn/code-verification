/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.MallocngBudgetInst

/-!
# Shared Helpers for Budgeted `__rdl_{alloc,realloc}` Proofs

Event-list and frame-condition lemmas, `mallocngBudgetPool` elimination (`mallocngBudgetPool_elim`),
and OOM-branch refutation from pure footprint and headroom bounds (`mallocngBudget_not_fits_of_oom`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Event-List and Frame-Condition Glue -/

@[simp] theorem RustAllocBudget.fitsEvents_singleton (A : RustAllocBudget) (st : A.σ)
    (ev : AllocEvent) : A.FitsEvents st [ev] ↔ A.FitsEvent st ev := by
  simp [RustAllocBudget.FitsEvents]

@[simp] theorem RustAllocBudget.stepEvents_singleton (A : RustAllocBudget) (st : A.σ)
    (ev : AllocEvent) : A.stepEvents [ev] st = A.step ev st := rfl

/-- `OomPreserved s0 sf` from `AllocCallPreserved s0 s1` and a callee OOM witness at `s1`. -/
theorem oomPreserved_of_allocCall_stepOom {svc : State → State} {stepB : Nat}
    {s0 s1 sf : State} (h01 : AllocCallPreserved s0 s1)
    (hOom : MallocngStepOomCond svc stepB s1 sf) : OomPreserved s0 sf :=
  ⟨hOom.1.trans h01.1, hOom.2.1.trans h01.2.1, hOom.2.2.1.trans h01.2.2.1⟩

/-! ## Opening `mallocngBudgetPool` -/

/-- Unpack `mallocngBudgetPool` into `MallocngModelEnv` plus `extra`, exposing `MallocngBudgetVmOk`
    and the pure `heap_footprint_bound` inequalities. -/
theorem mallocngBudgetPool_elim {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    {lim : MallocngBudgetLimits} {extra : SepProp} {γ : GhostName} {mAddrs : MallocngAddrs}
    {st : M.σ} {s : State} {m : Memory} {R : SepProp}
    (h : m ⊨ mallocngBudgetPool M I lim extra γ mAddrs st s ∗ R) :
    ∃ ivs staticIvs : List (BitVec 64 × Nat),
      MallocngBudgetVmOk lim staticIvs ivs s ∧
      ivs.length ≤ M.maxDynIvs st ∧ (ivs.map Prod.snd).sum ≤ M.footprint st ∧
      m ⊨ (MallocngModelEnv M I γ mAddrs s.tpidrEl0 s.brkStart st ivs s ∗ extra) ∗ R := by
  unfold mallocngBudgetPool at h
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  obtain ⟨ivs, h⟩ := h
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  obtain ⟨staticIvs, h⟩ := h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  obtain ⟨hVm, h⟩ := h
  have hEnt := Entails.extract_heap_fact
    (P := I.HeapM γ mAddrs s.tpidrEl0 s.brkStart s.brk st ivs)
    (fun hp hh => hSound.heap_footprint_bound γ mAddrs s.tpidrEl0 s.brkStart s.brk st ivs hp hh)
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hEnt)) h
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h2
  obtain ⟨⟨hLen, hSum, _⟩, _⟩ := h2
  refine ⟨ivs, staticIvs, hVm, hLen, hSum, ?_⟩
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) h
  unfold MallocngModelEnv
  exact Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)

/-! ## OOM-Branch Refutation from Pure Bounds -/

/-- Refute `MallocngStepOomCond ProofLib.allocMallocng stepB s1 sf` from `MallocngBudgetVmOk` at
    `s1`, the `heap_footprint_bound` inequalities for `(st, ivs0)`, `physPlusRw sf = physPlusRw s1`,
    and `FitsMallocngStep` with `stepB ≤ M.stepReserve ev st`. -/
theorem mallocngStepOomCond_false_of_bounds {M : AllocCostModel}
    {lim : MallocngBudgetLimits} {st : M.σ} {ev : AllocEvent} {stepB : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {s1 sf : State}
    (hVmOk : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hFits : FitsMallocngStep lim (M.stepReserve ev st) (M.maxDynIvs st) (M.footprint st))
    (hStep : stepB ≤ M.stepReserve ev st)
    (hPhysEq : ProofLib.physPlusRw sf = ProofLib.physPlusRw s1)
    (hOom : MallocngStepOomCond ProofLib.allocMallocng stepB s1 sf) :
    False := by
  rcases hVmOk with ⟨hStLen, hStSum, hPhysCap, hCovOr⟩
  rcases hFits with ⟨hRam, hVa⟩
  have hCov : ∀ a : BitVec 64, (s1.mem.perm a).mapped = true →
      MallocngInIntervals (staticIvs ++ ivs0) a := by
    intro a ha
    rcases hCovOr a ha with ⟨iv, hm, hin⟩ | ⟨iv, hm, hin⟩
    · exact ⟨iv, List.mem_append_left _ hm, hin⟩
    · exact ⟨iv, List.mem_append_right _ hm, hin⟩
  have hSum : ((staticIvs ++ ivs0).map Prod.snd).sum =
      (staticIvs.map Prod.snd).sum + (ivs0.map Prod.snd).sum := by
    simp [List.map_append, List.sum_append]
  have hLen : (staticIvs ++ ivs0).length = staticIvs.length + ivs0.length := List.length_append
  have hVaRoom : VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom
      ((staticIvs ++ ivs0).map Prod.snd).sum (staticIvs ++ ivs0).length stepB := by
    refine VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom.mono
      (S₂ := lim.staticBytes + M.footprint st)
      (n₂ := lim.staticCount + M.maxDynIvs st)
      (b₂ := M.stepReserve ev st)
      ?_ (by omega) (by omega) hStep
    unfold VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom
    omega
  exact VerifiedLibraries.Mallocng.Proofs.Cost.mallocngStepOomCond_false_of_fits
    allocMallocng_sanitizedSvc hCov hPhysEq (by omega) hVaRoom hOom

/-- OOM branch of one model C call that emits `ev` when `ok` and reserves `.alloc 0` otherwise:
    if the call ran out of memory then `ev` does not fit (`FitsMallocngEvent` forces `ok`, hence
    `stepB = M.stepReserve ev st`). -/
theorem mallocngBudget_not_fits_of_oom {M : AllocCostModel}
    {lim : MallocngBudgetLimits} {st : M.σ} {ev : AllocEvent} {ok : Bool} {stepB : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {s1 sf : State}
    (hVmOk : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hOk : ev.withinMaxAlloc → ok = true)
    (hStepB : stepB = if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st)
    (hPhysEq : ProofLib.physPlusRw sf = ProofLib.physPlusRw s1)
    (hOom : MallocngStepOomCond ProofLib.allocMallocng stepB s1 sf) :
    ¬ FitsMallocngEvent M lim st ev := by
  rintro ⟨hW, hF⟩
  rw [hOk hW] at hStepB
  simp only [↓reduceIte] at hStepB
  exact mallocngStepOomCond_false_of_bounds hVmOk hHeapLen hHeapSum hF (Nat.le_of_eq hStepB)
    hPhysEq hOom

end VerifiedLibraries.RustStd
