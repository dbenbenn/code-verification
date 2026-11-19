/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import LibsignalBinary.Heap.Fine.CostModel
public import LibsignalBinary.Heap.MallocngRustBudget
public import LibsignalBinary.Heap.NonVacBudget
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Fine-Grained Rust Global-Allocator Bundles and Coarse Projection

Instantiates `MallocngRustBudget` and `MallocngBridgeBudget` at `fineCostModel`:
- Projects `FineCoreImpl` and `FineHeapImpl` satisfaction to the underlying coarse `MallocngWF`
  invariant and dynamic-region bounds (`coarse_of_fineCore`, `coarse_of_fine`).
- Provides `RustCliAllocBudgetEntries`, `RustCliAllocNoOomEntries`, and unbudgeted
  `RustCliAllocEntries` bundles for both direct `__rdl_*` shims and 1-instruction `__rust_*`
  `B`-thunks, paired with startup pool initialization.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)
open LibsignalBinary.Heap

/-! ## Coarse `MallocngWF` Projection (`coarse_of_fine`) -/

/-! ## `RustCliAllocBudgetEntries` and `RustCliAllocNoOomEntries` Bundles -/

/-- Placed `__rustc::__rdl_{alloc,dealloc,realloc}` `RustCliAllocBudgetEntries fineCostModel`
    bundle for any program `P` containing `VerifiedLibraries.mallocngLib` at `mpl`. -/
theorem fineRustCliAllocBudgetEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      P rdlAddrs :=
  mallocngRustCliAllocBudgetEntries fineCostModelSound hP γ tp brkStart hShims hMemcpy

/-- 1-instruction `B`-thunk (`__rustc::__rust_{alloc,dealloc,realloc}`) lift of
    `fineRustCliAllocBudgetEntries`. -/
theorem fineRustCliAllocBudgetEntries_thunks
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      P thunkAddrs :=
  mallocngRustCliAllocBudgetEntries_thunks fineCostModelSound hP γ tp brkStart
    hThunks hShims hMemcpy

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) `RustCliAllocNoOomEntries fineCostModel`
    bundle at direct `__rustc::__rdl_{alloc,dealloc,realloc}` shims `rdlAddrs`. -/
theorem fineRustCliAllocNoOomEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocNoOomEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      lim P rdlAddrs :=
  mallocngRustCliAllocNoOomEntries fineCostModelSound hP γ tp brkStart lim hShims hMemcpy

/-! ## Startup Initialization and Entrypoint Assembly -/

end LibsignalBinary.Heap.Fine
