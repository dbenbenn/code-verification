/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.AllocMeta
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.AllocGroup
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.AllocSlot
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.MallocImpl
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Free
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Calloc
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.AlignedAlloc
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Realloc

/-!
# Placed Entry Contracts for the Per-Size-Class Fine Cost Model (`…Proofs.Cost.Fine.Entries`)

- **Layer & Role**: `Role::Proof` (untrusted). A plain (non-`module`) file because it imports the
  non-`module` `Cost/Fine/Free.lean`.
- **Contents**: Instantiates the closed helper chain (`__malloc_alloc_meta` → `alloc_group` →
  `alloc_slot` → `__libc_malloc_impl` → `__default_malloc`, plus `nontrivial_free` → `__libc_free`
  → `__libc_realloc`) and exports `mallocngFinePlacedEntries`, discharging all six placed C
  allocator entry contracts (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`,
  `posix_memalign`) over `(mallocngFineCostModel, mallocngFineIface)`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- Mode-parameterized closed `alloc_group` contract instantiated with `placed_allocMeta_fine_ok`. -/
theorem placed_allocGroup_fine_mode_closed_ok {ro : Bool} : AllocGroupFineAtOffStmt ro :=
  wp_placed_allocGroup_fine (placed_allocMeta_fine_ok (ro := ro))

/-- Mode-parameterized closed `alloc_slot` (`blk08`) contract. -/
theorem placed_allocSlot_fine_mode_closed_ok {ro : Bool} : AllocSlotFineStmt ro :=
  placed_allocSlot_fine_ok (placed_allocGroup_fine_mode_closed_ok (ro := ro))

/-- Mode-parameterized closed pre-enframe `__libc_malloc_impl` (`blk09`) contract. -/
theorem placed_libcMallocImpl_fine_raw_mode_closed_ok {ro : Bool} : LibcMallocImplFineRawStmt ro :=
  placed_libcMallocImpl_fine_raw_ok (placed_allocMeta_fine_ok (ro := ro))
    (placed_allocSlot_fine_mode_closed_ok (ro := ro))

/-- Mode-parameterized closed `__libc_malloc_impl` (`blk09`) contract over `mallocngFineCostModel`. -/
theorem placed_libcMallocImpl_fine_mode_closed_ok {ro : Bool} : LibcMallocImplFineStmt ro :=
  placed_libcMallocImpl_fine_ok (placed_libcMallocImpl_fine_raw_mode_closed_ok (ro := ro))

/-- Mode-parameterized closed `__default_malloc` (`blk04`) contract over `mallocngFineCostModel`. -/
theorem placed_defaultMalloc_fine_mode_closed_ok {ro : Bool} : DefaultMallocFineStmt ro :=
  placed_defaultMalloc_fine_ok (placed_libcMallocImpl_fine_mode_closed_ok (ro := ro))

/-- Mode-parameterized closed `__libc_realloc` (`blk14`) contract over `mallocngFineCostModel`. -/
theorem placed_libcRealloc_fine_mode_closed_ok {ro : Bool} : LibcReallocFineStmt ro :=
  placed_libcRealloc_fine_ok (placed_libcMallocImpl_fine_mode_closed_ok (ro := ro))
    (placed_libcFree_fine_ok (ro := ro))

/-- Closed `alloc_group` contract instantiated with `placed_allocMeta_fine_ok`. -/
theorem placed_allocGroup_fine_closed_ok : AllocGroupFineAtOffStmt :=
  placed_allocGroup_fine_mode_closed_ok (ro := false)

/-- Closed `alloc_slot` (`blk08`) contract instantiated with `placed_allocGroup_fine_closed_ok`. -/
theorem placed_allocSlot_fine_closed_ok : AllocSlotFineStmt :=
  placed_allocSlot_fine_mode_closed_ok (ro := false)

/-- Closed pre-enframe `__libc_malloc_impl` (`blk09`) contract shared by `malloc` and
    `aligned_alloc`. -/
theorem placed_libcMallocImpl_fine_raw_closed_ok : LibcMallocImplFineRawStmt :=
  placed_libcMallocImpl_fine_raw_mode_closed_ok (ro := false)

/-- Closed `__libc_malloc_impl` (`blk09`) contract over `mallocngFineCostModel`. -/
theorem placed_libcMallocImpl_fine_closed_ok : LibcMallocImplFineStmt :=
  placed_libcMallocImpl_fine_mode_closed_ok (ro := false)

/-- Closed `__default_malloc` (`blk04`) contract over `mallocngFineCostModel`. -/
theorem placed_defaultMalloc_fine_closed_ok : DefaultMallocFineStmt :=
  placed_defaultMalloc_fine_mode_closed_ok (ro := false)

/-- Closed `__libc_realloc` (`blk14`) contract over `mallocngFineCostModel`. -/
theorem placed_libcRealloc_fine_closed_ok : LibcReallocFineStmt :=
  placed_libcRealloc_fine_mode_closed_ok (ro := false)

/-- All six placed C allocator entry contracts over
    `(mallocngFineCostModel, mallocngFineModeIface ro)`. -/
theorem mallocngFineModePlacedEntries (ro : Bool)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) :
    MallocngModelPlacedEntryContracts mallocngFineCostModel (mallocngFineModeIface ro) mpl svc where
  malloc_ok :=
    fine_malloc_entry_ok (ro := ro) (placed_defaultMalloc_fine_mode_closed_ok (ro := ro))
      mpl svc hPl hSvc
  free_ok := fine_free_entry_ok (ro := ro) mpl svc hPl hSvc
  calloc_ok :=
    fine_calloc_entry_ok (ro := ro) (placed_defaultMalloc_fine_mode_closed_ok (ro := ro))
      mpl svc hPl hSvc
  realloc_ok :=
    fine_realloc_entry_ok (ro := ro) (placed_libcMallocImpl_fine_mode_closed_ok (ro := ro))
      (placed_libcFree_fine_ok (ro := ro)) mpl svc hPl hSvc
  alignedAlloc_ok :=
    fine_alignedAlloc_entry_ok (ro := ro) (placed_libcMallocImpl_fine_raw_mode_closed_ok (ro := ro))
      mpl svc hPl hSvc
  posixMemalign_ok :=
    fine_posixMemalign_entry_ok (ro := ro) (placed_libcMallocImpl_fine_raw_mode_closed_ok (ro := ro))
      mpl svc hPl hSvc

/-- All six placed C allocator entry contracts over `(mallocngFineCostModel, mallocngFineIface)`. -/
theorem mallocngFinePlacedEntries
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) :
    MallocngModelPlacedEntryContracts mallocngFineCostModel mallocngFineIface mpl svc :=
  mallocngFineModePlacedEntries false mpl svc hPl hSvc

/-- All six placed C allocator entry contracts over
    `(mallocngFineCostModel, mallocngFineRoIface)` (duplicable `.ro` `auxv`). -/
theorem mallocngFineRoPlacedEntries
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) :
    MallocngModelPlacedEntryContracts mallocngFineCostModel mallocngFineRoIface mpl svc :=
  mallocngFineModePlacedEntries true mpl svc hPl hSvc

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
