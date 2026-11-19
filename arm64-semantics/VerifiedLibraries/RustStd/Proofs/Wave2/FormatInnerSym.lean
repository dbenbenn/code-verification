/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Generated.AllocPlacedObj
public import ProofLib.Placed
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# `alloc::fmt::format::format_inner` Placement and Instruction Fetches

Placement typeclass (`FormatInnerPlacement`), mangled symbol lookups, and pre-decoded instruction
fetches (`gen_placed_fetches`) for block `3` (`alloc::fmt::format::format_inner`, 108 instructions)
of `allocMultiLib`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-- Placement typeclass for `allocMultiLib` (`format_inner`, block `3`). -/
class FormatInnerPlacement where
  mpl : MultiPlacement
  placeable : allocMultiLib.Placeable mpl

abbrev fmtInnerMpl [FormatInnerPlacement] : MultiPlacement := FormatInnerPlacement.mpl

/-- `P` installs no extern hooks inside code block `j` of `allocMultiLib`. -/
def FmtAllocBlockNoExtern (mpl : MultiPlacement) (P : Program) (j : Nat) : Prop :=
  ∀ off : Nat, off < (allocMultiLib.blockLib j).text.code.length →
    P.externAt? (mpl.base j + BitVec.ofNat 64 off) = none

theorem FmtAllocBlockNoExtern.of_no_extern {mpl : MultiPlacement} {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (j : Nat) :
    FmtAllocBlockNoExtern mpl P j :=
  fun _ _ => hext _

abbrev fmtInnerShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev fmtInnerAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev fmtInnerCoreFmtWriteRawSym : String :=
  "_RNvNtCs2kXltWtc1W_4core3fmt5write"

abbrev fmtInnerUnwrapFailedSym : String :=
  "_RNvNtCs2kXltWtc1W_4core6result13unwrap_failed"

abbrev fmtInnerHandleErrorSym : String :=
  "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error"

abbrev fmtInnerWriteStrBlockSym : String :=
  "<alloc::string::String as core::fmt::Write>::write_str [rust_alloc]"

abbrev fmtInnerWriteCharBlockSym : String :=
  "<alloc::string::String as core::fmt::Write>::write_char [rust_alloc]"

abbrev fmtInnerWriteFmtBlockSym : String :=
  "<alloc::string::String as core::fmt::Write>::write_fmt [rust_alloc]"

theorem lookupBlockSym_formatInner :
    Obj.lookupBlockSym "alloc::fmt::format::format_inner" allocMultiLib.blocks = some (3, 0) := by
  decide

theorem lookup_formatInner_blk3 :
    lookup "alloc::fmt::format::format_inner" allocMultiLib.blocks[3].symbols = some 0 := by
  decide

theorem lookupBlockSym_fmtShim_none :
    Obj.lookupBlockSym fmtInnerShimSym allocMultiLib.blocks = none := by
  decide

theorem lookupBlockSym_fmtAlloc_none :
    Obj.lookupBlockSym fmtInnerAllocSym allocMultiLib.blocks = none := by
  decide

theorem lookupBlockSym_coreFmtWriteRaw_none :
    Obj.lookupBlockSym fmtInnerCoreFmtWriteRawSym allocMultiLib.blocks = none := by
  decide

theorem lookupBlockSym_unwrapFailed_none :
    Obj.lookupBlockSym fmtInnerUnwrapFailedSym allocMultiLib.blocks = none := by
  decide

theorem lookupBlockSym_fmtHandleError_none :
    Obj.lookupBlockSym fmtInnerHandleErrorSym allocMultiLib.blocks = none := by
  decide

theorem lookupBlockSym_vtable34_none :
    Obj.lookupBlockSym "rust_alloc:.data.rel.ro..Lanon.34" allocMultiLib.blocks = none := by
  decide

def allocLib03 : PlacedLib := allocMultiLib.blockLib 3
def allocPl03 [FormatInnerPlacement] : Placement := allocMultiLib.blockPlacement fmtInnerMpl 3
theorem allocPlaceable03 [FormatInnerPlacement] : allocLib03.Placeable allocPl03 :=
  allocMultiLib.placeable_blockLib (by decide) FormatInnerPlacement.placeable
def allocPC03 [FormatInnerPlacement] : Program := allocLib03.program allocPl03

def allocProg03 : Program :=
  { code := allocLib03.text.code, symbols := allocLib03.text.symbols }
def allocTree03 : WordTree := word_tree_of% allocProg03
theorem alloc03_code_eq : allocLib03.text.code = allocTree03.toBytes := by rfl_kernel
theorem alloc03_tree_size : allocTree03.checkSize? = some 108 := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches allocPC03 allocLib03 allocTree03 alloc03_code_eq alloc03_tree_size
  via_placement allocPl03 allocPlaceable03 [0x0 → 0x188]
end

end VerifiedLibraries.RustStd
