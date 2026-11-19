/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Generated.CoreFmtPlacedObj
public import VerifiedLibraries.RustStd.Proofs.ExecSegSym
public import ProofLib.Placed.Multi
public import ProofLib.GenPlacedFetches
public import ProofLib.Process.OracleEq
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic Fetch and Block-Local Stepping for `core::fmt`

Provides `CoreFmtPlacement`, per-block `WordTree` fetch generation, call-cone block predicates, and
symbol resolution identities for `coreFmtMultiLib`. Also defines `LibBlockNoExtern` and `PureSegPreserved`
lifters that step pure segments of a `MultiPlacedLib` block under block-local hook freedom.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd

/-! ## Placement typeclass and call-cone block predicates -/

/-- Valid placement bundle for `coreFmtMultiLib`. -/
class CoreFmtPlacement where
  mpl : MultiPlacement
  placeable : coreFmtMultiLib.Placeable mpl

abbrev coreFmtMpl [CoreFmtPlacement] : MultiPlacement := CoreFmtPlacement.mpl

/-- Block `2`: `<core::fmt::Formatter>::write_str`. -/
def writeStrKeep (i : Nat) : Bool := i == 2

/-- Block `1`: `<core::fmt::Formatter>::pad`. -/
def padFastKeep (i : Nat) : Bool := i == 1

/-- Blocks `[1, 10]`: `<str as core::fmt::Display>::fmt` + `Formatter::pad`. -/
def strDisplayKeep (i : Nat) : Bool := i == 1 || i == 10

/-- Blocks `[1, 7, 10]`: `<&str as core::fmt::Display>::fmt` + `<str as Display>::fmt` + `pad`. -/
def strRefDisplayKeep (i : Nat) : Bool := i == 1 || i == 7 || i == 10

/-- Blocks `[0, 5]`: `<core::fmt::Formatter>::pad_integral` + `pad_integral::write_prefix`. -/
def padIntegralKeep (i : Nat) : Bool := i == 0 || i == 5

/-- Block `6`: `<u8 as core::fmt::Display>::fmt`. -/
def u8DisplaySelfKeep (i : Nat) : Bool := i == 6

/-- Blocks `[0, 5, 6]`: `<u8 as core::fmt::Display>::fmt` + `pad_integral` cone. -/
def u8DisplayKeep (i : Nat) : Bool := padIntegralKeep i || i == 6

/-- Block `8`: `<u32 as core::fmt::Display>::fmt`. -/
def u32DisplaySelfKeep (i : Nat) : Bool := i == 8

/-- Blocks `[0, 5, 8]`: `<u32 as core::fmt::Display>::fmt` + `pad_integral` cone. -/
def u32DisplayKeep (i : Nat) : Bool := padIntegralKeep i || i == 8

/-- Blocks `[3, 9]`: `<u64 as core::fmt::Display>::fmt` / `<usize as Display>::fmt` + `_fmt_inner`. -/
def u64DisplaySelfKeep (i : Nat) : Bool := i == 3 || i == 9

/-- Blocks `[0, 3, 5, 9]`: `<u64>` / `<usize>` `Display::fmt` + `_fmt_inner` + `pad_integral` cone. -/
def u64DisplayKeep (i : Nat) : Bool := padIntegralKeep i || u64DisplaySelfKeep i

/-! ## Per-block `WordTree` and `gen_placed_fetches` -/

-- Block 0: `<core::fmt::Formatter>::pad_integral` (239 words / 956 B)
def coreFmtLib00 : PlacedLib := coreFmtMultiLib.blockLib 0
def coreFmtPl00 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 0
theorem coreFmtPlaceable00 [CoreFmtPlacement] : coreFmtLib00.Placeable coreFmtPl00 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC00 [CoreFmtPlacement] : Program := coreFmtLib00.program coreFmtPl00
def coreFmtProg00 : Program := { code := coreFmtLib00.text.code, symbols := coreFmtLib00.text.symbols }
def coreFmtTree00 : WordTree := word_tree_of% coreFmtProg00
theorem coreFmt00_code_eq : coreFmtLib00.text.code = coreFmtTree00.toBytes := by rfl_kernel
theorem coreFmt00_tree_size : coreFmtTree00.checkSize? = some 239 := by rfl_kernel
theorem coreFmtNoSvc0_00 : checkBlockNoSvc0 coreFmtLib00.text = true := by decide

gen_placed_fetches coreFmtPC00 coreFmtLib00 coreFmtTree00 coreFmt00_code_eq coreFmt00_tree_size
  via_placement coreFmtPl00 coreFmtPlaceable00 [0x0 → 0x3b8]

-- Block 1: `<core::fmt::Formatter>::pad` (197 words / 788 B)
def coreFmtLib01 : PlacedLib := coreFmtMultiLib.blockLib 1
def coreFmtPl01 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 1
theorem coreFmtPlaceable01 [CoreFmtPlacement] : coreFmtLib01.Placeable coreFmtPl01 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC01 [CoreFmtPlacement] : Program := coreFmtLib01.program coreFmtPl01
def coreFmtProg01 : Program := { code := coreFmtLib01.text.code, symbols := coreFmtLib01.text.symbols }
def coreFmtTree01 : WordTree := word_tree_of% coreFmtProg01
theorem coreFmt01_code_eq : coreFmtLib01.text.code = coreFmtTree01.toBytes := by rfl_kernel
theorem coreFmt01_tree_size : coreFmtTree01.checkSize? = some 197 := by rfl_kernel
theorem coreFmtNoSvc0_01 : checkBlockNoSvc0 coreFmtLib01.text = true := by decide

gen_placed_fetches coreFmtPC01 coreFmtLib01 coreFmtTree01 coreFmt01_code_eq coreFmt01_tree_size
  via_placement coreFmtPl01 coreFmtPlaceable01 [0x0 → 0x28, 0x244 → 0x268]

-- Block 2: `<core::fmt::Formatter>::write_str` (3 words / 12 B)
def coreFmtLib02 : PlacedLib := coreFmtMultiLib.blockLib 2
def coreFmtPl02 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 2
theorem coreFmtPlaceable02 [CoreFmtPlacement] : coreFmtLib02.Placeable coreFmtPl02 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC02 [CoreFmtPlacement] : Program := coreFmtLib02.program coreFmtPl02
def coreFmtProg02 : Program := { code := coreFmtLib02.text.code, symbols := coreFmtLib02.text.symbols }
def coreFmtTree02 : WordTree := word_tree_of% coreFmtProg02
theorem coreFmt02_code_eq : coreFmtLib02.text.code = coreFmtTree02.toBytes := by rfl_kernel
theorem coreFmt02_tree_size : coreFmtTree02.checkSize? = some 3 := by rfl_kernel
theorem coreFmtNoSvc0_02 : checkBlockNoSvc0 coreFmtLib02.text = true := by decide

gen_placed_fetches coreFmtPC02 coreFmtLib02 coreFmtTree02 coreFmt02_code_eq coreFmt02_tree_size
  via_placement coreFmtPl02 coreFmtPlaceable02 [0x0 → 0x8]

-- Block 3: `<u64>::_fmt_inner [rust_core_fmt]` (107 words / 428 B)
def coreFmtLib03 : PlacedLib := coreFmtMultiLib.blockLib 3
def coreFmtPl03 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 3
theorem coreFmtPlaceable03 [CoreFmtPlacement] : coreFmtLib03.Placeable coreFmtPl03 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC03 [CoreFmtPlacement] : Program := coreFmtLib03.program coreFmtPl03
def coreFmtProg03 : Program := { code := coreFmtLib03.text.code, symbols := coreFmtLib03.text.symbols }
def coreFmtTree03 : WordTree := word_tree_of% coreFmtProg03
theorem coreFmt03_code_eq : coreFmtLib03.text.code = coreFmtTree03.toBytes := by rfl_kernel
theorem coreFmt03_tree_size : coreFmtTree03.checkSize? = some 107 := by rfl_kernel
theorem coreFmtNoSvc0_03 : checkBlockNoSvc0 coreFmtLib03.text = true := by decide

gen_placed_fetches coreFmtPC03 coreFmtLib03 coreFmtTree03 coreFmt03_code_eq coreFmt03_tree_size
  via_placement coreFmtPl03 coreFmtPlaceable03 [0x0 → 0x1a8]

-- Block 5: `<core::fmt::Formatter>::pad_integral::write_prefix [rust_core_fmt]` (34 words / 136 B)
def coreFmtLib05 : PlacedLib := coreFmtMultiLib.blockLib 5
def coreFmtPl05 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 5
theorem coreFmtPlaceable05 [CoreFmtPlacement] : coreFmtLib05.Placeable coreFmtPl05 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC05 [CoreFmtPlacement] : Program := coreFmtLib05.program coreFmtPl05
def coreFmtProg05 : Program := { code := coreFmtLib05.text.code, symbols := coreFmtLib05.text.symbols }
def coreFmtTree05 : WordTree := word_tree_of% coreFmtProg05
theorem coreFmt05_code_eq : coreFmtLib05.text.code = coreFmtTree05.toBytes := by rfl_kernel
theorem coreFmt05_tree_size : coreFmtTree05.checkSize? = some 34 := by rfl_kernel
theorem coreFmtNoSvc0_05 : checkBlockNoSvc0 coreFmtLib05.text = true := by decide

gen_placed_fetches coreFmtPC05 coreFmtLib05 coreFmtTree05 coreFmt05_code_eq coreFmt05_tree_size
  via_placement coreFmtPl05 coreFmtPlaceable05 [0x0 → 0x84]

-- Block 6: `<u8 as core::fmt::Display>::fmt` (41 words / 164 B)
def coreFmtLib06 : PlacedLib := coreFmtMultiLib.blockLib 6
def coreFmtPl06 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 6
theorem coreFmtPlaceable06 [CoreFmtPlacement] : coreFmtLib06.Placeable coreFmtPl06 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC06 [CoreFmtPlacement] : Program := coreFmtLib06.program coreFmtPl06
def coreFmtProg06 : Program := { code := coreFmtLib06.text.code, symbols := coreFmtLib06.text.symbols }
def coreFmtTree06 : WordTree := word_tree_of% coreFmtProg06
theorem coreFmt06_code_eq : coreFmtLib06.text.code = coreFmtTree06.toBytes := by rfl_kernel
theorem coreFmt06_tree_size : coreFmtTree06.checkSize? = some 41 := by rfl_kernel
theorem coreFmtNoSvc0_06 : checkBlockNoSvc0 coreFmtLib06.text = true := by decide

gen_placed_fetches coreFmtPC06 coreFmtLib06 coreFmtTree06 coreFmt06_code_eq coreFmt06_tree_size
  via_placement coreFmtPl06 coreFmtPlaceable06 [0x0 → 0xa0]

-- Block 7: `<&str as core::fmt::Display>::fmt` (4 words / 16 B)
def coreFmtLib07 : PlacedLib := coreFmtMultiLib.blockLib 7
def coreFmtPl07 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 7
theorem coreFmtPlaceable07 [CoreFmtPlacement] : coreFmtLib07.Placeable coreFmtPl07 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC07 [CoreFmtPlacement] : Program := coreFmtLib07.program coreFmtPl07
def coreFmtProg07 : Program := { code := coreFmtLib07.text.code, symbols := coreFmtLib07.text.symbols }
def coreFmtTree07 : WordTree := word_tree_of% coreFmtProg07
theorem coreFmt07_code_eq : coreFmtLib07.text.code = coreFmtTree07.toBytes := by rfl_kernel
theorem coreFmt07_tree_size : coreFmtTree07.checkSize? = some 4 := by rfl_kernel
theorem coreFmtNoSvc0_07 : checkBlockNoSvc0 coreFmtLib07.text = true := by decide

gen_placed_fetches coreFmtPC07 coreFmtLib07 coreFmtTree07 coreFmt07_code_eq coreFmt07_tree_size
  via_placement coreFmtPl07 coreFmtPlaceable07 [0x0 → 0xc]

-- Block 8: `<u32 as core::fmt::Display>::fmt` (75 words / 300 B)
def coreFmtLib08 : PlacedLib := coreFmtMultiLib.blockLib 8
def coreFmtPl08 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 8
theorem coreFmtPlaceable08 [CoreFmtPlacement] : coreFmtLib08.Placeable coreFmtPl08 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC08 [CoreFmtPlacement] : Program := coreFmtLib08.program coreFmtPl08
def coreFmtProg08 : Program := { code := coreFmtLib08.text.code, symbols := coreFmtLib08.text.symbols }
def coreFmtTree08 : WordTree := word_tree_of% coreFmtProg08
theorem coreFmt08_code_eq : coreFmtLib08.text.code = coreFmtTree08.toBytes := by rfl_kernel
theorem coreFmt08_tree_size : coreFmtTree08.checkSize? = some 75 := by rfl_kernel
theorem coreFmtNoSvc0_08 : checkBlockNoSvc0 coreFmtLib08.text = true := by decide

gen_placed_fetches coreFmtPC08 coreFmtLib08 coreFmtTree08 coreFmt08_code_eq coreFmt08_tree_size
  via_placement coreFmtPl08 coreFmtPlaceable08 [0x0 → 0x128]

-- Block 9: `<u64 as core::fmt::Display>::fmt` / `<usize as core::fmt::Display>::fmt` (24 words / 96 B)
def coreFmtLib09 : PlacedLib := coreFmtMultiLib.blockLib 9
def coreFmtPl09 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 9
theorem coreFmtPlaceable09 [CoreFmtPlacement] : coreFmtLib09.Placeable coreFmtPl09 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC09 [CoreFmtPlacement] : Program := coreFmtLib09.program coreFmtPl09
def coreFmtProg09 : Program := { code := coreFmtLib09.text.code, symbols := coreFmtLib09.text.symbols }
def coreFmtTree09 : WordTree := word_tree_of% coreFmtProg09
theorem coreFmt09_code_eq : coreFmtLib09.text.code = coreFmtTree09.toBytes := by rfl_kernel
theorem coreFmt09_tree_size : coreFmtTree09.checkSize? = some 24 := by rfl_kernel
theorem coreFmtNoSvc0_09 : checkBlockNoSvc0 coreFmtLib09.text = true := by decide

gen_placed_fetches coreFmtPC09 coreFmtLib09 coreFmtTree09 coreFmt09_code_eq coreFmt09_tree_size
  via_placement coreFmtPl09 coreFmtPlaceable09 [0x0 → 0x5c]

-- Block 10: `<str as core::fmt::Display>::fmt` (5 words / 20 B)
def coreFmtLib10 : PlacedLib := coreFmtMultiLib.blockLib 10
def coreFmtPl10 [CoreFmtPlacement] : Placement := coreFmtMultiLib.blockPlacement coreFmtMpl 10
theorem coreFmtPlaceable10 [CoreFmtPlacement] : coreFmtLib10.Placeable coreFmtPl10 :=
  coreFmtMultiLib.placeable_blockLib (by decide) CoreFmtPlacement.placeable
def coreFmtPC10 [CoreFmtPlacement] : Program := coreFmtLib10.program coreFmtPl10
def coreFmtProg10 : Program := { code := coreFmtLib10.text.code, symbols := coreFmtLib10.text.symbols }
def coreFmtTree10 : WordTree := word_tree_of% coreFmtProg10
theorem coreFmt10_code_eq : coreFmtLib10.text.code = coreFmtTree10.toBytes := by rfl_kernel
theorem coreFmt10_tree_size : coreFmtTree10.checkSize? = some 5 := by rfl_kernel
theorem coreFmtNoSvc0_10 : checkBlockNoSvc0 coreFmtLib10.text = true := by decide

gen_placed_fetches coreFmtPC10 coreFmtLib10 coreFmtTree10 coreFmt10_code_eq coreFmt10_tree_size
  via_placement coreFmtPl10 coreFmtPlaceable10 [0x0 → 0x10]

/-! ## Symbol resolution and `fnAddr` identities -/

abbrev writePrefixIntSym : String :=
  "<core::fmt::Formatter>::pad_integral::write_prefix [rust_core_fmt]"

abbrev u64FmtInnerIntSym : String :=
  "<u64>::_fmt_inner [rust_core_fmt]"

abbrev strDisplayMangledSym : String :=
  "_RNvXsi_NtCs2kXltWtc1W_4core3fmteNtB5_7Display3fmt"

theorem fnAddr_padIntegral {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<core::fmt::Formatter>::pad_integral" = mpl.base 0 :=
  fnAddr_eq_base hpl 0 _ (by decide) (by decide)

theorem fnAddr_pad {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<core::fmt::Formatter>::pad" = mpl.base 1 :=
  fnAddr_eq_base hpl 1 _ (by decide) (by decide)

theorem fnAddr_writeStr {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<core::fmt::Formatter>::write_str" = mpl.base 2 :=
  fnAddr_eq_base hpl 2 _ (by decide) (by decide)

theorem fnAddr_u64FmtInner {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl u64FmtInnerIntSym = mpl.base 3 :=
  fnAddr_eq_base hpl 3 _ (by decide) (by decide)

theorem fnAddr_writePrefix {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl writePrefixIntSym = mpl.base 5 :=
  fnAddr_eq_base hpl 5 _ (by decide) (by decide)

theorem fnAddr_u8Display {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<u8 as core::fmt::Display>::fmt" = mpl.base 6 :=
  fnAddr_eq_base hpl 6 _ (by decide) (by decide)

theorem fnAddr_strRefDisplay {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<&str as core::fmt::Display>::fmt" = mpl.base 7 :=
  fnAddr_eq_base hpl 7 _ (by decide) (by decide)

theorem fnAddr_u32Display {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<u32 as core::fmt::Display>::fmt" = mpl.base 8 :=
  fnAddr_eq_base hpl 8 _ (by decide) (by decide)

theorem fnAddr_u64Display {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<u64 as core::fmt::Display>::fmt" = mpl.base 9 :=
  fnAddr_eq_base hpl 9 _ (by decide) (by decide)

theorem fnAddr_usizeDisplay {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<usize as core::fmt::Display>::fmt" = mpl.base 9 :=
  fnAddr_eq_base hpl 9 _ (by decide) (by decide)

theorem fnAddr_strDisplay {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.fnAddr mpl "<str as core::fmt::Display>::fmt" = mpl.base 10 :=
  fnAddr_eq_base hpl 10 _ (by decide) (by decide)

theorem resolve_padIntegral {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.resolve mpl "<core::fmt::Formatter>::pad_integral" = mpl.base 0 := by
  have hblk := lookupBlockSym_of_lookup (blocks := coreFmtMultiLib.blocks) (i := 0)
    (name := "<core::fmt::Formatter>::pad_integral") (off := 0) (hi := by decide)
    (hnd := hpl.symbols_nodup) (hl := by decide)
  simp [MultiPlacedLib.resolve, hblk]

theorem resolve_pad {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.resolve mpl "<core::fmt::Formatter>::pad" = mpl.base 1 := by
  have hblk := lookupBlockSym_of_lookup (blocks := coreFmtMultiLib.blocks) (i := 1)
    (name := "<core::fmt::Formatter>::pad") (off := 0) (hi := by decide)
    (hnd := hpl.symbols_nodup) (hl := by decide)
  simp [MultiPlacedLib.resolve, hblk]

theorem resolve_u64FmtInner {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.resolve mpl u64FmtInnerIntSym = mpl.base 3 := by
  have hblk := lookupBlockSym_of_lookup (blocks := coreFmtMultiLib.blocks) (i := 3)
    (name := u64FmtInnerIntSym) (off := 0) (hi := by decide)
    (hnd := hpl.symbols_nodup) (hl := by decide)
  simp [MultiPlacedLib.resolve, hblk]

theorem resolve_writePrefix {mpl : MultiPlacement} (hpl : coreFmtMultiLib.Placeable mpl) :
    coreFmtMultiLib.resolve mpl writePrefixIntSym = mpl.base 5 := by
  have hblk := lookupBlockSym_of_lookup (blocks := coreFmtMultiLib.blocks) (i := 5)
    (name := writePrefixIntSym) (off := 0) (hi := by decide)
    (hnd := hpl.symbols_nodup) (hl := by decide)
  simp [MultiPlacedLib.resolve, hblk]

theorem resolve_decDigitsLut (mpl : MultiPlacement) :
    coreFmtMultiLib.resolve mpl "rust_core_fmt:.rodata..Lanon.203" =
      mpl.ρ "rust_core_fmt:.rodata..Lanon.203" := by
  have hnone :
      Obj.lookupBlockSym "rust_core_fmt:.rodata..Lanon.203" coreFmtMultiLib.blocks = none := by
    decide
  simp [MultiPlacedLib.resolve, hnone]

/-! ## Block-local hook freedom and pure-segment lifters -/

/-- `P` installs no extern hooks inside code block `j` of `lib` placed at `mpl`. -/
def LibBlockNoExtern (lib : MultiPlacedLib) (mpl : MultiPlacement) (P : Program) (j : Nat) :
    Prop :=
  ∀ off : Nat, off < (lib.blockLib j).text.code.length →
    P.externAt? (mpl.base j + BitVec.ofNat 64 off) = none

theorem LibBlockNoExtern.of_no_extern {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (j : Nat) :
    LibBlockNoExtern lib mpl P j :=
  fun _ _ => hext _

/-- Every kept block `j` (`keep j = true`) of `lib` is free of extern hooks in `P`. -/
def LibKeepNoExtern (lib : MultiPlacedLib) (keep : Nat → Bool) (mpl : MultiPlacement)
    (P : Program) : Prop :=
  ∀ j : Nat, j < lib.blocks.length → keep j = true → LibBlockNoExtern lib mpl P j

theorem LibKeepNoExtern.of_no_extern {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {P : Program} (hext : ∀ pc, P.externAt? pc = none) :
    LibKeepNoExtern lib keep mpl P :=
  fun j _ _ => LibBlockNoExtern.of_no_extern hext j

/-- What a pure non-syscall instruction segment preserves on the real state `s ↝ sm`:
    `NonSyscallPreserved s sm` plus `sm.oracle = s.oracle ∧ sm.symtab = s.symtab`. -/
def PureSegPreserved (s sm : State) : Prop :=
  ProofLib.NonSyscallPreserved s sm ∧ sm.oracle = s.oracle ∧ sm.symtab = s.symtab

theorem PureSegPreserved.refl (s : State) : PureSegPreserved s s :=
  ⟨ProofLib.NonSyscallPreserved.refl s, rfl, rfl⟩

theorem PureSegPreserved.trans {s0 s1 s2 : State}
    (h01 : PureSegPreserved s0 s1) (h12 : PureSegPreserved s1 s2) :
    PureSegPreserved s0 s2 :=
  ⟨ProofLib.NonSyscallPreserved.trans h01.1 h12.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

private theorem strip_codeLoaded_local {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_local (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_local {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem execInst_oracle_symtab_local {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).oracle = s.oracle ∧ (execInst inst s).symtab = s.symtab := by
  let Q : Program := { svc := Syscall.standard }
  have hev : Q.evalInst inst s = execInst inst s :=
    Arm64.evalInst_eq_execInst_of_not_isSvc0 (prog := Q) h s
  rw [← hev]
  exact ⟨Arm64.evalInst_oracle_of_standard rfl inst s, Arm64.evalInst_symtab Q inst s⟩

private theorem steps_rebase_lift_block_local {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ PureSegPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, PureSegPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_local hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_local hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_local R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              simpa using (ProofLib.strip_perm_x_imp hx0).2
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hpseg_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      have hstep_pure : PureSegPreserved s1 (execInst inst s1) :=
        ⟨ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1,
         execInst_oracle_symtab_local hnsvc0 s1⟩
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, PureSegPreserved.trans hstep_pure hpseg_rest⟩

/-- Run a pure segment of block `j` of `lib` in `SepWP` under `CodeLoadedWhere keep`, requiring
    only block-local hook freedom `LibBlockNoExtern lib mpl P j`, refreshing `CodeLoadedWhere` and
    supplying `PureSegPreserved s sm` (`NonSyscallPreserved`, `oracle`, and `symtab`). -/
theorem sepWP_seg_lib_block_pureWhere {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < lib.blocks.length ∧ keep j = true)
    (hext_blk : LibBlockNoExtern lib mpl P j)
    (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoadedWhere keep mpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' → lib.CodeLoadedWhere keep mpl sm.mem →
            PureSegPreserved s sm →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keepExec := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj.1 hj.2).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by intro pc; simp [R_j]
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    simp only [R_j, Program.rebase, MultiPlacedLib.blockProgram, PlacedLib.program,
      Obj.CodeBlock.length_patched] at hoff ⊢
    exact hext_blk off (Nat.lt_of_lt_of_le hoff (Nat.mul_div_le _ 4))
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 lib mpl j hchk
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keepExec hm
  have hcpu_in : SameCpuState (ProofLib.stripS keepExec s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keepExec s) hcpu_in) hm_strip
      (strip_codeLoaded_local hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hpseg⟩ :=
      steps_rebase_lift_block_local hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : lib.CodeLoadedWhere keep mpl sm.mem := hsteps_P.codeLoadedWhere hcl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hpseg.1.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keepExec sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keepExec sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hpseg
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-- Full-`CodeLoaded` variant of `sepWP_seg_lib_block_pureWhere`. -/
theorem sepWP_seg_lib_block_pure {lib : MultiPlacedLib} {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < lib.blocks.length)
    (hext_blk : LibBlockNoExtern lib mpl P j)
    (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' → lib.CodeLoaded mpl sm.mem →
            PureSegPreserved s sm →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom :=
  sepWP_seg_lib_block_pureWhere (keep := fun _ => true) j ⟨hj, rfl⟩ hext_blk hchk
    (fun i hi _ => hcl i hi) fun s' hcpu =>
      SepWP.mono (hseg s' hcpu) fun sm' Pm _ _ hcont sm hsm hclw hpseg =>
        hcont sm hsm (fun i hi => hclw i hi rfl) hpseg

/-- `SepWPp` counterpart of `sepWP_seg_lib_block_pureWhere`. -/
theorem sepWPp_seg_lib_block_pureWhere {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < lib.blocks.length ∧ keep j = true)
    (hext_blk : LibBlockNoExtern lib mpl P j)
    (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoadedWhere keep mpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' → lib.CodeLoadedWhere keep mpl sm.mem →
            PureSegPreserved s sm →
            SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom := by
  let R_j := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keepExec := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj.1 hj.2).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by intro pc; simp [R_j]
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    simp only [R_j, Program.rebase, MultiPlacedLib.blockProgram, PlacedLib.program,
      Obj.CodeBlock.length_patched] at hoff ⊢
    exact hext_blk off (Nat.lt_of_lt_of_le hoff (Nat.mul_div_le _ 4))
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 lib mpl j hchk
  intro R hm hL_P
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keepExec hm
  have hcpu_in : SameCpuState (ProofLib.stripS keepExec s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keepExec s) hcpu_in) hm_strip
      (strip_codeLoaded_local hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hpseg⟩ :=
      steps_rebase_lift_block_local hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : lib.CodeLoadedWhere keep mpl sm.mem := hsteps_P.codeLoadedWhere hcl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hpseg.1.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keepExec sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keepExec sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hpseg
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm (hsteps_P.codeLoaded hL_P)
    exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

end VerifiedLibraries.RustStd.CoreFmt
