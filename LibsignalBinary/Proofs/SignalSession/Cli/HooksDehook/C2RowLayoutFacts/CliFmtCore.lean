/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `coreMultiLib`, `coreFmtMultiLib`, and Crate `Display::fmt` Shim Facts

Supplies the concrete 0-hook stock-ELF (`0d6227d21a4550baedafa8c9caf9a975266592662e339a92eaa774ec54cd7020`)
`Obj.MultiPlacement` witnesses (`c2CoreMpl` and `c2CoreFmtMpl`), `Placeable` proofs, symbol
resolutions, RX block-walk & `CodeLoaded` / `CodeLoadedWhere` discharges (`u8DisplayKeep`,
`u32DisplayKeep`, `u64DisplayKeep`, `strDisplayKeep`), `.rodata` `RoDataAt` (`decDigitsLutBytes`
and `UTF8_CHAR_WIDTH`), crate-local `String`/`&str` `Display::fmt` shim classifier & target ties,
and `.text.lib2` hull / `LsRetAddr624` bounds for `core::fmt::write`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open VerifiedLibraries.RustStd
  (checkStrRefDisplayShimBlock checkStringDisplayShimBlock coreFmtDecDigitsLutSym
   coreFmtMultiLib coreFmtWriteSym coreMultiLib decDigitsLutBytes displayShimTargetSym
   strDisplayFmtSym strRefDisplayFmtSym u32DisplayFmtSym u64DisplayFmtSym u8DisplayFmtSym
   usizeDisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt
  (strDisplayKeep u32DisplayKeep u64DisplayKeep u8DisplayKeep)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (lsFmtWriteSym)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkMultiBlockWalk checkProgCodeSubslice_of_multiBlockWalk checkRoSegSlice
   codeLoaded_of_multiBlockWalk f3CodeInv_roDataAt_of_roSegSlice resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (c2CorePlacedData1 f3LsRetAddr624_lt_firstExternStub keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxWordTree)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2FromUtf8Addr c2FromUtf8TableAddr c2Lib2RoLo c2Lib2TextHi
   c2Lib2TextLo c2MemrchrAddr wp4HandleErrorAddr)

/-! ## 1. Entry Addresses & Concrete `Obj.MultiPlacement` Definitions -/

/-- Stock-ELF entry address of `core::fmt::write` (`lsFmtWriteSym`, `0x47a058`). -/
@[expose] def c2FmtWriteAddr : BitVec 64 := c2MemrchrAddr - 2592#64

/-- Mangled `libsignal_session` extern symbols for integer and `str` `Display::fmt`. -/
abbrev lsU8DisplayFmtSym : String :=
  "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt"
abbrev lsU32DisplayFmtSym : String :=
  "_RNvXs8_NtNtNtCskxtBwYRO61I_4core3fmt3num3impmNtB9_7Display3fmt"
abbrev lsU64DisplayFmtSym : String :=
  "_RNvXsd_NtNtNtCskxtBwYRO61I_4core3fmt3num3impyNtB9_7Display3fmt"
abbrev lsUsizeDisplayFmtSym : String :=
  "_RNvXsi_NtNtNtCskxtBwYRO61I_4core3fmt3num3impjNtB9_7Display3fmt"
abbrev lsStrDisplayFmtSym : String :=
  "_RNvXsi_NtCskxtBwYRO61I_4core3fmteNtB5_7Display3fmt"

/-- Concrete 0-hook stock-ELF `Obj.MultiPlacement` for `coreMultiLib` (`3/3` blocks + `4/4`
    `.rodata`/`.data.rel.ro` objects in `lib2_0.o`). -/
@[expose] def c2CoreMpl : Obj.MultiPlacement where
  base i :=
    match i with
    | 0 => c2MemrchrAddr - 2592#64
    | 1 => c2FromUtf8Addr
    | 2 => c2MemrchrAddr
    | _ => 0#64
  ρ sym :=
    if sym == "rust_core:.data.rel.ro..Lanon.216" then
      c2Lib2RoLo + 88#64
    else if sym == "rust_core:.data.rel.ro..Lanon.217" then
      c2Lib2RoLo + 112#64
    else if sym == "rust_core:.rodata.str1.1+0x0" then
      c2Lib2RoLo + 880#64
    else if sym == "rust_core:.rodata..Lanon.208" then
      c2FromUtf8TableAddr
    else if sym == "_RNvNtNtCs2kXltWtc1W_4core5slice5index16slice_index_fail" then
      0x47a9c4#64
    else 0#64

/-- Concrete 0-hook stock-ELF `Obj.MultiPlacement` for `coreFmtMultiLib` (`10/11` blocks linked in
    `lib2_0.o`; unlinked `B07` `<&str as Display>::fmt` placed at disjoint dummy `0x51c000#64`). -/
@[expose] def c2CoreFmtMpl : Obj.MultiPlacement where
  base i :=
    match i with
    |  0 => c2Lib2TextLo + 56#64
    |  1 => c2Lib2TextLo + 1012#64
    |  2 => c2Lib2TextLo + 1800#64
    |  3 => c2Lib2TextLo + 1812#64
    |  4 => c2MemrchrAddr - 1696#64
    |  5 => c2MemrchrAddr + 436#64
    |  6 => c2MemrchrAddr + 572#64
    |  7 => 0x51c000#64
    |  8 => c2FromUtf8Addr - 700#64
    |  9 => c2FromUtf8Addr - 144#64
    | 10 => c2FromUtf8Addr - 48#64
    | _  => 0x530000#64
  ρ sym :=
    if sym == "rust_core_fmt:.data.rel.ro..Lanon.93" then
      c2Lib2RoLo + 64#64
    else if sym == "rust_core_fmt:.rodata.str1.1+0x0" then
      c2FromUtf8TableAddr - 533#64
    else if sym == "rust_core_fmt:.rodata..Lanon.203" then
      c2FromUtf8TableAddr - 403#64
    else if sym == "_RNvNtCs2kXltWtc1W_4core9panicking18panic_bounds_check" then
      0x47a2a4#64
    else 0#64

/-- Keep predicate selecting all 10 linked `coreFmtMultiLib` blocks (`0..6, 8..10`). -/
@[expose] def c2CoreFmtActiveKeep (j : Nat) : Bool :=
  decide (j < 11 ∧ j ≠ 7)

/-! ## 2. `Placeable` & Extern Symbol Resolutions -/

set_option maxRecDepth 2000000 in
theorem c2CoreMpl_placeable : coreMultiLib.Placeable c2CoreMpl :=
  coreMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

set_option maxRecDepth 2000000 in
theorem c2CoreFmtMpl_placeable : coreFmtMultiLib.Placeable c2CoreFmtMpl :=
  coreFmtMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

theorem c2_resolve_fmtWrite_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFmtWriteSym = c2FmtWriteAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFmtWriteSym).trans (by rfl_kernel)

theorem c2_resolve_fmtWrite_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFmtWriteSym =
      coreMultiLib.fnAddr c2CoreMpl coreFmtWriteSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFmtWriteSym).trans (by rfl_kernel)

theorem c2_resolve_u8DisplayFmt_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsU8DisplayFmtSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl u8DisplayFmtSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsU8DisplayFmtSym).trans (by rfl_kernel)

theorem c2_resolve_u32DisplayFmt_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsU32DisplayFmtSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl u32DisplayFmtSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsU32DisplayFmtSym).trans (by rfl_kernel)

theorem c2_resolve_u64DisplayFmt_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsU64DisplayFmtSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl u64DisplayFmtSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsU64DisplayFmtSym).trans (by rfl_kernel)

theorem c2_resolve_usizeDisplayFmt_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsUsizeDisplayFmtSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl usizeDisplayFmtSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsUsizeDisplayFmtSym).trans (by rfl_kernel)

theorem c2_resolve_strDisplayFmt_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsStrDisplayFmtSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl strDisplayFmtSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsStrDisplayFmtSym).trans (by rfl_kernel)

/-! ## 3. RX Block-Walk & `CodeLoaded` / `CodeLoadedWhere` Discharges -/

set_option maxRecDepth 2000000 in
private theorem c2_core_allBlocksWalk_ok :
    ((List.range coreMultiLib.blocks.length).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        coreMultiLib c2CoreMpl j) = true := by
  rfl_kernel

theorem c2_core_rx_blocks :
    ∀ j < coreMultiLib.blocks.length,
      checkProgCodeSubslice f3TrialRxProg (coreMultiLib.blockProgram c2CoreMpl j) = true :=
  fun j hj =>
    checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
      (List.all_eq_true.mp c2_core_allBlocksWalk_ok j (List.mem_range.mpr hj))

theorem c2_core_codeLoaded_of_rxCode {m : Memory} (hRx : f3TrialRxProg.CodeLoaded m) :
    coreMultiLib.CodeLoaded c2CoreMpl m :=
  fun j hj =>
    codeLoaded_of_multiBlockWalk hRx rfl rfl rfl
      (List.all_eq_true.mp c2_core_allBlocksWalk_ok j (List.mem_range.mpr hj))

theorem c2_core_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    coreMultiLib.CodeLoaded c2CoreMpl m :=
  c2_core_codeLoaded_of_rxCode hInv.rxCode

private def c2CoreFmtActiveIndices : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10]

set_option maxRecDepth 2000000 in
private theorem c2_coreFmt_activeWalk_ok :
    (c2CoreFmtActiveIndices.all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        coreFmtMultiLib c2CoreFmtMpl j) = true := by
  rfl_kernel

private theorem mem_c2CoreFmtActiveIndices {j : Nat} (hj : j < 11) (hne : j ≠ 7) :
    j ∈ c2CoreFmtActiveIndices := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 8, _ | 9, _ | 10, _ => decide
  | 7, _ => exact False.elim (hne rfl)

theorem c2_coreFmt_active_rx_blocks {j : Nat} (hj : j < 11) (hne : j ≠ 7) :
    checkProgCodeSubslice f3TrialRxProg (coreFmtMultiLib.blockProgram c2CoreFmtMpl j) = true :=
  checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
    (List.all_eq_true.mp c2_coreFmt_activeWalk_ok j (mem_c2CoreFmtActiveIndices hj hne))

theorem c2_coreFmt_codeLoadedWhere_active_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere c2CoreFmtActiveKeep c2CoreFmtMpl m :=
  fun j _ hk => by
    obtain ⟨hj, hne⟩ := of_decide_eq_true hk
    exact codeLoaded_of_multiBlockWalk hRx rfl rfl rfl
      (List.all_eq_true.mp c2_coreFmt_activeWalk_ok j (mem_c2CoreFmtActiveIndices hj hne))

private theorem c2_coreFmt_keep_sub_active {keep : Nat → Bool}
    (hsub : ((List.range 11).all fun j => !(keep j) || c2CoreFmtActiveKeep j) = true)
    {m : Memory} (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere keep c2CoreFmtMpl m := by
  have hlen : coreFmtMultiLib.blocks.length = 11 := by decide
  intro j hj hk
  rw [hlen] at hj
  have hall := List.all_eq_true.mp hsub j (List.mem_range.mpr hj)
  simp only [ hk, Bool.not_true, Bool.false_or] at hall
  exact c2_coreFmt_codeLoadedWhere_active_of_rxCode hRx j (by rw [hlen]; exact hj) hall

theorem c2_coreFmt_codeLoadedWhere_u8_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep c2CoreFmtMpl m :=
  c2_coreFmt_keep_sub_active (by decide) hRx

theorem c2_coreFmt_codeLoadedWhere_u32_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep c2CoreFmtMpl m :=
  c2_coreFmt_keep_sub_active (by decide) hRx

theorem c2_coreFmt_codeLoadedWhere_u64_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep c2CoreFmtMpl m :=
  c2_coreFmt_keep_sub_active (by decide) hRx

theorem c2_coreFmt_codeLoadedWhere_str_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere strDisplayKeep c2CoreFmtMpl m :=
  c2_coreFmt_keep_sub_active (by decide) hRx

/-! ## 4. `.rodata` Slices (`DEC_DIGITS_LUT` & `UTF8_CHAR_WIDTH`) -/

set_option maxRecDepth 4000000 in
private theorem c2_coreFmt_decDigitsLut_ro_ok :
    checkRoSegSlice f3PatchedElf
      (coreFmtMultiLib.resolve c2CoreFmtMpl coreFmtDecDigitsLutSym)
      decDigitsLutBytes = true := by
  rfl_kernel

theorem c2_coreFmt_roDataAt_decDigitsLut {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m (coreFmtMultiLib.resolve c2CoreFmtMpl coreFmtDecDigitsLutSym) decDigitsLutBytes :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_coreFmt_decDigitsLut_ro_ok

set_option maxRecDepth 4000000 in
private theorem c2_core_utf8Table_ro_ok :
    checkRoSegSlice f3PatchedElf c2FromUtf8TableAddr c2CorePlacedData1 = true := by
  rfl_kernel

theorem c2_core_roDataAt_utf8Table {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m c2FromUtf8TableAddr c2CorePlacedData1 :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_core_utf8Table_ro_ok

/-! ## 5. Crate-Local `String` & `&str` `Display::fmt` Shims (`libsignalSessionLib`) -/

/-- All 5 `<String as Display>::fmt` shim blocks in `libsignalSessionLib` (`seg[1]`). -/
@[expose] def c2StringDisplayShimBlocks : List Nat := [121, 191, 216, 498, 537]

/-- All 5 20-byte `&str`-forwarding `Display::fmt` shim blocks in `libsignalSessionLib` (`seg[1]`):
    block `78` (`<InvalidSessionError as Display>::fmt`) and crate-local `<&str as Display>::fmt`
    shims `170, 395, 477, 529`. -/
@[expose] def c2StrRefDisplayShimBlocks : List Nat := [78, 170, 395, 477, 529]

set_option maxRecDepth 2000000 in
private theorem c2_stringDisplayShim_all_ok :
    (c2StringDisplayShimBlocks.all fun bi =>
      checkStringDisplayShimBlock libsignalSessionLib bi &&
      (displayShimTargetSym libsignalSessionLib bi == lsStrDisplayFmtSym)) = true := by
  rfl_kernel

theorem c2_stringDisplayShim_check {bi : Nat} (hbi : bi ∈ c2StringDisplayShimBlocks) :
    checkStringDisplayShimBlock libsignalSessionLib bi = true := by
  have h := List.all_eq_true.mp c2_stringDisplayShim_all_ok bi hbi
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem c2_stringDisplayShim_target_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {bi : Nat} (hbi : bi ∈ c2StringDisplayShimBlocks) :
    libsignalSessionLib.resolve mpl (displayShimTargetSym libsignalSessionLib bi) =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl strDisplayFmtSym := by
  have h := List.all_eq_true.mp c2_stringDisplayShim_all_ok bi hbi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2]
  exact c2_resolve_strDisplayFmt_fnAddr hLs

set_option maxRecDepth 2000000 in
private theorem c2_strRefDisplayShim_all_ok :
    (c2StrRefDisplayShimBlocks.all fun bi =>
      checkStrRefDisplayShimBlock libsignalSessionLib bi &&
      (displayShimTargetSym libsignalSessionLib bi == lsStrDisplayFmtSym)) = true := by
  rfl_kernel

theorem c2_strRefDisplayShim_check {bi : Nat} (hbi : bi ∈ c2StrRefDisplayShimBlocks) :
    checkStrRefDisplayShimBlock libsignalSessionLib bi = true := by
  have h := List.all_eq_true.mp c2_strRefDisplayShim_all_ok bi hbi
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem c2_strRefDisplayShim_target_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {bi : Nat} (hbi : bi ∈ c2StrRefDisplayShimBlocks) :
    libsignalSessionLib.resolve mpl (displayShimTargetSym libsignalSessionLib bi) =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl strDisplayFmtSym := by
  have h := List.all_eq_true.mp c2_strRefDisplayShim_all_ok bi hbi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2]
  exact c2_resolve_strDisplayFmt_fnAddr hLs

/-! ## 6. `.text.lib2` Hull Inclusions & `LsRetAddr624` Guard -/

theorem c2_fmtWrite_keepLib2Text : keepLib2Text c2FmtWriteAddr = true := by
  decide

set_option maxRecDepth 400000 in
private theorem c2_core_blocks_in_lib2 :
    ((List.range coreMultiLib.blocks.length).all fun j =>
      let b := (c2CoreMpl.base j).toNat
      let len := (coreMultiLib.blockLib j).text.code.length
      Nat.beq (len % 4) 0 &&
      Nat.ble c2Lib2TextLo.toNat b &&
      Nat.ble (b + len) c2Lib2TextHi.toNat) = true := by
  rfl_kernel

theorem c2_core_block_sub_keepLib2Text {j : Nat} (hj : j < coreMultiLib.blocks.length)
    {pc : BitVec 64} (hk : progKeep (coreMultiLib.blockProgram c2CoreMpl j) pc = true) :
    keepLib2Text pc = true := by
  have hbnd := List.all_eq_true.mp c2_core_blocks_in_lib2 j (List.mem_range.mpr hj)
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨⟨hal, hlo⟩, hhi⟩
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk
  have hplen : (coreMultiLib.blockProgram c2CoreMpl j).code.length =
      (coreMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  have hbase : (coreMultiLib.blockProgram c2CoreMpl j).base = c2CoreMpl.base j := rfl
  rw [hbase, hplen] at hk
  exact c2_keepLib2Text_of_sub_lt hk hlo hhi

set_option maxRecDepth 400000 in
private theorem c2_coreFmt_active_in_lib2 :
    (c2CoreFmtActiveIndices.all fun j =>
      let b := (c2CoreFmtMpl.base j).toNat
      let len := (coreFmtMultiLib.blockLib j).text.code.length
      Nat.beq (len % 4) 0 &&
      Nat.ble c2Lib2TextLo.toNat b &&
      Nat.ble (b + len) c2Lib2TextHi.toNat) = true := by
  rfl_kernel

theorem c2_coreFmt_active_sub_keepLib2Text {j : Nat} (hj : j < 11) (hne : j ≠ 7)
    {pc : BitVec 64} (hk : progKeep (coreFmtMultiLib.blockProgram c2CoreFmtMpl j) pc = true) :
    keepLib2Text pc = true := by
  have hbnd := List.all_eq_true.mp c2_coreFmt_active_in_lib2 j (mem_c2CoreFmtActiveIndices hj hne)
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨⟨hal, hlo⟩, hhi⟩
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk
  have hplen : (coreFmtMultiLib.blockProgram c2CoreFmtMpl j).code.length =
      (coreFmtMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  have hbase : (coreFmtMultiLib.blockProgram c2CoreFmtMpl j).base = c2CoreFmtMpl.base j := rfl
  rw [hbase, hplen] at hk
  exact c2_keepLib2Text_of_sub_lt hk hlo hhi

theorem c2_fmtWrite_lr_ne [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    lr ≠ c2FmtWriteAddr := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hge : c2FirstExternStubAddr.toNat ≤ c2FmtWriteAddr.toNat := by decide
  intro heq
  rw [heq] at hlt
  omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
