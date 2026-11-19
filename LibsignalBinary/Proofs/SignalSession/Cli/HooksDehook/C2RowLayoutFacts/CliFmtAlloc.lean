/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `allocMultiLib` and `<String as fmt::Write>` Vtable Layout Facts

Supplies the concrete 0-hook stock-ELF (`0d6227d21a4550baedafa8c9caf9a975266592662e339a92eaa774ec54cd7020`)
`Obj.MultiPlacement` (`c2AllocMpl`) for all `9/9` code blocks (`B04` `<String as Clone>::clone` at
`wp4Blk623Base = 0x4736a0` in `seg[1]`, `B00..03,B05..08` in `seg[2]` `.text.lib2`) and `6/6`
`.rodata`/`.data.rel.ro` objects of `allocMultiLib`, discharging:
1. `c2AllocMpl_placeable : allocMultiLib.Placeable c2AllocMpl`
2. `lsFormatInnerSym` resolution, `fmtInnerCoreFmtWriteRawSym` → `c2CoreMpl` tie, and allocator /
   `memcpy` / `handle_error` resolution equalities
3. `CodeLoadedWhere stringWriterKeep` on `f3TrialRxProg` (`seg[2]` only) and full `9/9`-block
   `allocMultiLib.CodeLoaded` under `F3CodeInv` (`seg[1]` + `seg[2]`, directly satisfying
   `CliFormatInnerLink.clAlloc`)
4. `<String as fmt::Write>` `.data.rel.ro` vtable method-slot `RoDataAt` at
   `(allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64` (`writeStr`, `writeChar`, `writeFmt`)
5. `.text.lib2` hull inclusions and `LsRetAddr624` bounds.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open VerifiedLibraries.RustStd
  (allocBudgetHandleErrorSym allocFormatInnerSym allocMultiLib allocRustAllocSym
   allocRustNoAllocShimSym allocRustReallocSym allocStringWriteAddrs coreFmtWriteSym
   coreMultiLib fmtInnerCoreFmtWriteRawSym stringWriterKeep)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (lsFormatInnerSym)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkMultiBlockWalk checkProgCodeSubslice_of_multiBlockWalk checkRoSegSlice
   checkSeg1BlockSlice codeLoaded_of_multiBlockWalk f3CodeInv_roDataAt_of_roSegSlice
   f3CodeInv_seg1_blockCodeLoaded resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore (c2CoreMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxWordTree)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2FromUtf8TableAddr c2Lib2RoHi c2Lib2RoLo c2Lib2TextHi c2Lib2TextLo
   c2MemrchrAddr c2TimeAddAddr wp4HandleErrorAddr wp4MemcpyRealAddr wp4NoShimV2Addr
   wp4WriteFileAddr)

/-! ## 1. Entry Address & Concrete `Obj.MultiPlacement` Definition -/

/-- Stock-ELF entry address of `alloc::fmt::format::format_inner` (`lsFormatInnerSym`, `0x4cb0e4`). -/
@[expose] def c2FormatInnerAddr : BitVec 64 := c2TimeAddAddr - 1512#64

/-- Concrete 0-hook stock-ELF `Obj.MultiPlacement` for all `9/9` blocks (`B04` at
    `wp4WriteFileAddr - 132#64 = 0x4736a0` in `seg[1]`, `B00..03,B05..08` in `seg[2]` `.text.lib2`)
    and `6/6` `.rodata`/`.data.rel.ro` objects of `allocMultiLib`. -/
@[expose] def c2AllocMpl : Obj.MultiPlacement where
  base i :=
    match i with
    | 0 => c2TimeAddAddr - 1940#64
    | 1 => c2TimeAddAddr - 1916#64
    | 2 => c2TimeAddAddr - 1796#64
    | 3 => c2TimeAddAddr - 1512#64
    | 4 => wp4WriteFileAddr - 132#64
    | 5 => c2TimeAddAddr - 1080#64
    | 6 => c2TimeAddAddr - 1060#64
    | 7 => c2TimeAddAddr - 776#64
    | 8 => c2TimeAddAddr - 652#64
    | _ => 0#64
  ρ sym :=
    if sym == "rust_alloc:.data.rel.ro..Lanon.6" then
      c2Lib2RoLo + 160#64
    else if sym == "rust_alloc:.data.rel.ro..Lanon.34" then
      c2Lib2RoLo + 216#64
    else if sym == "rust_alloc:.data.rel.ro..Lanon.37" then
      c2Lib2RoLo + 264#64
    else if sym == "rust_alloc:.rodata.str1.1+0x0" then
      c2FromUtf8TableAddr - 779#64
    else if sym == "rust_alloc:.rodata..Lanon.35" then
      c2Lib2RoHi - 178#64
    else if sym == "rust_alloc:.rodata..Lanon.50" then
      c2Lib2RoHi - 92#64
    else if sym == "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error" then
      wp4HandleErrorAddr
    else if sym == "_RNvNtCs2kXltWtc1W_4core6result13unwrap_failed" then
      0x47a258#64
    else if sym == "_Unwind_Resume" then
      0x473a50#64
    else if sym == "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" then
      wp4NoShimV2Addr - 16#64
    else if sym == "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" then
      wp4NoShimV2Addr - 12#64
    else if sym == "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" then
      wp4NoShimV2Addr - 8#64
    else if sym == "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" then
      wp4NoShimV2Addr
    else if sym == "memcpy" then
      wp4MemcpyRealAddr
    else if sym == "_RNvMsa_NtCs2kXltWtc1W_4core3fmtNtB5_9Formatter9write_str" then
      c2Lib2TextLo + 1800#64
    else if sym == "_RNvNtCs2kXltWtc1W_4core3fmt5write" then
      c2MemrchrAddr - 2592#64
    else 0#64

/-! ## 2. `Placeable`, Entry Resolution, & Callee Tie Equalities -/

set_option maxRecDepth 2000000 in
theorem c2AllocMpl_placeable : allocMultiLib.Placeable c2AllocMpl :=
  allocMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

theorem c2_resolve_formatInner_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFormatInnerSym = c2FormatInnerAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFormatInnerSym).trans (by rfl_kernel)

theorem c2_resolve_formatInner_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFormatInnerSym =
      allocMultiLib.fnAddr c2AllocMpl allocFormatInnerSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFormatInnerSym).trans (by rfl_kernel)

theorem c2_alloc_fmtWriteTie :
    allocMultiLib.resolve c2AllocMpl fmtInnerCoreFmtWriteRawSym =
      coreMultiLib.fnAddr c2CoreMpl coreFmtWriteSym := by
  rfl_kernel

theorem c2_alloc_handleError_resolve :
    allocMultiLib.resolve c2AllocMpl allocBudgetHandleErrorSym = wp4HandleErrorAddr := by
  rfl_kernel

theorem c2_alloc_memcpy_resolve :
    allocMultiLib.resolve c2AllocMpl "memcpy" = wp4MemcpyRealAddr := by
  rfl_kernel

theorem c2_alloc_noAllocShim_resolve :
    allocMultiLib.resolve c2AllocMpl allocRustNoAllocShimSym = wp4NoShimV2Addr := by
  rfl_kernel

theorem c2_alloc_rustAlloc_resolve :
    allocMultiLib.resolve c2AllocMpl allocRustAllocSym = wp4NoShimV2Addr - 16#64 := by
  rfl_kernel

theorem c2_alloc_rustRealloc_resolve :
    allocMultiLib.resolve c2AllocMpl allocRustReallocSym = wp4NoShimV2Addr - 8#64 := by
  rfl_kernel

/-! ## 3. `seg[1]` + `seg[2]` Code-Walk & `CodeLoaded` / `CodeLoadedWhere` Discharges -/

private def c2AllocSeg2Indices : List Nat := [0, 1, 2, 3, 5, 6, 7, 8]

set_option maxRecDepth 2000000 in
private theorem c2_alloc_seg2WalkA_ok :
    (([0, 1, 2, 3] : List Nat).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        allocMultiLib c2AllocMpl j) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem c2_alloc_seg2WalkB_ok :
    (([5, 6, 7, 8] : List Nat).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        allocMultiLib c2AllocMpl j) = true := by
  rfl_kernel

private theorem c2_alloc_seg2Walk_ok :
    (c2AllocSeg2Indices.all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        allocMultiLib c2AllocMpl j) = true := by
  change (([0, 1, 2, 3] ++ [5, 6, 7, 8]).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        allocMultiLib c2AllocMpl j) = true
  rw [List.all_append]
  exact Bool.and_eq_true_iff.mpr ⟨c2_alloc_seg2WalkA_ok, c2_alloc_seg2WalkB_ok⟩

private theorem mem_c2AllocSeg2Indices {j : Nat} (hj : j < 9) (hne : j ≠ 4) :
    j ∈ c2AllocSeg2Indices := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 7, _ | 8, _ => decide
  | 4, _ => exact False.elim (hne rfl)

theorem c2_alloc_seg2_rx_blocks {j : Nat} (hj : j < 9) (hne : j ≠ 4) :
    checkProgCodeSubslice f3TrialRxProg (allocMultiLib.blockProgram c2AllocMpl j) = true :=
  checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
    (List.all_eq_true.mp c2_alloc_seg2Walk_ok j (mem_c2AllocSeg2Indices hj hne))

theorem c2_alloc_stringWriter_codeLoaded_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    allocMultiLib.CodeLoadedWhere stringWriterKeep c2AllocMpl m := by
  have hlen : allocMultiLib.blocks.length = 9 := by decide
  have hsub : ((List.range 9).all fun j => !(stringWriterKeep j) || decide (j ≠ 4)) = true := by
    decide
  intro j hj hk
  rw [hlen] at hj
  have hall := List.all_eq_true.mp hsub j (List.mem_range.mpr hj)
  simp only [hk, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hall
  exact codeLoaded_of_multiBlockWalk hRx rfl rfl rfl
    (List.all_eq_true.mp c2_alloc_seg2Walk_ok j (mem_c2AllocSeg2Indices hj hall))

theorem c2_alloc_stringWriter_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    allocMultiLib.CodeLoadedWhere stringWriterKeep c2AllocMpl m :=
  c2_alloc_stringWriter_codeLoaded_of_rxCode hInv.rxCode

set_option maxRecDepth 4000000 in
private theorem c2_alloc_seg1_blk4_ok :
    checkSeg1BlockSlice f3PatchedElf allocMultiLib c2AllocMpl 4 = true := by
  rfl_kernel

theorem c2_alloc_seg1_blk4_codeLoaded {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    (allocMultiLib.blockProgram c2AllocMpl 4).CodeLoaded m :=
  f3CodeInv_seg1_blockCodeLoaded hLs hInv c2_alloc_seg1_blk4_ok

/-- Full `9/9`-block `CodeLoaded` witness for `allocMultiLib` at `c2AllocMpl` under `F3CodeInv`
    (blocks `0..3, 5..8` in `seg[2]` + block `4` `<String as Clone>::clone` in `seg[1]`). -/
theorem c2_alloc_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    allocMultiLib.CodeLoaded c2AllocMpl m := by
  have hlen : allocMultiLib.blocks.length = 9 := by decide
  intro j hj
  rw [hlen] at hj
  by_cases h4 : j = 4
  · subst h4; exact c2_alloc_seg1_blk4_codeLoaded hLs hInv
  · exact codeLoaded_of_checkProgCodeSubslice hInv.rxCode (c2_alloc_seg2_rx_blocks hj h4)

/-! ## 4. `<String as fmt::Write>` `.data.rel.ro` Vtable Slots (`seg[0]`) -/

/-- Little-endian 8-byte representation of a 64-bit pointer word. -/
@[expose] def leBytes64 (w : BitVec 64) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
   w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]

/-- Expected 24-byte method-pointer slice (`writeStr`, `writeChar`, `writeFmt`) at
    `(allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64`. -/
@[expose] def c2StringWriteVtableSlotsBytes : List (BitVec 8) :=
  let va := allocStringWriteAddrs c2AllocMpl
  leBytes64 va.writeStr ++ leBytes64 va.writeChar ++ leBytes64 va.writeFmt

set_option maxRecDepth 4000000 in
private theorem c2_alloc_vtableSlots_ro_ok :
    checkRoSegSlice f3PatchedElf
      ((allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64)
      c2StringWriteVtableSlotsBytes = true := by
  rfl_kernel

theorem c2_alloc_roDataAt_vtableSlots {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m ((allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64)
      c2StringWriteVtableSlotsBytes :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_alloc_vtableSlots_ro_ok

set_option maxRecDepth 4000000 in
private theorem c2_alloc_vtableWriteStr_ro_ok :
    checkRoSegSlice f3PatchedElf
      ((allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeStr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_alloc_vtableWriteChar_ro_ok :
    checkRoSegSlice f3PatchedElf
      ((allocStringWriteAddrs c2AllocMpl).vtable + 0x20#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeChar) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_alloc_vtableWriteFmt_ro_ok :
    checkRoSegSlice f3PatchedElf
      ((allocStringWriteAddrs c2AllocMpl).vtable + 0x28#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeFmt) = true := by
  rfl_kernel

theorem c2_alloc_roDataAt_vtableWriteStr {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m ((allocStringWriteAddrs c2AllocMpl).vtable + 0x18#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeStr) :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_alloc_vtableWriteStr_ro_ok

theorem c2_alloc_roDataAt_vtableWriteChar {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m ((allocStringWriteAddrs c2AllocMpl).vtable + 0x20#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeChar) :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_alloc_vtableWriteChar_ro_ok

theorem c2_alloc_roDataAt_vtableWriteFmt {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m ((allocStringWriteAddrs c2AllocMpl).vtable + 0x28#64)
      (leBytes64 (allocStringWriteAddrs c2AllocMpl).writeFmt) :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_alloc_vtableWriteFmt_ro_ok

/-! ## 5. `.text.lib2` Hull Inclusions & `LsRetAddr624` Guard -/

theorem c2_formatInner_keepLib2Text : keepLib2Text c2FormatInnerAddr = true := by
  decide

set_option maxRecDepth 400000 in
private theorem c2_alloc_seg2_in_lib2 :
    (c2AllocSeg2Indices.all fun j =>
      let b := (c2AllocMpl.base j).toNat
      let len := (allocMultiLib.blockLib j).text.code.length
      Nat.beq (len % 4) 0 &&
      Nat.ble c2Lib2TextLo.toNat b &&
      Nat.ble (b + len) c2Lib2TextHi.toNat) = true := by
  rfl_kernel

theorem c2_alloc_seg2_sub_keepLib2Text {j : Nat} (hj : j < 9) (hne : j ≠ 4)
    {pc : BitVec 64} (hk : progKeep (allocMultiLib.blockProgram c2AllocMpl j) pc = true) :
    keepLib2Text pc = true := by
  have hbnd := List.all_eq_true.mp c2_alloc_seg2_in_lib2 j (mem_c2AllocSeg2Indices hj hne)
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨⟨hal, hlo⟩, hhi⟩
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk
  have hplen : (allocMultiLib.blockProgram c2AllocMpl j).code.length =
      (allocMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  have hbase : (allocMultiLib.blockProgram c2AllocMpl j).base = c2AllocMpl.base j := rfl
  rw [hbase, hplen] at hk
  exact c2_keepLib2Text_of_sub_lt hk hlo hhi

theorem c2_formatInner_lr_ne [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    lr ≠ c2FormatInnerAddr := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hge : c2FirstExternStubAddr.toNat ≤ c2FormatInnerAddr.toNat := by decide
  intro heq
  rw [heq] at hlt
  omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
