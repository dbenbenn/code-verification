/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `signalSessionIoMultiLib` and `muslSysPlacedLib` Layout Facts

Supplies the concrete 0-hook stock-ELF (`0d6227d21a4550baedafa8c9caf9a975266592662e339a92eaa774ec54cd7020`)
`Obj.MultiPlacement` witnesses (`c2CliIoMpl` and `c2MuslSysMpl`), `Placeable` proofs, symbol
resolutions, callee tie equalities, `seg[1]`/`:text_a` + `seg[2]`/`f3TrialRxProg` `CodeLoaded`
discharges, and `LsRetAddr624` return-address bounds for `libsignal_cli_io::write_file` and
`libsignal_cli_io::write_stdout`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl signalSessionIoMultiLib)
open CryptoVerification.SignalSession
  (cliElfBytes libsignalSessionLib lsWriteFileSym lsWriteStdoutSym)
open VerifiedLibraries.Musl (muslSysPlacedLib)
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (cliIoCloseSym cliIoErrnoLocationSym cliIoHandleErrorSym cliIoMemcpySym cliIoOpenSym
   cliIoReadSym cliIoRustAllocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
   cliIoRustReallocSym cliIoWriteFileSym cliIoWriteStdoutSym cliIoWriteSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkMultiBlockWalk checkProgCodeSubslice_of_multiBlockWalk checkSeg1BlockSlice
   codeLoaded_of_multiBlockWalk f3CodeInv_seg1_blockCodeLoaded resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Lib2TextLo c2StartupLrLit wp4HandleErrorAddr wp4IoFinishGrowAddr wp4MemcpyRealAddr
   wp4NoShimV2Addr wp4ReadFileAddr wp4ReadStdinAddr wp4WriteFileAddr wp4WriteStdoutAddr)

/-! ## 1. Concrete Stock-ELF `Obj.MultiPlacement` Definitions -/

/-- Concrete 0-hook stock-ELF `Obj.MultiPlacement` for `signalSessionIoMultiLib`
    (`5/5` blocks: blocks `1` `write_file` and `2` `write_stdout` in `seg[1]` `:text_a`;
    blocks `0` `read_stdin`, `3` `read_file`, and `4` `finish_grow` in `seg[2]` `.text.b_pre`). -/
@[expose] def c2CliIoMpl : Obj.MultiPlacement where
  base i :=
    match i with
    | 0 => wp4ReadStdinAddr
    | 1 => wp4WriteFileAddr
    | 2 => wp4WriteStdoutAddr
    | 3 => wp4ReadFileAddr
    | 4 => wp4IoFinishGrowAddr
    | _ => 0#64
  ρ sym :=
    if sym == "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" then
      wp4HandleErrorAddr
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
    else if sym == "__errno_location" then
      c2StartupLrLit + 836#64
    else if sym == "open" then
      c2StartupLrLit + 1104#64
    else if sym == "close" then
      c2Lib2TextLo - 1048#64
    else if sym == "read" then
      c2Lib2TextLo - 980#64
    else if sym == "write" then
      c2Lib2TextLo - 928#64
    else 0#64

/-- Concrete 0-hook stock-ELF `Obj.MultiPlacement` for `muslSysPlacedLib`
    (`blocks 0..8` linked in `seg[2]`; unused `fstat`/`fstatat` `9..10` and unreferenced data
    symbols placed at disjoint dummy addresses above `seg[3]`). -/
@[expose] def c2MuslSysMpl : Obj.MultiPlacement where
  base i :=
    match i with
    |  0 => c2StartupLrLit + 836#64
    |  1 => c2StartupLrLit + 1260#64
    |  2 => c2Lib2TextLo - 1104#64
    |  3 => c2Lib2TextLo - 1068#64
    |  4 => c2Lib2TextLo - 1052#64
    |  5 => c2Lib2TextLo - 1048#64
    |  6 => c2Lib2TextLo - 980#64
    |  7 => c2Lib2TextLo - 928#64
    |  8 => c2StartupLrLit + 1104#64
    |  9 => 0x4f4000#64
    | 10 => 0x4f8000#64
    | _  => 0x4e0000#64
  ρ sym :=
    if sym == "muslEmptyCStr" then
      0x4d2000#64
    else if sym == "fstat" then
      0x4d0000#64
    else if sym == "fstatat" then
      0x4d1000#64
    else if sym == "__procfdname" then
      0x4d3000#64
    else 0#64

/-- Keep predicate selecting the 9 linked `musl` syscall blocks (`0..8`) in `seg[2]`. -/
@[expose] def muslSys9Keep (j : Nat) : Bool :=
  decide (j < 9)

/-! ## 2. `Placeable`, Entry Resolution, & Callee Tie Equalities -/

set_option maxRecDepth 2000000 in
theorem c2CliIoMpl_placeable : signalSessionIoMultiLib.Placeable c2CliIoMpl :=
  signalSessionIoMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

set_option maxRecDepth 2000000 in
theorem c2MuslSysMpl_placeable : muslSysPlacedLib.Placeable c2MuslSysMpl :=
  muslSysPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

theorem c2_resolve_writeFile_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteFileSym = wp4WriteFileAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteFileSym).trans (by rfl_kernel)

theorem c2_resolve_writeFile_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteFileSym =
      signalSessionIoMultiLib.fnAddr c2CliIoMpl cliIoWriteFileSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteFileSym).trans (by rfl_kernel)

theorem c2_resolve_writeFile_resolve {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteFileSym =
      signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteFileSym).trans (by rfl_kernel)

theorem c2_resolve_writeStdout_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteStdoutSym = wp4WriteStdoutAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteStdoutSym).trans (by rfl_kernel)

theorem c2_resolve_writeStdout_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteStdoutSym =
      signalSessionIoMultiLib.fnAddr c2CliIoMpl cliIoWriteStdoutSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteStdoutSym).trans (by rfl_kernel)

theorem c2_resolve_writeStdout_resolve {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsWriteStdoutSym =
      signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsWriteStdoutSym).trans (by rfl_kernel)

theorem c2_cliIo_resolve_open :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoOpenSym = c2MuslSysMpl.base 8 := by
  rfl_kernel

theorem c2_cliIo_resolve_write :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteSym = c2MuslSysMpl.base 7 := by
  rfl_kernel

theorem c2_cliIo_resolve_close :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoCloseSym = c2MuslSysMpl.base 5 := by
  rfl_kernel

theorem c2_cliIo_resolve_read :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoReadSym = c2MuslSysMpl.base 6 := by
  rfl_kernel

theorem c2_cliIo_resolve_errno :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoErrnoLocationSym = c2MuslSysMpl.base 0 := by
  rfl_kernel

theorem c2_cliIo_resolve_handleError :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoHandleErrorSym = wp4HandleErrorAddr := by
  rfl_kernel

theorem c2_cliIo_resolve_memcpy :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoMemcpySym = wp4MemcpyRealAddr := by
  rfl_kernel

theorem c2_cliIo_resolve_noAllocShim :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoRustNoAllocShimSym = wp4NoShimV2Addr := by
  rfl_kernel

theorem c2_cliIo_resolve_rustAlloc :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoRustAllocSym = wp4NoShimV2Addr - 16#64 := by
  rfl_kernel

theorem c2_cliIo_resolve_rustDealloc :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoRustDeallocSym = wp4NoShimV2Addr - 12#64 := by
  rfl_kernel

theorem c2_cliIo_resolve_rustRealloc :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoRustReallocSym = wp4NoShimV2Addr - 8#64 := by
  rfl_kernel

/-! ## 3. `seg[1]` + `seg[2]` Code-Slice & `CodeLoaded` Discharges -/

set_option maxRecDepth 2000000 in
private theorem c2_cliIo_seg2Walk_ok :
    ([0, 3, 4].all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        signalSessionIoMultiLib c2CliIoMpl j) = true := by
  rfl_kernel

theorem c2_cliIo_seg2_rx_blocks {j : Nat} (hj : j ∈ [0, 3, 4]) :
    checkProgCodeSubslice f3TrialRxProg
      (signalSessionIoMultiLib.blockProgram c2CliIoMpl j) = true :=
  checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
    (List.all_eq_true.mp c2_cliIo_seg2Walk_ok j hj)

set_option maxRecDepth 4000000 in
private theorem c2_cliIo_seg1_blk1_ok :
    checkSeg1BlockSlice f3PatchedElf signalSessionIoMultiLib c2CliIoMpl 1 = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_cliIo_seg1_blk2_ok :
    checkSeg1BlockSlice f3PatchedElf signalSessionIoMultiLib c2CliIoMpl 2 = true := by
  rfl_kernel

theorem c2_cliIo_seg1_blk1_codeLoaded {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).CodeLoaded m :=
  f3CodeInv_seg1_blockCodeLoaded hLs hInv c2_cliIo_seg1_blk1_ok

theorem c2_cliIo_seg1_blk2_codeLoaded {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).CodeLoaded m :=
  f3CodeInv_seg1_blockCodeLoaded hLs hInv c2_cliIo_seg1_blk2_ok

/-- Full `5/5`-block `CodeLoaded` witness for `signalSessionIoMultiLib` at `c2CliIoMpl`
    under `F3CodeInv`. -/
theorem c2_cliIo_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    signalSessionIoMultiLib.CodeLoaded c2CliIoMpl m := by
  have hlen : signalSessionIoMultiLib.blocks.length = 5 := by decide
  intro i hi
  rw [hlen] at hi
  match i, hi with
  | 0, _ =>
    exact codeLoaded_of_checkProgCodeSubslice hInv.rxCode (c2_cliIo_seg2_rx_blocks (by decide))
  | 1, _ => exact c2_cliIo_seg1_blk1_codeLoaded hLs hInv
  | 2, _ => exact c2_cliIo_seg1_blk2_codeLoaded hLs hInv
  | 3, _ =>
    exact codeLoaded_of_checkProgCodeSubslice hInv.rxCode (c2_cliIo_seg2_rx_blocks (by decide))
  | 4, _ =>
    exact codeLoaded_of_checkProgCodeSubslice hInv.rxCode (c2_cliIo_seg2_rx_blocks (by decide))

set_option maxRecDepth 2000000 in
private theorem c2_muslSys9Walk_ok :
    ((List.range 9).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        muslSysPlacedLib c2MuslSysMpl j) = true := by
  rfl_kernel

theorem c2_muslSys9_rx_blocks {j : Nat} (hj : j < 9) :
    checkProgCodeSubslice f3TrialRxProg
      (muslSysPlacedLib.blockProgram c2MuslSysMpl j) = true :=
  checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
    (List.all_eq_true.mp c2_muslSys9Walk_ok j (List.mem_range.mpr hj))

theorem c2_muslSys_codeLoadedWhere9_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    muslSysPlacedLib.CodeLoadedWhere muslSys9Keep c2MuslSysMpl m :=
  fun j _ hj =>
    codeLoaded_of_multiBlockWalk hRx rfl rfl rfl
      (List.all_eq_true.mp c2_muslSys9Walk_ok j (List.mem_range.mpr (of_decide_eq_true hj)))

theorem c2_muslSys_codeLoadedWhere9_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    muslSysPlacedLib.CodeLoadedWhere muslSys9Keep c2MuslSysMpl m :=
  c2_muslSys_codeLoadedWhere9_of_rxCode hInv.rxCode

/-- Byte length of the panic-free `seg[2]` prefix `[f3RxSegBase, c2Lib2TextLo)`. -/
@[expose] def c2WriteLoByteLen : Nat :=
  (c2Lib2TextLo - f3RxSegBase).toNat

/-- Panic-free `Syscall.standard` prefix of `f3TrialRxProg` covering `.text.b_pre`, `mallocng`,
    and all 9 `muslSysPlacedLib` syscall blocks (`[0x474000, 0x479798)`). -/
@[expose] noncomputable def f3WriteLoRxProg : Program :=
  { base := f3RxSegBase
    code := f3TrialRxProg.code.take c2WriteLoByteLen
    svc := Syscall.standard }

theorem f3WriteLoRxProg_base : f3WriteLoRxProg.base = f3RxSegBase := rfl
theorem f3WriteLoRxProg_svc : f3WriteLoRxProg.svc = Syscall.standard := rfl
theorem f3WriteLoRxProg_no_ext (pc : BitVec 64) : f3WriteLoRxProg.externAt? pc = none := rfl

theorem f3TrialRxProg_code_len : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

private theorem c2WriteLoByteLen_le_rx : c2WriteLoByteLen ≤ 4 * f3RxWordCount := by decide

theorem f3WriteLoRxProg_code_len : f3WriteLoRxProg.code.length = c2WriteLoByteLen := by
  dsimp only [f3WriteLoRxProg]
  rw [List.length_take, f3TrialRxProg_code_len]
  exact Nat.min_eq_left c2WriteLoByteLen_le_rx

theorem f3WriteLoRxProg_getElem (i : Nat)
    (h1 : i < f3WriteLoRxProg.code.length) (h2 : i < f3TrialRxProg.code.length) :
    f3WriteLoRxProg.code[i]'h1 = f3TrialRxProg.code[i]'h2 := by
  dsimp only [f3WriteLoRxProg] at h1 ⊢
  simp only [List.getElem_take]

theorem f3WriteLoRxProg_codeLoaded_of_trial {m : Memory}
    (hcl : f3TrialRxProg.CodeLoaded m) :
    f3WriteLoRxProg.CodeLoaded m := by
  have hlen_le : f3WriteLoRxProg.code.length ≤ f3TrialRxProg.code.length := by
    rw [f3WriteLoRxProg_code_len, f3TrialRxProg_code_len]
    exact c2WriteLoByteLen_le_rx
  have hbase : f3WriteLoRxProg.base = f3TrialRxProg.base :=
    f3WriteLoRxProg_base.trans f3TrialRxProg_base.symm
  have halign := hcl.aligned
  rw [← hbase] at halign
  have hnowrap : f3WriteLoRxProg.base.toNat + f3WriteLoRxProg.code.length ≤ 2 ^ 64 := by
    have hnw := hcl.no_wrap
    rw [← hbase] at hnw
    omega
  refine Program.CodeLoaded.intro halign hnowrap fun i hi => ?_
  have hi_full : i < f3TrialRxProg.code.length := Nat.lt_of_lt_of_le hi hlen_le
  have haddr : f3WriteLoRxProg.base + BitVec.ofNat 64 i =
      f3TrialRxProg.base + BitVec.ofNat 64 i :=
    congrArg (· + BitVec.ofNat 64 i) hbase
  have hbyte_mem : m.read8 (f3WriteLoRxProg.base + BitVec.ofNat 64 i) =
      f3WriteLoRxProg.code[i]'hi := by
    rw [haddr, f3WriteLoRxProg_getElem i hi hi_full]
    exact hcl.byte_eq i hi_full
  have hperm_mem := hcl.perm_eq i hi_full
  rw [← haddr] at hperm_mem
  have hlazy_mem := hcl.isLazyFree_eq i hi_full
  rw [← haddr] at hlazy_mem
  exact ⟨hbyte_mem, hperm_mem, hlazy_mem⟩

set_option maxRecDepth 400000 in
theorem c2_muslSys9_in_writeLo :
    ((List.range 9).all fun j =>
      let P := muslSysPlacedLib.blockProgram c2MuslSysMpl j
      Nat.ble f3RxSegBase.toNat P.base.toNat &&
        Nat.ble (P.base.toNat + P.code.length)
          (f3RxSegBase.toNat + c2WriteLoByteLen)) = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
theorem c2_cliIo_seg2_in_writeLo :
    ([0, 3, 4].all fun j =>
      let P := signalSessionIoMultiLib.blockProgram c2CliIoMpl j
      Nat.ble f3RxSegBase.toNat P.base.toNat &&
        Nat.ble (P.base.toNat + P.code.length)
          (f3RxSegBase.toNat + c2WriteLoByteLen)) = true := by
  rfl_kernel

theorem c2_muslSys_codeLoadedWhere9_of_writeLo {m : Memory}
    (hLo : f3WriteLoRxProg.CodeLoaded m) :
    muslSysPlacedLib.CodeLoadedWhere muslSys9Keep c2MuslSysMpl m := by
  intro j _ hj_dec
  have hj : j < 9 := of_decide_eq_true hj_dec
  have hbnd := List.all_eq_true.mp c2_muslSys9_in_writeLo j (List.mem_range.mpr hj)
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hbnd
  obtain ⟨hlo, hhi⟩ := hbnd
  obtain ⟨hAlign, hNoWrap, hSub⟩ := rxSubslice_of_checkProgCodeSubslice (c2_muslSys9_rx_blocks hj)
  generalize muslSysPlacedLib.blockProgram c2MuslSysMpl j = P at hlo hhi hAlign hNoWrap hSub ⊢
  refine Program.CodeLoaded.intro hAlign hNoWrap fun i hi => ?_
  obtain ⟨k, hk_trial, haddr, hbyte⟩ := hSub i hi
  have hk_nat : k < 4 * f3RxWordCount := by
    rw [← f3TrialRxProg_code_len]; exact hk_trial
  rw [f3TrialRxProg_base] at haddr
  have hrx_top : f3RxSegBase.toNat + 4 * f3RxWordCount < 2 ^ 64 := by decide
  have hlo_top : f3RxSegBase.toNat + c2WriteLoByteLen < 2 ^ 64 := by decide
  have hlhs : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hrhs : (f3RxSegBase + BitVec.ofNat 64 k).toNat = f3RxSegBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have heq_nat : P.base.toNat + i = f3RxSegBase.toNat + k :=
    hlhs.symm.trans ((congrArg BitVec.toNat haddr).trans hrhs)
  have hk_lo : k < f3WriteLoRxProg.code.length := by
    rw [f3WriteLoRxProg_code_len]; omega
  have hbyte_lo : f3WriteLoRxProg.code[k]'hk_lo = f3TrialRxProg.code[k]'hk_trial :=
    f3WriteLoRxProg_getElem k hk_lo hk_trial
  have haddr_lo : P.base + BitVec.ofNat 64 i = f3WriteLoRxProg.base + BitVec.ofNat 64 k := by
    rw [f3WriteLoRxProg_base]; exact haddr
  have hbyte_eq : m.read8 (P.base + BitVec.ofNat 64 i) = P.code[i]'hi := by
    rw [haddr_lo, hbyte, ← hbyte_lo]
    exact hLo.byte_eq k hk_lo
  have hperm_eq := hLo.perm_eq k hk_lo
  rw [← haddr_lo] at hperm_eq
  have hlazy_eq : m.isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
    rw [haddr_lo]; exact hLo.isLazyFree_eq k hk_lo
  exact ⟨hbyte_eq, hperm_eq, hlazy_eq⟩

/-! ## 4. `LsRetAddr624` Upper Bound Below `wp4WriteFileAddr` -/

set_option maxRecDepth 400000 in
private theorem c2_lsRetAddr624_le_writeFile_ok :
    (Nat.beq libsignalSessionLib.blocks.length 624 &&
     Nat.beq cliElfBlockBases.length 624 &&
     (List.range 624).all (fun j =>
       Nat.ble ((cliElfBlockBases.getD j 0#64).toNat + lsLen j) wp4WriteFileAddr.toNat)) = true := by
  rfl_kernel

/-- Every `LsRetAddr624 lr` in crate blocks `0..623` lies strictly below `wp4WriteFileAddr`
    (`0x473724`), and therefore outside `write_file` (`0x473724..0x473854`), `write_stdout`
    (`0x473854..0x47390c`), all extern stubs (`0x47390c..`), and all of `seg[2]` (`0x474000..`). -/
theorem c2_lsRetAddr624_lt_writeFile [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr) :
    lr.toNat < wp4WriteFileAddr.toNat := by
  rcases hRet with ⟨j, hj, o, ho, rfl⟩
  have hok := c2_lsRetAddr624_le_writeFile_ok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  have hjlen : j < libsignalSessionLib.blocks.length := by
    rw [hok.1.1]; exact hj
  have hbase_eq : lsmpl.base j = cliElfMultiPlacement.base j :=
    (cliElf_linkedAt_unique hLs).1 j hjlen
  have hdef : cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 := rfl
  have hbnd : (cliElfBlockBases.getD j 0#64).toNat + lsLen j ≤ wp4WriteFileAddr.toNat := by
    have hall := List.all_eq_true.mp hok.2 j (List.mem_range.mpr hj)
    rwa [Nat.ble_eq] at hall
  rw [hbase_eq, hdef]
  have hwf_lt : wp4WriteFileAddr.toNat < 2 ^ 64 := BitVec.isLt wp4WriteFileAddr
  have hadd : ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o).toNat =
      (cliElfBlockBases.getD j 0#64).toNat + o := by
    have ho' : (BitVec.ofNat 64 o).toNat = o := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, ho', Nat.mod_eq_of_lt (by omega)]
  omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite
