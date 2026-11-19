/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `Placeable`, RX Subslice, `.rodata` `K64`, and Hull Glue for `sha2::sha512::compress512`

Supplies the concrete 0-hook stock-ELF (`0d6227d21a4550baedafa8c9caf9a975266592662e339a92eaa774ec54cd7020`)
placement, `Placeable`, symbol resolution, RX code-subslice (`checkProgCodeSubslice`), `.rodata`
`sha512KBytes` (`640` B), `.text.lib2` hull bounds, and `LsRetAddr624` exclusion for
`compress512Sym` (`sha2::sha512::compress512`), directly discharging every field of
`Compress512Row.C2Compress512LayoutFacts`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512K64Data compress512Lib compress512Sym sha2K64Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkCodeBlockWalk checkProgCodeSubslice_of_codeBlockWalk checkRoSegSlice
   f3CodeInv_roDataAt_of_roSegSlice resolve_lsExtern_eq_cliElf_rho roSlice_of_checkRoSegSlice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxWordTree)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Compress256Addr c2Compress256K32Addr c2FirstExternStubAddr c2Lib2TextHi c2Lib2TextLo)

/-- Mangled symbol alias matching `CliBinaryPq` naming convention. -/
abbrev lsCompress512Sym : String := compress512Sym

/-- Stock-ELF entry address of `sha2::sha512::compress512` (`0x4bcf18`, immediately after
    `compress256` in `.text.lib2`). -/
@[expose] def c2Compress512Addr : BitVec 64 := c2Compress256Addr + 7636#64

/-- Stock-ELF `.rodata.lib2` address of the 640-byte SHA-512 `K64` table (`0x413bb0`,
    immediately after `sha256`'s 256-byte `K32` table). -/
@[expose] def c2Compress512K64Addr : BitVec 64 := c2Compress256K32Addr + 256#64

/-- Byte length of `compress512Block.code` (`2,413` instructions = `9,652` B). -/
@[expose] def c2Compress512ByteLen : Nat := 9652

/-- Concrete 0-hook stock-ELF `Obj.Placement` for `compress512Lib`
    (definitionally `rfl`-equal to `compress512Placement c2Compress512Addr c2Compress512K64Addr`). -/
@[expose] def c2Compress512Pl : Obj.Placement where
  base := c2Compress512Addr
  ρ sym := if sym == sha2K64Sym then c2Compress512K64Addr else 0#64

/-- Placed `Program` of `compress512Lib` at `c2Compress512Pl` with `Syscall.standard`
    (definitionally `rfl`-equal to `compress512SubProg c2Compress512Pl`). -/
@[expose] def c2Compress512SubProg : Program :=
  { compress512Lib.program c2Compress512Pl (fun _ => none) with svc := Syscall.standard }

/-- Execute-keep predicate `[c2Compress512Addr, c2Compress512Addr + 9652)`
    (definitionally `rfl`-equal to `keepR_compress512 c2Compress512Pl`). -/
@[expose] def keepR_c2Compress512 (pc : BitVec 64) : Bool :=
  decide ((pc - c2Compress512Addr).toNat < c2Compress512ByteLen)

theorem c2Compress512Pl_base : c2Compress512Pl.base = c2Compress512Addr :=
  rfl

theorem c2Compress512Pl_k64 : c2Compress512Pl.ρ sha2K64Sym = c2Compress512K64Addr := by
  simp [c2Compress512Pl]

set_option maxRecDepth 2000000 in
theorem c2_checkCompress512Placeable_ok :
    compress512Lib.text.checkPlaceable c2Compress512Pl = true := by
  rfl_kernel

theorem c2_compress512Lib_placeable :
    compress512Lib.Placeable c2Compress512Pl where
  text := CodeBlock.placeable_of_checkPlaceable c2_checkCompress512Placeable_ok
  data_nodup := by decide
  data_ok := by
    intro d hd
    simp only [compress512Lib, List.mem_singleton] at hd
    subst hd
    refine ⟨by decide, by decide, ?_, ?_⟩
    · dsimp only [compress512K64Data]; rw [c2Compress512Pl_k64]; decide
    · dsimp only [compress512K64Data]; rw [c2Compress512Pl_k64]; decide +kernel
  data_relocs_ok := by
    intro d hd r hr
    simp only [compress512Lib, List.mem_singleton] at hd
    subst hd
    cases hr

theorem c2_compress512_resolve_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl compress512Sym = c2Compress512Addr :=
  (resolve_lsExtern_eq_cliElf_rho hLs compress512Sym).trans (by rfl_kernel)

set_option maxRecDepth 2000000 in
private theorem c2_compress512_walk_ok :
    checkCodeBlockWalk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      compress512Lib.text c2Compress512Pl = true := by
  rfl_kernel

private theorem with_svc_base (P : Program) (s : State → State) :
    ({ P with svc := s } : Program).base = P.base := rfl

private theorem with_svc_code (P : Program) (s : State → State) :
    ({ P with svc := s } : Program).code = P.code := rfl

private theorem placedLib_program_base (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (ext : String → Option (State → State)) :
    (lib.program pl ext).base = pl.base := rfl

private theorem placedLib_program_code (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (ext : String → Option (State → State)) :
    (lib.program pl ext).code = lib.text.patched pl := rfl

set_option maxRecDepth 2000000 in
private theorem c2Compress512SubProg_base :
    c2Compress512SubProg.base = c2Compress512Pl.base :=
  (with_svc_base (compress512Lib.program c2Compress512Pl (fun _ => none)) Syscall.standard).trans
    (placedLib_program_base compress512Lib c2Compress512Pl (fun _ => none))

set_option maxRecDepth 2000000 in
private theorem c2Compress512SubProg_code :
    c2Compress512SubProg.code = compress512Lib.text.patched c2Compress512Pl :=
  (with_svc_code (compress512Lib.program c2Compress512Pl (fun _ => none)) Syscall.standard).trans
    (placedLib_program_code compress512Lib c2Compress512Pl (fun _ => none))

set_option maxRecDepth 2000000 in
theorem c2_compress512_rx_subslice :
    checkProgCodeSubslice f3TrialRxProg c2Compress512SubProg = true :=
  checkProgCodeSubslice_of_codeBlockWalk
    c2Compress512SubProg_base c2Compress512SubProg_code rfl rfl rfl c2_compress512_walk_ok

theorem c2_compress512_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    c2Compress512SubProg.CodeLoaded m :=
  codeLoaded_of_checkProgCodeSubslice hInv.rxCode c2_compress512_rx_subslice

set_option maxRecDepth 2000000 in
private theorem c2_compress512_roSegSlice_ok :
    checkRoSegSlice f3PatchedElf c2Compress512K64Addr sha512KBytes = true := by
  rfl_kernel

theorem c2_compress512_ro_slice :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2Compress512K64Addr sha512KBytes = true :=
  roSlice_of_checkRoSegSlice c2_compress512_roSegSlice_ok

theorem c2_compress512_roDataAt_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m c2Compress512K64Addr sha512KBytes :=
  f3CodeInv_roDataAt_of_roSegSlice hLs hInv c2_compress512_roSegSlice_ok

theorem c2_compress512_in_lib2_lo :
    c2Lib2TextLo.toNat ≤ c2Compress512Addr.toNat := by
  decide

theorem c2_compress512_in_lib2_hi :
    c2Compress512Addr.toNat + c2Compress512ByteLen ≤ c2Lib2TextHi.toNat := by
  decide

theorem keepR_c2Compress512_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepR_c2Compress512 pc = true) :
    keepLib2Text pc = true :=
  c2_keepLib2Text_of_sub_lt (of_decide_eq_true hk)
    c2_compress512_in_lib2_lo c2_compress512_in_lib2_hi

theorem keepR_c2Compress512_sub_rxProg {pc : BitVec 64}
    (hk : keepR_c2Compress512 pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_c2Compress512_sub_keepLib2Text hk)

theorem c2_compress512_hKeep [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    keepR_c2Compress512 lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
  cases hk : keepR_c2Compress512 lr
  · rfl
  · have hlib2 := keepR_c2Compress512_sub_keepLib2Text hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512
