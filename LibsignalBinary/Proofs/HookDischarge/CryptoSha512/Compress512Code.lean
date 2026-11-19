/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.OpcodeExclusion
public meta import ProofLib.ProgramReflection
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Bytes

/-!
# Relocatable `Obj.PlacedLib` model of `sha2::sha512::compress512`

Relocatable object model for `_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512` (`9,652` bytes =
`2,413` instructions, alignment `4`, single relaxable `ADRP`+`ADD` relocation pair at
`+0x48`/`+0x4c` targeting the `640`-byte read-only round-constant table `sha512KBytes` at
`pl.ρ sha2K64Sym`).

Defines:
- `compress512Sym`, `sha2K64Sym`, `compress512Block`, `compress512K64Data`, `compress512Lib`.
- `Compress512Placement`, `compress512PC`, `compress512Tree`, `compress512_code_eq`,
  `compress512_tree_size`, `gen_placed_fnOffs`.
- Placement-generic `SVC` and `MSR TPIDR_EL0` exclusion (`compress512_program_noSvc`,
  `compress512_program_noMsrTpidrEl0`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Bytes (compress512CodeBytes)

/-- Raw `.symtab` symbol name of `sha2::sha512::compress512` in `libsha2` / `libsignal-cli`. -/
@[expose] def compress512Sym : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512"

/-- Data-object symbol key for `sha2`'s 640-byte SHA-512 round-constant table `K64` in `.rodata`. -/
@[expose] def sha2K64Sym : String :=
  "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0"

/-- Relocatable `.text` block of `sha2::sha512::compress512` (`9,652` B, `ADRP`+`ADD` at `0x48`). -/
@[expose] def compress512Block : Obj.CodeBlock where
  code := compress512CodeBytes
  align := 4
  symbols := [(compress512Sym, 0)]
  relocs := [
    { off := 0x48, kind := .adrpHi21, sym := sha2K64Sym, addend := 0 },
    { off := 0x4c, kind := .addLo12, sym := sha2K64Sym, addend := 0 }]
  externs := []
  weakRefs := []

/-- Read-only `.rodata` object for `K64` (`640` bytes = `sha512KBytes`, 8-byte aligned). -/
@[expose] def compress512K64Data : Obj.SymDataInfo where
  sym := sha2K64Sym
  align := 8
  readOnly := true
  bytes := sha512KBytes
  zeroTail := 0
  relocs := []

/-- Relocatable `Obj.PlacedLib` packaging `compress512Block` and `compress512K64Data`. -/
@[expose] def compress512Lib : Obj.PlacedLib where
  name := "sha2_compress512"
  text := compress512Block
  data := [compress512K64Data]
  exports := [compress512Sym]

/-- Ambient `Placeable` placement of `compress512Lib` (covers both `--no-relax` `ADRP`+`ADD` and
    `stock-lld` `NOP`+`ADR` relaxation at `+0x48`/`+0x4c`). -/
class Compress512Placement where
  pl : Obj.Placement
  placeable : compress512Lib.Placeable pl

/-- `compress512Lib` placed under `Compress512Placement.pl`. -/
@[expose] def compress512PC [Compress512Placement] : Program :=
  compress512Lib.program Compress512Placement.pl

/-- Unrelocated text block at base `0` for `word_tree_of%` / `sym_chars_of%`. -/
@[expose] def compress512TextProg : Program :=
  { code := compress512Block.code, symbols := compress512Block.symbols }

set_option maxRecDepth 600000 in
@[expose] def compress512Tree : WordTree := word_tree_of% compress512TextProg

set_option maxRecDepth 600000 in
theorem compress512_code_eq : compress512Lib.text.code = compress512Tree.toBytes := by
  rfl_kernel

set_option maxRecDepth 600000 in
theorem compress512_tree_size : compress512Tree.checkSize? = some 2413 := by
  rfl_kernel

@[expose] def compress512SymChars : List (List Char × Nat) :=
  sym_chars_of% compress512TextProg

theorem compress512_symbols_eq :
    compress512Lib.text.symbols = toStringSymbols compress512SymChars := by
  rfl_kernel

theorem compress512_symbols_fresh : allFreshCharSymbols compress512SymChars = true := by
  rfl_kernel

gen_placed_fnOffs compress512PC compress512Lib compress512SymChars
  compress512_symbols_eq compress512_symbols_fresh

/-! ## Placement-Generic `SVC` and `MSR TPIDR_EL0` Exclusion -/

/-- Word pattern for all `SVC #imm16` encodings (`11010100_000_imm16_00001`). -/
@[expose] def svcAnyPat : Obj.WordPat := ⟨0xffe0001f#32, 0xd4000001#32⟩

theorem svcAnyPat_matches (w : BitVec 32) : svcAnyPat.matches w = isSvcWord w := by
  rfl

set_option maxRecDepth 600000 in
theorem compress512_patchSafe_noSvc :
    Obj.CodeBlock.patchSafe svcAnyPat compress512Block = true := by
  rfl_kernel

set_option maxRecDepth 600000 in
theorem compress512_patchSafe_noMsrTpidrEl0 :
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat compress512Block = true := by
  rfl_kernel

set_option maxRecDepth 600000 in
/-- Every placement of `compress512Lib` is free of `SVC #imm16` instructions. -/
theorem compress512_program_noSvc (pl : Obj.Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (compress512Lib.program pl externs overrides svc).allInstrs (fun i => !i.isSvc) = true :=
  Obj.PlacedLib.program_allInstrs_of_patchSafe (lib := compress512Lib)
    (fun w _ hd hw => decode_not_isSvc hd (by rw [← svcAnyPat_matches]; exact hw))
    compress512_patchSafe_noSvc pl externs overrides svc

set_option maxRecDepth 600000 in
/-- Every placement of `compress512Lib` is free of `MSR TPIDR_EL0, Xt` instructions. -/
theorem compress512_program_noMsrTpidrEl0 (pl : Obj.Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (compress512Lib.program pl externs overrides svc).allInstrs
      (fun i => !i.isMsrTpidrEl0) = true :=
  Obj.PlacedLib.program_noMsrTpidrEl0_of_patchSafe (lib := compress512Lib)
    compress512_patchSafe_noMsrTpidrEl0 pl externs overrides svc

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
