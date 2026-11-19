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
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Bytes -- proof-setup: allow-public-import

/-!
# Relocatable `Obj.PlacedLib` Model of `sha2::sha256::compress256`

Packages `_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256` (`7,636` bytes = `1,909` instructions,
alignment `4`, single relaxable `ADRP`+`ADD` relocation pair at `+0xd0`/`+0xd4` targeting the
`256`-byte read-only round-constant table `sha256KBytes` at `pl.ρ sha2K32Sym`), together with its
`WordTree` representation (`compress256Tree`), placement offsets (`gen_placed_fnOffs`), and
placement-generic `SVC` and `MSR TPIDR_EL0` exclusion theorems (`compress256_program_noSvc`,
`compress256_program_noMsrTpidrEl0`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Bytes (compress256CodeBytes)

/-- Raw `.symtab` symbol name of `sha2::sha256::compress256` in `libsha2` / `libsignal-cli`. -/
@[expose] def compress256Sym : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"

/-- Data-object symbol key for `sha2::consts::K32` (`256` bytes in `.rodata`). -/
@[expose] def sha2K32Sym : String :=
  "sha2:.rodata.sha2::consts::K32"

/-- Relocatable `.text` block of `sha2::sha256::compress256` (`7,636` B, `ADRP`+`ADD` at `0xd0`). -/
@[expose] def compress256Block : Obj.CodeBlock where
  code := compress256CodeBytes
  align := 4
  symbols := [(compress256Sym, 0)]
  relocs := [
    { off := 0xd0, kind := .adrpHi21, sym := sha2K32Sym, addend := 0 },
    { off := 0xd4, kind := .addLo12, sym := sha2K32Sym, addend := 0 }]
  externs := []
  weakRefs := []

/-- Read-only `.rodata` object for `sha2::consts::K32` (`256` bytes = `sha256KBytes`). -/
@[expose] def compress256K32Data : Obj.SymDataInfo where
  sym := sha2K32Sym
  align := 4
  readOnly := true
  bytes := sha256KBytes
  zeroTail := 0
  relocs := []

/-- Relocatable `Obj.PlacedLib` packaging `compress256Block` and `compress256K32Data`. -/
@[expose] def compress256Lib : Obj.PlacedLib where
  name := "sha2_compress256"
  text := compress256Block
  data := [compress256K32Data]
  exports := [compress256Sym]

/-- Ambient `Placeable` placement of `compress256Lib` (covers both `--no-relax` `ADRP`+`ADD` and
    `stock-lld` `NOP`+`ADR` relaxation at `+0xd0`/`+0xd4`). -/
class Compress256Placement where
  pl : Obj.Placement
  placeable : compress256Lib.Placeable pl

/-- `compress256Lib` placed under `Compress256Placement.pl`. -/
@[expose] def compress256PC [Compress256Placement] : Program :=
  compress256Lib.program Compress256Placement.pl

/-- Unrelocated text block at base `0` for `word_tree_of%` / `sym_chars_of%`. -/
@[expose] def compress256TextProg : Program :=
  { code := compress256Block.code, symbols := compress256Block.symbols }

set_option maxRecDepth 400000 in
@[expose] def compress256Tree : WordTree := word_tree_of% compress256TextProg

set_option maxRecDepth 400000 in
theorem compress256_code_eq : compress256Lib.text.code = compress256Tree.toBytes := by
  rfl_kernel

set_option maxRecDepth 400000 in
theorem compress256_tree_size : compress256Tree.checkSize? = some 1909 := by
  rfl_kernel

@[expose] def compress256SymChars : List (List Char × Nat) :=
  sym_chars_of% compress256TextProg

theorem compress256_symbols_eq :
    compress256Lib.text.symbols = toStringSymbols compress256SymChars := by
  rfl_kernel

theorem compress256_symbols_fresh : allFreshCharSymbols compress256SymChars = true := by
  rfl_kernel

gen_placed_fnOffs compress256PC compress256Lib compress256SymChars
  compress256_symbols_eq compress256_symbols_fresh

/-! ## Placement-Generic `SVC` and `MSR TPIDR_EL0` Exclusion -/

/-- Word pattern for all `SVC #imm16` encodings (`11010100_000_imm16_00001`). -/
@[expose] def svcAnyPat : Obj.WordPat := ⟨0xffe0001f#32, 0xd4000001#32⟩

theorem svcAnyPat_matches (w : BitVec 32) : svcAnyPat.matches w = isSvcWord w := by
  rfl

set_option maxRecDepth 400000 in
theorem compress256_patchSafe_noSvc :
    Obj.CodeBlock.patchSafe svcAnyPat compress256Block = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
theorem compress256_patchSafe_noMsrTpidrEl0 :
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat compress256Block = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
/-- Every placement of `compress256Lib` is free of `SVC #imm16` instructions. -/
theorem compress256_program_noSvc (pl : Obj.Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (compress256Lib.program pl externs overrides svc).allInstrs (fun i => !i.isSvc) = true :=
  Obj.PlacedLib.program_allInstrs_of_patchSafe (lib := compress256Lib)
    (fun w _ hd hw => decode_not_isSvc hd (by rw [← svcAnyPat_matches]; exact hw))
    compress256_patchSafe_noSvc pl externs overrides svc

set_option maxRecDepth 400000 in
/-- Every placement of `compress256Lib` is free of `MSR TPIDR_EL0, Xt` instructions. -/
theorem compress256_program_noMsrTpidrEl0 (pl : Obj.Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (compress256Lib.program pl externs overrides svc).allInstrs
      (fun i => !i.isMsrTpidrEl0) = true :=
  Obj.PlacedLib.program_noMsrTpidrEl0_of_patchSafe (lib := compress256Lib)
    compress256_patchSafe_noMsrTpidrEl0 pl externs overrides svc

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
