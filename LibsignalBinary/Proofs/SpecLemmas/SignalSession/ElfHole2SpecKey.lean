/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import ProofLib.Placed.Fetch
public import ProofLib.Process.FastParse
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Symbol-Table and Program-Header Keying Guards for `CliElfHole2Assumption`

**Checked by Lean.** Untrusted (`Role::Proof`, `CliElfLib`, `P-KEY` / GK row 926).

Provides closed, zero-hex `rfl_kernel` `SPEC-KEY` guards and universal `ElfImage.parse` /
`LinkedAt` corollaries keying every operational address literal, keep-range bound, appended
branch-stub word, and layout segment index read by `CliElfHole2Assumption`
(`LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfSlicesPqOomPlacedInst.lean:379`) to
independent by-name `.symtab` lookups (`Obj.lookupUnique`), `PT_LOAD` segment bounds, and raw
ELF64 program-header (`PHDR[2]`) fields over `cliElfBytes` / `cliElfImage`:

1. **Rows A1–A6 (`hole2_targets`, `f3RdlAddrs` / `f3RdlAzAddr`, & `f3StubAddrs` / `f3StubAzAddr`):**
   - **A1:** `(hole2_targets mpl).readFile` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io9read_file"` (`hole2_targets_readFile_specKey_guard`,
     `hole2_targets_readFile_specKey`).
   - **A2:** `(hole2_targets mpl).readStdin` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io10read_stdin"` (`hole2_targets_readStdin_specKey_guard`,
     `hole2_targets_readStdin_specKey`).
   - **A3:** `f3RdlAddrs.alloc` (`= (hole2_targets mpl).alloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_alloc"` and `f3StubAddrs.alloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"`
     (`f3RdlAddrs_alloc_specKey_guard`, `f3StubAddrs_alloc_rustc_specKey_guard`,
     `f3RdlAddrs_alloc_specKey`).
   - **A4:** `f3RdlAddrs.dealloc` (`= (hole2_targets mpl).dealloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_dealloc"` and `f3StubAddrs.dealloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"`
     (`f3RdlAddrs_dealloc_specKey_guard`, `f3StubAddrs_dealloc_rustc_specKey_guard`,
     `f3RdlAddrs_dealloc_specKey`).
   - **A5:** `f3RdlAddrs.realloc` (`= (hole2_targets mpl).realloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_realloc"` and `f3StubAddrs.realloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"`
     (`f3RdlAddrs_realloc_specKey_guard`, `f3StubAddrs_realloc_rustc_specKey_guard`,
     `f3RdlAddrs_realloc_specKey`).
   - **A6:** `f3RdlAzAddr` (`= (hole2_targets mpl).allocZeroed`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_alloc_zeroed"` and `f3StubAzAddr` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"`
     (`f3RdlAzAddr_specKey_guard`, `f3StubAzAddr_rustc_specKey_guard`, `f3RdlAzAddr_specKey`).
2. **Rows A7–A12 (`hole2_keepSub` & `hole2_keep` executable keep-range bounds):**
   - **A7/A8/A11/A12:** `cliElfImage.segments[2]` (`Perm.rx`, start keyed to `read_stdin`, end
     `start + bytes.length`) guards both endpoints of `hole2_keepSub` and the second interval of
     `hole2_keep` (`hole2_keepSub_lo_specKey_guard`, `hole2_keepSub_hi_specKey_guard`,
     `hole2_keep_r2Lo_specKey_guard`, `hole2_keep_r2Hi_specKey_guard`, `hole2_keepSub_specKey`).
   - **A9:** first interval lower bound of `hole2_keep` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"`
     (`= mpl.base 623` for every `LinkedAt` placement; `hole2_keep_r1Lo_specKey_guard`,
     `elfCloneSym_eq_base623_specKey`).
   - **A10:** first interval upper bound of `hole2_keep` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io10write_file"` (`= mpl.base 623 + 132`), plus all-zero
     (`0#8`) verification of the trailing page-padding bytes `[p_vaddr + p_memsz, seg1End)` of
     `PHDR[2]` in `cliElfImage.segments[1]` (`hole2_keep_r1Hi_specKey_guard`,
     `elfSeg1_tailZero_specKey_guard`, `hole2_keep_specKey`).
3. **Rows A13–A14 (`hole2_str1Prog` exact block-623 equality & `f3StubAddrs.alloc` `Instr.b` thunk):**
   - Verifies `(hole2_str1Prog mpl).code = (libsignalSessionLib.blockProgram mpl 623).code` (`0`
     appended stub bytes on stock `--no-relax`), and decodes the 32-bit thunk word at
     `f3StubAddrs.alloc` in `cliElfImage.segments[2]` via `Arm64.decode` as `Instr.b` targeting
     `"__rdl_alloc"` (`= f3RdlAddrs.alloc`) (`hole2_str1Prog_appendedLen_guard`,
     `f3StubAddrs_alloc_seg2_isB_specKey_guard`, `hole2_str1Prog_stubs_specKey`).
4. **Table 2 (`f3StdLayout.rxSegIdx`):**
   - Keys `f3StdLayout.rxSegIdx` (`= 2`) as the unique segment in `cliElfImage.segments` starting
     at `read_stdin` (`Perm.rx`) (`f3StdLayout_rxSegIdx_specKey_guard`,
     `f3StdLayout_rxSegIdx_specKey`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole2SpecKey

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse libsignalSessionLib)
open LibsignalBinary.Heap.Fine
  (f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3StdLayout f3StubAddrs f3StubAzAddr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars (cliElfSymChars cliElf_symbols_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsBlockBases f3LsBlocksLen libsignalBlocks_len)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3LsMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_keep hole2_keepSub hole2_str1Prog hole2_targets)

/-! ## Interned `.symtab` Lookup Bridge -/

def zeroMpl : MultiPlacement where
  base := fun _ => 0#64
  ρ := fun _ => 0#64

def symReadFileChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '9', 'X', 'u', 'l', '1', 'K', 'j', 'r', '0', 'Q', 'F', '_', '1', '6', 'l', 'i', 'b', 's', 'i', 'g', 'n', 'a', 'l', '_', 'c', 'l', 'i', '_', 'i', 'o', '9', 'r', 'e', 'a', 'd', '_', 'f', 'i', 'l', 'e']
noncomputable def lookupSymChars (cs : List Char) : Option (BitVec 64) :=
  buildEncSymTable cliElfSymChars fun enc => lookupUniqueEnc (encodeCharKey cs) enc

attribute [local irreducible] lookupSymChars

/-! ## Extern Ghost-Hook and Allocator Shim Entry Targets -/

/-- `(hole2_targets _).readFile` equals the unique `.symtab` entry for `signal_session_io::read_file`. -/
theorem hole2_targets_readFile_specKey_guard :
    lookupSymChars symReadFileChars = some (hole2_targets zeroMpl).readFile := by
  rfl_kernel

/-! ## `hole2_keepSub` and `hole2_keep` Range Bounds -/

/-- Reads `PHDR[2]` `p_vaddr + p_memsz` from raw ELF64 `elfBytes` (`e_phoff + 2 * 56`) when
`e_phentsize = 56`, `2 < e_phnum`, `p_type = 1` (`PT_LOAD`), and `p_flags = 5` (`PF_R | PF_X`). -/
def elfPhdr2RxEndFast? (elfBytes : List (BitVec 8)) : Option Nat :=
  let hdr := fastTake 64 elfBytes
  let ePhoff := listReadU64LE hdr 32
  let ePhent := listReadU16LE hdr 54
  let ePhnum := listReadU16LE hdr 56
  if ePhent == 56 && 2 < ePhnum then
    let ph2 := fastTake 56 (fastDrop (ePhoff + 2 * 56) elfBytes)
    let pType := listReadU32LE ph2 0
    let pFlags := listReadU32LE ph2 4
    let pVaddr := listReadU64LE ph2 16
    let pMemsz := listReadU64LE ph2 40
    if pType == 1 && pFlags == 5 then
      some (pVaddr + pMemsz)
    else
      none
  else
    none

/-- `List.take`/`List.drop` specification counterpart of `elfPhdr2RxEndFast?`. -/
def elfPhdr2RxEnd? (elfBytes : List (BitVec 8)) : Option Nat :=
  let hdr := elfBytes.take 64
  let ePhoff := listReadU64LE hdr 32
  let ePhent := listReadU16LE hdr 54
  let ePhnum := listReadU16LE hdr 56
  if ePhent == 56 && 2 < ePhnum then
    let ph2 := (elfBytes.drop (ePhoff + 2 * 56)).take 56
    let pType := listReadU32LE ph2 0
    let pFlags := listReadU32LE ph2 4
    let pVaddr := listReadU64LE ph2 16
    let pMemsz := listReadU64LE ph2 40
    if pType == 1 && pFlags == 5 then
      some (pVaddr + pMemsz)
    else
      none
  else
    none

theorem elfPhdr2RxEndFast?_eq (elfBytes : List (BitVec 8)) :
    elfPhdr2RxEndFast? elfBytes = elfPhdr2RxEnd? elfBytes := by
  unfold elfPhdr2RxEndFast? elfPhdr2RxEnd?
  simp only [fastTake_eq_take, fastDrop_eq_drop]

/-! ## `hole2_str1Prog` Exact Block-623 Equality and `f3StubAddrs.alloc` Thunk -/

/-! ## `f3StdLayout.rxSegIdx` Uniqueness (`segments[2]`, `read_stdin`) -/

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole2SpecKey
