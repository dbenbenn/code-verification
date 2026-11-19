/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Bytes
public import VerifiedLibraries.Mallocng.Proofs.Common
import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

/-!
# Concrete Startup, Initial-Pool, and Branch-Stub Witnesses on `f3TrialElf`

**Checked by Lean.** Instantiates on `f3TrialElf` (via `F3LayoutData`):
- `F3StartupCode` and whole-process `musl` startup/exit harnesses (`MuslHarnessNeedLocksN 80`,
  `MuslHarnessN 80`);
- separation-logic entailments from `StdExtraRo ∗ StdExtraRw` to `mallocngLib.dataInit f3MallocngMpl`;
- fine-budget and no-OOM Rust global allocator contracts (`__rdl_{alloc,dealloc,realloc,alloc_zeroed}`)
  on `f3TrialRxProg` (`seg[5]`);
- `ElfInitFine` pool and `cMainAddr` entry witnesses; and
- 1-hop `.img.text` (`seg[1]`) `--branch-stubs` `Instr.b` execution lifts into `seg[5]`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Mallocng (
  MallocngAuxvAt MallocngBrkStartWf MallocngRoTablesAt MallocngRuntime
  mallocngAddrsOfPlacement mallocngSizeClassBytes mallocngDebruijn32Table
  mallocngMedCntTabBytes mallocngSmallCntTabBytes
)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng mallocngLib_dataInit_eq)
open VerifiedLibraries.RustStd (StdErrnoCell mallocngPlacedCAddrs mallocngRustCliAlloc)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  Inputs cliProcessInputs patchElfTokensPlaced
)
open CryptoVerification.SignalSession.Cli (
  cliInputs CliInputsOk InputsLoadable
)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.InitStack (cliStackSize)
open LibsignalBinary.Heap (
  BudgetLimits RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntriesBase RustCliAllocNoOomEntriesBase
  allocMemcpyVmSpec rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  rustCliAllocNoOomSpecBase
)
open LibsignalBinary.Heap.IfaceSimp (
  allocCallPreserved_setPC_left oomPreserved_setPC_left
)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Heap.Fine (
  CliElfMallocngLayout StartupVmPreserved allocMemsetVmSpec
  cliElf_fineBudgetPool_of_init cliElf_fineBudgetPool_and_entries_of_init
  f3SegCount f3SegByteSum f3RxWordCount f3StdLayout f3MallocngMpl
  f3StubAddrs f3RdlAddrs f3StubAzAddr f3RdlAzAddr
  fineCostModel fineRustCliAllocBudget
  fineRustCliAllocBudgetEntries fineRustCliAllocNoOomEntries
  fineRdlAllocZeroed_budget_placed_ok fineRdlAllocZeroed_noOom_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec (
  MuslHarnessNeedLocksN
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (
  steps_of_loaded_b_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup (
  F3StartupCode checkF3StartupCode f3StartupCode_of_wordTree
  cStrAtRO argvAtRO MuslHarnessN
  f3StartupResidual f3StartupMainPre f3StartupMainPreNeedLocks
  f3InitFineBudgetPool f3InitMallocngHeap
  f3MuslHarnessNeedLocks80_of_layout f3MuslHarness80_of_layout
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (
  f3TrialElf f3TrialElf_cliElfMallocngLayout f3TrialElf_patched_cliElfMallocngLayout
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3RxSegBase f3ImgTextBase f3TrialRxProg f3TrialRxWordTree
  f3TrialRxWordTree_eq f3TrialRxWordTree_size f3TrialRxProg_base
  f3TrialRxProg_svc f3TrialRxProg_no_ext f3TrialRxProg_externs_none
  f3TrialRxProg_overrides_none f3TrialRxProg_stubs f3TrialRxProg_symbols
  f3Trial_matchesImage f3Trial_progContainsMallocng f3Trial_seg5ShimBundle
  f3Trial_allocMemcpyVm_ok f3Trial_allocMemsetVm_ok
  f3StubAlloc_mem_targets f3StubDealloc_mem_targets f3StubRealloc_mem_targets
  f3StubAz_mem_targets f3StubAlloc_addr_eq f3StubDealloc_addr_eq
  f3StubRealloc_addr_eq f3StubAz_addr_eq f3Trial_keepsFrozen_stub_at
)

set_option maxRecDepth 400000

/-! ## Startup Code and `musl` Startup/Exit Harnesses -/

private theorem f3Trial_startupCode_chk :
    checkF3StartupCode f3StdLayout f3RxSegBase f3TrialRxWordTree = true := by
  rfl_kernel

/-- `F3StartupCode` witness for `f3TrialRxProg` (`seg[5]`). -/
theorem f3Trial_startupCode : F3StartupCode f3TrialRxProg f3StdLayout :=
  f3StartupCode_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    f3TrialRxProg_svc f3TrialRxProg_stubs f3TrialRxProg_symbols
    f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
    (by rw [f3TrialRxProg_base]; exact f3Trial_startupCode_chk)

/-! ## `StdExtraRo ∗ StdExtraRw` to `mallocngLib.dataInit` Bridge -/

/-- `MallocngAddrs` resolved from `f3MallocngMpl`. -/
noncomputable abbrev f3MAddrs : VerifiedLibraries.Mallocng.MallocngAddrs :=
  mallocngAddrsOfPlacement f3MallocngMpl

/-- Zero-initialized alignment padding (`4` + `5` bytes) inside the 200-byte `mallocng` `.rodata`
block. -/
@[expose] noncomputable def f3MallocngRoPad : SepProp :=
  ((f3MAddrs.sizeClasses + 132#64) ↦ᵣ List.replicate 4 0#8) ∗
  ((f3MAddrs.sizeClasses + 163#64) ↦ᵣ List.replicate 5 0#8)

theorem f3MAddrs_libc : f3MAddrs.libc = f3StdLayout.libcAddr := by
  rfl_kernel

private theorem f3MAddrs_debruijnFree :
    f3MAddrs.debruijnFree = f3MAddrs.sizeClasses + 96#64 := by
  rfl_kernel

private theorem f3MAddrs_medCntTab :
    f3MAddrs.medCntTab = f3MAddrs.sizeClasses + 128#64 := by
  rfl_kernel

private theorem f3MAddrs_smallCntTab :
    f3MAddrs.smallCntTab = f3MAddrs.sizeClasses + 136#64 := by
  rfl_kernel

private theorem f3MAddrs_debruijnAlloc :
    f3MAddrs.debruijnAlloc = f3MAddrs.sizeClasses + 168#64 := by
  rfl_kernel

private theorem f3ExtraRo_eq :
    f3StdLayout.extraRoSlices = [(f3MAddrs.sizeClasses, ProofLib.mallocngRoTablesBytes)] := by
  rfl_kernel

private theorem f3ExtraRw_eq :
    f3StdLayout.extraRwAtoms =
      [ .u32 f3MAddrs.lock 0#32,
        .u32 f3MAddrs.aaReplaced 0#32,
        .u32 f3MAddrs.replaced 0#32,
        .bytes f3MAddrs.ctx (List.replicate 928 0#8) ] := by
  rfl_kernel

private theorem roTablesBytes_eq :
    ProofLib.mallocngRoTablesBytes = VerifiedLibraries.Mallocng.mallocngRoTablesBytes := by
  rfl_kernel

private theorem len_sizeClassBytes : mallocngSizeClassBytes.length = 96 := by rfl_kernel
private theorem len_debruijn32Table : mallocngDebruijn32Table.length = 32 := by rfl_kernel
private theorem len_medCntTabBytes : mallocngMedCntTabBytes.length = 4 := by rfl_kernel
private theorem len_smallCntTabBytes : mallocngSmallCntTabBytes.length = 27 := by rfl_kernel

private theorem roTablesBytes_pointsToRO_split (sc : BitVec 64) :
    (sc ↦ᵣ VerifiedLibraries.Mallocng.mallocngRoTablesBytes) =
      (sc ↦ᵣ mallocngSizeClassBytes) ∗
      ((sc + 96#64) ↦ᵣ mallocngDebruijn32Table) ∗
      ((sc + 128#64) ↦ᵣ mallocngMedCntTabBytes) ∗
      ((sc + 132#64) ↦ᵣ List.replicate 4 0#8) ∗
      ((sc + 136#64) ↦ᵣ mallocngSmallCntTabBytes) ∗
      ((sc + 163#64) ↦ᵣ List.replicate 5 0#8) ∗
      ((sc + 168#64) ↦ᵣ mallocngDebruijn32Table) := by
  unfold VerifiedLibraries.Mallocng.mallocngRoTablesBytes
  simp only [List.append_assoc]
  rw [pointsToBytesRO_append, len_sizeClassBytes]
  rw [show sc + BitVec.ofNat 64 96 = sc + 96#64 from rfl]
  rw [pointsToBytesRO_append, len_debruijn32Table]
  rw [show sc + 96#64 + BitVec.ofNat 64 32 = sc + 128#64 by bv_omega]
  rw [pointsToBytesRO_append, len_medCntTabBytes]
  rw [show sc + 128#64 + BitVec.ofNat 64 4 = sc + 132#64 by bv_omega]
  rw [pointsToBytesRO_append, List.length_replicate]
  rw [show sc + 132#64 + BitVec.ofNat 64 4 = sc + 136#64 by bv_omega]
  rw [pointsToBytesRO_append, len_smallCntTabBytes]
  rw [show sc + 136#64 + BitVec.ofNat 64 27 = sc + 163#64 by bv_omega]
  rw [pointsToBytesRO_append, List.length_replicate]
  rw [show sc + 163#64 + BitVec.ofNat 64 5 = sc + 168#64 by bv_omega]

/-- Unpacks `StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout` into `MallocngRoTablesAt f3MAddrs`,
the four `mallocng` `.bss` globals, and `f3MallocngRoPad`. -/
theorem f3StdExtra_entails_mallocngStartupData :
    StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout ⊢
      MallocngRoTablesAt f3MAddrs ∗
      (f3MAddrs.ctx ↦ₛ List.replicate 928 0#8) ∗
      (f3MAddrs.lock ↦₃₂ 0#32) ∗
      (f3MAddrs.replaced ↦₃₂ 0#32) ∗
      (f3MAddrs.aaReplaced ↦₃₂ 0#32) ∗
      f3MallocngRoPad := by
  unfold StdExtraRo StdExtraRw
  rw [f3ExtraRo_eq, f3ExtraRw_eq]
  dsimp only [roSliceListSep, rwAtomListSep, RwAtom.toSepProp]
  rw [roTablesBytes_eq, roTablesBytes_pointsToRO_split f3MAddrs.sizeClasses]
  unfold MallocngRoTablesAt f3MallocngRoPad
  rw [f3MAddrs_debruijnFree, f3MAddrs_medCntTab, f3MAddrs_smallCntTab, f3MAddrs_debruijnAlloc]
  sep_entail

/-- Entails `VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗ f3MallocngRoPad` from
`StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout`. -/
theorem f3StdExtra_entails_mallocngDataInit :
    StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout ⊢
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗ f3MallocngRoPad := by
  refine Entails.trans f3StdExtra_entails_mallocngStartupData ?_
  have hEq : VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl =
      (MallocngRoTablesAt f3MAddrs ∗
        (f3MAddrs.ctx ↦ₛ List.replicate 928 0#8) ∗
        (f3MAddrs.lock ↦₃₂ 0#32) ∗
        (f3MAddrs.replaced ↦₃₂ 0#32) ∗
        (f3MAddrs.aaReplaced ↦₃₂ 0#32)) :=
    mallocngLib_dataInit_eq f3MallocngMpl
  rw [hEq]
  sep_entail

/-! ## Rust Global Allocator Contracts on `f3TrialRxProg` -/

/-! ## `ElfInitFine` Pool and `cMainAddr` Entry Witnesses -/

/-- Produces `A.pool lim fineCostModel.init sm` and `cliMainStk` stack ownership at `cMainAddr`
entry from `f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R`. -/
theorem f3TrialElf_main_fineBudgetPool {lim : BudgetLimits} {i : Inputs} {sm : State} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart
      sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜f3TrialRxProg.CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of f3TrialElf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = f3StdLayout.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = f3StdLayout.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          f3MallocngRoPad ∗
          f3StartupResidual f3StdLayout f3TrialElf i) ∗ R := by
  have hrx : f3StdLayout.rxProgram f3TrialElf = f3TrialRxProg := rfl
  simpa only [hrx] using
    f3InitFineBudgetPool
      (f3TrialElf_cliElfMallocngLayout hcnt hbytes hphys)
      f3MAddrs_libc f3StdExtra_entails_mallocngDataInit hm

/-! ## `.img.text` 1-Hop `--branch-stubs` Execution Lifts -/

example {lim : BudgetLimits} {i : Inputs} {sm : State} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart
      sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜8371776 ≤ sm.sp.toNat⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp 8371776 ∗
          anyHeap) ∗ R := by
  obtain ⟨γ, hPool⟩ := f3TrialElf_main_fineBudgetPool hcnt hbytes hphys hm
  dsimp only [cliMainStk] at hPool ⊢
  simp only [sepConj_assoc,
    sepConj_left_comm ((fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart).pool
      lim fineCostModel.init sm),
    satisfies_pure_sepConj] at hPool
  obtain ⟨⟨_, hsp_ge, _⟩, hPool⟩ := hPool
  refine ⟨γ, Satisfies.mono ?_ hPool⟩
  rw [pure_sepConj_of_true hsp_ge]
  refine Entails.trans
    (Q := ((fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart).pool
        lim fineCostModel.init sm ∗
      argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
      stackAt sm.sp 8371776 ∗
      (f3MallocngRoPad ∗ f3StartupResidual f3StdLayout f3TrialElf i)) ∗ R)
    (by sep_entail)
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_anyHeap _)))))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
