/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.CpuProbe -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import
import ProofLib.Placed.Check
import ProofLib.Process.OracleEq
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Linked CPU-Probe Ghost Hook and `GhostRowOk` for `lsSpqrOnceCallSym`

`CliGhostHooks.extra` ghost-hook and block-617 replay proofs for
`<std::sys::sync::once::futex::Once>::call` (`lsSpqrOnceCallSym` / `spqrOnceCallSym`) on the
unprobed SPQR GF(2¹⁶) CPU-feature probe slow path (`STORAGE.0 : 0xff → 1`, `TOKEN + 8 : 3 → 0`):

- Kept region (`keepSpqrOnceCall`): covers the 5 `rxSeg` (`seg[2]`) slices (`Once::call`,
  `__aarch64_cas4_acq`, `__aarch64_swp4_rel`, `cpufeatures::aarch64::getauxval_hwcap`, musl
  `getauxval`) and 2 `libsignalSessionLib` `seg[1]` blocks (`321` `LazyLock` closure and `385`
  `use_accelerated::init`).
- Unconditional `HookOk` and `GhostRowSpecOk`: `spqrOnceCallGhost` wraps `linkedCallHookG` on
  `emptyStdProg` with fallback `spqrOnceCallFallback`, yielding `spqrOnceCallGhost_ok` and
  `spqrOnceCallGhost_rowSpecOk` without caller hypotheses.
- Generic-`InvS` `GhostRowReplayOn` and `GhostRowOk` (`entryGuard := True`): uses
  `LsRetAddrNoProbe (u.readReg64 .lr)` in `spqrOnceCallGhostSpec.pre` to discharge
  `keepSpqrOnceCall lsmpl (u.readReg64 .lr) = false` at every non-faulting call step.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliElf_parse cliExternsPlaced libsignalSessionLib
   lsSpqrOnceCallSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (LsRetAddrNoProbe spqrLazyLockVtableSym spqrOnceCallGhostSpec spqrProbeEnvAt
   spqrProbeEnvAtMpl_eq)
open LibsignalBinary.Heap (AllocCallPreserved FdsHiFrame VmPreserved)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (codeLoaded_pureWordsProg_of_hasWords)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealPre ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed hookNoAllocFailed_of_trace_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.CpuProbe
  (OnceCall198Code getauxvalHwcapInstrs getauxvalHwcapSpec getauxval_found_ro_ok onceCall198Chunks
   onceCall198EntryWords spqrLazyLockClosureWords spqrStorageOfHwcap
   spqrUseAcceleratedInitInstrs spqrUseAcceleratedInitSpec stdGetauxvalRoSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (ghostExternReplaysOn_of_linkedCallHookG_liftVis hookOk_linkedCallHookG linkedCallHookG
   linkedCallHookG_activeRealPre_of_noException linkedCallHookG_eq_conj linkedCallHookG_fs
   linkedCallHookG_fsT linkedCallHookG_visitedIn withStateGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_externAt_none emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
  (codeLoaded_stripExecOutside_of_keep)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec
  (SpqrOnceCallRowSpec spqrOnceCallFallback spqrOnceCallFallback_fs spqrOnceCallFallback_ok
   spqrOnceCallFallback_perm spqrOnceCallFallback_trace)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsBlocksLen f3TokenIdx f3TokenPins_ok f3TokenStorageIdx libsignalBlocks_len
   lsInternedBlocks_len lsInternedMultiLib ls_idsOk ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_stubs f3TrialRxProg_symbols
   f3TrialRxWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2TimeAddAddr)

/-! ## 1. Concrete `rxSeg` Addresses, Word Slices, & `f3CpuProbeLayout` -/

/-- Stock-ELF entry address of `<std::sys::sync::once::futex::Once>::call` (`0x4cb470`). -/
@[expose] def c2OnceCallAddr : BitVec 64 := c2TimeAddAddr - 604#64

/-- Stock-ELF entry address of `cpufeatures::aarch64::getauxval_hwcap` (`0x4cb468`). -/
@[expose] def c2HwcapAddr : BitVec 64 := c2TimeAddAddr - 612#64

/-- Stock-ELF entry address of `__aarch64_cas4_acq` (`0x47942c`). -/
@[expose] def c2Cas4AcqAddr : BitVec 64 := f3StdLayout.rustEnableLseAddr - 88#64

/-- Stock-ELF entry address of `__aarch64_swp4_rel` (`0x47945c`). -/
@[expose] def c2Swp4RelAddr : BitVec 64 := f3StdLayout.rustEnableLseAddr - 40#64

/-- Mangled `cpufeatures::aarch64::getauxval_hwcap` symbol name. -/
abbrev lsGetauxvalHwcapSym : String :=
  "_RNvNtCslWItzXo2NmA_11cpufeatures7aarch6415getauxval_hwcap"

/-- `f3StdLayout` specialized with the concrete outline-atomic addresses `c2Cas4AcqAddr` and
    `c2Swp4RelAddr` (preserving `haveLseAtomicsAddr`, `libcAddr`, and `getauxvalAddr` by `rfl`). -/
@[expose] def f3CpuProbeLayout : StdBinaryLayout :=
  { f3StdLayout with
    cas4AcqAddr := c2Cas4AcqAddr
    swp4RelAddr := c2Swp4RelAddr }

@[expose] def c2OnceCallWords : List (BitVec 32) :=
  [ 0xd10183ff#32, 0xa9027bfd#32, 0xa9035ff8#32, 0xa90457f6#32,
    0xa9054ff4#32, 0x910083fd#32, 0x910023e8#32, 0x88dffc16#32,
    0xaa0303f5#32, 0xaa0203f4#32, 0xaa0003f3#32, 0x91002118#32,
    0x37000081#32, 0xaa0403f7#32, 0x14000049#32, 0x88dffe76#32,
    0x120006d7#32, 0x51000ae8#32, 0x7100091f#32, 0x121e02c8#32,
    0x540001a2#32, 0x32000101#32, 0x2a1603e0#32, 0xaa1303e2#32,
    0x97feb7d7#32, 0x6b16001f#32, 0x540004a0#32, 0x2a0003f6#32,
    0x12000417#32, 0x51000ae8#32, 0x7100091f#32, 0x121e0008#32,
    0x54fffea3#32, 0x710006ff#32, 0x540005c1#32, 0x35000108#32,
    0x321e02d6#32, 0x52800020#32, 0xaa1303e2#32, 0x2a1603e1#32,
    0x97feb7c7#32, 0x7100041f#32, 0x54fffe21#32, 0xf90007ff#32,
    0xb9400268#32, 0x6b16011f#32, 0x54fffc21#32, 0xb9400be8#32,
    0x52800c40#32, 0xaa1303e1#32, 0x52801122#32, 0x2a1603e3#32,
    0xaa1f03e5#32, 0x7100011f#32, 0x12800006#32, 0x9a9f1304#32,
    0x97feb66c#32, 0xb6fffac0#32, 0x97fead4f#32, 0xb9400008#32,
    0x7100111f#32, 0x54fffde0#32, 0x17ffffd1#32, 0x71000aff#32,
    0x1a9f17e8#32, 0xf94012a9#32, 0xb9000bff#32, 0x390033e8#32,
    0x910023e1#32, 0xaa1403e0#32, 0xd63f0120#32, 0xb9400be0#32,
    0xaa1303e1#32, 0x97feb7b2#32, 0x361000c0#32, 0x52800c40#32,
    0xaa1303e1#32, 0x52801022#32, 0x12b00003#32, 0x97feb655#32,
    0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32,
    0x910183ff#32, 0xd65f03c0#32 ]

@[expose] def c2Cas4AcqWords : List (BitVec 32) :=
  [ 0x900002b0#32, 0x395cc210#32, 0x34000070#32, 0x88e07c41#32,
    0xd65f03c0#32, 0x2a0003f0#32, 0x885ffc40#32, 0x6b10001f#32,
    0x54000061#32, 0x88117c41#32, 0x35ffff91#32, 0xd65f03c0#32 ]

@[expose] def c2Swp4RelWords : List (BitVec 32) :=
  [ 0x900002b0#32, 0x395cc210#32, 0x34000070#32, 0xb8608020#32,
    0xd65f03c0#32, 0x2a0003f0#32, 0x885f7c20#32, 0x8811fc30#32,
    0x35ffffd1#32, 0xd65f03c0#32 ]

@[expose] def c2HwcapWords : List (BitVec 32) :=
  [ 0x52800200#32, 0x17feb68c#32 ]

@[expose] def c2GetauxvalWords : List (BitVec 32) :=
  [ 0xa9be7bfd#32, 0xf1005c1f#32, 0x910003fd#32, 0xf9000bf3#32,
    0x54000120#32, 0xb00002a1#32, 0xf943b021#32, 0xf9400033#32,
    0xeb00027f#32, 0xb4000133#32, 0x540000c0#32, 0x91004021#32,
    0x17fffffb#32, 0xb00002a0#32, 0x395d6813#32, 0x14000006#32,
    0xf9400433#32, 0x14000004#32, 0x97fff6ec#32, 0x52800041#32,
    0xb9000001#32, 0xaa1303e0#32, 0xf9400bf3#32, 0xa8c27bfd#32,
    0xd65f03c0#32 ]

/-- 17-instruction concrete word slice of `spqr::encoding::gf::check_accelerated::use_accelerated::init`
    (`libsignalSessionLib` block `385` in `cliElfImage.segments[1]`). -/
@[expose] def c2Blk385Words : List (BitVec 32) :=
  [ 0xa9be7bfd#32, 0xf9000bf3#32, 0x910003fd#32, 0xd00003f3#32,
    0x39400268#32, 0x7103fd1f#32, 0x54000080#32, 0xf9400bf3#32,
    0xa8c27bfd#32, 0xd65f03c0#32, 0x9401f461#32, 0xf27d041f#32,
    0x1a9f07e8#32, 0x39000268#32, 0xf9400bf3#32, 0xa8c27bfd#32,
    0xd65f03c0#32 ]

@[expose] def c2OnceCallSubProg : Program := pureWordsProg c2OnceCallAddr c2OnceCallWords
@[expose] def c2Cas4AcqSubProg : Program := pureWordsProg c2Cas4AcqAddr c2Cas4AcqWords
@[expose] def c2Swp4RelSubProg : Program := pureWordsProg c2Swp4RelAddr c2Swp4RelWords
@[expose] def c2HwcapSubProg : Program := pureWordsProg c2HwcapAddr c2HwcapWords
@[expose] def c2GetauxvalSubProg : Program :=
  pureWordsProg f3StdLayout.getauxvalAddr c2GetauxvalWords
@[expose] noncomputable def c2Blk321SubProg : Program :=
  pureWordsProg (cliElfMultiPlacement.base 321) spqrLazyLockClosureWords
@[expose] noncomputable def c2Blk385SubProg : Program :=
  pureWordsProg (cliElfMultiPlacement.base 385) c2Blk385Words

@[expose] noncomputable def spqrBlk321Prog (mpl : MultiPlacement) : Program :=
  libsignalSessionLib.blockProgram mpl 321 (fun _ => none) (fun _ => none) Syscall.standard

@[expose] noncomputable def spqrBlk385Prog (mpl : MultiPlacement) : Program :=
  libsignalSessionLib.blockProgram mpl 385 (fun _ => none) (fun _ => none) Syscall.standard

/-- Tight 7-interval kept-region byte predicate for `lsSpqrOnceCallSym`. -/
@[expose] noncomputable def keepSpqrOnceCall (_mpl : MultiPlacement) (pc : BitVec 64) : Bool :=
  progKeep c2OnceCallSubProg pc ||
  progKeep c2Cas4AcqSubProg pc ||
  progKeep c2Swp4RelSubProg pc ||
  progKeep c2HwcapSubProg pc ||
  progKeep c2GetauxvalSubProg pc ||
  progKeep c2Blk321SubProg pc ||
  progKeep c2Blk385SubProg pc

theorem keepSpqrOnceCall_entry (mpl : MultiPlacement) :
    keepSpqrOnceCall mpl c2OnceCallAddr = true := by
  have hlen : c2OnceCallSubProg.code.length = 344 := by rfl_kernel
  have hbase : c2OnceCallSubProg.base = c2OnceCallAddr := rfl
  have h : progKeep c2OnceCallSubProg c2OnceCallAddr = true := by
    unfold progKeep
    rw [hbase, hlen, BitVec.sub_self, BitVec.toNat_zero]
    decide
  unfold keepSpqrOnceCall
  simp [h]

/-- Trivial entry guard for `lsSpqrOnceCallSym` (`LsRetAddrNoProbe` is carried inside
    `spqrOnceCallGhostSpec.pre`). -/
@[expose] def spqrOnceCallEntryGuard (_mpl : MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. `WordTree` & `InElf` Sub-Program Certificates -/

private theorem f3Trial_onceCall_hasWords :
    f3TrialRxProg.hasWords c2OnceCallAddr c2OnceCallWords :=
  hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel)

private theorem f3Trial_cas4Acq_hasWords :
    f3TrialRxProg.hasWords c2Cas4AcqAddr c2Cas4AcqWords :=
  hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel)

private theorem f3Trial_swp4Rel_hasWords :
    f3TrialRxProg.hasWords c2Swp4RelAddr c2Swp4RelWords :=
  hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel)

private theorem f3Trial_hwcap_hasWords :
    f3TrialRxProg.hasWords c2HwcapAddr c2HwcapWords :=
  hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel)

private theorem f3Trial_getauxval_hasWords :
    f3TrialRxProg.hasWords f3StdLayout.getauxvalAddr c2GetauxvalWords :=
  hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel)

private theorem elfMaps_eq_of_len_eq {img : ElfImage} {addr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} {ok : Perm → Bool}
    (h1 : ElfMaps img addr bs1 ok) (h2 : ElfMaps img addr bs2 ok)
    (hlen : bs1.length = bs2.length) :
    bs1 = bs2 := by
  refine List.ext_getElem hlen fun i hi1 hi2 => ?_
  obtain ⟨q1, hq1, _⟩ := h1 i hi1
  obtain ⟨q2, hq2, _⟩ := h2 i hi2
  rw [hq1] at hq2
  exact (Prod.mk.inj (Option.some.inj hq2)).2

private noncomputable def checkElfRxSlice (addr : BitVec 64) (expected : List (BitVec 8)) : Bool :=
  match Obj.Interned.regionView addr cliElfImage.segments with
  | some (p, bs, _) => (p == Perm.rx) && Obj.Interned.isPrefixOfFast expected bs
  | none => false

private theorem elfMaps_of_checkElfRxSlice {addr : BitVec 64} {expected : List (BitVec 8)}
    (hok : checkElfRxSlice addr expected = true) :
    ElfMaps cliElfImage addr expected (· == Perm.rx) := by
  unfold checkElfRxSlice at hok
  cases hrv : Obj.Interned.regionView addr cliElfImage.segments with
  | none => rw [hrv] at hok; nomatch hok
  | some v =>
    rcases v with ⟨p, bs, m⟩
    rw [hrv] at hok
    dsimp only at hok
    simp only [Bool.and_eq_true, Obj.Interned.isPrefixOfFast_eq, List.isPrefixOf_iff_prefix] at hok
    have hv := (Obj.Interned.view_of_regionView hrv).2
    exact Obj.Interned.elfMaps_of_view (hv.of_prefix hok.2) hok.1

set_option maxRecDepth 2000000 in
private theorem c2_blk321_elf_ok :
    checkElfRxSlice (cliElfMultiPlacement.base 321) c2Blk321SubProg.code = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem c2_blk385_elf_ok :
    checkElfRxSlice (cliElfMultiPlacement.base 385) c2Blk385SubProg.code = true := by
  rfl_kernel

private theorem ls_blocks_len_624 : libsignalSessionLib.blocks.length = 624 := by
  have h1 := Nat.beq_eq.mp libsignalBlocks_len
  have h2 : f3LsBlocksLen = 624 := by rfl_kernel
  exact h1.trans h2

private theorem ls_blk_code_len_eq {j : Nat} (hj : j < libsignalSessionLib.blocks.length) :
    (libsignalSessionLib.blocks[j]'hj).code.length =
      (lsInternedMultiLib.blocks.getD j { code := [] }).code.length := by
  have hj_int : j < lsInternedMultiLib.blocks.length := by
    have h1 := Nat.beq_eq.mp lsInternedBlocks_len
    have h2 : f3LsBlocksLen = 624 := by rfl_kernel
    have h3 := ls_blocks_len_624
    omega
  have h1 : (libsignalSessionLib.blocks[j]'hj) =
      libsignalSessionLib.blocks.getD j { code := [] } :=
    (Obj.Interned.getD_of_lt hj).symm
  rw [h1, ls_toMultiPlacedLib_eq]
  simp only [Obj.Interned.MultiLib.toMultiPlacedLib_blocks, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hj_int, Option.map_some, Option.getD_some,
    Obj.Interned.Block.toCodeBlock]

private theorem elfMaps_getElem_eq {img : ElfImage} {addr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} {ok : Perm → Bool}
    (h1 : ElfMaps img addr bs1 ok) (h2 : ElfMaps img addr bs2 ok)
    {i : Nat} (hi1 : i < bs1.length) (hi2 : i < bs2.length) :
    bs2[i]'hi2 = bs1[i]'hi1 := by
  obtain ⟨q1, hq1, _⟩ := h1 i hi1
  obtain ⟨q2, hq2, _⟩ := h2 i hi2
  rw [hq1] at hq2
  exact (Prod.mk.inj (Option.some.inj hq2)).2.symm

private theorem codeLoaded_blkSubProg_of_linkedAt {mpl : MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsCl : LibsignalCodeLoaded mpl m)
    {j : Nat} (hj624 : j < 624)
    (hj_unmut : (j ∈ CryptoVerification.libsignalMutatedBlocks) = false)
    {subProg : Program}
    (hbase_sub : subProg.base = cliElfMultiPlacement.base j)
    (hlen_le : subProg.code.length ≤ (lsInternedMultiLib.blocks.getD j { code := [] }).code.length)
    (helf : checkElfRxSlice (cliElfMultiPlacement.base j) subProg.code = true) :
    subProg.CodeLoaded m := by
  have hj : j < libsignalSessionLib.blocks.length := by rw [ls_blocks_len_624]; exact hj624
  have ⟨img, hparse, hpl, hin⟩ := hLs
  have himg : img = cliElfImage := Except.ok.inj (hparse.symm.trans cliElf_parse)
  subst himg
  have hbase : mpl.base j = cliElfMultiPlacement.base j :=
    (cliElf_linkedAt_unique hLs).1 j hj
  have hm1 := hin.blocks j hj
  rw [hbase] at hm1
  have hm2 := elfMaps_of_checkElfRxSlice helf
  have hlen1 :
      subProg.code.length ≤
        ((libsignalSessionLib.blocks[j]'hj).patched
          (libsignalSessionLib.blockPlacement mpl j)).length := by
    rw [CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok j hj).len_aligned,
      ls_blk_code_len_eq hj]
    exact hlen_le
  have hcl_blk := hLsCl j hj624 hj_unmut (fun _ => none) (fun _ => none) Syscall.standard
  let blkP := libsignalSessionLib.blockProgram mpl j (fun _ => none) (fun _ => none)
    Syscall.standard
  have hcl_blk' : blkP.CodeLoaded m := hcl_blk
  have hbase_blk : subProg.base = blkP.base := by
    dsimp only [blkP, MultiPlacedLib.blockProgram, PlacedLib.program,
      MultiPlacedLib.blockPlacement]
    exact hbase_sub.trans hbase.symm
  have hcode_blk :
      blkP.code =
      (libsignalSessionLib.blocks[j]'hj).patched (libsignalSessionLib.blockPlacement mpl j) := by
    dsimp only [blkP, MultiPlacedLib.blockProgram, PlacedLib.program]
    rw [libsignalSessionLib.blockLib_text hj]
  have hlen_blk : subProg.code.length ≤ blkP.code.length := by
    rw [hcode_blk]; exact hlen1
  have hnw_blk : blkP.base.toNat + blkP.code.length ≤ 2 ^ 64 := hcl_blk'.no_wrap
  refine Program.CodeLoaded.intro
    (hbase_blk ▸ hcl_blk'.aligned)
    (by rw [hbase_blk]; omega)
    fun i hi => ?_
  have hi_blk : i < blkP.code.length := by omega
  have hbyte := hcl_blk'.byte_eq i hi_blk
  have hperm := hcl_blk'.perm_eq i hi_blk
  have hlf := hcl_blk'.isLazyFree_eq i hi_blk
  rw [← hbase_blk] at hbyte hperm hlf
  have hget_eq : subProg.code[i]'hi = blkP.code[i]'hi_blk := by
    have h1 : blkP.code[i]'hi_blk =
        ((libsignalSessionLib.blocks[j]'hj).patched
          (libsignalSessionLib.blockPlacement mpl j))[i]'(by omega) := by
      simp only [hcode_blk]
    rw [h1]
    exact elfMaps_getElem_eq hm1 hm2 (by omega) hi
  rw [← hget_eq] at hbyte
  exact ⟨hbyte, hperm, hlf⟩

theorem keepSpqrOnceCall_eq_cliElf_of_linkedAt {mpl : MultiPlacement}
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    keepSpqrOnceCall mpl = keepSpqrOnceCall cliElfMultiPlacement :=
  rfl

/-! ## 3. Guard Predicate (`SpqrProbeGuard`) & `stripS` Invariance -/

/-- State guard ensuring all 7 code chunks of `Once::call` are `CodeLoaded` in `s.mem` and `mpl` is
    linked in `cliElfBytes`. -/
@[expose] def SpqrProbeGuard (mpl : MultiPlacement) (s : State) : Prop :=
  c2OnceCallSubProg.CodeLoaded s.mem ∧
  c2Cas4AcqSubProg.CodeLoaded s.mem ∧
  c2Swp4RelSubProg.CodeLoaded s.mem ∧
  c2HwcapSubProg.CodeLoaded s.mem ∧
  c2GetauxvalSubProg.CodeLoaded s.mem ∧
  c2Blk321SubProg.CodeLoaded s.mem ∧
  c2Blk385SubProg.CodeLoaded s.mem ∧
  libsignalSessionLib.LinkedAt cliElfBytes mpl

set_option maxRecDepth 400000 in
private theorem lsLen_321_beq :
    Nat.beq (lsInternedMultiLib.blocks.getD 321 { code := [] }).code.length 64 = true := by
  rfl_kernel

private theorem lsLen_321_eq_64 :
    (lsInternedMultiLib.blocks.getD 321 { code := [] }).code.length = 64 :=
  Nat.beq_eq.mp lsLen_321_beq

set_option maxRecDepth 400000 in
private theorem lsLen_385_beq :
    Nat.beq (lsInternedMultiLib.blocks.getD 385 { code := [] }).code.length 68 = true := by
  rfl_kernel

private theorem lsLen_385_eq_68 :
    (lsInternedMultiLib.blocks.getD 385 { code := [] }).code.length = 68 :=
  Nat.beq_eq.mp lsLen_385_beq

theorem spqrProbeGuard_of_codeLoaded {mpl : MultiPlacement} {s : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsCl : LibsignalCodeLoaded mpl s.mem)
    (hRx : f3TrialRxProg.CodeLoaded s.mem) :
    SpqrProbeGuard mpl s :=
  ⟨codeLoaded_pureWordsProg_of_hasWords hRx f3Trial_onceCall_hasWords (by decide),
   codeLoaded_pureWordsProg_of_hasWords hRx f3Trial_cas4Acq_hasWords (by decide),
   codeLoaded_pureWordsProg_of_hasWords hRx f3Trial_swp4Rel_hasWords (by decide),
   codeLoaded_pureWordsProg_of_hasWords hRx f3Trial_hwcap_hasWords (by decide),
   codeLoaded_pureWordsProg_of_hasWords hRx f3Trial_getauxval_hasWords (by decide),
   codeLoaded_blkSubProg_of_linkedAt hLs hLsCl (j := 321) (by decide) (by decide)
     rfl (by rw [lsLen_321_eq_64]; decide) c2_blk321_elf_ok,
   codeLoaded_blkSubProg_of_linkedAt hLs hLsCl (j := 385) (by decide) (by decide)
     rfl (by rw [lsLen_385_eq_68]; decide) c2_blk385_elf_ok,
   hLs⟩

theorem spqrProbeGuard_of_keepsFrozen {mpl : MultiPlacement} {s s' : State}
    (hG : SpqrProbeGuard mpl s) (hkf : s.mem.KeepsFrozen s'.mem) :
    SpqrProbeGuard mpl s' :=
  ⟨hG.1.of_keepsFrozen hkf,
   hG.2.1.of_keepsFrozen hkf,
   hG.2.2.1.of_keepsFrozen hkf,
   hG.2.2.2.1.of_keepsFrozen hkf,
   hG.2.2.2.2.1.of_keepsFrozen hkf,
   hG.2.2.2.2.2.1.of_keepsFrozen hkf,
   hG.2.2.2.2.2.2.1.of_keepsFrozen hkf,
   hG.2.2.2.2.2.2.2⟩

private theorem progKeep_of_offset {P : Program} (hNoWrap : P.base.toNat + P.code.length ≤ 2 ^ 64)
    {off : Nat} (hoff : off < P.code.length) :
    progKeep P (P.base + BitVec.ofNat 64 off) = true := by
  unfold progKeep
  have hsub : P.base + BitVec.ofNat 64 off - P.base = BitVec.ofNat 64 off := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

private theorem codeLoaded_strip_of_progKeep_sub {P : Program} {keep : BitVec 64 → Bool}
    {m : Memory} (hSub : ∀ pc, progKeep P pc = true → keep pc = true) (hCL : P.CodeLoaded m) :
    P.CodeLoaded (stripExecOutside keep m) :=
  codeLoaded_stripExecOutside_of_keep
    (fun _ hoff => hSub _ (progKeep_of_offset hCL.no_wrap hoff)) hCL

theorem spqrProbeGuard_stripS (mpl : MultiPlacement) (entry : BitVec 64) (s0 : State)
    (_hFr : ExecFrozen s0.mem) (hG : SpqrProbeGuard mpl s0) :
    SpqrProbeGuard mpl (stripS (keepSpqrOnceCall mpl) (s0.setPC entry)) := by
  cases s0
  dsimp only [stripS, State.setPC] at hG ⊢
  refine ⟨codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.2.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.2.2.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.2.2.2.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.2.2.2.2.1,
    codeLoaded_strip_of_progKeep_sub (fun pc h => by unfold keepSpqrOnceCall; simp [h]) hG.2.2.2.2.2.2.1,
    hG.2.2.2.2.2.2.2⟩

theorem emptyStdProg_codeLoaded (m : Memory) : emptyStdProg.CodeLoaded m :=
  Program.CodeLoaded.intro (by decide) (by decide) (fun _ hi => nomatch hi)

/-! ## 4. Per-Chunk Instruction & `hasWords` Witnesses (`rfl_kernel`) -/

private theorem hasInstrs_of_all_fetch {P : Program} {base : BitVec 64} {instrs : List Instr}
    (hok : ((List.range instrs.length).all fun i =>
      P.fetch (base + BitVec.ofNat 64 (4 * i)) == instrs[i]?) = true) :
    hasInstrs P base instrs := by
  intro i hi
  have h := List.all_eq_true.mp hok i (List.mem_range.mpr hi)
  rw [beq_iff_eq, List.getElem?_eq_getElem hi] at h
  exact h

private theorem c2OnceCall_code :
    OnceCall198Code (c2OnceCallSubProg.withSvc noSyscalls)
      c2OnceCallAddr c2Cas4AcqAddr c2Swp4RelAddr := by
  dsimp only [OnceCall198Code, onceCall198Chunks, CodeChunks, CodeChunk.holds]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · exact hasInstrs_of_all_fetch (by rfl_kernel)
  · decide +kernel
  · decide +kernel
  · exact hasInstrs_of_all_fetch (by rfl_kernel)
  · decide +kernel
  · decide +kernel

private theorem c2Cas4Acq_hasInstrs :
    hasInstrs (c2Cas4AcqSubProg.withSvc noSyscalls)
      f3CpuProbeLayout.cas4AcqAddr (cas4AcqInstrs f3CpuProbeLayout) :=
  hasInstrs_of_all_fetch (by rfl_kernel)

private theorem c2Swp4Rel_hasInstrs :
    hasInstrs (c2Swp4RelSubProg.withSvc noSyscalls)
      f3CpuProbeLayout.swp4RelAddr (swp4RelInstrs f3CpuProbeLayout) :=
  hasInstrs_of_all_fetch (by rfl_kernel)

private theorem c2Getauxval_hasInstrs :
    hasInstrs (c2GetauxvalSubProg.withSvc noSyscalls)
      f3CpuProbeLayout.getauxvalAddr (getauxvalInstrs f3CpuProbeLayout) :=
  hasInstrs_of_all_fetch (by rfl_kernel)

private theorem c2Hwcap_hasInstrs :
    hasInstrs (c2HwcapSubProg.withSvc noSyscalls)
      c2HwcapAddr (getauxvalHwcapInstrs f3CpuProbeLayout c2HwcapAddr) :=
  hasInstrs_of_all_fetch (by rfl_kernel)

private theorem withSvc_pureWords_externAt_none (base : BitVec 64) (words : List (BitVec 32))
    (svc : State → State) (pc : BitVec 64) :
    ((pureWordsProg base words).withSvc svc).externAt? pc = none :=
  pureWordsProg_externAt_none base words pc

private noncomputable def c2Blk321NoSvc : Program :=
  c2Blk321SubProg.withSvc noSyscalls

private noncomputable def c2Blk385NoSvc : Program :=
  c2Blk385SubProg.withSvc noSyscalls

private theorem c2Blk321_svc : c2Blk321NoSvc.svc = noSyscalls := rfl

private theorem c2Blk385_svc : c2Blk385NoSvc.svc = noSyscalls := rfl

private theorem c2Blk321_externAt_none (pc : BitVec 64) : c2Blk321NoSvc.externAt? pc = none :=
  withSvc_pureWords_externAt_none (cliElfMultiPlacement.base 321) spqrLazyLockClosureWords
    noSyscalls pc

private theorem c2Blk385_externAt_none (pc : BitVec 64) : c2Blk385NoSvc.externAt? pc = none :=
  withSvc_pureWords_externAt_none (cliElfMultiPlacement.base 385) c2Blk385Words noSyscalls pc

private theorem c2Blk321_hasWords :
    c2Blk321NoSvc.hasWords (cliElfMultiPlacement.base 321) spqrLazyLockClosureWords := by
  have hcode : c2Blk321SubProg.code = (pureWordsProg 0#64 spqrLazyLockClosureWords).code := rfl
  have hread : ((List.range spqrLazyLockClosureWords.length).all fun i =>
      c2Blk321SubProg.readWordOff (4 * i) == spqrLazyLockClosureWords[i]?) = true := by
    have h0 : ((List.range spqrLazyLockClosureWords.length).all fun i =>
        (pureWordsProg 0#64 spqrLazyLockClosureWords).readWordOff (4 * i) ==
          spqrLazyLockClosureWords[i]?) = true := by
      rfl_kernel
    have hcongr : ∀ i, c2Blk321SubProg.readWordOff (4 * i) =
        (pureWordsProg 0#64 spqrLazyLockClosureWords).readWordOff (4 * i) := by
      intro i; dsimp only [Program.readWordOff]; rw [hcode]
    simpa only [hcongr] using h0
  exact pureWordsProg_hasWords (by decide) hread

set_option maxRecDepth 400000 in
private theorem c2Blk385_hasInstrs :
    hasInstrs c2Blk385NoSvc (cliElfMultiPlacement.base 385)
      (spqrUseAcceleratedInitInstrs (cliElfMultiPlacement.base 385)
        (cliElfMultiPlacement.ρ tokenStorageName) c2HwcapAddr) := by
  unfold c2Blk385NoSvc c2Blk385SubProg
  exact hasInstrs_of_all_fetch (by rfl_kernel)

/-! ## 5. Cross-Program `noSyscalls` `SepWP` Composition & `emptyStdProg` `subroutine_ok` -/

private theorem sepWP_seq_keepsFrozen {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid s Pre (fun sm Pm =>
      s.mem.KeepsFrozen sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s Pre post oom := by
  unfold SepWP reaches_pc at h1 ⊢
  intro R hm hCL
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hm_m, hcont⟩ | ⟨hoom_m, hm_oom⟩⟩ := h1 R hm hCL
  · have hcont' := hcont hsteps1.keepsFrozen
    dsimp only [SepWP, reaches_pc] at hcont'
    obtain ⟨sf, hsteps2, hout⟩ := hcont' R hm_m (hsteps1.codeLoaded hCL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom_m, hm_oom⟩⟩

private theorem sepWP_call_otherProg {α : Type} {P1 P2 : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (x : α) (F : SepProp)
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext1 : ∀ pc, P1.externAt? pc = none) (hext2 : ∀ pc, P2.externAt? pc = none)
    (hsvc : P2.svc = P1.svc)
    (hCL2 : P2.CodeLoaded s.mem)
    (hsub : subroutine_ok P2 entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P1 target_pc sf (spec.post x s sf ∗ F) post oom) :
    SepWP P1 target_pc s Pre post oom := by
  unfold SepWP reaches_pc
  intro R hm hCL1
  obtain ⟨sm, hsteps2, hout⟩ :=
    subroutine_ok_elim_steps_outcome hsub x (F ∗ R) s hpc hrun (hpre R hm) hsp hCL2
  have hsteps1 : Steps P1 s sm :=
    Steps.of_sameHooks (fun pc => (hext2 pc).trans (hext1 pc).symm) hsvc hsteps2
  rcases hout with ⟨⟨hpc_m, hsp_m, hrun_m⟩, hcs_m, hpost_m⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · rw [hlr] at hpc_m
    rw [← sepConj_assoc] at hpost_m
    have hn := hnext sm hpc_m hrun_m hsp_m hcs_m.2 hsteps2.keepsFrozen
    unfold SepWP at hn
    dsimp only [reaches_pc] at hn
    obtain ⟨sf, hsteps_next, hout_f⟩ :=
      hn R hpost_m (hsteps1.codeLoaded hCL1)
    exact ⟨sf, hsteps1.trans hsteps_next, hout_f⟩
  · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
  · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
  · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

section CpuProbeSplitExec
arm64_proof_prelude

private theorem step_str64_perm_s {prog : Program} {target_pc pc ea val : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  let m' := s.mem.write64 ea val
  have hm' := hstore.store hm
  have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
        MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write64 s.mem ea val) (Memory.keepsFrozen_write64 hcan val)
  unfold SepWP at hn
  exact hn R hm'

private theorem step_stp64_perm_s {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm
  have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm
  have hcan2_m1 := hstore2.writable hm1
  have hcan2 := hcan2_m1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hkf1 : s.mem.KeepsFrozen m1 := Memory.keepsFrozen_write64 hcan1 v1
  have hkf2 : m1.KeepsFrozen m2 := Memory.keepsFrozen_write64 hcan2_m1 v2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2,
        hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))
    (hkf1.trans hkf2)
  unfold SepWP at hn
  exact hn R hm2

private theorem step_str8_perm_s {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val
  have hm' := hstore.store hm
  have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
        MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write8 s.mem ea val)
  unfold SepWP at hn
  exact hn R hm'

private theorem c2Hwcap_split_ok :
    subroutine_ok (c2HwcapSubProg.withSvc noSyscalls) c2HwcapAddr
      (withStateGuard (fun s => (c2GetauxvalSubProg.withSvc noSyscalls).CodeLoaded s.mem)
        (getauxvalHwcapSpec f3CpuProbeLayout)) := by
  have hget := getauxval_found_ro_ok (c2GetauxvalSubProg.withSvc noSyscalls)
    f3CpuProbeLayout c2Getauxval_hasInstrs
  have hc := c2Hwcap_hasInstrs
  have hext_hw : ∀ pc, (c2HwcapSubProg.withSvc noSyscalls).externAt? pc = none :=
    fun pc => withSvc_pureWords_externAt_none c2HwcapAddr c2HwcapWords noSyscalls pc
  have hext_get : ∀ pc, (c2GetauxvalSubProg.withSvc noSyscalls).externAt? pc = none :=
    fun pc => withSvc_pureWords_externAt_none f3StdLayout.getauxvalAddr c2GetauxvalWords
      noSyscalls pc
  have hsvc_eq : (c2GetauxvalSubProg.withSvc noSyscalls).svc =
      (c2HwcapSubProg.withSvc noSyscalls).svc := rfl
  generalize c2HwcapSubProg.withSvc noSyscalls = P_hw at hc hext_hw hsvc_eq ⊢
  generalize c2GetauxvalSubProg.withSvc noSyscalls = P_get at hget hext_get hsvc_eq ⊢
  generalize f3CpuProbeLayout = L at hget hc ⊢
  generalize c2HwcapAddr = addr at hc ⊢
  apply subroutine_ok_of_sepWP_init
  rintro ⟨hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [withStateGuard, getauxvalHwcapSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hCL_get, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hnonull, hfind⟩, hpre⟩
  refine ⟨((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have_instrs hc 0 2
  wp_steps 2
  refine sepWP_call_otherProg (P2 := P_get)
    (ret_pc := s0.readReg64 .lr)
    (x := (16#64, hwcap, auxvAddr, entries)) (F := emp)
    hext_hw hext_get hsvc_eq hCL_get hget
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => by
      dsimp only [stdGetauxvalRoSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm], by decide, hnonull, hfind⟩, ?_⟩
      exact Satisfies.mono (by sep_entail) hm)
    rfl rfl rfl
    fun sf hpc_f hrun_f hsp_f hcs_f _ => ?_
  dsimp only [stdGetauxvalRoSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_f, hstd_f⟩
  apply SepWP.done hpc_f hrun_f
  refine ⟨fun hm => ?_, by simpa [wp_norm, arm64_norm] using hsp_f, ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, hstd_f⟩, Satisfies.mono (by sep_entail) hm⟩
  · exact CalleeSavedPreserved.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f

private theorem stackAt_64_eq_20_20_s (sp : BitVec 64) :
    stackAt sp 0x40 =
      stackFrameAt (sp - 0x20#64) 0x20 ∗ stackFrameAt sp 0x20 := by
  rw [← stackAt_eq_stackFrameAt sp 0x20, ← stackAt_eq_stackFrameAt (sp - 0x20#64) 0x20]
  have hs := stackAt_split_bottom sp 0x20 0x20 (by decide)
  simpa [stackAt, BitVec.sub_sub] using hs

private theorem blk385_split_gen (P P_hw P_get : Program) (L : StdBinaryLayout)
    (initAddr storageAddr hwcapAddr : BitVec 64)
    (hc : hasInstrs P initAddr (spqrUseAcceleratedInitInstrs initAddr storageAddr hwcapAddr))
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = noSyscalls)
    (hext_hw : ∀ pc, P_hw.externAt? pc = none) (hsvc_hw : P_hw.svc = noSyscalls)
    (hhw_ok : subroutine_ok P_hw hwcapAddr
      (withStateGuard (fun s => P_get.CodeLoaded s.mem) (getauxvalHwcapSpec L))) :
    subroutine_ok P initAddr
      (withStateGuard
        (fun s => P_hw.CodeLoaded s.mem ∧ P_get.CodeLoaded s.mem)
        (spqrUseAcceleratedInitSpec L storageAddr)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [withStateGuard, spqrUseAcceleratedInitSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hCL_hw, hCL_get⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hnonull, hfind⟩, hpre⟩
  refine ⟨(storageAddr ↦₈ 0xff#8) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x20 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackAt_64_eq_20_20_s, hsf]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have_instrs hc 0 7
  have_instrs hc 10 7
  refine step_stp64_perm_s (ea2 := s0.sp - 24#64) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 hkf1 => ?_
  refine step_str64_perm_s (ea := s0.sp - 16#64) (wb := none)
    (val := s0.readReg64 (.gpr 19#5))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_1
    (by simp only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned,
      wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) fun m2 hm2 hkf2 => ?_
  wp_steps 6
  have hkf12 : s0.mem.KeepsFrozen m2 := hkf1.trans hkf2
  refine sepWP_call_otherProg (P2 := P_hw)
    (ret_pc := initAddr + 44#64)
    (x := (hwcap, auxvAddr, entries))
    (F := (storageAddr ↦₈ 0xff#8) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3))
    hext hext_hw (hsvc_hw.trans hsvc.symm)
    (hCL_hw.of_keepsFrozen hkf12)
    hhw_ok
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [withStateGuard, getauxvalHwcapSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hCL_get.of_keepsFrozen hkf12, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hnonull, hfind⟩, ?_⟩
      simp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (by sep_entail)) hm)
    rfl rfl rfl
    fun s1 hpc1 hrun1 hsp1 hcs1 _ => ?_
  dsimp only [withStateGuard, getauxvalHwcapSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_1, hstd1⟩
  have hx19_1 : s1.readReg64 (.gpr 19#5) =
      ((initAddr + 12#64) &&& ~~~4095#64) + adrpOff (initAddr + 12#64) storageAddr := by
    rw [hcs1.readReg64_x19]
    simp [wp_norm, arm64_norm]
  have hsp1_eq : s1.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm] using hsp1
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]
    exact s0.spAligned_sub 32#64 hsp
  wp_steps 2
  refine step_str8_perm_s (ea := storageAddr) (wb := none) (val := spqrStorageOfHwcap hwcap)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
    hf_13 rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, hx19_1])
    (by simp only [spqrStorageOfHwcap, wp_norm, arm64_norm])
    (by wp_sep_access) fun m3 hm3 => ?_
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hstd1.1, hstd1.2.1, hstd1.2.2.1, hstd1.2.2.2.1, hstd1.2.2.2.2.1, hstd1.2.2.2.2.2.1,
      hstd1.2.2.2.2.2.2.1,
      fun a => (congrFun hm3 a).trans ((hstd1.2.2.2.2.2.2.2 a).trans
        ((congrFun hm2 a).trans (congrFun hm1 a)))⟩, ?_⟩
    rw [stackAt_64_eq_20_20_s, hsf]
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
    refine Entails.trans
      (Q := (storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗
        ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
        (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackFrameAt (s0.sp - 32#64) 32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3)))
      (by sep_entail) ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
    exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
      (Entails.sepExists_right (s0.readReg64 (.gpr 30#5))
        (Entails.sepExists_right (s0.readReg64 (.gpr 19#5))
          (Entails.sepExists_right w3 (by sep_entail))))
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with
      ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]
    simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

private theorem c2Blk385_split_ok :
    subroutine_ok c2Blk385NoSvc (cliElfMultiPlacement.base 385)
      (withStateGuard
        (fun s => (c2HwcapSubProg.withSvc noSyscalls).CodeLoaded s.mem ∧
          (c2GetauxvalSubProg.withSvc noSyscalls).CodeLoaded s.mem)
        (spqrUseAcceleratedInitSpec f3CpuProbeLayout
          (cliElfMultiPlacement.ρ tokenStorageName))) :=
  blk385_split_gen c2Blk385NoSvc (c2HwcapSubProg.withSvc noSyscalls)
    (c2GetauxvalSubProg.withSvc noSyscalls) f3CpuProbeLayout
    (cliElfMultiPlacement.base 385) (cliElfMultiPlacement.ρ tokenStorageName) c2HwcapAddr
    c2Blk385_hasInstrs c2Blk385_externAt_none c2Blk385_svc
    (fun pc => withSvc_pureWords_externAt_none c2HwcapAddr c2HwcapWords noSyscalls pc) rfl
    c2Hwcap_split_ok

private def closureSplitSpecGen (P_init P_hw P_get : Program)
    (libcAddr initAddr tokenAddr storageAddr : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
      List (BitVec 64 × BitVec 64)) where
  pre := fun (dataPtr, slotPtr, finishPtr, hwcap, auxvAddr, entries) s0 =>
    ⌜P_init.CodeLoaded s0.mem ∧
      P_hw.CodeLoaded s0.mem ∧
      P_get.CodeLoaded s0.mem ∧
      s0.readReg64 .x0 = dataPtr ∧
      s0.readReg64 .x1 = finishPtr ∧
      tokenAddr ≠ 0#64 ∧
      (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
      entries.find? (·.1 == 16#64) = some (16#64, hwcap)⌝ ∗
    ((dataPtr ↦₆₄ slotPtr) ∗
      (slotPtr ↦₆₄ tokenAddr) ∗
      (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((finishPtr + 4#64) ↦₈ 0#8) ∗
      (storageAddr ↦₈ 0xff#8) ∗
      ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40)
  post := fun (dataPtr, slotPtr, finishPtr, hwcap, auxvAddr, entries) s0 sf =>
    ⌜StdFieldsPreserved s0 sf⌝ ∗
    ((dataPtr ↦₆₄ slotPtr) ∗
      (slotPtr ↦₆₄ 0#64) ∗
      (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((finishPtr + 4#64) ↦₈ 0#8) ∗
      (storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗
      ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem blk321_split_gen (P P_init P_hw P_get : Program) (L : StdBinaryLayout)
    (closureAddr initAddr tokenAddr storageAddr : BitVec 64)
    (hcode : P.hasWords closureAddr spqrLazyLockClosureWords)
    (hext1 : ∀ pc, P.externAt? pc = none) (hext2 : ∀ pc, P_init.externAt? pc = none)
    (hsvc : P_init.svc = P.svc)
    (hinit : subroutine_ok P_init initAddr
      (withStateGuard
        (fun s => P_hw.CodeLoaded s.mem ∧ P_get.CodeLoaded s.mem)
        (spqrUseAcceleratedInitSpec L storageAddr))) :
    subroutine_ok P closureAddr
      (closureSplitSpecGen P_init P_hw P_get L.libcAddr initAddr tokenAddr storageAddr) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dataPtr, slotPtr, finishPtr, hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [closureSplitSpecGen] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hCL_385, hCL_hw, hCL_get, hx0, hx1, htok_nz, hnonull, hfind⟩, hpre⟩
  refine ⟨(dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((finishPtr + 4#64) ↦₈ 0#8) ∗ (storageAddr ↦₈ 0xff#8) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackAt s0.sp 0x40, hpre, ?_⟩
  have hcode' : P.hasCode closureAddr spqrLazyLockClosureWords := hcode
  have hstk_split : stackAt s0.sp 0x40 =
      stackAt (s0.sp - 0x10#64) 0x30 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1)) := by
    have h1 := stackAt_split_bottom s0.sp 0x10 0x30 (by decide)
    have h2 : stackAt s0.sp 0x10 =
        (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
          ((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1)) := by
      rw [stackAt_eq_stackFrameAt s0.sp 0x10]
      simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
    simpa [stackAt, BitVec.sub_sub, h2] using h1
  have hstk_back :
      (stackAt (s0.sp - 0x10#64) 0x30 ∗
        ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .lr)) ⊢ stackAt s0.sp 0x40 := by
    rw [hstk_split]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
      (Entails.sepExists_right (s0.readReg64 .lr) (Entails.refl _))
  refine sepWP_seq_keepsFrozen (mid := initAddr) ?_
  wp_conv_pre => rw [hstk_split]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  wp_steps 12
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  intro hkf_m
  refine sepWP_call_otherProg (P2 := P_init)
    (ret_pc := s0.readReg64 .lr)
    (x := (hwcap, auxvAddr, entries))
    (F := (dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ 0#64) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((finishPtr + 4#64) ↦₈ 0#8))
    hext1 hext2 hsvc
    (hCL_385.of_keepsFrozen hkf_m)
    hinit
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    (fun _ hm => by
      dsimp only [withStateGuard, spqrUseAcceleratedInitSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hCL_hw.of_keepsFrozen hkf_m, hCL_get.of_keepsFrozen hkf_m⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hnonull, hfind⟩, ?_⟩
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right hstk_back))))
      simp only [wp_norm, arm64_norm, bv_lin_norm]
      sep_entail)
    rfl rfl rfl
    fun sf hpc_f hrun_f hsp_f hcs_f _ => ?_
  dsimp only [withStateGuard, spqrUseAcceleratedInitSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hstd_f
  apply SepWP.done hpc_f hrun_f
  refine ⟨fun hm => ?_, by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_f,
    CalleeSavedPreserved.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm])
    hstd_f.toFields, ?_⟩
  refine Satisfies.mono ?_ hm
  simp only [wp_norm, arm64_norm, bv_lin_norm]
  sep_entail

private noncomputable abbrev spqrClosureSplitSpec :=
  closureSplitSpecGen c2Blk385NoSvc (c2HwcapSubProg.withSvc noSyscalls)
    (c2GetauxvalSubProg.withSvc noSyscalls) f3CpuProbeLayout.libcAddr
    (cliElfMultiPlacement.base 385)
    (cliElfMultiPlacement.ρ tokenName) (cliElfMultiPlacement.ρ tokenStorageName)

private theorem c2Blk321_split_ok :
    subroutine_ok c2Blk321NoSvc (cliElfMultiPlacement.base 321) spqrClosureSplitSpec :=
  blk321_split_gen c2Blk321NoSvc c2Blk385NoSvc
    (c2HwcapSubProg.withSvc noSyscalls) (c2GetauxvalSubProg.withSvc noSyscalls) f3CpuProbeLayout
    (cliElfMultiPlacement.base 321) (cliElfMultiPlacement.base 385)
    (cliElfMultiPlacement.ρ tokenName) (cliElfMultiPlacement.ρ tokenStorageName)
    c2Blk321_hasWords c2Blk321_externAt_none c2Blk385_externAt_none
    (c2Blk385_svc.trans c2Blk321_svc.symm) c2Blk385_split_ok

private theorem step_ldar32_words_s {prog : Program} {target_pc : BitVec 64}
    (addr : BitVec 64) (words : List (BitVec 32))
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w : BitVec 32} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (i : Nat) (next_pc : BitVec 64) (halign : MemWidth.isAligned .W32 ea = true)
    (rt' : Reg) (hw : prog.hasCode addr words)
    (hget : words[i]? = some w := by rfl)
    (hdec : decode w = some (.ldarStlr .W32 true rn rt) := by rfl)
    (hrt : rt = rt' := by decide) (hrn : rn ≠ .sp := by decide)
    (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by
      simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (haddr : s.readReg64 rn = ea := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hload : SepLoad32 ea P v := by wp_sep_access_fast)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt' (v.zeroExtend 64)).setPC next_pc) P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hrt hpc_next
  have hsp : checkRegSPAligned s rn = true := by cases rn <;> simp_all [checkRegSPAligned]
  apply SepWP.weaken_pre_frame (P' := ⌜s.mem.read32 ea = v ∧ s.mem.canRead ea 4 = true⌝ ∗ P)
  · intro R hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hload.load hm, hload.readable hm⟩, hm⟩
  · apply SepWP.pure_elim
    rintro ⟨hread, hcan⟩
    refine SepWP.step_pure
      (s' := (s.writeReg64 rt (v.zeroExtend 64)).setPC (addr + BitVec.ofNat 64 (4 * (i + 1))))
      hpc hrun (Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec) ?_ rfl hnext
    have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by
      cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
    have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
    rw [hs_eq]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

private theorem pointsTo8_combine32_sub_s (sp o0 o1 o2 o3 : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl)
    (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R =
      ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3
  simpa only [sepConj_assoc,
    show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin,
    show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin,
    show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin] using
    congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)

private theorem pointsTo32_split8_sub_s (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32)
    (R : SepProp) (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl)
    (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R =
      ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗
        ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [pointsTo8_combine32_sub_s sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3,
    show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by
      bv_bits]

private theorem combine_cell_byte4_sat_s (sp o8 o4 o3 o2 o1 : BitVec 64) {lo : BitVec 32}
    {b0 b1 b2 b3 : BitVec 8} {m : Memory} {P R : SepProp} (hm : m ⊨ P)
    (hf : P = (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
      ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) ∗ R := by sep_focus)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl)
    (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) :
    m ⊨ (((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) ∗ R) := by
  rwa [hf, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    pointsTo8_combine32_sub_s sp o4 o3 o2 o1 b0 b1 b2 b3 R h1 h2 h3,
    pointsTo32_combine64_sub sp o8 o4 lo _ R h4] at hm

private theorem stackAt_a0_eq_60_40_s (sp : BitVec 64) :
    stackAt sp 0xa0 = stackAt (sp - 0x60#64) 0x40 ∗ stackAt sp 0x60 := by
  have hs := stackAt_split_bottom sp 0x60 0x40 (by decide)
  simpa [stackAt, BitVec.sub_sub] using hs

private def spqrOnceCallStdSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64) where
  pre := spqrOnceCallGhostSpec.pre
  post := fun (dataPtr, slotPtr) s0 sf =>
    ⌜StdFieldsPreserved s0 sf⌝ ∗
    (lsρ tokenStorageName ↦₈ 1#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
    spqrProbeEnvAt ∗
    (dataPtr ↦₆₄ slotPtr) ∗
    (slotPtr ↦₆₄ 0#64) ∗
    stackAt s0.sp 0xa0
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private noncomputable def spqrVtableIdx : Nat :=
  lsInternedMultiLib.names.idxOf spqrLazyLockVtableSym

set_option maxRecDepth 400000 in
private theorem spqrVtable_pin_ok :
    (Nat.blt spqrVtableIdx lsInternedMultiLib.names.length &&
      (lsInternedMultiLib.names.getD spqrVtableIdx "" == spqrLazyLockVtableSym) &&
      (Obj.Interned.lookupBlockSymId spqrVtableIdx lsInternedMultiLib.blocks == none)) = true := by
  rfl_kernel

private theorem rho_eq_cliElf_of_pin {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {idx : Nat} {sym : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (hnm : lsInternedMultiLib.names.getD idx "" = sym)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    mpl.ρ sym = cliElfMultiPlacement.ρ sym := by
  have huniq := (cliElf_linkedAt_unique hLs).2.2.1
  have hmem : sym ∈ lsInternedMultiLib.names := by
    rw [← hnm, Obj.Interned.getD_of_lt hlt]
    exact List.getElem_mem hlt
  have hnone : Obj.lookupBlockSym sym libsignalSessionLib.blocks = none := by
    rw [← hnm, ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
    exact hid
  exact huniq sym hmem hnone

set_option maxHeartbeats 800000 in
set_option maxRecDepth 400000 in
private theorem c2OnceCall_noSvc_ok [LibsignalPlacement] :
    subroutine_ok (c2OnceCallSubProg.withSvc noSyscalls) c2OnceCallAddr
      (withStateGuard (SpqrProbeGuard lsmpl) spqrOnceCallStdSpec) := by
  have hcas_sub := cas4Acq_ok (c2Cas4AcqSubProg.withSvc noSyscalls) f3CpuProbeLayout
    c2Cas4Acq_hasInstrs
  have hswp_sub := swp4Rel_ok (c2Swp4RelSubProg.withSvc noSyscalls) f3CpuProbeLayout
    c2Swp4Rel_hasInstrs
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dataPtr, slotPtr⟩ R s0 hpc hrun hpre hsp
  dsimp only [withStateGuard, spqrOnceCallStdSpec, spqrOnceCallGhostSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hG, hpre⟩
  rcases hG with ⟨_hCL_once, hCL_cas, hCL_swp, hCL_hw, hCL_get, hCL_321_sub, hCL_385_sub, hLs⟩
  have hlen_blocks := ls_blocks_len_624
  have hCL_321 : c2Blk321NoSvc.CodeLoaded s0.mem := hCL_321_sub.of_base_code rfl rfl
  have hCL_385 : c2Blk385NoSvc.CodeLoaded s0.mem := hCL_385_sub.of_base_code rfl rfl
  have huniq := cliElf_linkedAt_unique hLs
  have hb321 : lsmpl.base 321 = cliElfMultiPlacement.base 321 := huniq.1 321 (by omega)
  have hb385 : lsmpl.base 385 = cliElfMultiPlacement.base 385 := huniq.1 385 (by omega)
  have htp := f3TokenPins_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at htp
  rcases htp with ⟨⟨⟨⟨⟨htok_lt, htok_nm⟩, htok_id⟩, hsto_lt⟩, hsto_nm⟩, hsto_id⟩
  have hvp := spqrVtable_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hvp
  rcases hvp with ⟨⟨hvt_lt, hvt_nm⟩, hvt_id⟩
  have hrho_sto : lsmpl.ρ tokenStorageName = cliElfMultiPlacement.ρ tokenStorageName :=
    rho_eq_cliElf_of_pin hLs hsto_lt hsto_nm hsto_id
  have hrho_tok : lsmpl.ρ tokenName = cliElfMultiPlacement.ρ tokenName :=
    rho_eq_cliElf_of_pin hLs htok_lt htok_nm htok_id
  have hrho_vt : lsmpl.ρ spqrLazyLockVtableSym = cliElfMultiPlacement.ρ spqrLazyLockVtableSym :=
    rho_eq_cliElf_of_pin hLs hvt_lt hvt_nm hvt_id
  dsimp only [lsρ, spqrProbeEnvAt] at hpre ⊢
  rw [spqrProbeEnvAtMpl_eq lsmpl, hb321, hb385, hrho_sto, hrho_tok, hrho_vt] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hlr_np, hx0, hx1, hx2, hx3⟩, hpre⟩
  have h321_ok : subroutine_ok c2Blk321NoSvc (cliElfMultiPlacement.base 321)
      (closureSplitSpecGen c2Blk385NoSvc (c2HwcapSubProg.withSvc noSyscalls)
        (c2GetauxvalSubProg.withSvc noSyscalls) f3StdLayout.libcAddr
        (cliElfMultiPlacement.base 385)
        (cliElfMultiPlacement.ρ tokenName) (cliElfMultiPlacement.ρ tokenStorageName)) :=
    c2Blk321_split_ok
  have hc := c2OnceCall_code
  have hext_once : ∀ pc, (c2OnceCallSubProg.withSvc noSyscalls).externAt? pc = none :=
    fun pc => withSvc_pureWords_externAt_none c2OnceCallAddr c2OnceCallWords noSyscalls pc
  have hext_cas : ∀ pc, (c2Cas4AcqSubProg.withSvc noSyscalls).externAt? pc = none :=
    fun pc => withSvc_pureWords_externAt_none c2Cas4AcqAddr c2Cas4AcqWords noSyscalls pc
  have hext_swp : ∀ pc, (c2Swp4RelSubProg.withSvc noSyscalls).externAt? pc = none :=
    fun pc => withSvc_pureWords_externAt_none c2Swp4RelAddr c2Swp4RelWords noSyscalls pc
  have hCL_cas0 : (c2Cas4AcqSubProg.withSvc noSyscalls).CodeLoaded s0.mem :=
    hCL_cas.of_base_code rfl rfl
  have hCL_swp0 : (c2Swp4RelSubProg.withSvc noSyscalls).CodeLoaded s0.mem :=
    hCL_swp.of_base_code rfl rfl
  have hCL_hw0 : (c2HwcapSubProg.withSvc noSyscalls).CodeLoaded s0.mem :=
    hCL_hw.of_base_code rfl rfl
  have hCL_get0 : (c2GetauxvalSubProg.withSvc noSyscalls).CodeLoaded s0.mem :=
    hCL_get.of_base_code rfl rfl
  have hsvc_cas : (c2Cas4AcqSubProg.withSvc noSyscalls).svc =
      (c2OnceCallSubProg.withSvc noSyscalls).svc := rfl
  have hsvc_swp : (c2Swp4RelSubProg.withSvc noSyscalls).svc =
      (c2OnceCallSubProg.withSvc noSyscalls).svc := rfl
  have hsvc_321 : c2Blk321NoSvc.svc = (c2OnceCallSubProg.withSvc noSyscalls).svc := c2Blk321_svc
  have hext_321 : ∀ pc, c2Blk321NoSvc.externAt? pc = none := c2Blk321_externAt_none
  change subroutine_ok _ c2Cas4AcqAddr (stdCas4Spec f3StdLayout.haveLseAtomicsAddr) at hcas_sub
  change subroutine_ok _ c2Swp4RelAddr (stdSwp4Spec f3StdLayout.haveLseAtomicsAddr) at hswp_sub
  generalize cliElfMultiPlacement.ρ tokenStorageName = storageAddr at h321_ok hpre ⊢
  generalize cliElfMultiPlacement.ρ tokenName = tokenAddr at h321_ok hx0 hpre ⊢
  generalize cliElfMultiPlacement.ρ spqrLazyLockVtableSym = vtableAddr at hx3 hpre ⊢
  generalize cliElfMultiPlacement.base 321 = closureAddr at h321_ok hpre ⊢
  generalize cliElfMultiPlacement.base 385 = initAddr at h321_ok hpre ⊢
  generalize c2OnceCallSubProg.withSvc noSyscalls = P_once at hc hext_once hsvc_cas hsvc_swp hsvc_321 ⊢
  generalize c2Cas4AcqSubProg.withSvc noSyscalls = P_cas at hcas_sub hext_cas hCL_cas0 hsvc_cas
  generalize c2Swp4RelSubProg.withSvc noSyscalls = P_swp at hswp_sub hext_swp hCL_swp0 hsvc_swp
  generalize c2HwcapSubProg.withSvc noSyscalls = P_hw at h321_ok hCL_hw0
  generalize c2GetauxvalSubProg.withSvc noSyscalls = P_get at h321_ok hCL_get0
  generalize c2Blk321NoSvc = P_321 at h321_ok hCL_321 hsvc_321 hext_321
  generalize c2Blk385NoSvc = P_385 at h321_ok hCL_385
  generalize c2OnceCallAddr = onceCallAddr at hpc hc ⊢
  generalize c2Cas4AcqAddr = cas4Addr at hc hcas_sub
  generalize c2Swp4RelAddr = swp4Addr at hc hswp_sub
  generalize f3StdLayout.haveLseAtomicsAddr = haveLseAddr at hcas_sub hswp_sub hpre ⊢
  generalize f3StdLayout.libcAddr = libcAddr at h321_ok hpre ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right] at hpre
  obtain ⟨haveLse, hpre⟩ := (satisfies_sepExists _ _).mp hpre
  obtain ⟨auxvAddr, hpre⟩ := (satisfies_sepExists _ _).mp hpre
  obtain ⟨entries, hpre⟩ := (satisfies_sepExists _ _).mp hpre
  have hpre_pure :
      s0.mem ⊨ ⌜MemWidth.isAligned .W32 (tokenAddr + 8#64) = true ∧ tokenAddr ≠ 0#64 ∧
        (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
        entries.find? (·.1 == 16#64) = some (16#64, 0x1b#64)⌝ ∗
        (((storageAddr ↦₈ 0xff#8) ∗ ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗
          (tokenAddr ↦₆₄ᵣ initAddr) ∗ ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗
          (haveLseAddr ↦₈ᵣ haveLse) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
          (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ (dataPtr ↦₆₄ slotPtr) ∗
          (slotPtr ↦₆₄ tokenAddr) ∗ stackAt s0.sp 0xa0) ∗ R) :=
    Satisfies.mono (by sep_entail) hpre
  rw [satisfies_pure_sepConj] at hpre_pure
  rcases hpre_pure with ⟨⟨halign, htok_nz, hnonull, hfind⟩, hpre_flat⟩
  refine ⟨(storageAddr ↦₈ 0xff#8) ∗ ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗
      (tokenAddr ↦₆₄ᵣ initAddr) ∗ ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗
      (haveLseAddr ↦₈ᵣ haveLse) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ (dataPtr ↦₆₄ slotPtr) ∗
      (slotPtr ↦₆₄ tokenAddr) ∗ stackAt s0.sp 0xa0, hpre_flat, ?_⟩
  dsimp only [OnceCall198Code, onceCall198Chunks, CodeChunks, CodeChunk.holds] at hc
  rcases hc with ⟨hw_entry, hi_cas, hw_mid, hw_call, hi_swp, hw_tbz, hw_epi⟩
  have hcode_entry : P_once.hasCode onceCallAddr onceCall198EntryWords := hw_entry
  have hf_cas : P_once.fetch (onceCallAddr + 0x60#64) =
      some (.bl (cas4Addr - (onceCallAddr + 0x60#64))) := by
    simpa using hi_cas.fetch_at_zero
  have hcode_mid : P_once.hasCode (onceCallAddr + 0x64#64)
      [0x6b16001f#32, 0x540004a0#32] := hw_mid
  have hcode_call : P_once.hasCode (onceCallAddr + 0xfc#64)
      [ 0x71000aff#32, 0x1a9f17e8#32, 0xf94012a9#32, 0xb9000bff#32,
        0x390033e8#32, 0x910023e1#32, 0xaa1403e0#32, 0xd63f0120#32,
        0xb9400be0#32, 0xaa1303e1#32 ] := hw_call
  have hf_swp : P_once.fetch (onceCallAddr + 0x124#64) =
      some (.bl (swp4Addr - (onceCallAddr + 0x124#64))) := by
    simpa using hi_swp.fetch_at_zero
  have hcode_tbz : P_once.hasCode (onceCallAddr + 0x128#64)
      [0x361000c0#32] := hw_tbz
  have hcode_epi : P_once.hasCode (onceCallAddr + 0x140#64)
      [ 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32,
        0x910183ff#32, 0xd65f03c0#32 ] := hw_epi
  refine SepWP.weaken_pre
    (P' := ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗ (haveLseAddr ↦₈ᵣ haveLse) ∗
      ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗ stackAt s0.sp 0x60 ∗
      ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
        (storageAddr ↦₈ 0xff#8) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
        (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackAt (s0.sp - 0x60#64) 0x40))
    (by rw [stackAt_a0_eq_60_40_s]; sep_entail) ?_
  rw [stackAt_eq_cells s0.sp 12]
  simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 12 (apply SepWP.exists_left; intro _)
  rw [pointsTo64_split32_sub s0.sp 88#64 84#64,
    pointsTo32_split8_sub_s s0.sp 84#64 83#64 82#64 81#64]
  refine sepWP_seq_keepsFrozen (mid := cas4Addr) ?_
  wp_steps 7
  refine step_ldar32_words_s onceCallAddr onceCall198EntryWords 7 (onceCallAddr + 0x20#64)
    halign (.gpr 22#5) hcode_entry (hnext := ?_)
  have hx1_bit0 : (s0.readReg64 .x1).getLsbD 0 = true := by
    have h0 := congrArg (fun x : BitVec 32 => x.getLsbD 0) hx1
    simpa [BitVec.truncate, BitVec.getLsbD_setWidth] using h0
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
  intro hkf_c1
  refine sepWP_call_otherProg (P2 := P_cas)
    (ret_pc := onceCallAddr + 0x64#64)
    (x := (haveLse, tokenAddr + 8#64, 3#32, 3#32, 1#32))
    (F := ?_)
    hext_once hext_cas hsvc_cas
    (hCL_cas0.of_keepsFrozen hkf_c1) hcas_sub
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by
      simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢
      simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x60#64 hsp)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [stdCas4Spec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm], halign⟩, ?_⟩
      exact Satisfies.mono (by sep_frame) hm)
    rfl rfl rfl
    fun s1 hpc1 hrun1 hsp1 hcs1 hkf_s1 => ?_
  dsimp only [stdCas4Spec]
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_1, hstd1⟩
  have hx19_1 : s1.readReg64 .x19 = tokenAddr + 8#64 := by
    rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hx20_1 : s1.readReg64 .x20 = dataPtr := by
    rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
  have hx21_1 : s1.readReg64 .x21 = vtableAddr := by
    rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]
  have hx22_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 := by
    have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this
  have hx23_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 := by
    have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this
  have hsp1_eq : s1.sp = s0.sp - 0x60#64 := by
    rw [hsp1]; simp [wp_norm, arm64_norm, bv_lin_norm]
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s0.spAligned_sub 0x60#64 hsp
  have hstd_s1 : StdFieldsPreserved s0 s1 :=
    StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm]) hstd1.toFields
  have hkf01 : s0.mem.KeepsFrozen s1.mem := hkf_c1.trans hkf_s1
  refine sepWP_seq_keepsFrozen (mid := closureAddr) ?_
  wp_steps; wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
  intro hkf_c2
  have hkf02 : s0.mem.KeepsFrozen _ := hkf01.trans hkf_c2
  have hfin4 : (s0.sp - 0x58#64) + 4#64 = s0.sp - 0x54#64 := by bv_lin
  refine sepWP_call_otherProg (P2 := P_321)
    (ret_pc := onceCallAddr + 0x11c#64)
    (x := (dataPtr, slotPtr, s0.sp - 0x58#64, 0x1b#64, auxvAddr, entries))
    (F := ?_)
    hext_once hext_321 hsvc_321
    (hCL_321.of_keepsFrozen hkf02) h321_ok
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp1_al)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [closureSplitSpecGen]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hCL_385.of_keepsFrozen hkf02,
        hCL_hw0.of_keepsFrozen hkf02,
        hCL_get0.of_keepsFrozen hkf02,
        by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm, bv_lin_norm],
        htok_nz, hnonull, hfind⟩, ?_⟩
      simp only [wp_norm, arm64_norm, hsp1_eq, hfin4]
      exact Satisfies.mono (by sep_frame) hm)
    rfl rfl rfl
    fun s2 hpc2 hrun2 hsp2 hcs2 hkf_s2 => ?_
  dsimp only [closureSplitSpecGen]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hstd2
  have hx19_2 : s2.readReg64 .x19 = tokenAddr + 8#64 := by
    rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
  have hsp2_eq : s2.sp = s0.sp - 0x60#64 := by
    rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s0.spAligned_sub 0x60#64 hsp
  have hkf0_s2 : s0.mem.KeepsFrozen s2.mem := hkf02.trans hkf_s2
  refine sepWP_seq_keepsFrozen (mid := swp4Addr) ?_
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun2])
  intro hkf_c3
  have hkf03 : s0.mem.KeepsFrozen _ := hkf0_s2.trans hkf_c3
  refine sepWP_call_otherProg (P2 := P_swp)
    (ret_pc := onceCallAddr + 0x128#64)
    (x := (haveLse, tokenAddr + 8#64, 1#32, 0#32))
    (F := ?_)
    hext_once hext_swp hsvc_swp
    (hCL_swp0.of_keepsFrozen hkf03) hswp_sub
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun2])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp2_eq] using hsp2_al)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [stdSwp4Spec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm], halign⟩, ?_⟩
      exact Satisfies.mono (by sep_frame) hm)
    rfl rfl rfl
    fun s3 hpc3 hrun3 hsp3 hcs3 _ => ?_
  dsimp only [stdSwp4Spec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_3, hstd3⟩
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_3
  have hsp3_eq : s3.sp = s0.sp - 0x60#64 := by
    rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by
    simp only [State.spAligned, hsp3_eq]; exact s0.spAligned_sub 0x60#64 hsp
  wp_steps; wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · refine (satisfies_sepExists _ _).mpr ⟨haveLse,
      (satisfies_sepExists _ _).mpr ⟨auxvAddr,
        (satisfies_sepExists _ _).mpr ⟨entries, ?_⟩⟩⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨StdFieldsPreserved.trans hstd_s1
        (StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm])
          (StdFieldsPreserved.trans hstd2
            (StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm])
              (StdFieldsPreserved.trans hstd3.toFields
                (by simp [StdFieldsPreserved, wp_norm, arm64_norm]))))), ?_⟩
    rw [pure_sepConj_of_true ⟨halign, htok_nz, hnonull, hfind⟩]
    have hhw1 : spqrStorageOfHwcap 0x1b#64 = 1#8 := rfl
    simp only [wp_norm, arm64_norm, hsp1_eq, hfin4, hhw1] at hm
    replace hm := combine_cell_byte4_sat_s s0.sp 88#64 84#64 83#64 82#64 81#64 hm
    rw [stackAt_a0_eq_60_40_s s0.sp, stackAt_eq_cells s0.sp 12]
    simp only [Nat.reduceMul]; cells_unfold
    simp only [sepExists_sepConj_left]
    change s3.mem ⊨ _
    sep_entail
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with
      ⟨_, _, _, _, _, _, g25_1, g26_1, g27_1, g28_1, _, gv_1⟩
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with
      ⟨_, _, _, _, _, _, g25_2, g26_2, g27_2, g28_2, _, gv_2⟩
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with
      ⟨_, _, _, _, _, _, g25_3, g26_3, g27_3, g28_3, _, gv_3⟩
    simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm,
      g25_1, g26_1, g27_1, g28_1, gv_1,
      g25_2, g26_2, g27_2, g28_2, gv_2,
      g25_3, g26_3, g27_3, g28_3, gv_3]

end CpuProbeSplitExec

/-- Full `subroutine_ok` on `emptyStdProg` for `withStateGuard (SpqrProbeGuard lsmpl) spqrOnceCallGhostSpec`. -/
theorem spqrOnceCall_emptyStdProg_ok [LibsignalPlacement] :
    subroutine_ok emptyStdProg c2OnceCallAddr
      (withStateGuard (SpqrProbeGuard lsmpl) spqrOnceCallGhostSpec) := by
  apply subroutine_ok_of_steps_outcome
  rintro ⟨dataPtr, slotPtr⟩ R s0 hpc hrun hpre hsp _hCL_empty
  have hG : SpqrProbeGuard lsmpl s0 := by
    dsimp only [withStateGuard] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1
  have hCL_once : (c2OnceCallSubProg.withSvc noSyscalls).CodeLoaded s0.mem :=
    hG.1.of_base_code rfl rfl
  obtain ⟨sf, hsteps_once, hout⟩ :=
    subroutine_ok_elim_steps_outcome c2OnceCall_noSvc_ok
      (dataPtr, slotPtr) R s0 hpc hrun hpre hsp hCL_once
  have hsteps_empty_no : Steps (emptyStdProg.withSvc noSyscalls) s0 sf :=
    Steps.of_sameHooks (P := emptyStdProg.withSvc noSyscalls)
      (fun pc => (withSvc_pureWords_externAt_none c2OnceCallAddr c2OnceCallWords noSyscalls pc).trans
        (show (emptyStdProg.withSvc noSyscalls).externAt? pc = none from rfl).symm)
      rfl hsteps_once
  rcases hout with ⟨⟨hpc_f, hsp_f, hrun_f⟩, hcs_f, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨hsteps_std, hns⟩ :=
      steps_lift_noSyscalls emptyStdProg_externAt_none emptyStdProg_svc hsteps_empty_no hrun_f
    have horacle : sf.oracle = s0.oracle :=
      Steps.oracle_eq_of_standard emptyStdProg_svc emptyStdProg_externAt_none hsteps_std
    have hsymtab : sf.symtab = s0.symtab := hsteps_std.symtab_eq
    dsimp only [withStateGuard, spqrOnceCallStdSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hstd, hpost_mem⟩
    have hvm : VmPreserved s0 sf :=
      ⟨⟨hstd.2.2.2.2.2, hstd.2.2.2.2.1, hstd.2.2.1⟩,
       hns.2.2.2.2.1,
       fun a => congrFun hns.2.1 a,
       FdsHiFrame.of_fs_eq hstd.1⟩
    have hacp : AllocCallPreserved s0 sf :=
      ⟨hstd.1, hstd.2.1, hstd.2.2.2.1, hstd.2.2.1, hstd.2.2.2.2.2, horacle, hsymtab⟩
    refine ⟨sf, hsteps_std, Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, hcs_f, ?_⟩⟩
    dsimp only [withStateGuard, spqrOnceCallGhostSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvm, hacp, hstd.2.1⟩, hpost_mem⟩
  · exact (not_satisfies_false_sepConj hp).elim
  · exact (not_satisfies_false_sepConj he).elim
  · exact (not_satisfies_false_sepConj ho).elim

/-! ## 6. `spqrOnceCallGhost`, Unconditional `HookOk` & `GhostRowSpecOk` -/

private theorem keepFsTrace_spqrOnceCallFallback_eq [LibsignalPlacement] :
    keepFsTrace spqrOnceCallFallback = spqrOnceCallFallback := by
  funext s0
  unfold keepFsTrace
  cases h : spqrOnceCallFallback s0
  have hfs := spqrOnceCallFallback_fs s0
  have htr := spqrOnceCallFallback_trace s0
  rw [h] at hfs htr
  dsimp only at hfs htr
  subst hfs; subst htr
  rfl

/-- `stripS`-invariant companion of `spqrOnceCallGhostSpec` omitting `mem.perm` equality inside
    `post` (`mem.perm` equality is recovered unconditionally across `linkedCallHookG` via
    `perm_eq_of_stripExecOutside_keepsFrozen`). -/
@[expose] def spqrOnceCallNoPermSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64) where
  pre := spqrOnceCallGhostSpec.pre
  post := fun (dataPtr, slotPtr) s0 sf =>
    ⌜sf.brkStart = s0.brkStart ∧ sf.brk = s0.brk ∧ sf.physMemAvail = s0.physMemAvail ∧
      AllocCallPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
    (lsρ tokenStorageName ↦₈ 1#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
    spqrProbeEnvAt ∗
    (dataPtr ↦₆₄ slotPtr) ∗
    (slotPtr ↦₆₄ 0#64) ∗
    stackAt s0.sp 0xa0
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem spqrOnceCall_noPerm_emptyStdProg_ok [LibsignalPlacement] :
    subroutine_ok emptyStdProg c2OnceCallAddr
      (withStateGuard (SpqrProbeGuard lsmpl) spqrOnceCallNoPermSpec) := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hpre hsp hCL
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome spqrOnceCall_emptyStdProg_ok x R s0 hpc hrun hpre hsp hCL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withStateGuard, spqrOnceCallGhostSpec, spqrOnceCallNoPermSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.1.1, hpost.1.1.1.2.1, hpost.1.1.2.1, hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩
  · exact (not_satisfies_false_sepConj hp).elim
  · exact (not_satisfies_false_sepConj he).elim
  · exact (not_satisfies_false_sepConj ho).elim

private theorem spqrOnceCallFallback_noPerm_ok [LibsignalPlacement] :
    HookOk spqrOnceCallFallback spqrOnceCallNoPermSpec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := spqrOnceCallFallback_ok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [spqrOnceCallGhostSpec, spqrOnceCallNoPermSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.1.1, hpost.1.1.1.2.1, hpost.1.1.2.1, hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩
  · exact (not_satisfies_false_sepConj hp).elim
  · exact (not_satisfies_false_sepConj he).elim
  · exact (not_satisfies_false_sepConj ho).elim

private theorem specStripSInvariant_spqrOnceCallNoPerm [LibsignalPlacement]
    (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep spqrOnceCallNoPermSpec :=
  ⟨fun _ s => by cases s; rfl,
   fun _ s0 sf => by cases s0; cases sf; rfl,
   fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem specPreservesFsTrace_spqrOnceCallNoPerm [LibsignalPlacement] :
    SpecPreservesFsTrace spqrOnceCallNoPermSpec := by
  intro _ _ s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [spqrOnceCallNoPermSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs := hpost.1.2.2.2.1.1
    have htr := hpost.1.2.2.2.2
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact (not_satisfies_false_sepConj hp).elim
  · exact (not_satisfies_false_sepConj he).elim
  · exact (not_satisfies_false_sepConj ho).elim

private theorem spqrOnceCallNoPerm_pre_setPC [LibsignalPlacement]
    (x : BitVec 64 × BitVec 64) (s : State) (pc : BitVec 64) :
    spqrOnceCallNoPermSpec.pre x (s.setPC pc) = spqrOnceCallNoPermSpec.pre x s := by
  cases s; rfl

private theorem spqrOnceCallNoPerm_out_setPC [LibsignalPlacement]
    (x : BitVec 64 × BitVec 64) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome spqrOnceCallNoPermSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome spqrOnceCallNoPermSpec x R s0 sf := by
  cases s0; cases sf; exact h

/-- `W`-independent linked ghost-call hook for `lsSpqrOnceCallSym` (`spqrOnceCallSym`). -/
@[expose] noncomputable def spqrOnceCallGhost [LibsignalPlacement] : State → State :=
  linkedCallHookG
    (SpqrProbeGuard lsmpl)
    (keepSpqrOnceCall lsmpl)
    emptyStdProg
    emptyStdProg
    c2OnceCallAddr
    spqrOnceCallNoPermSpec
    spqrOnceCallFallback

theorem spqrOnceCallGhost_fs [LibsignalPlacement] (s0 : State) :
    (spqrOnceCallGhost s0).fs = s0.fs :=
  linkedCallHookG_fs _ _ _ _ _ _ _ s0

theorem spqrOnceCallGhost_fsT [LibsignalPlacement] :
    HookFsTraced IsFsC spqrOnceCallGhost :=
  linkedCallHookG_fsT _ _ _ _ _ _ _

theorem spqrOnceCallGhost_preserves_execFrozen [LibsignalPlacement] {u : State}
    (hfr : ExecFrozen u.mem) :
    ExecFrozen (spqrOnceCallGhost u).mem := by
  unfold spqrOnceCallGhost
  rw [linkedCallHookG_eq_conj]
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
    · rw [keepFsTrace_spqrOnceCallFallback_eq]
      exact ExecFrozen.of_perm_eq hfr (spqrOnceCallFallback_perm u)
  · exact hfr

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · have hst := hstrip a
    rw [ProofLib.strip_perm, ProofLib.strip_perm] at hst
    have hfr0_a := hfr0 a
    have hfrf_a := hfrf a
    unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a <;> cases hpf : mf.perm a
    · rfl
    · rw [hp0, hpf] at hst; nomatch hst
    · rw [hp0, hpf] at hst; nomatch hst
    · rename_i p0 pf
      rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
      simp only [Option.map_some, Option.some.injEq] at hst
      have hx0 : p0.x = false := by
        cases hx : p0.x
        · rfl
        · have ⟨hr0, hw0⟩ := hfr0_a (by simp [Option.x, hx])
          exact False.elim (hfrozen0 (by simp [Option.r, Option.w] at hr0 hw0; simp [hr0, hw0]))
      have hsp0 : ProofLib.stripPerm (keep a) p0 = p0 := by
        unfold ProofLib.stripPerm; rw [hx0]; simp
      rw [hsp0] at hst
      have hxf : pf.x = false := by
        cases hx : pf.x
        · rfl
        · have ⟨hrf, hwf⟩ := hfrf_a (by simp [Option.x, hx])
          simp only [Option.r, Option.w] at hrf hwf
          have hr_eq : (ProofLib.stripPerm (keep a) pf).r = true := by
            unfold ProofLib.stripPerm; cases keep a <;> simp [hx, hrf]
          have hw_eq : (ProofLib.stripPerm (keep a) pf).w = false := by
            unfold ProofLib.stripPerm; cases keep a <;> simp [hx, hwf]
          rw [hst] at hr_eq hw_eq
          exact False.elim (hfrozen0 (by simp [hr_eq, hw_eq]))
      have hspf : ProofLib.stripPerm (keep a) pf = pf := by
        unfold ProofLib.stripPerm; rw [hxf]; simp
      rw [hspf] at hst
      exact congrArg some hst

private theorem linkedCallHookG_perm_and_trace {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool}
    {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec specFull : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOkFull : subroutine_ok P_sub entryTarget (withStateGuard Guard specFull))
    (hPreEq : specFull.pre = spec.pre)
    (hInv : SpecStripSInvariant keep spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hPostPermTr : ∀ x R s0 sf,
      SubroutineOutcome (withStateGuard Guard specFull) x R s0 sf →
      Returned s0 sf ∧
      (∀ a : BitVec 64, sf.mem.perm a = s0.mem.perm a) ∧
      sf.trace = s0.trace)
    (hFbPerm : ∀ s0 a, ((keepFsTrace fallback s0).mem).perm a = s0.mem.perm a)
    (hFbTr : ∀ s0, (keepFsTrace fallback s0).trace = s0.trace)
    (s0 : State) :
    (∀ a : BitVec 64,
      (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0).mem.perm a =
        s0.mem.perm a) ∧
    (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0).trace = s0.trace := by
  classical
  have hEq := linkedCallHookG_eq_conj Guard keep P_real P_sub entryTarget spec fallback s0
  rw [hEq]
  by_cases hPre : ActiveRealPre spec s0
  · rw [dite_eq_left_of_eq_true (eq_true hPre)]
    by_cases hReal : Guard s0 ∧
        LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ActiveRealRun
          keep P_real P_sub entryTarget s0
    · rw [dite_eq_left_of_eq_true (eq_true hReal)]
      rcases hPre with ⟨hrun, hsp, x, R, hpre⟩
      let s1 := s0.setPC entryTarget
      let s1' := stripS keep s1
      have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
        change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
        rwa [hPrePC x s0 entryTarget]
      have hs1'_pre : s1'.mem ⊨ specFull.pre x s1' ∗ R := by
        have hsat :=
          LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.satisfies_stripExecOutside
            keep hs1_pre
        rw [← hInv.pre_eq x s1] at hsat
        rwa [hPreEq]
      have hs1'_preG : s1'.mem ⊨ (withStateGuard Guard specFull).pre x s1' ∗ R := by
        dsimp only [withStateGuard]
        rw [sepConj_assoc, pure_sepConj_of_true (hGuardStrip s0 hReal.2.1 hReal.1)]
        exact hs1'_pre
      obtain ⟨sf', hsteps', hout'⟩ :=
        subroutine_ok_elim_steps_outcome hOkFull x R s1' rfl hrun hs1'_preG hsp hReal.2.2.2.1
      obtain ⟨hret', hperm', htr'⟩ := hPostPermTr x R s1' sf' hout'
      have hr0 : Returned s0 sf' := ⟨hret'.1, hret'.2.1, hret'.2.2⟩
      obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
        LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.stepsUntil_of_stripS_standard
          (s0 := s0) hsvc_real hsvc_sub hreal_no
          (fun pc f he => nomatch hsub_no pc ▸ he)
          hReal.2.2.1 hsteps' (Or.inl hr0) (by rw [hr0.2.2]; decide) s1 rfl hReal.2.1
      have hchoose := Classical.choose_spec hReal.2.2.2.2
      have hdet : Classical.choose hReal.2.2.2.2 = sf :=
        StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
      rw [hdet]
      rw [hsf_eq] at hperm' htr'
      exact ⟨perm_eq_of_stripExecOutside_keepsFrozen hReal.2.1 hfr_sf
        huntil.toSteps.keepsFrozen hperm', htr'⟩
    · rw [dite_eq_right_of_eq_false (eq_false hReal)]
      exact ⟨hFbPerm s0, hFbTr s0⟩
  · rw [dite_eq_right_of_eq_false (eq_false hPre)]
    exact ⟨fun _ => rfl, rfl⟩

theorem spqrOnceCallGhost_perm_and_trace [LibsignalPlacement] (s0 : State) :
    (∀ a : BitVec 64, (spqrOnceCallGhost s0).mem.perm a = s0.mem.perm a) ∧
    (spqrOnceCallGhost s0).trace = s0.trace :=
  linkedCallHookG_perm_and_trace (spec := spqrOnceCallNoPermSpec)
    emptyStdProg_svc emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    emptyStdProg_externAt_none
    (spqrProbeGuard_stripS lsmpl c2OnceCallAddr)
    spqrOnceCall_emptyStdProg_ok
    rfl
    (specStripSInvariant_spqrOnceCallNoPerm (keepSpqrOnceCall lsmpl))
    spqrOnceCallNoPerm_pre_setPC
    (fun _ _ s1' sf' hout => by
      rcases hout with ⟨hret, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
      · dsimp only [withStateGuard, spqrOnceCallGhostSpec] at hpost
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
        exact ⟨hret, hpost.1.1.2.2.1, hpost.1.2.2⟩
      · exact (not_satisfies_false_sepConj hp).elim
      · exact (not_satisfies_false_sepConj he).elim
      · exact (not_satisfies_false_sepConj ho).elim)
    (fun s a => by rw [keepFsTrace_spqrOnceCallFallback_eq]; exact spqrOnceCallFallback_perm s a)
    (fun s => by rw [keepFsTrace_spqrOnceCallFallback_eq]; exact spqrOnceCallFallback_trace s)
    s0

theorem spqrOnceCallGhost_trace [LibsignalPlacement] (s0 : State) :
    (spqrOnceCallGhost s0).trace = s0.trace :=
  (spqrOnceCallGhost_perm_and_trace s0).2

theorem spqrOnceCallGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed spqrOnceCallGhost :=
  hookNoAllocFailed_of_trace_eq _ spqrOnceCallGhost_trace

/-- Unconditional `HookOk`: `spqrOnceCallGhost` satisfies `spqrOnceCallGhostSpec`
    for every `[LibsignalPlacement]`. -/
theorem spqrOnceCallGhost_ok [LibsignalPlacement] :
    HookOk spqrOnceCallGhost spqrOnceCallGhostSpec := by
  have hNoPerm : HookOk spqrOnceCallGhost spqrOnceCallNoPermSpec :=
    hookOk_linkedCallHookG
      emptyStdProg_svc emptyStdProg_svc
      (fun pc _ => emptyStdProg_externAt_none pc)
      emptyStdProg_externAt_none
      (spqrProbeGuard_stripS lsmpl c2OnceCallAddr)
      spqrOnceCall_noPerm_emptyStdProg_ok
      (specStripSInvariant_spqrOnceCallNoPerm (keepSpqrOnceCall lsmpl))
      specPreservesFsTrace_spqrOnceCallNoPerm
      spqrOnceCallNoPerm_pre_setPC
      spqrOnceCallNoPerm_out_setPC
      (by rw [keepFsTrace_spqrOnceCallFallback_eq]; exact spqrOnceCallFallback_noPerm_ok)
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hNoPerm x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [spqrOnceCallNoPermSpec, spqrOnceCallGhostSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hbrkS, hbrk, hphys, hacp, htr⟩, hmem⟩
    have hperm := (spqrOnceCallGhost_perm_and_trace s0).1
    have hvm : VmPreserved s0 (spqrOnceCallGhost s0) :=
      ⟨⟨hbrkS, hbrk, hacp.2.2.2.1⟩, hphys, hperm, FdsHiFrame.of_fs_eq hacp.1⟩
    exact ⟨⟨hvm, hacp, htr⟩, hmem⟩
  · exact (not_satisfies_false_sepConj hp).elim
  · exact (not_satisfies_false_sepConj he).elim
  · exact (not_satisfies_false_sepConj ho).elim

private theorem elimIfFalse {c : Bool} {A B : Prop} (hc : c = false) (hb : B) :
    (if c then A else B) := by
  rw [hc]; exact hb

private theorem elimIfTrue {c : Bool} {A B : Prop} (hc : c = true) (ha : A) :
    (if c then A else B) := by
  rw [hc]; exact ha

set_option maxRecDepth 400000 in
private theorem extraRowSpec_spqrOnceCall [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsSpqrOnceCallSym f := by
  unfold ExtraRowSpec
  iterate 37 refine elimIfFalse (by rfl_kernel) ?_
  exact elimIfTrue (by rfl_kernel) (SpqrOnceCallRowSpec.intro f)

set_option maxRecDepth 400000 in
/-- Unconditional `GhostRowSpecOk` matching the `lsSpqrOnceCallSym` arm of `ExtraRowSpec`. -/
theorem spqrOnceCallGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsSpqrOnceCallSym spqrOnceCallGhost where
  fs_eq := spqrOnceCallGhost_fs
  fsT := spqrOnceCallGhost_fsT
  rowSpec := extraRowSpec_spqrOnceCall spqrOnceCallGhost

/-! ## 7. `LsRetAddrNoProbe` Disjointness, `StepsVisitedIn`, & `GhostRowReplayOn` -/

set_option maxRecDepth 400000 in
private noncomputable def checkNoProbeDisjointB : Bool :=
  let rxLo := f3RxSegBase.toNat
  let b321 := (cliElfBlockBases.getD 321 0#64).toNat
  let l321 := lsLen 321
  let b385 := (cliElfBlockBases.getD 385 0#64).toNat
  let l385 := lsLen 385
  Nat.ble (b321 + l321) rxLo &&
  Nat.ble (b385 + l385) rxLo &&
  (List.range 624).all fun j =>
    let bj := (cliElfBlockBases.getD j 0#64).toNat
    let lj := lsLen j
    Nat.ble (bj + lj) rxLo &&
    (Nat.beq j 321 || Nat.ble (bj + lj) b321 || Nat.ble (b321 + l321) bj) &&
    (Nat.beq j 385 || Nat.ble (bj + lj) b385 || Nat.ble (b385 + l385) bj)

set_option maxRecDepth 400000 in
private theorem checkNoProbeDisjoint_ok : checkNoProbeDisjointB = true := by
  rfl_kernel

private theorem progKeep_false_of_lt_base {P : Program} {lr : BitVec 64}
    (hlt : lr.toNat < P.base.toNat)
    (hhi : P.base.toNat + P.code.length < 2 ^ 64) :
    progKeep P lr = false := by
  unfold progKeep
  rw [decide_eq_false_iff_not]
  have hsub : (lr - P.base).toNat = 2 ^ 64 + lr.toNat - P.base.toNat := by
    rw [BitVec.toNat_sub]; omega
  omega

private theorem progKeep_false_of_disjoint {P : Program} {lr : BitVec 64}
    (hdisj : lr.toNat < P.base.toNat ∨ P.base.toNat + P.code.length ≤ lr.toNat)
    (hhi : P.base.toNat + P.code.length < 2 ^ 64) :
    progKeep P lr = false := by
  rcases hdisj with hlt | hge
  · exact progKeep_false_of_lt_base hlt hhi
  · unfold progKeep
    rw [decide_eq_false_iff_not]
    have hsub : (lr - P.base).toNat = lr.toNat - P.base.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    omega

theorem keepSpqrOnceCall_false_of_lsRetAddrNoProbe [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddrNoProbe lr) :
    keepSpqrOnceCall lsmpl lr = false := by
  rcases hRet with ⟨j, hj, hne321, hne385, o, ho, rfl⟩
  have hok := checkNoProbeDisjoint_ok
  unfold checkNoProbeDisjointB at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  rcases hok with ⟨⟨hb321_lt, hb385_lt⟩, hall⟩
  have hlen624 := ls_blocks_len_624
  have hjlen : j < libsignalSessionLib.blocks.length := by rw [hlen624]; exact hj
  have hbase_j : lsmpl.base j = cliElfMultiPlacement.base j :=
    (cliElf_linkedAt_unique hLs).1 j hjlen
  have hdef_j : cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 := rfl
  have hj_row := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hj_row
  rcases hj_row with ⟨⟨h_lt_rx, h_d321⟩, h_d385⟩
  rw [hbase_j, hdef_j]
  have hrx_bound : f3RxSegBase.toNat < 2 ^ 48 := by decide
  have hlr_nat : ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o).toNat =
      (cliElfBlockBases.getD j 0#64).toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlt_rx : ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o).toNat < f3RxSegBase.toNat := by
    omega
  have ha1 : f3RxSegBase.toNat ≤ c2OnceCallSubProg.base.toNat ∧
      c2OnceCallSubProg.base.toNat + c2OnceCallSubProg.code.length < 2 ^ 64 :=
    ⟨by decide, Nat.blt_eq.mp (by rfl_kernel)⟩
  have ha2 : f3RxSegBase.toNat ≤ c2Cas4AcqSubProg.base.toNat ∧
      c2Cas4AcqSubProg.base.toNat + c2Cas4AcqSubProg.code.length < 2 ^ 64 :=
    ⟨by decide, Nat.blt_eq.mp (by rfl_kernel)⟩
  have ha3 : f3RxSegBase.toNat ≤ c2Swp4RelSubProg.base.toNat ∧
      c2Swp4RelSubProg.base.toNat + c2Swp4RelSubProg.code.length < 2 ^ 64 :=
    ⟨by decide, Nat.blt_eq.mp (by rfl_kernel)⟩
  have ha4 : f3RxSegBase.toNat ≤ c2HwcapSubProg.base.toNat ∧
      c2HwcapSubProg.base.toNat + c2HwcapSubProg.code.length < 2 ^ 64 :=
    ⟨by decide, Nat.blt_eq.mp (by rfl_kernel)⟩
  have ha5 : f3RxSegBase.toNat ≤ c2GetauxvalSubProg.base.toNat ∧
      c2GetauxvalSubProg.base.toNat + c2GetauxvalSubProg.code.length < 2 ^ 64 :=
    ⟨by decide, Nat.blt_eq.mp (by rfl_kernel)⟩
  have h1 : progKeep c2OnceCallSubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false :=
    progKeep_false_of_lt_base (by omega) ha1.2
  have h2 : progKeep c2Cas4AcqSubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false :=
    progKeep_false_of_lt_base (by omega) ha2.2
  have h3 : progKeep c2Swp4RelSubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false :=
    progKeep_false_of_lt_base (by omega) ha3.2
  have h4 : progKeep c2HwcapSubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false :=
    progKeep_false_of_lt_base (by omega) ha4.2
  have h5 : progKeep c2GetauxvalSubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false :=
    progKeep_false_of_lt_base (by omega) ha5.2
  have h321_code_len : c2Blk321SubProg.code.length ≤ lsLen 321 := by decide
  have h385_code_len : c2Blk385SubProg.code.length ≤ lsLen 385 := by decide
  have h6 : progKeep c2Blk321SubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false := by
    have hbase321 : c2Blk321SubProg.base = cliElfBlockBases.getD 321 0#64 := rfl
    refine progKeep_false_of_disjoint ?_ (by rw [hbase321]; omega)
    rw [hbase321]
    rcases h_d321 with (rfl | hle) | hge
    · exact False.elim (hne321 rfl)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have h7 : progKeep c2Blk385SubProg
      ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o) = false := by
    have hbase385 : c2Blk385SubProg.base = cliElfBlockBases.getD 385 0#64 := rfl
    refine progKeep_false_of_disjoint ?_ (by rw [hbase385]; omega)
    rw [hbase385]
    rcases h_d385 with (rfl | hle) | hge
    · exact False.elim (hne385 rfl)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unfold keepSpqrOnceCall
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl

theorem spqrOnceCallGhost_keepLr_false_of_noException [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) {u : State}
    (hnoex : ∀ msg, (spqrOnceCallGhost u).status ≠ .Exception msg) :
    keepSpqrOnceCall lsmpl (u.readReg64 .lr) = false := by
  have hAct : ActiveRealPre spqrOnceCallNoPermSpec u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  rcases hAct with ⟨_, _, ⟨_, _⟩, R, hpre⟩
  dsimp only [spqrOnceCallNoPermSpec, spqrOnceCallGhostSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact keepSpqrOnceCall_false_of_lsRetAddrNoProbe hLs hpre.1.1

/-- `h2fsgen_StepsVisitedIn` witness on `emptyStdProg` for `spqrOnceCallGhost` (consumed by
    `StepsStrictAvoid` in `ElfSampleNttStuckDivergeExtraWideTable`). -/
theorem spqrOnceCallGhost_visitedIn [LibsignalPlacement] {u : State}
    (hG : SpqrProbeGuard lsmpl u)
    (hnoex : ∀ msg, (spqrOnceCallGhost u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) :
    h2fsgen_StepsVisitedIn (keepSpqrOnceCall lsmpl) emptyStdProg (u.setPC c2OnceCallAddr)
        (spqrOnceCallGhost u) ∧
      ExecFrozen (spqrOnceCallGhost u).mem := by
  have hAct : ActiveRealPre spqrOnceCallNoPermSpec u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr : keepSpqrOnceCall lsmpl (u.readReg64 .lr) = false :=
    spqrOnceCallGhost_keepLr_false_of_noException hG.2.2.2.2.2.2.2 hnoex
  exact linkedCallHookG_visitedIn
    emptyStdProg_svc emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    emptyStdProg_externAt_none
    (spqrProbeGuard_stripS lsmpl c2OnceCallAddr)
    spqrOnceCall_noPerm_emptyStdProg_ok
    (specStripSInvariant_spqrOnceCallNoPerm (keepSpqrOnceCall lsmpl))
    specPreservesFsTrace_spqrOnceCallNoPerm
    spqrOnceCallNoPerm_pre_setPC
    spqrOnceCallNoPerm_out_setPC
    hG hAct hFr hlr
    (emptyStdProg_codeLoaded _)

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u; dsimp only [State.setPC] at hpc ⊢; subst hpc; rfl

/-- Generic-`InvS` `GhostRowReplayOn` for `lsSpqrOnceCallSym` (`entryGuard := fun _ => True`). -/
theorem spqrOnceCallGhost_rowReplayOn [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hTargetEq : libsignalSessionLib.resolve lsmpl lsSpqrOnceCallSym = c2OnceCallAddr)
    (hGuard : ∀ u : State, InvS u → SpqrProbeGuard lsmpl u)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepSpqrOnceCall lsmpl pc = true →
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn lsmpl mmpl InvS EG lsSpqrOnceCallSym (fun _ => True) spqrOnceCallGhost where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨spqrOnceCallGhost_preserves_execFrozen hfr, spqrOnceCallGhost_fs u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hRealStubNone :
        (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W).externAt?
          (libsignalSessionLib.resolve lsmpl lsSpqrOnceCallSym) = none := by
      rw [hTargetEq]
      exact hRealHullNoExt W (keepSpqrOnceCall_entry lsmpl)
    refine ⟨hRealStubNone, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have _ := hrun
    obtain ⟨hvis, hfr_fu⟩ := spqrOnceCallGhost_visitedIn (hGuard u hInvU) hnoex hfr
    have hStepsSet :
        Steps (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC c2OnceCallAddr) (spqrOnceCallGhost u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepSpqrOnceCall lsmpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
        rfl
        (fun pc _ => emptyStdProg_externAt_none pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)] at hStepsSet
    exact ⟨hStepsSet, hfr_fu, hInvKeep u (spqrOnceCallGhost u) hInvU hkf (spqrOnceCallGhost_fs u)⟩

/-- Full per-row `GhostRowOk` bundle for `lsSpqrOnceCallSym` (`entryGuard := guardOf lsSpqrOnceCallSym`). -/
theorem spqrOnceCallGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hTargetEq : libsignalSessionLib.resolve lsmpl lsSpqrOnceCallSym = c2OnceCallAddr)
    (hGuard : ∀ u : State, InvS u → SpqrProbeGuard lsmpl u)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepSpqrOnceCall lsmpl pc = true →
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowOk lsmpl mmpl InvS EG lsSpqrOnceCallSym (guardOf lsSpqrOnceCallSym)
      spqrOnceCallGhost := by
  have hRep := spqrOnceCallGhost_rowReplayOn mmpl InvS EG hLs hTargetEq hGuard hInvKeep hRealHullNoExt
  exact ⟨spqrOnceCallGhost_rowSpecOk,
    ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays

