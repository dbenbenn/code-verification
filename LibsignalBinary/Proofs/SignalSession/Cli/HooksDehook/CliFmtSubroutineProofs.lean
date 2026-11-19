/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.AsciiNum
public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import GeneratedLean.LibsignalSessionPlacedObjShard10

/-!
# `.rodata`-Guarded Subroutine Proofs for `lsFmtWriteSym` and `lsFormatInnerSym`

Subroutine-correctness proofs discharging `cliFmtWriteProtoAddrSpec` and
`cliFormatInnerLsCallSpec` (`CliFmtGhostSpecs`) against placed `core::fmt::write`,
`alloc::fmt::format::format_inner`, `<String as fmt::Write>`, `core::fmt` integer/string
formatters, `<spqr::Error as Display>::fmt` (block `412`), and rebased `libsignalSessionLib`
sub-formatters:
- Block `217`: `<core::num::nonzero::NonZero<u8> as core::fmt::Display>::fmt` (40 B)
- Block `214`: `<libsignal_core::address::DeviceId as core::fmt::Display>::fmt` (60 B)
- Block `215`: `<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt` (72 B)
-/

set_option autoImplicit false
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic ProofLib.Step
open CryptoVerification
  (LibsignalPlacement LibsignalRoLoaded libsignalSessionLib libsignalSessionLib_blocks_length
   ls_resolve_data_ultra lsroCheck lsro_intro_chk lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecErrStr1Addr cliAesDecErrStr2Addr)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (PoolMemTransport callBytes callLens fmtWriteKnownEvents formatInnerKnownEvents
   knownArgOom knownArgPanic knownArgStep lsFmtWriteSym toRustAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof
  (CliFmtWriteLink cliCoreFmtWriteVecAtSpec cliCoreFmtWrite_vecU8At_placed_ok
   cliStrRefDisplayShim_fmtArg_ok cliStringBudgetWriteStrCall_ok cliStringDisplayShim_fmtArg_ok
   cliU32Display_fmtArg_ok cliU8Display_fmtArg_ok decodeFmtArguments_fromStr
   decodeFmtArguments_shortLiteral stringWriteVtableAt_dup_writeStr)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
  (CliFormatInnerLink cliAllocFormatInnerSpec cliAllocFormatInner_placed_ok
   formatInnerKnownEvents_fromStr)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
  (withFsTraceExact withRoMemGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (CliFmtWriteProtoAddrCall CliFmtWriteVtableKind CliFormatInnerLsCall CliFormatInnerLsShape
   cliFmtWriteProtoAddrSpec cliFormatInnerLsCallSpec cliStrRefDisplayShimBlocks
   cliStringDisplayShimBlocks dotTplBytes lsDeviceIdDisplayBlock lsNonZeroU8DisplayBlock
   lsProtocolAddressDisplayBlock lsSpqrErrorDisplayBlock lsU32DisplayFmtSym lsU8DisplayFmtSym
   oneArgTplBytes prefixedOneArgTplBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay
  (cliAllocFormatInner_spqrErrorDisplayPrefixed_cells_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
  (SpqrErrorDisplayLink StringBufAppendMany appendMany_singleton_iff blockProgram_rebase_eq_lsProg
   callPieces calleeSavedPreserved_across_fp_frame cliAllocFormatInnerManyTightSpec
   cliAllocFormatInnerMany_tight_placed_ok fmtArgEntriesAt_false_pair
   fmtArgEntriesAt_false_singleton fmtInnerBudgetW_split_R_eq fmtInnerBudgetW_transport
   formatterAt_entails_memRegion24 getLsbD0_sub_even_of_spAligned manyArgOom manyArgPanic
   manyArgStep manyLens panic_frame_anyHeap reaches_manyOom reaches_manyPanic roEntriesAt
   roEntriesAt_dup_mem run_many spAligned_sub_16k spqrErrorCellsAt spqrErrorDispKeep
   spqrErrorPieces)
open VerifiedLibraries.RustStd
  (FmtBuf FmtCall FmtCallbacks FmtInnerBudgetArgsOk FmtOptions FmtWriteFrame IoCallFrame
   RustAllocBudget StringWriteAddrs allocFormatInnerSym allocMultiLib
   allocStringWriteAddrs call_wpp_where checkStrRefDisplayShimBlock
   checkStringDisplayShimBlock coreFmtDecDigitsLutSym coreFmtMultiLib coreFmtWriteSpec
   coreFmtWriteSym coreFmtWrite_ok coreMultiLib decDigitsLutBytes decodeFmtArguments
   defaultFmtOptions displayShimTargetSym fmtArgCallSpec fmtArgEntriesAt fmtArgumentsAt fmtBufVecAt
   fmtEstimatedCapacity fmtInnerBudgetOom fmtInnerBudgetPanic fmtInnerBudgetStep fmtInnerBudgetW
   fmtLiteralLen fmtRef32 fmtRef8 fmtRefStr fmtRefString fmtSrcBytes fmtStartsWithPlaceholder
   fmtWriteFrame_of_pureSeg formatInnerFrame formatterAt stringAppendEvents stringWriteVtableAt
   stringWriterStack subroutine_ok_drop_codeLoadedWhere u32DisplayFmtSym u8DisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern sepWPp_seg_lib_block_pureWhere strDisplayKeep u32DisplayKeep
   u8DisplayKeep)

/-! ## 1. `.rodata` Guards (`StringWriteVtableRoAt`, `cliFmtWriteRoGuard`, `cliFormatInnerRoGuard`)
       & `stripExecOutside` Invariance -/

/-- Pure `.rodata` image invariant for the 3 function-pointer slots (`+0x18`, `+0x20`, `+0x28`) of
    a `<String as core::fmt::Write>` vtable `va`. -/
@[expose] def StringWriteVtableRoAt (va : StringWriteAddrs) (m : Memory) : Prop :=
  RoDataAt m (va.vtable + 0x18#64) (unpack64 va.writeStr) ∧
  RoDataAt m (va.vtable + 0x20#64) (unpack64 va.writeChar) ∧
  RoDataAt m (va.vtable + 0x28#64) (unpack64 va.writeFmt)

/-- Pure `.rodata` memory guard for `lsFmtWriteSym` (`cliFmtWriteProtoAddrSpec`):
    `LibsignalRoLoaded lsmpl`, `DEC_DIGITS_LUT`, and all 3 crate-local `<String as fmt::Write>`
    vtables. -/
@[expose] def cliFmtWriteRoGuard [LibsignalPlacement]
    (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) (m : Memory) : Prop :=
  LibsignalRoLoaded lsmpl m ∧
  RoDataAt m (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym) decDigitsLutBytes ∧
  ∀ k : CliFmtWriteVtableKind, StringWriteVtableRoAt (allocStringWriteAddrs (mplAllocOf k)) m

/-- Pure `.rodata` memory guard for `lsFormatInnerSym` (`cliFormatInnerLsCallSpec`):
    `LibsignalRoLoaded lsmpl`, `DEC_DIGITS_LUT`, the `allocMultiLib` `<String as fmt::Write>`
    vtable, and the two `libsignal_cli` AES-decrypt `.rodata` error strings (`51` B and `17` B). -/
@[expose] def cliFormatInnerRoGuard [LibsignalPlacement]
    (mplAlloc mplFmt : MultiPlacement) (m : Memory) : Prop :=
  LibsignalRoLoaded lsmpl m ∧
  RoDataAt m (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym) decDigitsLutBytes ∧
  StringWriteVtableRoAt (allocStringWriteAddrs mplAlloc) m ∧
  m.RO cliAesDecErrStr1Addr 51 ∧
  m.RO cliAesDecErrStr2Addr 17

/-- Introduce `(addr ↦ᵣ bs)` onto any `m ⊨ P` from `RoDataAt m addr bs` (`bs.length ≤ 2 ^ 64`). -/
theorem sat_roDataAt {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (hro : RoDataAt m addr bs) (hlen : bs.length ≤ 2 ^ 64) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (addr ↦ᵣ bs) ∗ P :=
  Satisfies.rodata_intro hro.1 hro.2 hlen hP

/-- Introduce `stringWriteVtableAt va` onto `m ⊨ P` from `StringWriteVtableRoAt va m`. -/
theorem sat_stringWriteVtableAt {va : StringWriteAddrs} {m : Memory}
    (hv : StringWriteVtableRoAt va m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ stringWriteVtableAt va ∗ P := by
  unfold stringWriteVtableAt
  rw [pointsTo64RO_eq_pointsToBytesRO, pointsTo64RO_eq_pointsToBytesRO,
    pointsTo64RO_eq_pointsToBytesRO, sepConj_assoc, sepConj_assoc]
  have hlen : ∀ w : BitVec 64, (unpack64 w).length ≤ 2 ^ 64 := fun w => by
    rw [unpack64_length]; omega
  exact sat_roDataAt hv.1 (hlen _) (sat_roDataAt hv.2.1 (hlen _) (sat_roDataAt hv.2.2 (hlen _) hP))

/-- Introduce `(coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)` from
    `RoDataAt`. -/
theorem sat_decDigitsLut {mplFmt : MultiPlacement} {m : Memory}
    (hlut : RoDataAt m (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym) decDigitsLutBytes)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ P := by
  have hlen : decDigitsLutBytes.length ≤ 2 ^ 64 := by
    have h200 : decDigitsLutBytes.length = 200 := rfl
    omega
  exact sat_roDataAt hlut hlen hP

/-- `stripExecOutside keep` preserves read8 at every address, hence `readBytes` on every slice. -/
theorem readBytes_stripExecOutside (keep : BitVec 64 → Bool) (m : Memory)
    (addr : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).readBytes addr len = m.readBytes addr len := by
  induction len generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.readBytes, strip_read8, ih]

/-- `stripExecOutside keep` preserves `m.RO addr len` (since `Perm.ro` already has `x = false`). -/
theorem ro_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory} {addr : BitVec 64} {len : Nat}
    (hro : m.RO addr len) :
    (stripExecOutside keep m).RO addr len := by
  intro a ha
  have ⟨hp, hlf⟩ := hro a ha
  refine ⟨?_, ?_⟩
  · rw [strip_perm, hp]
    cases keep a <;> rfl
  · rw [strip_isLazyFree]
    exact hlf

/-- `stripExecOutside keep` preserves `RoDataAt`. -/
theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {addr : BitVec 64} {bs : List (BitVec 8)} (h : RoDataAt m addr bs) :
    RoDataAt (stripExecOutside keep m) addr bs :=
  ⟨ro_stripExecOutside keep h.1, (readBytes_stripExecOutside keep m addr bs.length).trans h.2⟩

/-- `stripExecOutside keep` preserves `StringWriteVtableRoAt`. -/
theorem stringWriteVtableRoAt_stripExecOutside (keep : BitVec 64 → Bool)
    {va : StringWriteAddrs} {m : Memory} (h : StringWriteVtableRoAt va m) :
    StringWriteVtableRoAt va (stripExecOutside keep m) :=
  ⟨roDataAt_stripExecOutside keep h.1,
   roDataAt_stripExecOutside keep h.2.1,
   roDataAt_stripExecOutside keep h.2.2⟩

/-- `stripExecOutside keep` preserves `HoldsBytes m addr bs (fun _ => Perm.ro)`. -/
theorem holdsBytes_ro_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {addr : BitVec 64} {bs : List (BitVec 8)}
    (hhb : HoldsBytes m addr bs (fun _ => Perm.ro)) :
    HoldsBytes (stripExecOutside keep m) addr bs (fun _ => Perm.ro) := by
  intro i hi
  obtain ⟨hrd, hp, hlf⟩ := hhb i hi
  let a := addr + BitVec.ofNat 64 i
  change m.perm a = some Perm.ro at hp
  change m.isLazyFree a = false at hlf
  refine ⟨(strip_read8 keep m a).trans hrd, ?_, ?_⟩
  · change (stripExecOutside keep m).perm a = some Perm.ro
    rw [strip_perm, hp]
    cases keep a <;> rfl
  · change (stripExecOutside keep m).isLazyFree a = false
    rw [strip_isLazyFree]
    exact hlf

/-- `stripExecOutside keep` preserves `LibsignalRoLoaded`. -/
theorem libsignalRoLoaded_stripExecOutside (keep : BitVec 64 → Bool) {pl : MultiPlacement}
    {m : Memory} (h : LibsignalRoLoaded pl m) :
    LibsignalRoLoaded pl (stripExecOutside keep m) :=
  fun d hd hro => holdsBytes_ro_stripExecOutside keep (h d hd hro)

/-- `stripExecOutside keep` preserves `cliFmtWriteRoGuard`. -/
theorem cliFmtWriteRoGuard_stripExecOutside [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement} {mplFmt : MultiPlacement} {m : Memory}
    (h : cliFmtWriteRoGuard mplAllocOf mplFmt m) :
    cliFmtWriteRoGuard mplAllocOf mplFmt (stripExecOutside keep m) :=
  ⟨libsignalRoLoaded_stripExecOutside keep h.1,
   roDataAt_stripExecOutside keep h.2.1,
   fun k => stringWriteVtableRoAt_stripExecOutside keep (h.2.2 k)⟩

/-- `stripExecOutside keep` preserves `cliFormatInnerRoGuard`. -/
theorem cliFormatInnerRoGuard_stripExecOutside [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {mplAlloc mplFmt : MultiPlacement} {m : Memory}
    (h : cliFormatInnerRoGuard mplAlloc mplFmt m) :
    cliFormatInnerRoGuard mplAlloc mplFmt (stripExecOutside keep m) :=
  ⟨libsignalRoLoaded_stripExecOutside keep h.1,
   roDataAt_stripExecOutside keep h.2.1,
   stringWriteVtableRoAt_stripExecOutside keep h.2.2.1,
   ro_stripExecOutside keep h.2.2.2.1,
   ro_stripExecOutside keep h.2.2.2.2⟩

/-! ## 2. Keep Predicates, Kernel-Checked Shim Classifiers, & Linkage Bundles -/

/-- Mangled `libsignal_session` extern symbol for `<str as core::fmt::Display>::fmt`. -/
abbrev lsStrDisplayFmtSym : String :=
  "_RNvXsi_NtCskxtBwYRO61I_4core3fmteNtB5_7Display3fmt"

/-- `libsignalSessionLib` code-block keep predicate for `lsFmtWriteSym`:
    the 5 `<String as Display>::fmt` shims plus Block `214` (`<DeviceId as Display>::fmt`) and
    Block `217` (`<NonZero<u8> as Display>::fmt`). -/
@[expose] def fmtWriteSubLsKeep (j : Nat) : Bool :=
  decide (j ∈ cliStringDisplayShimBlocks ∨ j = 214 ∨ j = 217)

/-- `libsignalSessionLib` code-block keep predicate for `lsFormatInnerSym`:
    the 5 `<String as Display>::fmt` shims, the 5 `<&str as Display>::fmt` shims, Blocks `214, 215,
    217`, and `spqrErrorDispKeep` (`Blocks 392, 393, 394, 396, 397, 412`). -/
@[expose] def formatInnerSubLsKeep (j : Nat) : Bool :=
  decide (j ∈ cliStringDisplayShimBlocks ∨ j ∈ cliStrRefDisplayShimBlocks ∨
    j = 214 ∨ j = 215 ∨ j = 217 ∨ spqrErrorDispKeep j = true)

theorem cliStringDisplayShim_lt {bi : Nat} (hbi : bi ∈ cliStringDisplayShimBlocks) :
    bi < libsignalSessionLib.blocks.length := by
  rw [libsignalSessionLib_blocks_length]
  simp only [cliStringDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem cliStrRefDisplayShim_lt {bi : Nat} (hbi : bi ∈ cliStrRefDisplayShimBlocks) :
    bi < libsignalSessionLib.blocks.length := by
  rw [libsignalSessionLib_blocks_length]
  simp only [cliStrRefDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem cliStringDisplayShim_check {bi : Nat} (hbi : bi ∈ cliStringDisplayShimBlocks) :
    checkStringDisplayShimBlock libsignalSessionLib bi = true := by
  simp only [cliStringDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> exact eagerReduce (Eq.refl true)

theorem cliStrRefDisplayShim_check {bi : Nat} (hbi : bi ∈ cliStrRefDisplayShimBlocks) :
    checkStrRefDisplayShimBlock libsignalSessionLib bi = true := by
  simp only [cliStrRefDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> exact eagerReduce (Eq.refl true)

theorem cliStringDisplayShim_targetSym {bi : Nat} (hbi : bi ∈ cliStringDisplayShimBlocks) :
    displayShimTargetSym libsignalSessionLib bi = lsStrDisplayFmtSym := by
  simp only [cliStringDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> exact eagerReduce (Eq.refl lsStrDisplayFmtSym)

theorem cliStrRefDisplayShim_targetSym {bi : Nat} (hbi : bi ∈ cliStrRefDisplayShimBlocks) :
    displayShimTargetSym libsignalSessionLib bi = lsStrDisplayFmtSym := by
  simp only [cliStrRefDisplayShimBlocks, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl <;> exact eagerReduce (Eq.refl lsStrDisplayFmtSym)

theorem ls_resolve_strDisplayFmtSym [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsStrDisplayFmtSym = lsρ lsStrDisplayFmtSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

theorem fmtWriteSubLsKeep_of_stringShim {bi : Nat} (hbi : bi ∈ cliStringDisplayShimBlocks) :
    fmtWriteSubLsKeep bi = true :=
  decide_eq_true (Or.inl hbi)

theorem formatInnerSubLsKeep_of_stringShim {bi : Nat} (hbi : bi ∈ cliStringDisplayShimBlocks) :
    formatInnerSubLsKeep bi = true :=
  decide_eq_true (Or.inl hbi)

theorem formatInnerSubLsKeep_of_strRefShim {bi : Nat} (hbi : bi ∈ cliStrRefDisplayShimBlocks) :
    formatInnerSubLsKeep bi = true :=
  decide_eq_true (Or.inr (Or.inl hbi))

theorem formatInnerSubLsKeep_of_spqr {j : Nat} (hj : spqrErrorDispKeep j = true) :
    formatInnerSubLsKeep j = true :=
  decide_eq_true (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hj)))))

/-- Complete linkage bundle for `lsFmtWriteSym` (`cliFmtWriteProtoAddrSpec`) across all 3
    crate-local `<String as core::fmt::Write>` vtables (`CliFmtWriteVtableKind`). -/
structure CliFmtWriteSubLink [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (P : Program)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) : Prop where
  linkAlloc : ∀ k : CliFmtWriteVtableKind, CliFmtWriteLink M A lim P mplCore (mplAllocOf k)
  vtEq : ∀ k : CliFmtWriteVtableKind, (allocStringWriteAddrs (mplAllocOf k)).vtable = k.vtableAddr
  plFmt : coreFmtMultiLib.Placeable mplFmt
  noExtFmtStr : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P
  clFmtStr : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m
  noExtFmtU8 : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P
  clFmtU8 : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m
  plLs : libsignalSessionLib.Placeable lsmpl
  noExtLs : LibKeepNoExtern libsignalSessionLib fmtWriteSubLsKeep lsmpl P
  clLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere fmtWriteSubLsKeep lsmpl m
  tieFmtWrite : lsρ lsFmtWriteSym = coreMultiLib.fnAddr mplCore coreFmtWriteSym
  tieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
  tieStrDisplay : lsρ lsStrDisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym

/-- Complete linkage bundle for `lsFormatInnerSym` (`cliFormatInnerLsCallSpec`) across all 13 call
    shapes in `CliFormatInnerLsShape`. -/
structure CliFormatInnerSubLink [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (P : Program)
    (mplCore mplAlloc mplFmt : MultiPlacement) : Prop extends
    SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt where
  noExtFmtStr : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P
  clFmtStr : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m
  noExtFmtU8 : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P
  clFmtU8 : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m
  plLs : libsignalSessionLib.Placeable lsmpl
  noExtLsAll : LibKeepNoExtern libsignalSessionLib formatInnerSubLsKeep lsmpl P
  clLsAll : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere formatInnerSubLsKeep lsmpl m
  tieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
  tieStrDisplay : lsρ lsStrDisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym

/-! ## 3. Rebased Sub-Formatters (`Blocks 217, 214, 215`) -/

/-- `libsignal_core` `.rodata` template symbols referenced by Block `214` (`"{}"`) and Block `215`
    (`"{}.{}"`). -/
abbrev lsOneArgTplSym : String := "libsignal_core:.rodata.str1.1+0x62"
abbrev lsDotTplSym : String := "libsignal_core:.rodata.str1.1+0x10e"

@[expose] def protoAddrRoList : List (String × List (BitVec 8)) :=
  [(lsOneArgTplSym, oneArgTplBytes), (lsDotTplSym, dotTplBytes)]

@[expose] def protoAddrRoSep (pl : MultiPlacement) : SepProp :=
  roEntriesAt pl protoAddrRoList

private theorem protoAddrRoList_chk :
    protoAddrRoList.all (fun p => lsroCheck p.1 p.2) = true := by
  exact eagerReduce (Eq.refl true)

theorem sat_protoAddrRoSep {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ protoAddrRoSep pl ∗ P := by
  dsimp only [protoAddrRoSep, protoAddrRoList, roEntriesAt]
  have hchk := protoAddrRoList_chk
  simp only [protoAddrRoList, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hchk
  rw [sepConj_emp, sepConj_assoc]
  exact lsro_intro_chk hro hchk.1 (lsro_intro_chk hro hchk.2 hP)

theorem protoAddrRoSep_dup_in_R [LibsignalPlacement] {F R_client R_rest : SepProp}
    {sym : String} {bs : List (BitVec 8)}
    (hmem : (sym, bs) ∈ protoAddrRoList := by decide)
    (hR : R_client = F ∗ (protoAddrRoSep lsmpl ∗ R_rest)) :
    R_client = (lsmpl.ρ sym ↦ᵣ bs) ∗ R_client := by
  rw [hR]
  dsimp only [protoAddrRoSep]
  refine (congrArg (fun X => F ∗ (X ∗ R_rest)) (roEntriesAt_dup_mem lsmpl hmem)).trans ?_
  sep_ac_rfl

/-- Lift a known single-slice `fmtArgCallSpec` (`knownArgStep`) to `manyArgStep` when
    `argPieces idx = [bs]`. -/
theorem fmtArgCallSpec_many_of_known_gen {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {R_client : SepProp} {t0 : State} {P : Program}
    {argBytes : Nat → List (BitVec 8)} {argPieces : Nat → List (List (BitVec 8))}
    {stackBytes idx : Nat} {out valPtr fmtFn : BitVec 64} {opts : FmtOptions}
    {bs : List (BitVec 8)}
    (hbs : argBytes idx = bs)
    (hpcs : argPieces idx = [bs])
    (hk : subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
        stackBytes out va.vtable idx valPtr fmtFn opts)) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx valPtr fmtFn opts) := by
  refine subroutine_ok_mono hk
    (fun _ _ _ h => h)
    (fun (st, f) _ _ sf hpost => by
      dsimp only [fmtArgCallSpec] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine Entails.sepExists_mono fun ok => Entails.sepExists_mono fun st' => ?_
      refine Entails.pure_left fun ⟨hw0, hstep⟩ => ?_
      dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes] at hstep
      dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces]
      rw [hbs] at hstep
      rw [hpcs]
      exact Entails.pure_right ⟨hw0, hstep.1, appendMany_singleton_iff.mpr hstep.2⟩
        (Entails.refl _))
    (fun (st, _) _ _ sf hpan => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, knownArgPanic, callBytes] at hpan
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces]
      rw [hbs] at hpan
      rw [hpcs]
      refine Satisfies.mono (sepConj_mono_left ?_) hpan
      exact Entails.pure_left fun hp =>
        Entails.pure_right ⟨[], bs, [], st, rfl, .nil st, hp⟩ (Entails.refl _))
    (hoom := fun (st, _) _ _ sf hoom => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, knownArgOom, callBytes] at hoom
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces]
      rw [hbs] at hoom
      rw [hpcs]
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨⟨[], bs, [], st, rfl, .nil st, hoom.1⟩, hoom.2⟩)

/-- Converse of `fmtArgCallSpec_many_of_known_gen`: project a 1-piece `manyArgStep` (`[bs]`)
    onto `knownArgStep` (`bs`). -/
theorem fmtArgCallSpec_known_of_many_singleton {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {R_client : SepProp} {t0 : State} {P : Program}
    {argBytes : Nat → List (BitVec 8)} {argPieces : Nat → List (List (BitVec 8))}
    {stackBytes idx : Nat} {out valPtr fmtFn : BitVec 64} {opts : FmtOptions}
    {bs : List (BitVec 8)}
    (hbs : argBytes idx = bs)
    (hpcs : argPieces idx = [bs])
    (hm : subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx valPtr fmtFn opts)) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
        stackBytes out va.vtable idx valPtr fmtFn opts) := by
  refine subroutine_ok_mono hm
    (fun _ _ _ h => h)
    (fun (st, f) _ _ sf hpost => by
      dsimp only [fmtArgCallSpec] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine Entails.sepExists_mono fun ok => Entails.sepExists_mono fun st' => ?_
      refine Entails.pure_left fun ⟨hw0, hstep⟩ => ?_
      dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces] at hstep
      dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
      rw [hpcs] at hstep
      rw [hbs]
      exact Entails.pure_right ⟨hw0, hstep.1, appendMany_singleton_iff.mp hstep.2⟩
        (Entails.refl _))
    (fun (st, _) _ _ sf hpan => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces] at hpan
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, knownArgPanic, callBytes]
      rw [hpcs] at hpan
      rw [hbs]
      refine Satisfies.mono (sepConj_mono_left ?_) hpan
      refine Entails.pure_left fun ⟨pre_p, p, post_p, st_m, heq, hpre_m, hp⟩ => ?_
      cases pre_p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        cases hpre_m
        exact Entails.pure_right hp (Entails.refl _)
      | cons hd tl =>
        simp only [List.cons_append, List.cons.injEq] at heq
        nomatch (List.append_eq_nil_iff.mp heq.2.symm).2)
    (hoom := fun (st, _) _ _ sf hoom => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces] at hoom
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, knownArgOom, callBytes]
      rw [hpcs] at hoom
      rw [hbs]
      rw [satisfies_pure_sepConj] at hoom ⊢
      rcases hoom.1 with ⟨pre_p, p, post_p, st_m, heq, hpre_m, hnf⟩
      refine ⟨?_, hoom.2⟩
      cases pre_p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        cases hpre_m
        exact hnf
      | cons hd tl =>
        simp only [List.cons_append, List.cons.injEq] at heq
        nomatch (List.append_eq_nil_iff.mp heq.2.symm).2)

private theorem subroutine_ok_of_multiCodeLoaded_local {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (hcl : ∀ m, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (hok : subroutine_ok P addr (lib.withCodeLoaded mpl spec)) :
    subroutine_ok P addr spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R₀ s0 hpc hrun hpre hsp0 hclP
  have hpre' : s0.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0 ∗ R₀ := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜lib.CodeLoaded mpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl s0.mem hclP, hpre⟩
  exact hok.mono_outcome x R₀ s0 hpc hrun hpre' hsp0 fun _ hout => hout

/-- Initialize a `SepWPp` proof of `subroutine_ok P entry spec` with
    `libsignalSessionLib.CodeLoadedWhere keepLs lsmpl s0.mem`. -/
theorem subroutine_ok_of_sepWPp_clLsWhere [LibsignalPlacement] {α : Type} {P : Program}
    {keepLs : Nat → Bool} {entry : BitVec 64} {spec : Spec α}
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere keepLs lsmpl m)
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.spAligned = true →
      libsignalSessionLib.CodeLoadedWhere keepLs lsmpl s0.mem →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWPp P (s0.readReg64 Reg.lr) s0 P_init
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.onPanic x s0 sf ∗ R)
          (spec.onOom x s0)) :
    subroutine_ok P entry spec := by
  refine subroutine_ok_drop_codeLoadedWhere hclLs ?_
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨
    (spec.pre x s0 ∗ ⌜libsignalSessionLib.CodeLoadedWhere keepLs lsmpl s0.mem⌝) ∗ R
    at hpre
  have hpre' :
      s0.mem ⊨ ⌜libsignalSessionLib.CodeLoadedWhere keepLs lsmpl s0.mem⌝ ∗
        (spec.pre x s0 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  exact h x R s0 hpc0 hrun0 hsp0 hpre'.1 hpre'.2

private theorem fmtInnerBudgetW_dup_R {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {P_dup R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} (hdup : R = P_dup ∗ R) :
    fmtInnerBudgetW B st0 va R t0 out st s =
      P_dup ∗ fmtInnerBudgetW B st0 va R t0 out st s :=
  (congrArg (fun X => fmtInnerBudgetW B st0 va X t0 out st s) hdup).trans
    (fmtInnerBudgetW_split_R_eq B st0 va P_dup R t0 out st s)

private theorem fmtInnerBudgetW_dup_vtable {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} :
    fmtInnerBudgetW B st0 va R t0 out st s =
      ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
        fmtInnerBudgetW B st0 va R t0 out st s := by
  let F : SepProp → SepProp := fun V =>
    ⌜IoCallFrame t0 s ∧ s.fs = t0.fs ∧ s.trace = t0.trace⌝ ∗
      Rust.vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      fmtBufVecAt B st.cap st.ptr st.bytes ∗
      B.pool (B.stepEvents st.evs st0) s ∗ V ∗ R
  change F (stringWriteVtableAt va) =
    ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ F (stringWriteVtableAt va)
  refine (congrArg F (stringWriteVtableAt_dup_writeStr va)).trans ?_
  dsimp only [F]
  sep_ac_rfl

private theorem fmtInnerBudgetW_dup_vtable_and_R {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {P_dup R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} (hdup : R = P_dup ∗ R) :
    fmtInnerBudgetW B st0 va R t0 out st s =
      ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ P_dup ∗
        fmtInnerBudgetW B st0 va R t0 out st s := by
  refine fmtInnerBudgetW_dup_vtable.trans ?_
  refine (congrArg (fun X => ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ X)
    (fmtInnerBudgetW_dup_R hdup)).trans ?_
  sep_ac_rfl

/-- Keep-parametric `call_wpp_where` discharge for nested `bl lsFmtWriteSym` (`core::fmt::write`)
    inside any `libsignalSessionLib` `fmtFn` callback over `fmtInnerBudgetW`, preserving
    `libsignalSessionLib.CodeLoadedWhere keepLs lsmpl` across the call. -/
theorem nested_coreFmtWrite_many_keep_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {keepLs : Nat → Bool} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (st0 : M.σ) {R_client R_sub F_frame : SepProp}
    (argPieces subPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes subStack outerIdx : Nat)
    (out valPtr fmtFn f ret_pc tplPtr argsPtr : BitVec 64)
    (opts : FmtOptions) (tpl : List (BitVec 8)) (args : List (BitVec 64 × BitVec 64))
    (cs : List FmtCall) (st : FmtBuf) (R : SepProp) (s0 sm : State)
    (hpcs : argPieces outerIdx = cs.flatMap (callPieces subPieces))
    (hsubStk : stringWriterStack ≤ subStack ∧ 0x70 + subStack ≤ 2 ^ 64)
    (heven : argsPtr.getLsbD 0 = false)
    (hdec : decodeFmtArguments tplPtr argsPtr tpl args = some cs)
    (htpl_dup : R_sub = (tplPtr ↦ᵣ tpl) ∗ R_sub)
    (hargsOk : ∀ idx val fn opt, FmtCall.fmtArg idx val fn opt ∈ cs →
      subroutine_ok P fn
        (fmtArgCallSpec
          (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
            (allocStringWriteAddrs mplAlloc) R_sub t0 out)
          (fmtInnerBudgetStep (manyArgStep subPieces))
          (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
          (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
            (manyArgOom (toRustAllocBudget M A lim) st0 subPieces))
          subStack out (allocStringWriteAddrs mplAlloc).vtable idx val fn opt))
    (hcl_sm : libsignalSessionLib.CodeLoadedWhere keepLs lsmpl sm.mem)
    (hframe : FmtWriteFrame s0 sm)
    (hpc_sm : sm.pc = coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (hrun_sm : sm.status = .Running)
    (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = ret_pc)
    (hx0_sm : sm.readReg64 .x0 = out)
    (hx1_sm : sm.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable)
    (hx2_sm : sm.readReg64 .x2 = tplPtr)
    (hx3_sm : sm.readReg64 .x3 = argsPtr)
    (hnext : ∀ (sf_call : State) (st' : FmtBuf),
      sf_call.pc = ret_pc → sf_call.status = .Running →
      sf_call.sp = sm.sp → CalleeSavedPreserved sm sf_call →
      libsignalSessionLib.CodeLoadedWhere keepLs lsmpl sf_call.mem →
      sf_call.readReg32 .x0 = 0#32 →
      manyArgStep argPieces (.fmtArg outerIdx valPtr fmtFn opts) st true st' →
      SepWPp P (s0.readReg64 Reg.lr) sf_call
        (fmtArgEntriesAt false argsPtr args ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0
            (allocStringWriteAddrs mplAlloc) R_sub t0 out st' sf_call ∗
          stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (fmtArgCallSpec
              (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
                (allocStringWriteAddrs mplAlloc) R_client t0 out)
              (fmtInnerBudgetStep (manyArgStep argPieces))
              (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
              (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
                (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
              stackBytes out (allocStringWriteAddrs mplAlloc).vtable
              outerIdx valPtr fmtFn opts).post (st, f) s0 sf ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (fmtArgCallSpec
              (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
                (allocStringWriteAddrs mplAlloc) R_client t0 out)
              (fmtInnerBudgetStep (manyArgStep argPieces))
              (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
              (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
                (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
              stackBytes out (allocStringWriteAddrs mplAlloc).vtable
              outerIdx valPtr fmtFn opts).onPanic (st, f) s0 sf ∗ R)
        (fun sf =>
          (fmtArgCallSpec
            (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
              (allocStringWriteAddrs mplAlloc) R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
              (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
            stackBytes out (allocStringWriteAddrs mplAlloc).vtable
            outerIdx valPtr fmtFn opts).onOom (st, f) s0 sf)) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    SepWPp P (s0.readReg64 Reg.lr) sm
      (fmtArgEntriesAt false argsPtr args ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
        stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable outerIdx valPtr fmtFn opts).post (st, f) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable outerIdx valPtr fmtFn opts).onPanic (st, f) s0 sf ∗ R)
      (fun sf =>
        (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
          (fmtInnerBudgetStep (manyArgStep argPieces))
          (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
          (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
          stackBytes out va.vtable outerIdx valPtr fmtFn opts).onOom (st, f) s0 sf) := by
  intro B va
  have hcb :
      FmtCallbacks P (fmtInnerBudgetW B st0 va R_sub t0 out)
        (fmtInnerBudgetStep (manyArgStep subPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 subPieces))
        subStack out va.vtable va.writeStr cs :=
    { transport := fun st_i s_i s_i' hf =>
        fmtInnerBudgetW_transport B st0 va R_sub t0 out st_i s_i s_i' hf
      write_str := fun ptr sbs _ =>
        cliStringBudgetWriteStrCall_ok L st0 R_sub
          (manyArgStep subPieces) (manyArgPanic subPieces) (manyArgOom B st0 subPieces)
          t0 subStack out ptr sbs ⟨hsubStk.1, by omega⟩
      fmt_arg := hargsOk }
  have hcore := subroutine_ok_of_multiCodeLoaded_local L.clCore
    (coreFmtWrite_ok L.plCore L.noExtCore0
      (fmtInnerBudgetW B st0 va R_sub t0 out)
      (fmtInnerBudgetStep (manyArgStep subPieces))
      (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
      (fmtInnerBudgetOom B st0 (manyArgOom B st0 subPieces))
      subStack)
  refine call_wpp_where (x := (out, va.vtable, va.writeStr, false, tpl, args, st))
    (F := F_frame) hcore hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ _ hm_pan => ?_)
    (fun sf_call hpcf hrunf hspf hcsf hcl_sf => ?_)
    (fun sf R' _ hoom => ?_)
  · refine Satisfies.mono ?_ hm
    have htr := fmtInnerBudgetW_transport B st0 va R_sub t0 out st s0 sm hframe
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left htr))) ?_
    have hdupW := fmtInnerBudgetW_dup_vtable_and_R (B := B) (st0 := st0) (va := va)
      (t0 := t0) (out := out) (st := st) (s := sm) htpl_dup
    refine Entails.trans (Entails.of_eq (show
      (fmtArgEntriesAt false argsPtr args ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st sm ∗
        stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R' =
      (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
        ((tplPtr ↦ᵣ tpl) ∗ fmtArgEntriesAt false argsPtr args) ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st sm ∗
        stackFrameAt sm.sp (0x70 + subStack)) ∗ (F_frame ∗ R') by
      dsimp only [toRustAllocBudget, B] at hdupW ⊢
      conv => lhs; rw [hdupW]
      sep_ac_rfl)) ?_
    refine sepConj_mono_left ?_
    dsimp only [coreFmtWriteSpec, fmtArgumentsAt]
    rw [hx2_sm, hx3_sm, heven]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.pure_right ⟨hx0_sm, hx1_sm, hsubStk.2, cs, hdec, hcb⟩ (Entails.refl _)
  · dsimp only [coreFmtWriteSpec, fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic,
      callPieces] at hm_pan ⊢
    rw [hx2_sm, hx3_sm] at hm_pan
    rw [hpcs]
    refine Satisfies.mono (sepConj_mono_left ?_) hm_pan
    refine Entails.trans panic_frame_anyHeap ?_
    refine Entails.pure_left fun ⟨cs', c, st_m, hdec', hreach, hpC⟩ => ?_
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    exact Entails.pure_right (reaches_manyPanic hreach hpC) (Entails.refl _)
  · dsimp only [coreFmtWriteSpec, fmtArgumentsAt]
    rw [hx2_sm, hx3_sm, heven]
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro R' hm_after hL_P
    rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
    rcases hm_after with ⟨ok, hm_after⟩
    rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
    rcases hm_after with ⟨st', hm_after⟩
    have hm1 :
        sf_call.mem ⊨ ⌜(sf_call.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
          ∃ cs', decodeFmtArguments tplPtr argsPtr tpl args = some cs' ∧
            VerifiedLibraries.RustStd.FmtRun (fmtInnerBudgetStep (manyArgStep subPieces)) cs' st ok st'⌝ ∗
          (((fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗
            (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl))) ∗ R') := by
      refine Satisfies.mono ?_ hm_after
      exact Entails.of_eq (by sep_ac_rfl)
    rw [satisfies_pure_sepConj] at hm1
    rcases hm1 with ⟨⟨hw0, cs', hdec', hrun'⟩, hm2⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    obtain ⟨hok, happ⟩ := run_many hrun'
    subst hok
    have hstep_outer :
        manyArgStep argPieces (.fmtArg outerIdx valPtr fmtFn opts) st true st' := by
      dsimp only [manyArgStep, callPieces]
      rw [hpcs]
      exact ⟨rfl, happ⟩
    have hm3 :
        sf_call.mem ⊨
          (fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R' := by
      have hdrop :
          ((fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗
            (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl))) ∗ R' =
          (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl)) ∗
            ((fmtArgEntriesAt false argsPtr args ∗
              fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
              stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R') := by
        sep_ac_rfl
      rw [hdrop] at hm2
      exact Satisfies.drop_left hm2
    exact hnext sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0 hstep_outer R' hm3 hL_P
  · dsimp only [coreFmtWriteSpec, fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom,
      callPieces] at hoom ⊢
    rw [hx2_sm, hx3_sm] at hoom
    rw [hpcs]
    rw [satisfies_pure_sepConj] at hoom ⊢
    rcases hoom.1 with ⟨cs', c, st_m, hdec', hreach, hoC⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    exact ⟨reaches_manyOom hreach hoC, Satisfies.drop_left hoom.2⟩

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 217

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 214

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 215

private theorem ls_checkNoSvc0_217 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 217).text = true := by
  rw [← blkLib_eq_217]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_214 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 214).text = true := by
  rw [← blkLib_eq_214]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_215 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 215).text = true := by
  rw [← blkLib_eq_215]; exact eagerReduce (Eq.refl true)

private theorem stack32_split (sp0 : BitVec 64) (stackBytes : Nat)
    (hfit : 32 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp0 stackBytes =
      (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ((sp0 - 32#64) ↦₆₄ v0) ∗ ((sp0 - 24#64) ↦₆₄ v1) ∗
        ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3)) ∗
        stackFrameAt (sp0 - 32#64) (stackBytes - 32) := by
  have h1 : stackBytes = 32 + (stackBytes - 32) := by omega
  conv => lhs; rw [h1]
  rw [stackFrameAt_split sp0 32 (stackBytes - 32) (by omega)]
  have h32 : stackFrameAt sp0 32 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ((sp0 - 32#64) ↦₆₄ v0) ∗ ((sp0 - 24#64) ↦₆₄ v1) ∗
        ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3) := by
    simp only [arm64_norm]
  rw [h32]

private theorem stack32_fold (sp0 v0 v1 v2 v3 : BitVec 64) (stackBytes : Nat)
    (hfit : 32 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    ((sp0 - 32#64) ↦₆₄ v0) ∗ ((sp0 - 24#64) ↦₆₄ v1) ∗
      ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3) ∗
      stackFrameAt (sp0 - 32#64) (stackBytes - 32) ⊢
    stackFrameAt sp0 stackBytes := by
  rw [stack32_split sp0 stackBytes hfit]
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp0 - 32#64) ↦₆₄ v0) ∗ ((sp0 - 24#64) ↦₆₄ v1) ∗
      ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3)) ∗
      stackFrameAt (sp0 - 32#64) (stackBytes - 32) by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.refl _))))

private theorem stack32_mem8_fold (sp0 v0 v2 v3 : BitVec 64) (stackBytes : Nat)
    (hfit : 32 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    ((sp0 - 32#64) ↦₆₄ v0) ∗ memRegion (sp0 - 24#64) 8 ∗
      ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3) ∗
      stackFrameAt (sp0 - 32#64) (stackBytes - 32) ⊢
    stackFrameAt sp0 stackBytes := by
  have hm8 : memRegion (sp0 - 24#64) 8 = ∃∗ v1 : BitVec 64, ((sp0 - 24#64) ↦₆₄ v1) := by
    rw [memRegion_cells (sp0 - 24#64) 1 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp]
  rw [hm8]
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun v1 => ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ((sp0 - 32#64) ↦₆₄ v0) ∗ ((sp0 - 24#64) ↦₆₄ v1) ∗
      ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3) ∗
      stackFrameAt (sp0 - 32#64) (stackBytes - 32) by sep_ac_rfl)) ?_
  exact stack32_fold sp0 v0 v1 v2 v3 stackBytes hfit

private theorem stack48_split (sp0 : BitVec 64) (stackBytes : Nat)
    (hfit : 48 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp0 stackBytes =
      (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
        ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
        ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5)) ∗
        stackFrameAt (sp0 - 48#64) (stackBytes - 48) := by
  have h1 : stackBytes = 48 + (stackBytes - 48) := by omega
  conv => lhs; rw [h1]
  rw [stackFrameAt_split sp0 48 (stackBytes - 48) (by omega)]
  have h48 : stackFrameAt sp0 48 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
        ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
        ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5) := by
    simp only [arm64_norm]
  rw [h48]

private theorem stack48_fold (sp0 v0 v1 v2 v3 v4 v5 : BitVec 64) (stackBytes : Nat)
    (hfit : 48 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
      ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
      ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5) ∗
      stackFrameAt (sp0 - 48#64) (stackBytes - 48) ⊢
    stackFrameAt sp0 stackBytes := by
  rw [stack48_split sp0 stackBytes hfit]
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
      ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
      ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5)) ∗
      stackFrameAt (sp0 - 48#64) (stackBytes - 48) by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

private theorem slot8_split_at4 (base : BitVec 64) (v : BitVec 64) :
    (base ↦₆₄ v) ⊢
      memRegion base 4 ∗ (∃∗ b4 : BitVec 8, ((base + 4#64) ↦₈ b4)) ∗ memRegion (base + 5#64) 3 := by
  have hm8 : (base ↦₆₄ v) ⊢ memRegion base 8 := by
    rw [memRegion_cells base 1 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp]
    exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans hm8 ?_
  have hsplit : memRegion base 8 =
      memRegion base 4 ∗ (∃∗ b4 : BitVec 8, ((base + 4#64) ↦₈ b4)) ∗ memRegion (base + 5#64) 3 := by
    conv =>
      lhs
      rw [show (8 : Nat) = 4 + 4 by decide,
        memRegion_split base 4 4 (by decide),
        show (4 : Nat) = 1 + 3 by decide,
        memRegion_split (base + 4#64) 1 3 (by decide),
        memRegion_one,
        show base + 4#64 + 1#64 = base + 5#64 by bv_omega]
  exact Entails.of_eq hsplit

private theorem slot8_fold_at4 (base : BitVec 64) (b4 : BitVec 8) :
    memRegion base 4 ∗ ((base + 4#64) ↦₈ b4) ∗ memRegion (base + 5#64) 3 ⊢
      memRegion base 8 := by
  have hm1 : ((base + 4#64) ↦₈ b4) ⊢ memRegion (base + 4#64) 1 := by
    rw [memRegion_one]
    exact Entails.sepExists_right b4 (Entails.refl _)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hm1)) ?_
  have hmerge : memRegion base 4 ∗ (memRegion (base + 4#64) 1 ∗ memRegion (base + 5#64) 3) =
      memRegion base 8 := by
    conv =>
      rhs
      rw [show (8 : Nat) = 4 + 4 by decide,
        memRegion_split base 4 4 (by decide),
        show (4 : Nat) = 1 + 3 by decide,
        memRegion_split (base + 4#64) 1 3 (by decide),
        show base + 4#64 + 1#64 = base + 5#64 by bv_omega]
  exact Entails.of_eq hmerge

private theorem decode_oneArgTpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 oneArgTplBytes [(v0, fn0)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, oneArgTplBytes, heven, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem decode_dotTpl (x2 x3 v0 fn0 v1 fn1 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 dotTplBytes [(v0, fn0), (v1, fn1)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions,
            FmtCall.writeStr (x2 + 2#64) [0x2e#8],
            FmtCall.fmtArg 1 v1 fn1 defaultFmtOptions] := by
  simp only [decodeFmtArguments, dotTplBytes, heven, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem fmtRef8_false (p : BitVec 64) (v : BitVec 8) :
    fmtRef8 false p v = (p ↦₈ v) :=
  rfl

private theorem fmtRef8_true (p : BitVec 64) (v : BitVec 8) :
    fmtRef8 true p v = (p ↦₈ᵣ v) :=
  rfl

private theorem fmtArgCallSpec_congr_R {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {R1 R2 : SepProp} {Step : FmtCall → FmtBuf → Bool → FmtBuf → Prop}
    {Panic : FmtCall → FmtBuf → State → Prop} {Oom : FmtCall → FmtBuf → State → Prop}
    {stackBytes idx : Nat} {t0 : State} {out valPtr fn : BitVec 64} {opts : FmtOptions}
    {P : Program} (hR : R1 = R2)
    (hok : subroutine_ok P fn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R2 t0 out)
        (fmtInnerBudgetStep Step) (fmtInnerBudgetPanic t0 Panic)
        (fmtInnerBudgetOom B st0 Oom) stackBytes out va.vtable idx valPtr fn opts)) :
    subroutine_ok P fn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R1 t0 out)
        (fmtInnerBudgetStep Step) (fmtInnerBudgetPanic t0 Panic)
        (fmtInnerBudgetOom B st0 Oom) stackBytes out va.vtable idx valPtr fn opts) :=
  hR ▸ hok

/-- Placed `fmtArgCallSpec` for `<core::num::nonzero::NonZero<u8> as core::fmt::Display>::fmt`
    (`libsignalSessionLib` Block `217`, `40` B), parametric over `keepLs`. -/
theorem lsNonZeroU8Display_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {keepLs : Nat → Bool} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextU8Fmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclU8Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (hkeep217 : keepLs 217 = true)
    (hnoExt217 : LibBlockNoExtern libsignalSessionLib lsmpl P 217)
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere keepLs lsmpl m)
    (_htieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out valPtr : BitVec 64)
    (valRo : Bool) (val : BitVec 8)
    (hpcs : argPieces idx = [formatDecimalNat val.toNat])
    (hstk : 32 + 192 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (fmtRef8 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 217)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx valPtr (lsmpl.base 217) defaultFmtOptions) := by
  dsimp only
  let lutAtom : SepProp :=
    coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes
  apply subroutine_ok_of_sepWPp_clLsWhere hclLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  let tmpPtr : BitVec 64 := s0.sp - 20#64
  let R_sub : SepProp := (fmtRef8 false tmpPtr val ∗ lutAtom) ∗ R_rest
  have hu8 := fmtArgCallSpec_many_of_known_gen (argBytes := fun _ => formatDecimalNat val.toNat)
    (argPieces := argPieces) rfl hpcs
    (cliU8Display_fmtArg_ok L hplFmt hextU8Fmt hclU8Fmt st0 R_rest
      (fun _ => formatDecimalNat val.toNat) t0 stringWriterStack (stackBytes - 32)
      idx out tmpPtr false val rfl ⟨Nat.le_refl _, by omega⟩ (by omega))
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((fmtRef8 valRo valPtr val ∗
          formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            (lutAtom ∗ R_rest) t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR]; dsimp only [fmtInnerBudgetW, lutAtom]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack32_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) ∗
        ((fmtRef8 valRo valPtr val ∗
          formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            (lutAtom ∗ R_rest) t0 out st s0 ∗
          stackFrameAt (s0.sp - 32#64) (stackBytes - 32)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 4 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3
  have hm2 :
      s0.mem ⊨
        (∃∗ b4 : BitVec 8,
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ memRegion (s0.sp - 24#64) 4 ∗
          (tmpPtr ↦₈ b4) ∗ memRegion (s0.sp - 19#64) 3 ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) ∗
        ((fmtRef8 valRo valPtr val ∗
          formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            (lutAtom ∗ R_rest) t0 out st s0 ∗
          stackFrameAt (s0.sp - 32#64) (stackBytes - 32)) ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left ?_) hm1
    have hs := slot8_split_at4 (s0.sp - 24#64) v1
    have ha4 : s0.sp - 24#64 + 4#64 = tmpPtr := by dsimp only [tmpPtr]; bv_omega
    have ha5 : s0.sp - 24#64 + 5#64 = s0.sp - 19#64 := by bv_omega
    rw [ha4, ha5] at hs
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left hs)) ?_
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) ?_
    rw [sepExists_sepConj_left]
    exact Entails.sepExists_mono fun _ => Entails.of_eq (by sep_ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  rcases hm2 with ⟨b4, hm2⟩
  rw [← sepConj_assoc] at hm2
  refine ⟨_, hm2, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 217
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep217⟩
    hnoExt217
    ls_checkNoSvc0_217
    (mid := coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_217).rebase (blkPl_217).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_217).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = valPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [tmpPtr]
  let F_frame : SepProp :=
    fmtRef8 valRo valPtr val ∗
      ((s0.sp - 32#64) ↦₆₄ v0) ∗ memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  cases valRo <;>
  · (first | (wp_conv_pre => rw [fmtRef8_false]) | (wp_conv_pre => rw [fmtRef8_true]))
    iterate 7 wp_step
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm])
      (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hsp_sm : sm.sp = s0.sp - 32#64 := by
      rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have hframe1 : FmtWriteFrame s0 sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    have hfp_in : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) :=
      hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr :=
      hcpu_in.readReg64 Reg.lr
    refine call_wpp_where (x := (st, f)) (F := F_frame) hu8 hcl_sm
      (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by
        unfold State.spAligned at hsp0 ⊢
        rw [hsp_sm]
        exact spAligned_sub_16k hsp0 32 (by decide))
      (by rw [hcpu_out.readReg64])
      (fun R' hm => ?_)
      (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
      (fun sf _ _ hm_pan => ?_)
      (fun sf_call hpcf hrunf hspf hcsf hcl_sf => ?_)
      (fun sf R' _ hoom => ?_)
    · refine Satisfies.mono ?_ hm
      have htr := fmtInnerBudgetW_transport (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) (lutAtom ∗ R_rest) t0 out st s0 sm hframe1
      have hx0_sm : sm.readReg64 .x0 = tmpPtr := by
        rw [hcpu_out.readReg64]; dsimp only [tmpPtr]; simp [arm64_norm]
      have hx1_sm : sm.readReg64 .x1 = f := by
        rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0
      dsimp only [fmtArgCallSpec]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            (lutAtom ∗ R_rest) t0 out st s0) ∗
            (((tmpPtr ↦₈ val) ∗
              formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
              stackFrameAt sm.sp (stackBytes - 32)) ∗ (F_frame ∗ R')) by
          dsimp only [F_frame, tmpPtr]
          (try rw [fmtRef8_false])
          (try rw [fmtRef8_true])
          rw [hsp_sm, hfp_in, hlr_in]
          sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left htr) ?_
      refine Entails.trans (Entails.of_eq (show
        fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
          (lutAtom ∗ R_rest) t0 out st sm ∗
          (((tmpPtr ↦₈ val) ∗
            formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
            stackFrameAt sm.sp (stackBytes - 32)) ∗ (F_frame ∗ R')) =
        (formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            R_sub t0 out st sm ∗
          stackFrameAt sm.sp (stackBytes - 32)) ∗ (F_frame ∗ R') by
        dsimp only [fmtInnerBudgetW, R_sub]
        rw [fmtRef8_false]
        sep_ac_rfl)) ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_right ⟨hx0_sm, hx1_sm⟩ (Entails.refl _)
    · dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces] at hm_pan ⊢
      exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan
    · dsimp only [fmtArgCallSpec]
      intro R' hm_after hL_P
      rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
      rcases hm_after with ⟨ok, hm_after⟩
      rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
      rcases hm_after with ⟨st', hm_after⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm_after
      rcases hm_after with ⟨⟨hw0_sf, hstep_u8⟩, hm_epi_raw⟩
      have hm_epi :
          sf_call.mem ⊨
            (memRegion f 24 ∗
              fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
                R_sub t0 out st' sf_call ∗
              stackFrameAt sm.sp (stackBytes - 32) ∗ F_frame) ∗ R' :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_epi_raw
      have hstep_217 :
          fmtInnerBudgetStep (manyArgStep argPieces)
            (.fmtArg idx valPtr (lsmpl.base 217) defaultFmtOptions) st ok st' := by
        dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces] at hstep_u8 ⊢
        exact hstep_u8
      have hsp_sf : sf_call.sp = s0.sp - 32#64 := hspf.trans hsp_sm
      refine sepWPp_seg_lib_block_pureWhere 217
        ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep217⟩
        hnoExt217
        ls_checkNoSvc0_217
        (mid := s0.readReg64 Reg.lr)
        hcl_sf
        (fun s2' hcpu2_in => ?_) R' hm_epi hL_P
      rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_217).rebase (blkPl_217).base (fun _ => none))]
      have hpc2' : s2'.pc = (blkPl_217).base + 28#64 := hcpu2_in.pc_eq.trans hpcf
      have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
      have hsp2' : s2'.sp = s0.sp - 32#64 := hcpu2_in.sp_eq.trans hsp_sf
      dsimp only [F_frame]
      wp_conv_pre => rw [hsp_sm]
      iterate 3 wp_step
      refine SepWP.done
        (by simp only [arm64_norm])
        (by simpa [arm64_norm] using hrun2')
        fun sf hcpu2_out _hcl_end hpseg2 => ?_
      have hpc_end : sf.pc = s0.readReg64 Reg.lr := by
        rw [hcpu2_out.pc_eq]; simp [arm64_norm]
      have hrun_end : sf.status = .Running := by
        rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
      have hsp_end : sf.sp = s0.sp := by
        rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
      have hw0_end : sf.readReg32 .x0 &&& 1#32 = if ok then 0#32 else 1#32 := by
        have hx0_eq : sf.readReg32 .x0 = sf_call.readReg32 .x0 :=
          (hcpu2_out.readReg32 .x0).trans (by simpa [arm64_norm] using hcpu2_in.readReg32 .x0)
        rw [hx0_eq]
        exact hw0_sf
      have hframe2 : FmtWriteFrame sf_call sf :=
        fmtWriteFrame_of_pureSeg hpseg2
          (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
          (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
      have hcs_end : CalleeSavedPreserved s0 sf :=
        calleeSavedPreserved_across_fp_frame hcpu_in hcpu_out hcsf hcpu2_in hcpu2_out
          (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
          (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
      exact fun R'' hm_end _ => ⟨sf, .refl sf, Or.inl ⟨hpc_end, hrun_end, _, hm_end, ⟨fun hm_post => by
        refine Satisfies.mono (sepConj_mono_left ?_) hm_post
        refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
        refine Entails.pure_right ⟨hw0_end, hstep_217⟩ ?_
        have htr2 := fmtInnerBudgetW_transport (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out st' sf_call sf hframe2
        have hm8_fold :
            memRegion (s0.sp - 24#64) 4 ∗ ((s0.sp - 20#64) ↦₈ val) ∗
              memRegion (s0.sp - 19#64) 3 ⊢ memRegion (s0.sp - 24#64) 8 := by
          have hs := slot8_fold_at4 (s0.sp - 24#64) val
          rwa [show s0.sp - 24#64 + 4#64 = s0.sp - 20#64 by bv_omega,
               show s0.sp - 24#64 + 5#64 = s0.sp - 19#64 by bv_omega] at hs
        have hstk_fold := stack32_mem8_fold s0.sp v0 (s0.readReg64 (.gpr 29#5))
          (s0.readReg64 Reg.lr) stackBytes ⟨by omega, hstk.2⟩
        refine Entails.trans (Entails.of_eq (show _ =
          memRegion f 24 ∗
            fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
              R_client t0 out st' sf_call ∗
            ((s0.sp - 32#64) ↦₆₄ v0) ∗
            (memRegion (s0.sp - 24#64) 4 ∗ ((s0.sp - 20#64) ↦₈ val) ∗
              memRegion (s0.sp - 19#64) 3) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
            stackFrameAt (s0.sp - 32#64) (stackBytes - 32) by
          rw [hR]
          dsimp only [toRustAllocBudget, fmtInnerBudgetW, R_sub, lutAtom, tmpPtr]
          (try rw [fmtRef8_false])
          (try rw [fmtRef8_true])
          sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_left htr2)) ?_
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hm8_fold)))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          memRegion f 24 ∗
            (fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
              R_client t0 out st' sf ∗
              (((s0.sp - 32#64) ↦₆₄ v0) ∗ memRegion (s0.sp - 24#64) 8 ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
                stackFrameAt (s0.sp - 32#64) (stackBytes - 32))) by
          sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right hstk_fold),
        hsp_end, hcs_end⟩⟩⟩
    · dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces] at hoom ⊢
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

/-- Placed `fmtArgCallSpec` (`manyArgStep`) for `<libsignal_core::address::DeviceId as Display>::fmt`
    (`libsignalSessionLib` Block `214`, `60` B), parametric over `keepLs`. -/
theorem lsDeviceIdDisplay_many_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {keepLs : Nat → Bool} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextU8Fmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclU8Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (hkeep214 : keepLs 214 = true)
    (hkeep217 : keepLs 217 = true)
    (hnoExt214 : LibBlockNoExtern libsignalSessionLib lsmpl P 214)
    (hnoExt217 : LibBlockNoExtern libsignalSessionLib lsmpl P 217)
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere keepLs lsmpl m)
    (htieFmtWrite : lsρ lsFmtWriteSym = coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (htieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out devPtr : BitVec 64)
    (devRo : Bool) (dev : BitVec 8)
    (hpcs : argPieces idx = [formatDecimalNat dev.toNat])
    (hstk : 368 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (fmtRef8 devRo devPtr dev ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
        (protoAddrRoSep lsmpl ∗ R_rest)) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 214)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx devPtr (lsmpl.base 214) defaultFmtOptions) := by
  intro B va
  apply subroutine_ok_of_sepWPp_clLsWhere hclLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = devPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack32_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) ∗
        ((formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt (s0.sp - 32#64) (stackBytes - 32)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 4 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 214
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep214⟩
    hnoExt214
    ls_checkNoSvc0_214
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_214).rebase (blkPl_214).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_214).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = devPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  wp_conv_pre => unfold formatterAt
  iterate 10 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack : Nat := stackBytes - 32 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => [formatDecimalNat dev.toNat]
  let F_frame : SepProp :=
    formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven32 : (s0.sp - 32#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 32 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 32 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 32#64) [(devPtr, lsmpl.base 217)] ∗
      fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) :=
      hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr :=
      hcpu_in.readReg64 Reg.lr
    have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [F_frame, formatterAt, fmtInnerBudgetW]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha24]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_keep_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out devPtr (lsmpl.base 214) f (lsmpl.base 214 + 48#64)
    (lsmpl.ρ lsOneArgTplSym) (s0.sp - 32#64) defaultFmtOptions oneArgTplBytes
    [(devPtr, lsmpl.base 217)]
    [FmtCall.fmtArg 0 devPtr (lsmpl.base 217) defaultFmtOptions]
    st R s0 sm
    (by simpa [subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven32
    (decode_oneArgTpl _ _ _ _ heven32)
    (protoAddrRoSep_dup_in_R (by decide) hR)
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨hidx, hval, hfn, hopt⟩
      subst idx_i val_i fn_i opt_i
      exact lsNonZeroU8Display_fmtArg_ok L hplFmt hextU8Fmt hclU8Fmt hkeep217 hnoExt217 hclLs
        htieU8 st0 subPieces t0 subStack 0 out devPtr devRo dev rfl
        ⟨by dsimp only [subStack]; omega, by omega⟩ hR)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by
      unfold State.spAligned at hsp0 ⊢
      rw [hsp_sm]
      exact spAligned_sub_16k hsp0 32 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 32#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 214
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep214⟩
    hnoExt214
    ls_checkNoSvc0_214
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_214).rebase (blkPl_214).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_214).base + 48#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 32#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  dsimp only [F_frame]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha24, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by
    rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by
    rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by
    rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
  have hw0_end : sf.readReg32 .x0 &&& 1#32 = 0#32 := by
    have h := (hcpu2_out.readReg32 .x0).trans (by simpa [arm64_norm] using hx0_2')
    rw [h]; decide
  have hframe2 : FmtWriteFrame sf_call sf :=
    fmtWriteFrame_of_pureSeg hpseg2
      (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
      (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
  have hcs_end : CalleeSavedPreserved s0 sf :=
    calleeSavedPreserved_across_fp_frame hcpu_in hcpu_out hcsf hcpu2_in hcpu2_out
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
  exact fun R' hm_end _ => ⟨sf, .refl sf, Or.inl ⟨hpc_end, hrun_end, _, hm_end, ⟨fun hm_post => by
    dsimp only [fmtArgCallSpec, fmtInnerBudgetStep]
    refine Satisfies.mono (sepConj_mono_left ?_) hm_post
    refine Entails.sepExists_right true (Entails.sepExists_right st' ?_)
    refine Entails.pure_right ⟨hw0_end, hstep_outer⟩ ?_
    have htr2 := fmtInnerBudgetW_transport B st0 va R_client t0 out st' sf_call sf hframe2
    have hfmt24 := formatterAt_entails_memRegion24 f out va.vtable defaultFmtOptions
    have hfold32 := stack32_fold s0.sp devPtr (lsmpl.base 217)
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes ⟨by omega, hstk.2⟩
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        fmtInnerBudgetW B st0 va R_client t0 out st' sf_call ∗
        (((s0.sp - 32#64) ↦₆₄ devPtr) ∗ ((s0.sp - 24#64) ↦₆₄ lsmpl.base 217) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 32#64) (stackBytes - 32)) by
      sep_ac_rfl)) ?_
    exact sepConj_mono hfmt24 (sepConj_mono htr2 hfold32),
    hsp_end, hcs_end⟩⟩⟩

/-- Placed `fmtArgCallSpec` (`knownArgStep`) for `<libsignal_core::address::DeviceId as Display>::fmt`
    (`libsignalSessionLib` Block `214`). -/
theorem lsDeviceIdDisplay_known_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {keepLs : Nat → Bool} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextU8Fmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclU8Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (hkeep214 : keepLs 214 = true)
    (hkeep217 : keepLs 217 = true)
    (hnoExt214 : LibBlockNoExtern libsignalSessionLib lsmpl P 214)
    (hnoExt217 : LibBlockNoExtern libsignalSessionLib lsmpl P 217)
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere keepLs lsmpl m)
    (htieFmtWrite : lsρ lsFmtWriteSym = coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (htieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argBytes : Nat → List (BitVec 8))
    (t0 : State) (stackBytes idx : Nat) (out devPtr : BitVec 64)
    (devRo : Bool) (dev : BitVec 8)
    (harg : argBytes idx = formatDecimalNat dev.toNat)
    (hstk : 368 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (fmtRef8 devRo devPtr dev ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
        (protoAddrRoSep lsmpl ∗ R_rest)) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 214)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
        stackBytes out va.vtable idx devPtr (lsmpl.base 214) defaultFmtOptions) := by
  intro B va
  exact fmtArgCallSpec_known_of_many_singleton
    (argPieces := fun _ => [formatDecimalNat dev.toNat]) harg rfl
    (lsDeviceIdDisplay_many_fmtArg_ok L hplFmt hextU8Fmt hclU8Fmt hkeep214 hkeep217
      hnoExt214 hnoExt217 hclLs htieFmtWrite htieU8 st0
      (fun _ => [formatDecimalNat dev.toNat]) t0 stackBytes idx out devPtr devRo dev rfl hstk hR)

/-- Placed `fmtArgCallSpec` (`manyArgStep`) for
    `<libsignal_core::address::ProtocolAddress as Display>::fmt`
    (`libsignalSessionLib` Block `215`, `72` B), emitting the 3 pieces
    `[nameBs, [0x2e#8], formatDecimalNat dev.toNat]`. -/
theorem lsProtoAddrDisplay_many_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {keepLs : Nat → Bool} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextStrFmt : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P)
    (hclStrFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m)
    (hextU8Fmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclU8Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (hplLs : libsignalSessionLib.Placeable lsmpl)
    (hkeep214 : keepLs 214 = true)
    (hkeep215 : keepLs 215 = true)
    (hkeep216 : keepLs 216 = true)
    (hkeep217 : keepLs 217 = true)
    (hnoExt214 : LibBlockNoExtern libsignalSessionLib lsmpl P 214)
    (hnoExt215 : LibBlockNoExtern libsignalSessionLib lsmpl P 215)
    (hnoExt216 : LibBlockNoExtern libsignalSessionLib lsmpl P 216)
    (hnoExt217 : LibBlockNoExtern libsignalSessionLib lsmpl P 217)
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere keepLs lsmpl m)
    (htieFmtWrite : lsρ lsFmtWriteSym = coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (htieU8 : lsρ lsU8DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
    (htieStr : lsρ lsStrDisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out addrPtr nameCap nameDataPtr : BitVec 64)
    (nameBs : List (BitVec 8)) (strRefRo strSrcRo devRo : Bool) (dev : BitVec 8)
    (hlen : nameBs.length < 2 ^ 60)
    (hpcs : argPieces idx = [nameBs, [0x2e#8], formatDecimalNat dev.toNat])
    (hstk : 528 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      ((fmtRefString strRefRo addrPtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
        fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
        (fmtRef8 devRo (addrPtr + 24#64) dev ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes))) ∗
        (protoAddrRoSep lsmpl ∗ R_rest)) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 215)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx addrPtr (lsmpl.base 215) defaultFmtOptions) := by
  intro B va
  apply subroutine_ok_of_sepWPp_clLsWhere hclLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = addrPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack48_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
          ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
          ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
          ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
        ((formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt (s0.sp - 48#64) (stackBytes - 48)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 6 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 215
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep215⟩
    hnoExt215
    ls_checkNoSvc0_215
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_215).rebase (blkPl_215).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_215).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = addrPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  wp_conv_pre => unfold formatterAt
  iterate 12 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack : Nat := stackBytes - 48 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) :=
    fun i => if i = 0 then [nameBs] else [formatDecimalNat dev.toNat]
  let F_frame : SepProp :=
    formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 48#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven48 : (s0.sp - 48#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 48 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 48 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 48#64)
      [(addrPtr, lsmpl.base 216), (addrPtr + 24#64, lsmpl.base 214)] ∗
      fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) :=
      hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr :=
      hcpu_in.readReg64 Reg.lr
    have ha40 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_omega
    have ha32 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_omega
    have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
    rw [fmtArgEntriesAt_false_pair]
    dsimp only [F_frame, formatterAt, fmtInnerBudgetW]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha40, ha32, ha24]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_keep_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out addrPtr (lsmpl.base 215) f (lsmpl.base 215 + 60#64)
    (lsmpl.ρ lsDotTplSym) (s0.sp - 48#64) defaultFmtOptions dotTplBytes
    [(addrPtr, lsmpl.base 216), (addrPtr + 24#64, lsmpl.base 214)]
    [FmtCall.fmtArg 0 addrPtr (lsmpl.base 216) defaultFmtOptions,
     FmtCall.writeStr (lsmpl.ρ lsDotTplSym + 2#64) [0x2e#8],
     FmtCall.fmtArg 1 (addrPtr + 24#64) (lsmpl.base 214) defaultFmtOptions]
    st R s0 sm
    (by simpa [subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven48
    (decode_dotTpl _ _ _ _ _ _ heven48)
    (protoAddrRoSep_dup_in_R (by decide) hR)
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨hidx, hval, hfn, hopt⟩ | ⟨hidx, hval, hfn, hopt⟩ <;>
        subst idx_i val_i fn_i opt_i
      · have htarget216 :
            libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib 216) =
              coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
          rw [cliStringDisplayShim_targetSym (by decide), ls_resolve_strDisplayFmtSym]
          exact htieStr
        exact fmtArgCallSpec_many_of_known_gen (argBytes := fun _ => nameBs)
          (argPieces := subPieces) rfl rfl
          (cliStringDisplayShim_fmtArg_ok L hplFmt hextStrFmt hclStrFmt hplLs 216
            hkeep216 (cliStringDisplayShim_check (by decide)) hnoExt216 hclLs htarget216
            st0 R_client
            ((fmtRef8 devRo (addrPtr + 24#64) dev ∗
              (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
              (protoAddrRoSep lsmpl ∗ R_rest))
            (fun _ => nameBs) t0 stringWriterStack subStack 0 out addrPtr nameCap nameDataPtr
            (lsmpl.base 216) strRefRo strSrcRo nameBs rfl hlen rfl
            ⟨Nat.le_refl _, by omega⟩ (by dsimp only [subStack]; omega)
            (by rw [hR]; sep_ac_rfl))
      · exact lsDeviceIdDisplay_many_fmtArg_ok L hplFmt hextU8Fmt hclU8Fmt hkeep214 hkeep217
          hnoExt214 hnoExt217 hclLs htieFmtWrite htieU8 st0 subPieces t0 subStack 1 out
          (addrPtr + 24#64) devRo dev rfl
          ⟨by dsimp only [subStack]; omega, by omega⟩
          (by rw [hR]; sep_ac_rfl))
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by
      unfold State.spAligned at hsp0 ⊢
      rw [hsp_sm]
      exact spAligned_sub_16k hsp0 48 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 48#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 215
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, hkeep215⟩
    hnoExt215
    ls_checkNoSvc0_215
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_215).rebase (blkPl_215).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_215).base + 60#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 48#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha40 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_omega
  have ha32 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_omega
  have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  dsimp only [F_frame]
  wp_conv_pre => rw [fmtArgEntriesAt_false_pair, ha40, ha32, ha24, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by
    rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by
    rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by
    rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
  have hw0_end : sf.readReg32 .x0 &&& 1#32 = 0#32 := by
    have h := (hcpu2_out.readReg32 .x0).trans (by simpa [arm64_norm] using hx0_2')
    rw [h]; decide
  have hframe2 : FmtWriteFrame sf_call sf :=
    fmtWriteFrame_of_pureSeg hpseg2
      (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
      (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
  have hcs_end : CalleeSavedPreserved s0 sf :=
    calleeSavedPreserved_across_fp_frame hcpu_in hcpu_out hcsf hcpu2_in hcpu2_out
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
  exact fun R' hm_end _ => ⟨sf, .refl sf, Or.inl ⟨hpc_end, hrun_end, _, hm_end, ⟨fun hm_post => by
    dsimp only [fmtArgCallSpec, fmtInnerBudgetStep]
    refine Satisfies.mono (sepConj_mono_left ?_) hm_post
    refine Entails.sepExists_right true (Entails.sepExists_right st' ?_)
    refine Entails.pure_right ⟨hw0_end, hstep_outer⟩ ?_
    have htr2 := fmtInnerBudgetW_transport B st0 va R_client t0 out st' sf_call sf hframe2
    have hfmt24 := formatterAt_entails_memRegion24 f out va.vtable defaultFmtOptions
    have hfold48 := stack48_fold s0.sp addrPtr (lsmpl.base 216) (addrPtr + 24#64)
      (lsmpl.base 214) (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        fmtInnerBudgetW B st0 va R_client t0 out st' sf_call ∗
        (((s0.sp - 48#64) ↦₆₄ addrPtr) ∗ ((s0.sp - 40#64) ↦₆₄ lsmpl.base 216) ∗
          ((s0.sp - 32#64) ↦₆₄ (addrPtr + 24#64)) ∗ ((s0.sp - 24#64) ↦₆₄ lsmpl.base 214) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 48#64) (stackBytes - 48)) by
      sep_ac_rfl)) ?_
    exact sepConj_mono hfmt24 (sepConj_mono htr2 hfold48),
    hsp_end, hcs_end⟩⟩⟩

/-! ## 4. Headline `.rodata`-Guarded `subroutine_ok` Discharges -/

private theorem decode_prefixedOneArgTpl (x0 x1 v0 fn0 : BitVec 64) (pfxBs : List (BitVec 8))
    (heven : x1.getLsbD 0 = false) (hlo : 1 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 127) :
    decodeFmtArguments x0 x1 (prefixedOneArgTplBytes pfxBs) [(v0, fn0)] =
      some [FmtCall.writeStr (x0 + 1#64) pfxBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  have hn0 : BitVec.ofNat 8 pfxBs.length ≠ 0#8 := by
    intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ht
    rw [Nat.mod_eq_of_lt (by omega)] at ht
    omega
  have hlt80 : pfxBs.length < 0x80 := by omega
  have hto : (BitVec.ofNat 8 pfxBs.length).toNat = pfxBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_rest : ¬ (pfxBs ++ [0xc0#8, 0x00#8]).length < pfxBs.length := by simp
  have htake : (pfxBs ++ [0xc0#8, 0x00#8]).take pfxBs.length = pfxBs := by simp
  have hdrop : (pfxBs ++ [0xc0#8, 0x00#8]).drop pfxBs.length = [0xc0#8, 0x00#8] := by simp
  dsimp only [prefixedOneArgTplBytes]
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte,
    List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil,
    Nat.zero_add]
  unfold VerifiedLibraries.RustStd.decodeFmtTemplate
  simp only [hn0, ↓reduceIte, hto, hlt80, hlen_rest, hdrop, htake]
  unfold VerifiedLibraries.RustStd.decodeFmtTemplate
  simp [VerifiedLibraries.RustStd.decodeFmtPlaceholder,
    VerifiedLibraries.RustStd.decodeFmtTemplate, defaultFmtOptions]

/-- Headline `.rodata`-guarded `subroutine_ok` for `core::fmt::write` on
    `cliFmtWriteProtoAddrSpec` (`<ProtocolAddress as Display>::fmt`, Block `215`). -/
theorem cliCoreFmtWrite_protoAddr_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits}
    {EnvOf : CliFmtWriteProtoAddrCall → List AllocEvent → Prop}
    {P : Program} {mplCore : MultiPlacement}
    {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement} {mplFmt : MultiPlacement}
    (L : CliFmtWriteSubLink M A lim P mplCore mplAllocOf mplFmt) :
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      (withRoMemGuard (cliFmtWriteRoGuard mplAllocOf mplFmt)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec M A lim EnvOf))) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨c, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hRoLs, hLutRo, hVtRoAll⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hshimMem, heven, hlen, hFit, hEx⟩, hm0⟩
  let mplAlloc := mplAllocOf c.vtKind
  let va := allocStringWriteAddrs mplAlloc
  let stackBytes : Nat := extHookStack - 0x70
  let lutAtom : SepProp :=
    coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes
  let R_client : SepProp :=
    (fmtRefString c.strRefRo c.namePtr c.nameCap c.nameDataPtr (BitVec.ofNat 64 c.nameBs.length) ∗
      fmtSrcBytes c.strSrcRo c.nameDataPtr c.nameBs) ∗
    (fmtRef8 c.devRo c.devPtr c.dev ∗ lutAtom) ∗
    protoAddrRoSep lsmpl
  let argBytes : Nat → List (BitVec 8) :=
    fun i => if i = 0 then c.nameBs else formatDecimalNat c.dev.toNat
  have hvt : va.vtable = c.vtKind.vtableAddr := L.vtEq c.vtKind
  have hdec := decode_dotTpl c.x2 c.x3 c.namePtr (lsmpl.base c.shimBlock)
    c.devPtr (lsmpl.base 214) heven
  have hArgsOk :
      FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
        (knownArgStep argBytes) (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0
        [FmtCall.fmtArg 0 c.namePtr (lsmpl.base c.shimBlock) defaultFmtOptions,
         FmtCall.writeStr (c.x2 + 2#64) [0x2e#8],
         FmtCall.fmtArg 1 c.devPtr (lsmpl.base 214) defaultFmtOptions] := by
    intro idx valPtr fmtFn opts hmem out
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      FmtCall.fmtArg.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have htarget :
          libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib c.shimBlock) =
            coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
        rw [cliStringDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
        exact L.tieStrDisplay
      exact cliStringDisplayShim_fmtArg_ok (L.linkAlloc c.vtKind) L.plFmt L.noExtFmtStr L.clFmtStr
        L.plLs c.shimBlock (fmtWriteSubLsKeep_of_stringShim hshimMem)
        (cliStringDisplayShim_check hshimMem)
        (L.noExtLs c.shimBlock (cliStringDisplayShim_lt hshimMem)
          (fmtWriteSubLsKeep_of_stringShim hshimMem))
        L.clLs htarget st0 R_client
        ((fmtRef8 c.devRo c.devPtr c.dev ∗ lutAtom) ∗ protoAddrRoSep lsmpl)
        argBytes s0 stringWriterStack stackBytes 0 out c.namePtr c.nameCap c.nameDataPtr
        (lsmpl.base c.shimBlock) c.strRefRo c.strSrcRo c.nameBs rfl hlen rfl
        ⟨Nat.le_refl _, by decide⟩ (by decide) (by dsimp only [R_client]; sep_ac_rfl)
    · exact lsDeviceIdDisplay_known_fmtArg_ok (R_client := R_client)
        (R_rest := fmtRefString c.strRefRo c.namePtr
          c.nameCap c.nameDataPtr (BitVec.ofNat 64 c.nameBs.length) ∗
          fmtSrcBytes c.strSrcRo c.nameDataPtr c.nameBs)
        (L.linkAlloc c.vtKind) L.plFmt L.noExtFmtU8 L.clFmtU8
        (by decide) (by decide)
        (L.noExtLs 214 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        (L.noExtLs 217 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        L.clLs L.tieFmtWrite L.tieU8 st0 argBytes s0 stackBytes 1 out c.devPtr c.devRo c.dev
        rfl ⟨by decide, by decide⟩ (by dsimp only [R_client, lutAtom]; sep_ac_rfl)
  have hstkEq : stackAt s0.sp extHookStack = stackFrameAt s0.sp (0x70 + stackBytes) :=
    (stackAt_eq_stackFrameAt s0.sp extHookStack (by decide)).trans
      (congrArg (stackFrameAt s0.sp) (by decide))
  have hm_ro :
      s0.mem ⊨ stringWriteVtableAt va ∗ lutAtom ∗ protoAddrRoSep lsmpl ∗
        ((vecU8At A.repAlloc c.v c.cap0 c.ptr0 c.bs ∗
          fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
          c.clientSep ∗ A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
    sat_stringWriteVtableAt (hVtRoAll c.vtKind)
      (sat_decDigitsLut hLutRo (sat_protoAddrRoSep hRoLs hm0))
  have hpre_sub :
      s0.mem ⊨
        (cliCoreFmtWriteVecAtSpec M A lim (EnvOf c) va R_client argBytes stackBytes P).pre
          (c.v, c.cap0, c.ptr0, c.bs, c.argsRo, dotTplBytes, c.args, st0) s0 ∗ R₀ := by
    dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    refine Satisfies.mono ?_ hm_ro
    have hevEq :
        fmtWriteKnownEvents c.bs.length c.cap0
          (callLens argBytes
            [FmtCall.fmtArg 0 c.namePtr (lsmpl.base c.shimBlock) defaultFmtOptions,
             FmtCall.writeStr (c.x2 + 2#64) [0x2e#8],
             FmtCall.fmtArg 1 c.devPtr (lsmpl.base 214) defaultFmtOptions]) = c.exactEvs := by
      rfl
    refine Entails.trans (Entails.of_eq (show _ =
      (vecU8At A.repAlloc c.v c.cap0 c.ptr0 c.bs ∗
        fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
        stringWriteVtableAt va ∗ R_client ∗ A.pool lim st0 s0 ∗
        stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀ by
      rw [hstkEq]
      dsimp only [R_client, CliFmtWriteProtoAddrCall.clientSep, CliFmtWriteProtoAddrCall.args,
        lsDeviceIdDisplayBlock]
      sep_ac_rfl)) ?_
    refine sepConj_mono_left ?_
    exact Entails.pure_right
      ⟨hx0, hx1.trans hvt.symm, by decide, by decide, hFit, _,
        hdec,
        by rw [hevEq]; exact hEx, hArgsOk⟩
      (Entails.refl _)
  have hok_sub := cliCoreFmtWrite_vecU8At_placed_ok (Env := EnvOf c)
    (R_client := R_client) (argBytes := argBytes) (stackBytes := stackBytes)
    (L.linkAlloc c.vtKind)
  refine hok_sub.mono_outcome _ R₀ s0 hpc hrun hpre_sub hsp0 ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ EnvOf c evs ∧
          ∃ cs, decodeFmtArguments c.x2 c.x3 dotTplBytes c.args = some cs ∧
            evs = fmtWriteKnownEvents c.bs.length c.cap0 (callLens argBytes cs) ∧
            bs' = c.bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((stringWriteVtableAt va ∗ lutAtom ∗ protoAddrRoSep lsmpl) ∗
            ((vecU8 A.repAlloc c.v bs' ∗
              fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
              c.clientSep ∗ A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp extHookStack) ∗ R₀)) :=
      Satisfies.mono (Entails.of_eq (by
        rw [← hstkEq]
        dsimp only [R_client, CliFmtWriteProtoAddrCall.clientSep]
        sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnv, _⟩, hp2⟩
    have hp3 := Satisfies.drop_left hp2
    dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec]
    refine Satisfies.mono (sepConj_mono_left ?_) hp3
    rw [pure_sepConj_of_true ⟨hfs, htr⟩]
    refine Entails.sepExists_right evs (Entails.sepExists_right bs' ?_)
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnv⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim

/-- Headline `.rodata`-guarded `subroutine_ok` for `alloc::fmt::format::format_inner` on
    `cliFormatInnerLsCallSpec` across all 13 call shapes in `CliFormatInnerLsShape`. -/
theorem cliAllocFormatInner_lsCall_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits}
    {EnvOf : CliFormatInnerLsCall → List AllocEvent → Prop}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFormatInnerSubLink M A lim P mplCore mplAlloc mplFmt) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      (withRoMemGuard (cliFormatInnerRoGuard mplAlloc mplFmt)
        (withFsTraceExact (cliFormatInnerLsCallSpec M A lim EnvOf))) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨c, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hRoLs, hLutRo, hVtRo, hAes1Ro, hAes2Ro⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
  rcases c with ⟨ret, x0, x1, argsRo, shape⟩
  let va := allocStringWriteAddrs mplAlloc
  let stackBytes : Nat := extHookStack - formatInnerFrame - 0x70
  let lutAtom : SepProp :=
    coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes
  have dischargeSingle :
      ∀ (sh : CliFormatInnerLsShape) (R_ro : SepProp)
        (argBytes : Nat → List (BitVec 8)) (cs : List FmtCall),
        let c0 : CliFormatInnerLsCall := ⟨ret, x0, x1, argsRo, sh⟩
        FitsEnv M lim st0 (EnvOf c0) →
        EnvOf c0 c0.exactEvs →
        (s0.mem ⊨ stringWriteVtableAt va ∗ R_ro ∗
          ((fmtArgumentsAt argsRo x0 x1 c0.tpl c0.args ∗
            memRegion ret 24 ∗ c0.clientSep ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀)) →
        decodeFmtArguments x0 x1 c0.tpl c0.args = some cs →
        fmtLiteralLen cs < 2 ^ 60 →
        formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) = c0.exactEvs →
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va (c0.clientSep ∗ R_ro)
          (knownArgStep argBytes) (knownArgPanic argBytes)
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs →
        reaches_outcome P
          (withRoMemGuard (cliFormatInnerRoGuard mplAlloc mplFmt)
            (withFsTraceExact (cliFormatInnerLsCallSpec M A lim EnvOf)))
          (c0, st0) R₀ s0 s0 := by
    intro sh R_ro argBytes cs c0 hFit0 hEx0 hm_ro hdec hlit hevEq hArgsOk
    have hpre_sub :
        s0.mem ⊨
          (cliAllocFormatInnerSpec M A lim (EnvOf c0) va (c0.clientSep ∗ R_ro)
            argBytes stackBytes P).pre (ret, argsRo, c0.tpl, c0.args, st0) s0 ∗ R₀ := by
      dsimp only [cliAllocFormatInnerSpec]
      rw [hx0, hx1]
      refine Satisfies.mono ?_ hm_ro
      refine Entails.trans (Entails.of_eq (show _ =
        (fmtArgumentsAt argsRo x0 x1 c0.tpl c0.args ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗ (c0.clientSep ∗ R_ro) ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀ by sep_ac_rfl)) ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_right
        ⟨hx8, by decide, by decide, hFit0, cs,
          hdec, hlit,
          by rw [hevEq]; exact hEx0, hArgsOk⟩
        (Entails.refl _)
    have hok_sub := cliAllocFormatInner_placed_ok (Env := EnvOf c0)
      (R_client := c0.clientSep ∗ R_ro) (argBytes := argBytes) (stackBytes := stackBytes)
      L.toCliFormatInnerLink
    refine hok_sub.mono_outcome _ R₀ s0 hpc hrun hpre_sub hsp0 ?_
    intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [cliAllocFormatInnerSpec] at hpost
      rw [hx0, hx1] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      rcases hpost with ⟨bs', hpost⟩
      have hp1 :
          sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
            EnvOf c0 evs ∧
            ∃ cs', decodeFmtArguments x0 x1 c0.tpl c0.args = some cs' ∧
              evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs') (callLens argBytes cs') ∧
              bs' = cs'.flatMap (callBytes argBytes)⌝ ∗
            ((stringWriteVtableAt va ∗ R_ro) ∗
              ((vecU8 A.repAlloc ret bs' ∗
                fmtArgumentsAt argsRo x0 x1 c0.tpl c0.args ∗
                c0.clientSep ∗ A.pool lim (M.stepEvents evs st0) sf ∗
                stackAt s0.sp extHookStack) ∗ R₀)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hp1
      rcases hp1 with ⟨⟨hacp, hfs, htr, hEnv, _⟩, hp2⟩
      have hp3 := Satisfies.drop_left hp2
      dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec]
      refine Satisfies.mono (sepConj_mono_left ?_) hp3
      rw [pure_sepConj_of_true ⟨hfs, htr⟩]
      refine Entails.sepExists_right evs (Entails.sepExists_right bs' ?_)
      rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnv⟩]
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [cliAllocFormatInnerSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [cliAllocFormatInnerSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [cliAllocFormatInnerSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  cases shape with
  | empty =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    refine dischargeSingle .empty emp (fun _ => []) [] hFit hEx
      (sat_stringWriteVtableAt hVtRo (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0))
      (by rw [hshOk]; rfl) (by decide) (by rw [hshOk]; rfl)
      (fun _ _ _ _ hm _ => by cases hm)
  | fromStr litBs =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hodd, hlenEq, hlt60⟩
    have hdec : decodeFmtArguments x0 x1 litBs [] = some [FmtCall.writeStr x0 litBs] :=
      decodeFmtArguments_fromStr x0 x1 litBs hodd hlenEq
    have hevEq :
        formatInnerKnownEvents (fmtEstimatedCapacity x1 [FmtCall.writeStr x0 litBs])
          (callLens (fun _ => []) [FmtCall.writeStr x0 litBs]) =
        (if litBs.length = 0 then [] else rustAllocEvents litBs.length 1) := by
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen, callLens, callBytes,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      rw [hodd]
      simp only [↓reduceIte, Nat.add_zero]
      exact formatInnerKnownEvents_fromStr litBs.length hlt60
    refine dischargeSingle (.fromStr litBs) emp (fun _ => []) [FmtCall.writeStr x0 litBs] hFit hEx
      (sat_stringWriteVtableAt hVtRo (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0))
      hdec (by simpa [fmtLiteralLen] using hlt60)
      (by simpa [CliFormatInnerLsCall.exactEvs] using hevEq)
      (fun _ _ _ _ hm _ => by simp only [List.mem_singleton, reduceCtorEq] at hm)
  | lit0 litBs =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hx1_0, hlo, hhi⟩
    have hdec : decodeFmtArguments x0 x1
        ([BitVec.ofNat 8 litBs.length] ++ litBs ++ [0x00#8]) [] =
        some [FmtCall.writeStr (x0 + 1#64) litBs] := by
      rw [hx1_0]
      exact decodeFmtArguments_shortLiteral x0 hlo hhi
    have hevEq :
        formatInnerKnownEvents
          (fmtEstimatedCapacity x1 [FmtCall.writeStr (x0 + 1#64) litBs])
          (callLens (fun _ => []) [FmtCall.writeStr (x0 + 1#64) litBs]) =
        formatInnerKnownEvents (2 * litBs.length) [litBs.length] := by
      have hemp : litBs.isEmpty = false := by
        cases litBs with
        | nil => simp at hlo
        | cons _ _ => rfl
      have hmod : (2 * litBs.length) % 2 ^ 64 = 2 * litBs.length := Nat.mod_eq_of_lt (by omega)
      rw [hx1_0]
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen, callLens,
        callBytes, List.map]
      simp only [BitVec.getLsbD_zero, hemp, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, hmod]
    refine dischargeSingle (.lit0 litBs) emp (fun _ => [])
      [FmtCall.writeStr (x0 + 1#64) litBs] hFit hEx
      (sat_stringWriteVtableAt hVtRo (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0))
      hdec (by dsimp only [fmtLiteralLen]; omega)
      (by simpa [CliFormatInnerLsCall.exactEvs] using hevEq)
      (fun _ _ _ _ hm _ => by simp only [List.mem_singleton, reduceCtorEq] at hm)
  | u8Display valPtr valRo val =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
    refine dischargeSingle (.u8Display valPtr valRo val) lutAtom argBytes
      [FmtCall.fmtArg 0 valPtr (lsρ lsU8DisplayFmtSym) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo hm0))
      (decode_oneArgTpl x0 x1 valPtr (lsρ lsU8DisplayFmtSym) hshOk)
      (by dsimp only [fmtLiteralLen]; decide)
      (by
        dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, callLens, callBytes,
          argBytes, CliFormatInnerLsCall.exactEvs]
        simp only [hshOk, Bool.false_eq_true, ↓reduceIte]
        rfl)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        rw [L.tieU8]
        exact fmtArgCallSpec_congr_R
          (by dsimp only [CliFormatInnerLsCall.clientSep, lutAtom]; sep_ac_rfl)
          (cliU8Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU8 L.clFmtU8
            st0 emp argBytes s0 stringWriterStack stackBytes 0 out valPtr valRo val
            rfl ⟨Nat.le_refl _, by decide⟩ (by decide)))
  | u32Display valPtr valRo val =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
    refine dischargeSingle (.u32Display valPtr valRo val) lutAtom argBytes
      [FmtCall.fmtArg 0 valPtr (lsρ lsU32DisplayFmtSym) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo hm0))
      (decode_oneArgTpl x0 x1 valPtr (lsρ lsU32DisplayFmtSym) hshOk)
      (by dsimp only [fmtLiteralLen]; decide)
      (by
        dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, callLens, callBytes,
          argBytes, CliFormatInnerLsCall.exactEvs]
        simp only [hshOk, Bool.false_eq_true, ↓reduceIte]
        rfl)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        have htie32 : lsρ lsU32DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym :=
          L.tieU32
        rw [htie32]
        exact fmtArgCallSpec_congr_R
          (by dsimp only [CliFormatInnerLsCall.clientSep, lutAtom]; sep_ac_rfl)
          (cliU32Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU32 L.clFmtU32
            st0 emp argBytes s0 stringWriterStack stackBytes 0 out valPtr valRo val
            rfl ⟨Nat.le_refl _, by decide⟩ (by decide)))
  | u8DisplayPrefixed pfxBs valPtr valRo val =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨heven, hlo, hhi⟩
    let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
    have hevEq :
        formatInnerKnownEvents
          (fmtEstimatedCapacity x1
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsρ lsU8DisplayFmtSym) defaultFmtOptions])
          (callLens argBytes
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsρ lsU8DisplayFmtSym) defaultFmtOptions]) =
        formatInnerKnownEvents (2 * pfxBs.length)
          [pfxBs.length, (formatDecimalNat val.toNat).length] := by
      have hemp : pfxBs.isEmpty = false := by
        cases pfxBs with
        | nil => simp at hlo
        | cons _ _ => rfl
      have hmod : (2 * pfxBs.length) % 2 ^ 64 = 2 * pfxBs.length := Nat.mod_eq_of_lt (by omega)
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen, callLens,
        callBytes, argBytes, List.map]
      simp only [heven, hemp, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hmod]
    refine dischargeSingle (.u8DisplayPrefixed pfxBs valPtr valRo val) lutAtom argBytes
      [FmtCall.writeStr (x0 + 1#64) pfxBs,
       FmtCall.fmtArg 0 valPtr (lsρ lsU8DisplayFmtSym) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo hm0))
      (decode_prefixedOneArgTpl x0 x1 valPtr (lsρ lsU8DisplayFmtSym) pfxBs heven hlo hhi)
      (by dsimp only [fmtLiteralLen]; omega)
      (by simpa [CliFormatInnerLsCall.exactEvs] using hevEq)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        rw [L.tieU8]
        exact fmtArgCallSpec_congr_R
          (by dsimp only [CliFormatInnerLsCall.clientSep, lutAtom]; sep_ac_rfl)
          (cliU8Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU8 L.clFmtU8
            st0 emp argBytes s0 stringWriterStack stackBytes 0 out valPtr valRo val
            rfl ⟨Nat.le_refl _, by decide⟩ (by decide)))
  | strRefDisplayShim shimBlock valPtr strPtr sbs refRo srcRo =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hshimMem, heven, hlen⟩
    let argBytes : Nat → List (BitVec 8) := fun _ => sbs
    refine dischargeSingle (.strRefDisplayShim shimBlock valPtr strPtr sbs refRo srcRo) emp argBytes
      [FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0))
      (decode_oneArgTpl x0 x1 valPtr (lsmpl.base shimBlock) heven)
      (by dsimp only [fmtLiteralLen]; decide)
      (by
        dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, callLens, callBytes,
          argBytes, CliFormatInnerLsCall.exactEvs]
        simp only [heven, Bool.false_eq_true, ↓reduceIte]
        rfl)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        have htarget :
            libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib shimBlock) =
              coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
          rw [cliStrRefDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
          exact L.tieStrDisplay
        exact cliStrRefDisplayShim_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtStr L.clFmtStr
          L.plLs shimBlock (formatInnerSubLsKeep_of_strRefShim hshimMem)
          (cliStrRefDisplayShim_check hshimMem)
          (L.noExtLsAll shimBlock (cliStrRefDisplayShim_lt hshimMem)
            (formatInnerSubLsKeep_of_strRefShim hshimMem))
          L.clLsAll htarget st0 _ emp argBytes s0 stringWriterStack stackBytes 0 out valPtr
          strPtr (lsmpl.base shimBlock) refRo srcRo sbs rfl hlen rfl
          ⟨Nat.le_refl _, by decide⟩ (by decide)
          (by dsimp only [CliFormatInnerLsCall.clientSep]; sep_ac_rfl))
  | strRefDisplayPrefixedShim pfxBs shimBlock valPtr strPtr sbs refRo srcRo =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hshimMem, heven, hlo, hhi, hlen⟩
    let argBytes : Nat → List (BitVec 8) := fun _ => sbs
    have hevEq :
        formatInnerKnownEvents
          (fmtEstimatedCapacity x1
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions])
          (callLens argBytes
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions]) =
        formatInnerKnownEvents (2 * pfxBs.length) [pfxBs.length, sbs.length] := by
      have hemp : pfxBs.isEmpty = false := by
        cases pfxBs with
        | nil => simp at hlo
        | cons _ _ => rfl
      have hmod : (2 * pfxBs.length) % 2 ^ 64 = 2 * pfxBs.length := Nat.mod_eq_of_lt (by omega)
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen, callLens,
        callBytes, argBytes, List.map]
      simp only [heven, hemp, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hmod]
    refine dischargeSingle
      (.strRefDisplayPrefixedShim pfxBs shimBlock valPtr strPtr sbs refRo srcRo) emp argBytes
      [FmtCall.writeStr (x0 + 1#64) pfxBs,
       FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0))
      (decode_prefixedOneArgTpl x0 x1 valPtr (lsmpl.base shimBlock) pfxBs heven hlo hhi)
      (by dsimp only [fmtLiteralLen]; omega)
      (by simpa [CliFormatInnerLsCall.exactEvs] using hevEq)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        have htarget :
            libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib shimBlock) =
              coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
          rw [cliStrRefDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
          exact L.tieStrDisplay
        exact cliStrRefDisplayShim_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtStr L.clFmtStr
          L.plLs shimBlock (formatInnerSubLsKeep_of_strRefShim hshimMem)
          (cliStrRefDisplayShim_check hshimMem)
          (L.noExtLsAll shimBlock (cliStrRefDisplayShim_lt hshimMem)
            (formatInnerSubLsKeep_of_strRefShim hshimMem))
          L.clLsAll htarget st0 _ emp argBytes s0 stringWriterStack stackBytes 0 out valPtr
          strPtr (lsmpl.base shimBlock) refRo srcRo sbs rfl hlen rfl
          ⟨Nat.le_refl _, by decide⟩ (by decide)
          (by dsimp only [CliFormatInnerLsCall.clientSep]; sep_ac_rfl))
  | cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hshimMem, heven, hlo, hhi⟩
    let errAddr : BitVec 64 := if isStr1 then cliAesDecErrStr1Addr else cliAesDecErrStr2Addr
    let errLen : Nat := if isStr1 then 51 else 17
    let sbs : List (BitVec 8) := s0.mem.readBytes errAddr errLen
    have hsbsLen : sbs.length = errLen := Memory.readBytes_length s0.mem errAddr errLen
    have hErrRo : s0.mem.RO errAddr sbs.length := by
      rw [hsbsLen]
      cases isStr1
      · exact hAes2Ro
      · exact hAes1Ro
    have hErrRead : s0.mem.readBytes errAddr sbs.length = sbs := by
      rw [hsbsLen]
    have hErrSat :
        s0.mem ⊨ stringWriteVtableAt va ∗ fmtSrcBytes true errAddr sbs ∗
          ((fmtArgumentsAt argsRo x0 x1
              (CliFormatInnerLsCall.tpl ⟨ret, x0, x1, argsRo,
                .cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo⟩)
              (CliFormatInnerLsCall.args ⟨ret, x0, x1, argsRo,
                .cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo⟩) ∗
            memRegion ret 24 ∗
            CliFormatInnerLsCall.clientSep ⟨ret, x0, x1, argsRo,
              .cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo⟩ ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) := by
      refine sat_stringWriteVtableAt hVtRo ?_
      dsimp only [fmtSrcBytes, ↓reduceIte]
      exact Satisfies.rodata_intro hErrRo hErrRead (by rw [hsbsLen]; cases isStr1 <;> decide) hm0
    let argBytes : Nat → List (BitVec 8) := fun _ => sbs
    have hevEq :
        formatInnerKnownEvents
          (fmtEstimatedCapacity x1
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions])
          (callLens argBytes
            [FmtCall.writeStr (x0 + 1#64) pfxBs,
             FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions]) =
        formatInnerKnownEvents (2 * pfxBs.length) [pfxBs.length, errLen] := by
      have hemp : pfxBs.isEmpty = false := by
        cases pfxBs with
        | nil => simp at hlo
        | cons _ _ => rfl
      have hmod : (2 * pfxBs.length) % 2 ^ 64 = 2 * pfxBs.length := Nat.mod_eq_of_lt (by omega)
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen, callLens,
        callBytes, argBytes, List.map]
      simp only [heven, hemp, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        hmod, hsbsLen]
    have hbvLen : BitVec.ofNat 64 sbs.length = (if isStr1 then 0x33#64 else 0x11#64) := by
      rw [hsbsLen]; cases isStr1 <;> rfl
    refine dischargeSingle
      (.cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo)
      (fmtSrcBytes true errAddr sbs) argBytes
      [FmtCall.writeStr (x0 + 1#64) pfxBs,
       FmtCall.fmtArg 0 valPtr (lsmpl.base shimBlock) defaultFmtOptions] hFit hEx
      hErrSat
      (decode_prefixedOneArgTpl x0 x1 valPtr (lsmpl.base shimBlock) pfxBs heven hlo hhi)
      (by dsimp only [fmtLiteralLen]; omega)
      (by simpa [CliFormatInnerLsCall.exactEvs, errLen] using hevEq)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩
        subst idx_i val_i fn_i opt_i
        have htarget :
            libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib shimBlock) =
              coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
          rw [cliStrRefDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
          exact L.tieStrDisplay
        exact cliStrRefDisplayShim_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtStr L.clFmtStr
          L.plLs shimBlock (formatInnerSubLsKeep_of_strRefShim hshimMem)
          (cliStrRefDisplayShim_check hshimMem)
          (L.noExtLsAll shimBlock (cliStrRefDisplayShim_lt hshimMem)
            (formatInnerSubLsKeep_of_strRefShim hshimMem))
          L.clLsAll htarget st0 _ emp argBytes s0 stringWriterStack stackBytes 0 out valPtr
          errAddr (lsmpl.base shimBlock) refRo true sbs rfl
          (by rw [hsbsLen]; cases isStr1 <;> decide) rfl
          ⟨Nat.le_refl _, by decide⟩ (by decide)
          (by
            dsimp only [CliFormatInnerLsCall.clientSep, errAddr]
            rw [hbvLen]
            sep_ac_rfl))
  | spqrErrorDisplayPrefixed pfxBs errPtr d b1 u1 q1 q2 =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨heven, hd, hlo, hhi⟩
    have hstkEq : stackAt s0.sp extHookStack =
        stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) :=
      (stackAt_eq_stackFrameAt s0.sp extHookStack (by decide)).trans
        (congrArg (stackFrameAt s0.sp) (by decide))
    have hok_spqr := cliAllocFormatInner_spqrErrorDisplayPrefixed_cells_placed_ok
      (Env := EnvOf ⟨ret, x0, x1, argsRo, .spqrErrorDisplayPrefixed pfxBs errPtr d b1 u1 q1 q2⟩)
      (R_rest := emp) (stackBytes := stackBytes) L.toSpqrErrorDisplayLink
      ret x0 x1 errPtr pfxBs argsRo d b1 u1 q1 q2 st0 heven hd hlo hhi hEx
      ⟨by decide, by decide⟩
    have hm_ro :
        s0.mem ⊨ stringWriteVtableAt va ∗ lutAtom ∗
          ((fmtArgumentsAt argsRo x0 x1 (prefixedOneArgTplBytes pfxBs)
              [(errPtr, lsmpl.base 412)] ∗
            memRegion ret 24 ∗ spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
      sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo hm0)
    refine hok_spqr.mono_outcome () R₀ s0 hpc hrun (by
      refine Satisfies.mono ?_ hm_ro
      rw [hstkEq]
      refine Entails.trans (Entails.of_eq (show _ =
        (fmtArgumentsAt argsRo x0 x1 ([BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8])
            [(errPtr, lsmpl.base 412)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗
          (spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗ lutAtom ∗ emp) ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀ by
        dsimp only [prefixedOneArgTplBytes]
        sep_ac_rfl)) ?_
      exact sepConj_mono_left
        (Entails.pure_right ⟨hx8, hx0, hx1, hFit, hRoLs⟩ (Entails.refl _))) hsp0 ?_
    intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨hacp, hfs, htr, hEnv, _⟩, hpost_mem⟩
      have hp2 :
          sf.mem ⊨ (stringWriteVtableAt va ∗ lutAtom) ∗
            ((vecU8 A.repAlloc ret (pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten) ∗
              fmtArgumentsAt argsRo x0 x1 (prefixedOneArgTplBytes pfxBs)
                [(errPtr, lsmpl.base lsSpqrErrorDisplayBlock)] ∗
              spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
        Satisfies.mono (Entails.of_eq (by
          rw [← hstkEq]
          dsimp only [prefixedOneArgTplBytes, lsSpqrErrorDisplayBlock]
          sep_ac_rfl)) hpost_mem
      have hp3 := Satisfies.drop_left hp2
      dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec,
        CliFormatInnerLsCall.tpl, CliFormatInnerLsCall.args, CliFormatInnerLsCall.clientSep]
      refine Satisfies.mono (sepConj_mono_left ?_) hp3
      rw [pure_sepConj_of_true ⟨hfs, htr⟩]
      refine Entails.sepExists_right evs
        (Entails.sepExists_right (pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten) ?_)
      rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnv⟩]
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  | protoAddrDisplay addrPtr nameCap nameDataPtr nameBs strRefRo strSrcRo devRo dev =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨heven, hlen⟩
    let argPieces : Nat → List (List (BitVec 8)) :=
      fun _ => [nameBs, [0x2e#8], formatDecimalNat dev.toNat]
    let R_client : SepProp :=
      ((fmtRefString strRefRo addrPtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
        fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
        (fmtRef8 devRo (addrPtr + 24#64) dev ∗ lutAtom)) ∗
        (protoAddrRoSep lsmpl ∗ emp)
    have hstkEq : stackAt s0.sp extHookStack =
        stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) :=
      (stackAt_eq_stackFrameAt s0.sp extHookStack (by decide)).trans
        (congrArg (stackFrameAt s0.sp) (by decide))
    have hm_ro :
        s0.mem ⊨ stringWriteVtableAt va ∗ lutAtom ∗ protoAddrRoSep lsmpl ∗
          ((fmtArgumentsAt argsRo x0 x1 oneArgTplBytes [(addrPtr, lsmpl.base 215)] ∗
            memRegion ret 24 ∗
            ((fmtRefString strRefRo addrPtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
              fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
              fmtRef8 devRo (addrPtr + 24#64) dev) ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
      sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo (sat_protoAddrRoSep hRoLs hm0))
    have hdec := decode_oneArgTpl x0 x1 addrPtr (lsmpl.base 215) heven
    have hArgsOk :
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (manyArgStep argPieces) (manyArgPanic argPieces)
          (manyArgOom (toRustAllocBudget M A lim) st0 argPieces) stackBytes s0
          [FmtCall.fmtArg 0 addrPtr (lsmpl.base 215) defaultFmtOptions] := by
      intro idx_i val_i fn_i opt_i hmem out
      simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨hidx, hval, hfn, hopt⟩
      subst idx_i val_i fn_i opt_i
      exact lsProtoAddrDisplay_many_fmtArg_ok (R_client := R_client) (R_rest := emp)
        L.toCliFmtWriteLink L.plFmt
        L.noExtFmtStr L.clFmtStr L.noExtFmtU8 L.clFmtU8 L.plLs
        (by decide) (by decide) (by decide) (by decide)
        (L.noExtLsAll 214 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        (L.noExtLsAll 215 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        (L.noExtLsAll 216 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        (L.noExtLsAll 217 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
        L.clLsAll L.tieFmtWrite L.tieU8 L.tieStrDisplay
        st0 argPieces s0 stackBytes 0 out addrPtr nameCap nameDataPtr nameBs
        strRefRo strSrcRo devRo dev hlen rfl ⟨by decide, by decide⟩ rfl
    have hevEq :
        formatInnerKnownEvents
          (fmtEstimatedCapacity x1
            [FmtCall.fmtArg 0 addrPtr (lsmpl.base 215) defaultFmtOptions])
          (manyLens argPieces
            [FmtCall.fmtArg 0 addrPtr (lsmpl.base 215) defaultFmtOptions]) =
        formatInnerKnownEvents 0 [nameBs.length, 1, (formatDecimalNat dev.toNat).length] := by
      dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, manyLens, callPieces, argPieces]
      simp only [heven, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hpre_many :
        s0.mem ⊨
          (cliAllocFormatInnerManyTightSpec M A lim
            (EnvOf ⟨ret, x0, x1, argsRo,
              .protoAddrDisplay addrPtr nameCap nameDataPtr nameBs strRefRo strSrcRo devRo dev⟩)
            va R_client argPieces stackBytes P).pre
            (ret, argsRo, oneArgTplBytes, [(addrPtr, lsmpl.base 215)], st0) s0 ∗ R₀ := by
      dsimp only [cliAllocFormatInnerManyTightSpec]
      rw [hx0, hx1]
      refine Satisfies.mono ?_ hm_ro
      rw [hstkEq]
      refine Entails.trans (Entails.of_eq (show _ =
        (fmtArgumentsAt argsRo x0 x1 oneArgTplBytes [(addrPtr, lsmpl.base 215)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀ by
        dsimp only [R_client]
        sep_ac_rfl)) ?_
      exact sepConj_mono_left
        (Entails.pure_right
          ⟨hx8, by decide, by decide, hFit, _,
            hdec, by dsimp only [fmtLiteralLen]; decide,
            by rw [hevEq]; exact hEx, hArgsOk⟩
          (Entails.refl _))
    have hok_many := cliAllocFormatInnerMany_tight_placed_ok
      (Env := EnvOf ⟨ret, x0, x1, argsRo,
        .protoAddrDisplay addrPtr nameCap nameDataPtr nameBs strRefRo strSrcRo devRo dev⟩)
      (R_client := R_client) (argPieces := argPieces) (stackBytes := stackBytes)
      L.toCliFormatInnerLink
    refine hok_many.mono_outcome _ R₀ s0 hpc hrun hpre_many hsp0 ?_
    intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [cliAllocFormatInnerManyTightSpec] at hpost
      rw [hx0, hx1] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      rcases hpost with ⟨bs', hpost⟩
      have hp1 :
          sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
            EnvOf ⟨ret, x0, x1, argsRo,
              .protoAddrDisplay addrPtr nameCap nameDataPtr nameBs strRefRo strSrcRo devRo dev⟩ evs ∧
            ∃ cs', decodeFmtArguments x0 x1 oneArgTplBytes [(addrPtr, lsmpl.base 215)] = some cs' ∧
              evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs') (manyLens argPieces cs') ∧
              bs' = (cs'.flatMap (callPieces argPieces)).flatten⌝ ∗
            ((stringWriteVtableAt va ∗ lutAtom ∗ protoAddrRoSep lsmpl) ∗
              ((vecU8 A.repAlloc ret bs' ∗
                fmtArgumentsAt argsRo x0 x1 oneArgTplBytes
                  [(addrPtr, lsmpl.base lsProtocolAddressDisplayBlock)] ∗
                ((fmtRefString strRefRo addrPtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
                  fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
                  fmtRef8 devRo (addrPtr + 24#64) dev) ∗
                A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗ R₀)) :=
        Satisfies.mono (Entails.of_eq (by
          rw [← hstkEq]
          dsimp only [R_client, lsProtocolAddressDisplayBlock]
          sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hp1
      rcases hp1 with ⟨⟨hacp, hfs, htr, hEnv, _⟩, hp2⟩
      have hp3 := Satisfies.drop_left hp2
      dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec]
      refine Satisfies.mono (sepConj_mono_left ?_) hp3
      rw [pure_sepConj_of_true ⟨hfs, htr⟩]
      refine Entails.sepExists_right evs (Entails.sepExists_right bs' ?_)
      rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnv⟩]
      exact Entails.of_eq (by dsimp only [CliFormatInnerLsCall.clientSep]; sep_ac_rfl)
    · dsimp only [cliAllocFormatInnerManyTightSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [cliAllocFormatInnerManyTightSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [cliAllocFormatInnerManyTightSpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  | dottedStringDevIdShim shimBlock namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hshimMem, heven, hlen⟩
    let argBytes : Nat → List (BitVec 8) :=
      fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
    refine dischargeSingle
      (.dottedStringDevIdShim shimBlock namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev)
      (lutAtom ∗ protoAddrRoSep lsmpl) argBytes
      [FmtCall.fmtArg 0 namePtr (lsmpl.base shimBlock) defaultFmtOptions,
       FmtCall.writeStr (x0 + 2#64) [0x2e#8],
       FmtCall.fmtArg 1 devPtr (lsmpl.base 214) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (sat_decDigitsLut hLutRo (sat_protoAddrRoSep hRoLs hm0))))
      (decode_dotTpl x0 x1 namePtr (lsmpl.base shimBlock) devPtr (lsmpl.base 214) heven)
      (by dsimp only [fmtLiteralLen]; decide)
      (by
        dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, callLens, callBytes,
          argBytes, CliFormatInnerLsCall.exactEvs]
        simp only [heven, Bool.false_eq_true, ↓reduceIte]
        rfl)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩ | ⟨hidx, hval, hfn, hopt⟩ <;>
          subst idx_i val_i fn_i opt_i
        · have htarget :
              libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib shimBlock) =
                coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
            rw [cliStringDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
            exact L.tieStrDisplay
          exact cliStringDisplayShim_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtStr L.clFmtStr
            L.plLs shimBlock (formatInnerSubLsKeep_of_stringShim hshimMem)
            (cliStringDisplayShim_check hshimMem)
            (L.noExtLsAll shimBlock (cliStringDisplayShim_lt hshimMem)
              (formatInnerSubLsKeep_of_stringShim hshimMem))
            L.clLsAll htarget st0 _
            (fmtRef8 devRo devPtr dev ∗ lutAtom ∗ protoAddrRoSep lsmpl)
            argBytes s0 stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr
            (lsmpl.base shimBlock) strRefRo strSrcRo nameBs rfl hlen rfl
            ⟨Nat.le_refl _, by decide⟩ (by decide)
            (by dsimp only [CliFormatInnerLsCall.clientSep]; sep_ac_rfl)
        · exact lsDeviceIdDisplay_known_fmtArg_ok
            (R_client := CliFormatInnerLsCall.clientSep ⟨ret, x0, x1, argsRo,
              .dottedStringDevIdShim shimBlock namePtr nameCap nameDataPtr devPtr nameBs
                strRefRo strSrcRo devRo dev⟩ ∗ (lutAtom ∗ protoAddrRoSep lsmpl))
            (R_rest := fmtRefString strRefRo namePtr nameCap nameDataPtr
              (BitVec.ofNat 64 nameBs.length) ∗ fmtSrcBytes strSrcRo nameDataPtr nameBs)
            L.toCliFmtWriteLink L.plFmt L.noExtFmtU8 L.clFmtU8
            (by decide) (by decide)
            (L.noExtLsAll 214 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
            (L.noExtLsAll 217 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
            L.clLsAll L.tieFmtWrite L.tieU8 st0 argBytes s0 stackBytes 1 out devPtr devRo dev
            rfl ⟨by decide, by decide⟩
            (by dsimp only [CliFormatInnerLsCall.clientSep, lutAtom]; sep_ac_rfl))
  | dottedStringU32Shim shimBlock namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev =>
    dsimp only [CliFormatInnerLsCall.shapePreOk] at hshOk
    rcases hshOk with ⟨hshimMem, heven, hlen⟩
    let argBytes : Nat → List (BitVec 8) :=
      fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
    refine dischargeSingle
      (.dottedStringU32Shim shimBlock namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev)
      lutAtom argBytes
      [FmtCall.fmtArg 0 namePtr (lsmpl.base shimBlock) defaultFmtOptions,
       FmtCall.writeStr (x0 + 2#64) [0x2e#8],
       FmtCall.fmtArg 1 devPtr (lsρ lsU32DisplayFmtSym) defaultFmtOptions] hFit hEx
      (sat_stringWriteVtableAt hVtRo (sat_decDigitsLut hLutRo hm0))
      (decode_dotTpl x0 x1 namePtr (lsmpl.base shimBlock) devPtr (lsρ lsU32DisplayFmtSym) heven)
      (by dsimp only [fmtLiteralLen]; decide)
      (by
        dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, callLens, callBytes,
          argBytes, CliFormatInnerLsCall.exactEvs]
        simp only [heven, Bool.false_eq_true, ↓reduceIte]
        rfl)
      (fun idx_i val_i fn_i opt_i hmem out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem
        rcases hmem with ⟨hidx, hval, hfn, hopt⟩ | ⟨hidx, hval, hfn, hopt⟩ <;>
          subst idx_i val_i fn_i opt_i
        · have htarget :
              libsignalSessionLib.resolve lsmpl (displayShimTargetSym libsignalSessionLib shimBlock) =
                coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym := by
            rw [cliStringDisplayShim_targetSym hshimMem, ls_resolve_strDisplayFmtSym]
            exact L.tieStrDisplay
          exact cliStringDisplayShim_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtStr L.clFmtStr
            L.plLs shimBlock (formatInnerSubLsKeep_of_stringShim hshimMem)
            (cliStringDisplayShim_check hshimMem)
            (L.noExtLsAll shimBlock (cliStringDisplayShim_lt hshimMem)
              (formatInnerSubLsKeep_of_stringShim hshimMem))
            L.clLsAll htarget st0 _
            (fmtRef32 devRo devPtr dev ∗ lutAtom)
            argBytes s0 stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr
            (lsmpl.base shimBlock) strRefRo strSrcRo nameBs rfl hlen rfl
            ⟨Nat.le_refl _, by decide⟩ (by decide)
            (by dsimp only [CliFormatInnerLsCall.clientSep]; sep_ac_rfl)
        · have htie32 : lsρ lsU32DisplayFmtSym = coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym :=
            L.tieU32
          rw [htie32]
          exact fmtArgCallSpec_congr_R
            (by dsimp only [CliFormatInnerLsCall.clientSep, lutAtom]; sep_ac_rfl)
            (cliU32Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU32 L.clFmtU32
              st0
              (fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
                fmtSrcBytes strSrcRo nameDataPtr nameBs)
              argBytes s0 stringWriterStack stackBytes 1 out devPtr devRo dev
              rfl ⟨Nat.le_refl _, by decide⟩ (by decide)))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
