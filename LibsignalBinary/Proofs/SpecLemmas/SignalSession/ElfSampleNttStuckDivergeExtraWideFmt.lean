/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Wide-Keep Formatter Extra Ghost `StepsStrictAvoid` of `mlkemSampleNttSyms` (`ElfSampleNttStuckDivergeExtraWideFmt`)

Proves `StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))`
on `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` for the wide-keep formatter
`ExtraGhostTable` rows `c2FmtWriteGhost` (`lsFmtWriteSym`) and `c2FormatInnerGhost`
(`lsFormatInnerSym`), running `cliCoreFmtWrite_protoAddr_ro_ok` and
`cliAllocFormatInner_lsCall_ro_ok` on `addS5Trap (c2FmtProgTrap lr)` with allocator and `memcpy`
callees lifted out of the pre-`SampleNTT` low prefix `f3LoRxProg` via
`ElfSampleNttStuckDivergeExtraWide`.
-/

set_option autoImplicit false
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.RustStd
  (allocFormatInnerSym allocMultiLib coreFmtMultiLib coreFmtWriteSym coreMultiLib
   formatterWriteStrSym u32DisplayFmtSym u64DisplayFmtSym u8DisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt (LibBlockNoExtern LibKeepNoExtern writeStrKeep)
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib_blocks_length ls_resolve_data_ultra lsmpl lsρ)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced cliPanicSymbolsLinked isCliPanicSymbolPlaced
   libsignalSessionLib)
open LibsignalBinary.Heap
  (BudgetLimits zeroBudgetLimits)
open LibsignalBinary.Heap.Fine
  (f3NoShimV2Addr f3RxWordCount f3StdLayout f3StubAddrs fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (lsFmtWriteSym lsFormatInnerSym rustBudgetAlloc_of_cliBase rustBudgetRealloc_of_cliBase)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (keepRxSeg keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
  (c2AllocMpl c2AllocMpl_placeable c2FormatInnerAddr c2_alloc_fmtWriteTie
   c2_alloc_handleError_resolve c2_alloc_memcpy_resolve c2_alloc_noAllocShim_resolve
   c2_alloc_rustAlloc_resolve c2_alloc_rustRealloc_resolve
   c2_alloc_stringWriter_codeLoaded_of_rxCode c2_resolve_formatInner_eq
   c2_resolve_formatInner_fnAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
  (c2CoreFmtActiveKeep c2CoreFmtMpl c2CoreFmtMpl_placeable c2CoreMpl c2CoreMpl_placeable
   c2FmtWriteAddr c2_coreFmt_codeLoadedWhere_active_of_rxCode
   c2_coreFmt_codeLoadedWhere_str_of_rxCode c2_coreFmt_codeLoadedWhere_u32_of_rxCode
   c2_coreFmt_codeLoadedWhere_u64_of_rxCode c2_coreFmt_codeLoadedWhere_u8_of_rxCode
   c2_core_codeLoaded_of_rxCode c2_resolve_fmtWrite_eq c2_resolve_fmtWrite_fnAddr
   c2_resolve_strDisplayFmt_fnAddr c2_resolve_u32DisplayFmt_fnAddr
   c2_resolve_u64DisplayFmt_fnAddr c2_resolve_u8DisplayFmt_fnAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow
  (ActiveC2FmtPre ActiveC2FmtRun c2AllocMpl_codeLoaded_of_c2FmtProg c2FmtExterns c2FmtGhost
   c2FmtImgGuard c2FmtProg c2FmtProgTrap c2FmtProgTrap_codeLoaded_iff
   c2FmtProgTrap_externAt_handleError c2FmtProgTrap_externAt_none_of_ge_stub_not_panic
   c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic c2FmtProgTrap_externAt_of_ne
   c2FmtProgTrap_externAt_self c2FmtProgTrap_svc c2FmtProg_codeLoaded_of_f3CodeInv
   c2FmtProg_externAt_eq_real c2FmtProg_externAt_none_of_lt_stub c2FmtProg_svc c2FmtWriteGhost
   c2FormatInnerGhost c2HaltHook c2LrTrapSym c2MplAllocCli c2MplAllocCli_handleError_resolve
   c2MplAllocCli_memcpy_resolve c2MplAllocCli_noAllocShim_resolve c2MplAllocCli_placeable
   c2MplAllocCli_rustAlloc_resolve c2MplAllocCli_rustRealloc_resolve
   c2MplAllocCli_stringWriter_codeLoaded c2MplAllocCli_vtable_eq c2_cliFmtWriteRoGuard
   c2_cliFormatInnerRoGuard ls_codeLoaded_of_c2FmtProg rxCode_of_c2FmtProg_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2Kyber1024EncapsAddr c2Mlkem768FromSeedAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
  (withFsTraceExact withRoMemGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays
  (fmtWriteGhostSpecOf fmtWriteGhostSpecOf_outcome_setPC fmtWriteGhostSpecOf_pre_setPC
   formatInnerGhostSpecOf formatInnerGhostSpecOf_outcome_setPC formatInnerGhostSpecOf_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (CliFmtWriteProtoAddrCall CliFmtWriteVtableKind CliFormatInnerLsCall
   LsRetAddrFmtWrite LsRetAddrFormatInner cliFmtWriteProtoAddrSpec cliFormatInnerLsCallSpec
   cliStrRefDisplayShimBlocks cliStringDisplayShimBlocks dotTplBytes
   extract_withLsRetFmtWrite extract_withLsRetFormatInner isFmtWriteInternalBlock
   isFormatInnerInternalBlock lsU32DisplayFmtSym lsU8DisplayFmtSym
   withLsRetFmtWrite withLsRetFormatInner)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs (ExactOrNilEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
  (CliFmtWriteSubLink CliFormatInnerSubLink cliAllocFormatInner_lsCall_ro_ok
   cliCoreFmtWrite_protoAddr_ro_ok cliFmtWriteRoGuard cliFormatInnerRoGuard
   fmtWriteSubLsKeep formatInnerSubLsKeep formatInnerSubLsKeep_of_spqr lsStrDisplayFmtSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
  (lsFormatterWriteStrSym lsU64DisplayFmtSym spqrErrorDispKeep)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr isLinkedPanicAddr_false_of_band
   isLinkedPanicAddr_false_of_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3CodeOk_of_patchedLoadState f3PatchedElf_eq_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3RxSegBase f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide
  (addS5Trap addS5Trap_codeLoaded_iff addS5Trap_externAt_of_not_s5 addS5Trap_externAt_s5
   addS5Trap_svc c2_alloc_withExecFrozen_ok c2_budgetAllocShim_f3Lo_ok c2_budgetMemcpy_f3Lo_ok
   c2_realloc_withExecFrozen_ok f3LoRxProg f3LoRxProg_codeLoaded_of_f3Trial f3LoWordCount
   fineHookPool_nonZeroEquivLim fitsEnv_nonZeroEquivLim keepLo keepLo_s5_false nonZeroEquivLim
   nonZeroEquivLim_ne_zero s5Addrs s5Addrs_contains_false_of_gt s5Addrs_contains_false_of_lt
   s5Addrs_eq_of_linkedAt s5TrapFn s5TrapSym withExecFrozenBudget
   withExecFrozenBudget_pool_entails withExecFrozenBudget_repAlloc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_stepsUntil_det)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4HandleErrorAddr wp4MemcpyRealAddr wp4NoShimV2Addr)

/-! ## 1. Trapped Formatter Program `P_fmt lr := addS5Trap (c2FmtProgTrap lr)` & `keepLo` Bridges -/

private noncomputable def P_fmt (lr : BitVec 64) : Program :=
  addS5Trap (c2FmtProgTrap lr)

private theorem isCliPanicSymbolPlaced_s5TrapSym :
    isCliPanicSymbolPlaced s5TrapSym = false := by
  have h1 : List.contains cliPanicSymbolsLinked s5TrapSym = false := by decide
  have h2 : Rust.isPanicSymbol s5TrapSym = false := by
    unfold Rust.isPanicSymbol
    have hsw : s5TrapSym.startsWith "core::panicking::" =
        List.isPrefixOf "core::panicking::".toList s5TrapSym.toList := by
      rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
    rw [hsw]
    decide
  unfold isCliPanicSymbolPlaced
  change (List.contains cliPanicSymbolsLinked s5TrapSym || Rust.isPanicSymbol s5TrapSym) = false
  rw [h1, h2]
  rfl

private theorem c2FmtProgTrap_s5TrapSym_none (lr : BitVec 64) :
    (c2FmtProgTrap lr).externs s5TrapSym = none := by
  have h1 : (s5TrapSym == c2LrTrapSym) = false := by decide
  have h2 : isCliPanicSymbolPlaced s5TrapSym = false := isCliPanicSymbolPlaced_s5TrapSym
  unfold c2FmtProgTrap c2FmtExterns
  dsimp only
  rw [h1, h2]
  rfl

private theorem P_fmt_svc (lr : BitVec 64) : (P_fmt lr).svc = Syscall.standard :=
  (addS5Trap_svc (c2FmtProgTrap lr)).trans (c2FmtProgTrap_svc lr)

private theorem P_fmt_codeLoaded_iff (lr : BitVec 64) (m : Memory) :
    (P_fmt lr).CodeLoaded m ↔ c2FmtProg.CodeLoaded m :=
  (addS5Trap_codeLoaded_iff (c2FmtProgTrap lr) m).trans (c2FmtProgTrap_codeLoaded_iff lr m)

private theorem P_fmt_externAt_s5 (lr : BitVec 64) {pc : BitVec 64}
    (hs5 : s5Addrs.contains pc = true) :
    (P_fmt lr).externAt? pc = some s5TrapFn :=
  addS5Trap_externAt_s5 (c2FmtProgTrap lr) hs5

private theorem P_fmt_externAt_of_not_s5 (lr : BitVec 64) {pc : BitVec 64}
    (hns5 : s5Addrs.contains pc = false) :
    (P_fmt lr).externAt? pc = (c2FmtProgTrap lr).externAt? pc :=
  addS5Trap_externAt_of_not_s5 (c2FmtProgTrap lr) (c2FmtProgTrap_s5TrapSym_none lr) hns5

private theorem P_fmt_cl_f3Lo (lr : BitVec 64) (m : Memory) (hm : (P_fmt lr).CodeLoaded m) :
    f3LoRxProg.CodeLoaded m :=
  f3LoRxProg_codeLoaded_of_f3Trial
    (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))

private theorem keepLo_sub_keepRxSeg {pc : BitVec 64} (hk : keepLo pc = true) :
    keepRxSeg pc = true := by
  unfold keepLo at hk
  rw [keepRxSeg_eq_lt]
  have hlt := of_decide_eq_true hk
  have hle : 4 * f3LoWordCount ≤ 4 * f3RxWordCount := by decide
  exact decide_eq_true (Nat.lt_of_lt_of_le hlt hle)

private theorem keepLo_lt_panic {pc : BitVec 64} (hk : keepLo pc = true) :
    pc.toNat < 0x479798 := by
  unfold keepLo at hk
  have hlt := of_decide_eq_true hk
  have hbase : f3RxSegBase.toNat = 0x474000 := rfl
  have hwc : 4 * f3LoWordCount = 0x5798 := rfl
  have hpc64 : pc.toNat < 2 ^ 64 := BitVec.isLt pc
  by_cases hle : f3RxSegBase.toNat ≤ pc.toNat
  · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)] at hlt
    omega
  · have hwrap : (pc - f3RxSegBase).toNat = 2 ^ 64 - f3RxSegBase.toNat + pc.toNat := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem P_fmt_ext_none_of_keepLo {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {pc : BitVec 64} (hk : keepLo pc = true) :
    (P_fmt lr).externAt? pc = none := by
  rw [P_fmt_externAt_of_not_s5 lr (keepLo_s5_false hk)]
  exact c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic hlr (keepLo_sub_keepRxSeg hk)
    (isLinkedPanicAddr_false_of_lt (keepLo_lt_panic hk))

private theorem P_fmt_externAt_handleError {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat) :
    (P_fmt lr).externAt? wp4HandleErrorAddr = some Rust.panicked := by
  rw [P_fmt_externAt_of_not_s5 lr (s5Addrs_contains_false_of_gt (by decide))]
  exact c2FmtProgTrap_externAt_handleError hlr

private theorem wp4MemcpyRealAddr_eq : wp4MemcpyRealAddr = f3StdLayout.memcpyAddr := by
  decide

private theorem wp4NoShimV2Addr_eq : wp4NoShimV2Addr = f3NoShimV2Addr := by
  decide

private theorem wp4RustAllocAddr_eq : wp4NoShimV2Addr - 16#64 = f3StubAddrs.alloc := by
  decide

private theorem wp4RustReallocAddr_eq : wp4NoShimV2Addr - 8#64 = f3StubAddrs.realloc := by
  decide

/-! ## 2. `seg[2]` Pre-`SampleNTT` and Post-`SampleNTT` `LibBlockNoExtern` Discharges on `P_fmt lr` -/

private def noPanicBand (b hi : Nat) : Bool :=
  Nat.ble hi 0x479798 ||
  (Nat.ble 0x4797d0 b && Nat.ble hi 0x47a20c) ||
  (Nat.ble 0x47a3d8 b && Nat.ble hi 0x47a9c4) ||
  (Nat.ble 0x47aa78 b && Nat.ble hi 0x47aba0) ||
  (Nat.ble 0x47ac2c b && Nat.ble hi 0x4cb070) ||
  Nat.ble 0x4cb0e4 b

private theorem isLinkedPanicAddr_false_of_noPanicBand {b len off : Nat} {pc : BitVec 64}
    (hband : noPanicBand b (b + len) = true)
    (hoff : off < len)
    (hpc : pc.toNat = b + off) :
    isLinkedPanicAddr pc = false := by
  unfold noPanicBand at hband
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hband
  apply isLinkedPanicAddr_false_of_band
  rcases hband with ((((hb0 | hb1) | hb2) | hb3) | hb4) | hb5
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

private def checkBlockPreS5 (L : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  let b := (mpl.base j).toNat
  let len := (L.blockLib j).text.code.length
  Nat.ble f3RxSegBase.toNat b &&
  Nat.ble (b + len) c2Mlkem768FromSeedAddr.toNat &&
  noPanicBand b (b + len)

private def checkBlockPostS5 (L : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  let b := (mpl.base j).toNat
  let len := (L.blockLib j).text.code.length
  Nat.ble f3RxSegBase.toNat b &&
  Nat.blt c2Kyber1024EncapsAddr.toNat b &&
  Nat.blt (b + len) (2 ^ 64) &&
  noPanicBand b (b + len)

private theorem noExtern_P_fmt_of_preS5 {L : MultiPlacedLib} {mpl : MultiPlacement} {j : Nat}
    {lr : BitVec 64} (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hchk : checkBlockPreS5 L mpl j = true) :
    LibBlockNoExtern L mpl (P_fmt lr) j := by
  unfold checkBlockPreS5 at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Nat.ble_eq] at hchk
  rcases hchk with ⟨⟨hge_rx, hle_s5⟩, hband⟩
  have hs5_lt : c2Mlkem768FromSeedAddr.toNat < 2 ^ 64 := BitVec.isLt c2Mlkem768FromSeedAddr
  have hstub_le_rx : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  intro off hoff
  let pc := mpl.base j + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = (mpl.base j).toNat + off := by
    dsimp only [pc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (P_fmt lr).externAt? pc = none
  rw [P_fmt_externAt_of_not_s5 lr (s5Addrs_contains_false_of_lt (by omega))]
  exact c2FmtProgTrap_externAt_none_of_ge_stub_not_panic hlr (by omega)
    (isLinkedPanicAddr_false_of_noPanicBand hband hoff hpc_nat)

private theorem noExtern_P_fmt_of_postS5 {L : MultiPlacedLib} {mpl : MultiPlacement} {j : Nat}
    {lr : BitVec 64} (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hchk : checkBlockPostS5 L mpl j = true) :
    LibBlockNoExtern L mpl (P_fmt lr) j := by
  unfold checkBlockPostS5 at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨⟨hge_rx, hgt_s5⟩, hlt64⟩, hband⟩
  have hstub_le_rx : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  intro off hoff
  let pc := mpl.base j + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = (mpl.base j).toNat + off := by
    dsimp only [pc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (P_fmt lr).externAt? pc = none
  rw [P_fmt_externAt_of_not_s5 lr (s5Addrs_contains_false_of_gt (by omega))]
  exact c2FmtProgTrap_externAt_none_of_ge_stub_not_panic hlr (by omega)
    (isLinkedPanicAddr_false_of_noPanicBand hband hoff hpc_nat)

set_option maxRecDepth 200000 in
private theorem c2Core_blk0_preS5_chk : checkBlockPreS5 coreMultiLib c2CoreMpl 0 = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem c2CoreFmt_active_preS5_chk :
    (([0, 1, 2, 3, 4, 5, 6, 8, 9, 10] : List Nat).all fun j =>
      checkBlockPreS5 coreFmtMultiLib c2CoreFmtMpl j) = true := by
  rfl_kernel

private theorem c2CoreFmt_active_noExtern_P_fmt {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {j : Nat} (hj : j < 11) (hne : j ≠ 7) :
    LibBlockNoExtern coreFmtMultiLib c2CoreFmtMpl (P_fmt lr) j := by
  have hmem : j ∈ ([0, 1, 2, 3, 4, 5, 6, 8, 9, 10] : List Nat) := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 8, _ | 9, _ | 10, _ => decide
    | 7, _ => exact False.elim (hne rfl)
  exact noExtern_P_fmt_of_preS5 hlr (List.all_eq_true.mp c2CoreFmt_active_preS5_chk j hmem)

set_option maxRecDepth 200000 in
private theorem c2Alloc_seg2_postS5_chk :
    (([1, 2, 3, 6, 7] : List Nat).all fun j =>
      checkBlockPostS5 allocMultiLib c2AllocMpl j) = true := by
  rfl_kernel

private theorem c2Alloc_seg2_noExtern_P_fmt {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {j : Nat} (hj : j ∈ ([1, 2, 3, 6, 7] : List Nat)) :
    LibBlockNoExtern allocMultiLib c2AllocMpl (P_fmt lr) j :=
  noExtern_P_fmt_of_postS5 hlr (List.all_eq_true.mp c2Alloc_seg2_postS5_chk j hj)

/-! ## 3. `seg[1]` Disjointness & `LibBlockNoExtern` Discharges on `P_fmt lr` -/

private def c2FmtWriteInternalIndices : List Nat :=
  [121, 157, 160, 181, 182, 191, 214, 216, 217,
   460, 465, 488, 489, 498, 517, 522, 533, 534, 537]

private def c2FormatInnerInternalIndices : List Nat :=
  [78, 121, 157, 160, 170, 181, 182, 191, 214, 215, 216, 217,
   392, 393, 394, 395, 396, 397, 412, 460, 465, 477, 488, 489, 498,
   517, 522, 529, 533, 534, 537, 623]

private def checkBlocksDisjointAux (skip : Nat → Bool) (pairs : List (Nat × Nat)) :
    Nat → List (BitVec 64) → Bool
  | _, [] => true
  | j, b :: bs =>
    (skip j ||
      pairs.all fun (bbi, lbi) =>
        Nat.ble (b.toNat + lsLen j) bbi || Nat.ble (bbi + lbi) b.toNat) &&
    checkBlocksDisjointAux skip pairs (j + 1) bs

private theorem checkBlocksDisjointAux_spec {skip : Nat → Bool} {pairs : List (Nat × Nat)} :
    ∀ (j : Nat) (bs : List (BitVec 64)),
      checkBlocksDisjointAux skip pairs j bs = true →
      ∀ (k : Nat) (hk : k < bs.length),
        skip (j + k) = true ∨
        ∀ p ∈ pairs, bs[k].toNat + lsLen (j + k) ≤ p.1 ∨ p.1 + p.2 ≤ bs[k].toNat
  | _, [], _, _, hk => nomatch hk
  | _, _ :: _, h, 0, _ => by
    simp only [checkBlocksDisjointAux, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.1 with hs | hall
    · exact Or.inl hs
    · refine Or.inr fun p hp => ?_
      have hp0 := List.all_eq_true.mp hall p hp
      simp only [Bool.or_eq_true, Nat.ble_eq] at hp0
      exact hp0
  | j, _ :: bs, h, k + 1, hk => by
    simp only [checkBlocksDisjointAux, Bool.and_eq_true] at h
    have ih := checkBlocksDisjointAux_spec (j + 1) bs h.2 k (by simp at hk; omega)
    simpa [Nat.add_right_comm, Nat.add_assoc] using ih

private noncomputable def c2InternalPairsOf (idxs : List Nat) : List (Nat × Nat) :=
  idxs.map fun bi => ((cliElfBlockBases.getD bi 0#64).toNat, lsLen bi)

set_option maxRecDepth 200000 in
private theorem c2_disjoint_fmtWrite_ok :
    checkBlocksDisjointAux isFmtWriteInternalBlock
      (c2InternalPairsOf c2FmtWriteInternalIndices) 0 cliElfBlockBases = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem c2_disjoint_formatInner_ok :
    checkBlocksDisjointAux isFormatInnerInternalBlock
      (c2InternalPairsOf c2FormatInnerInternalIndices) 0 cliElfBlockBases = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem c2_lsSub_codeLen_eq_lsLen :
    (([78, 121, 170, 191, 214, 215, 216, 217,
       392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat).all fun bi =>
      Nat.beq (libsignalSessionLib.blockLib bi).text.code.length (lsLen bi)) = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem c2_allocWriter_codeLen_eq_lsLen :
    (([(1, 157), (2, 160), (6, 181), (7, 182),
       (1, 460), (2, 465), (6, 488), (7, 489),
       (1, 517), (2, 522), (6, 533), (7, 534)] : List (Nat × Nat)).all fun (aj, bi) =>
      Nat.beq (allocMultiLib.blockLib aj).text.code.length (lsLen bi)) = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem cliElfBlockBases_bounds_chk :
    ((List.range 624).all fun bi =>
      Nat.ble ((cliElfBlockBases.getD bi 0#64).toNat + lsLen bi) c2FirstExternStubAddr.toNat) =
      true := by
  rfl_kernel

private theorem cliElfBlockBases_len_and_bounds :
    libsignalSessionLib.blocks.length = 624 ∧
    cliElfBlockBases.length = 624 ∧
    ∀ bi < 624, (cliElfBlockBases.getD bi 0#64).toNat + lsLen bi ≤ c2FirstExternStubAddr.toNat := by
  refine ⟨libsignalSessionLib_blocks_length, by decide, fun bi hbi => ?_⟩
  have hall := List.all_eq_true.mp cliElfBlockBases_bounds_chk bi (List.mem_range.mpr hbi)
  rwa [Nat.ble_eq] at hall

private theorem range_ne_lr_of_disjoint [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {skip : Nat → Bool} {idxs : List Nat}
    (hDisjOk : checkBlocksDisjointAux skip (c2InternalPairsOf idxs) 0 cliElfBlockBases = true)
    {lr : BitVec 64} {j : Nat} (hj : j < 624) {o : Nat} (ho : o < lsLen j)
    (hlrEq : lr = lsmpl.base j + BitVec.ofNat 64 o)
    (hnotSkip : skip j = false)
    {bi : Nat} (hbiMem : bi ∈ idxs) (hbi624 : bi < 624)
    {off : Nat} (hoff : off < lsLen bi) :
    cliElfMultiPlacement.base bi + BitVec.ofNat 64 off ≠ lr := by
  obtain ⟨hlenLs, hlenBases, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hj_lt : j < cliElfBlockBases.length := by omega
  have hspec := checkBlocksDisjointAux_spec 0 cliElfBlockBases hDisjOk j hj_lt
  rw [Nat.zero_add] at hspec
  rcases hspec with hs | hpairs
  · rw [hnotSkip] at hs; cases hs
  · have hpMem : ((cliElfBlockBases.getD bi 0#64).toNat, lsLen bi) ∈ c2InternalPairsOf idxs :=
      List.mem_map.mpr ⟨bi, hbiMem, rfl⟩
    have hdisj := hpairs _ hpMem
    have hbj_getD : cliElfBlockBases.getD j 0#64 = cliElfBlockBases[j] := by
      simp [List.getD, List.getElem?_eq_getElem hj_lt]
    have hbj_eq : lsmpl.base j = cliElfBlockBases[j] := by
      have h1 := (cliElf_linkedAt_unique hLs).1 j (by omega)
      have h2 : cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 := rfl
      exact h1.trans (h2.trans hbj_getD)
    have hbbi_eq : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
    have hj_bnd := hBounds j hj
    have hbi_bnd := hBounds bi hbi624
    rw [hbj_getD] at hj_bnd
    have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
    intro heq
    have hnat := congrArg BitVec.toNat heq
    rw [hlrEq, hbj_eq, hbbi_eq] at hnat
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
    dsimp only at hdisj
    omega

private theorem lsBlock_noExtern_P_fmt [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {skip : Nat → Bool} {idxs : List Nat}
    (hDisjOk : checkBlocksDisjointAux skip (c2InternalPairsOf idxs) 0 cliElfBlockBases = true)
    {lr : BitVec 64} {j : Nat} (hj : j < 624) {o : Nat} (ho : o < lsLen j)
    (hlrEq : lr = lsmpl.base j + BitVec.ofNat 64 o)
    (hnotSkip : skip j = false)
    {bi : Nat} (hbiMem : bi ∈ idxs) (hbi624 : bi < 624)
    (hLenEq : (libsignalSessionLib.blockLib bi).text.code.length = lsLen bi) :
    LibBlockNoExtern libsignalSessionLib lsmpl (P_fmt lr) bi := by
  obtain ⟨hlenLs, _, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hBaseEq : lsmpl.base bi = cliElfMultiPlacement.base bi :=
    (cliElf_linkedAt_unique hLs).1 bi (by omega)
  have hbi_bnd := hBounds bi hbi624
  have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  have hstub_le_s5 : c2FirstExternStubAddr.toNat ≤ c2Mlkem768FromSeedAddr.toNat := by decide
  intro off hoff
  rw [hLenEq] at hoff
  change (P_fmt lr).externAt? (lsmpl.base bi + BitVec.ofNat 64 off) = none
  rw [hBaseEq]
  have hdef : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
  have hpc_lt_stub : (cliElfMultiPlacement.base bi + BitVec.ofNat 64 off).toNat <
      c2FirstExternStubAddr.toNat := by
    rw [hdef, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [P_fmt_externAt_of_not_s5 lr (s5Addrs_contains_false_of_lt (by omega))]
  have hne := range_ne_lr_of_disjoint hLs hDisjOk hj ho hlrEq hnotSkip hbiMem hbi624 hoff
  rw [c2FmtProgTrap_externAt_of_ne hne]
  exact c2FmtProg_externAt_none_of_lt_stub hpc_lt_stub

private theorem allocWriter_noExtern_P_fmt [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddrFmtWrite lr)
    (k : CliFmtWriteVtableKind) {aj : Nat}
    (haj : aj = 1 ∨ aj = 2 ∨ aj = 6 ∨ aj = 7) :
    LibBlockNoExtern allocMultiLib (c2MplAllocCli k) (P_fmt lr) aj := by
  rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
  obtain ⟨_, _, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  have hstub_le_s5 : c2FirstExternStubAddr.toNat ≤ c2Mlkem768FromSeedAddr.toNat := by decide
  let bi : Nat :=
    match k, aj with
    | .libsignalSession, 1 => 157
    | .libsignalSession, 2 => 160
    | .libsignalSession, 6 => 181
    | .libsignalSession, 7 => 182
    | .cliRatchet, 1 => 460
    | .cliRatchet, 2 => 465
    | .cliRatchet, 6 => 488
    | .cliRatchet, 7 => 489
    | .cliHandshake, 1 => 517
    | .cliHandshake, 2 => 522
    | .cliHandshake, 6 => 533
    | _, _ => 534
  have hBaseEq : (c2MplAllocCli k).base aj = cliElfMultiPlacement.base bi := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> rfl
  have hbiMem : bi ∈ c2FmtWriteInternalIndices := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hbi624 : bi < 624 := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hPairMem : (aj, bi) ∈
      ([(1, 157), (2, 160), (6, 181), (7, 182),
        (1, 460), (2, 465), (6, 488), (7, 489),
        (1, 517), (2, 522), (6, 533), (7, 534)] : List (Nat × Nat)) := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hLenEq : (allocMultiLib.blockLib aj).text.code.length = lsLen bi := by
    have h0 := List.all_eq_true.mp c2_allocWriter_codeLen_eq_lsLen (aj, bi) hPairMem
    dsimp only at h0
    exact Nat.beq_eq.mp h0
  have hbi_bnd := hBounds bi hbi624
  intro off hoff
  rw [hLenEq] at hoff
  change (P_fmt lr).externAt? ((c2MplAllocCli k).base aj + BitVec.ofNat 64 off) = none
  rw [hBaseEq]
  have hdef : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
  have hpc_lt_stub : (cliElfMultiPlacement.base bi + BitVec.ofNat 64 off).toNat <
      c2FirstExternStubAddr.toNat := by
    rw [hdef, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [P_fmt_externAt_of_not_s5 lr (s5Addrs_contains_false_of_lt (by omega))]
  have hne := range_ne_lr_of_disjoint hLs c2_disjoint_fmtWrite_ok hj ho hlrEq hnotInt
    hbiMem hbi624 hoff
  rw [c2FmtProgTrap_externAt_of_ne hne]
  exact c2FmtProg_externAt_none_of_lt_stub hpc_lt_stub

/-! ## 4. Link Bundles `CliFmtWriteSubLink` & `CliFormatInnerSubLink` on `P_fmt lr` -/

private theorem lsρ_eq_resolve_fmtWrite [LibsignalPlacement] :
    lsρ lsFmtWriteSym = libsignalSessionLib.resolve lsmpl lsFmtWriteSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem lsρ_eq_resolve_u8 [LibsignalPlacement] :
    lsρ lsU8DisplayFmtSym = libsignalSessionLib.resolve lsmpl lsU8DisplayFmtSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem lsρ_eq_resolve_u32 [LibsignalPlacement] :
    lsρ lsU32DisplayFmtSym = libsignalSessionLib.resolve lsmpl lsU32DisplayFmtSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem lsρ_eq_resolve_u64 [LibsignalPlacement] :
    lsρ lsU64DisplayFmtSym = libsignalSessionLib.resolve lsmpl lsU64DisplayFmtSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem lsρ_eq_resolve_strDisplay [LibsignalPlacement] :
    lsρ lsStrDisplayFmtSym = libsignalSessionLib.resolve lsmpl lsStrDisplayFmtSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem lsρ_eq_resolve_writeStr [LibsignalPlacement] :
    lsmpl.ρ lsFormatterWriteStrSym =
      libsignalSessionLib.resolve lsmpl lsFormatterWriteStrSym :=
  Eq.symm (ls_resolve_data_ultra (eagerReduce (Eq.refl true)))

private theorem c2_resolve_writeStr_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFormatterWriteStrSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl formatterWriteStrSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFormatterWriteStrSym).trans (by rfl_kernel)

private theorem c2_coreFmt_codeLoadedWhere_writeStr_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere writeStrKeep c2CoreFmtMpl m := by
  have hlen : coreFmtMultiLib.blocks.length = 11 := by decide
  have hsub :
      ((List.range 11).all fun j => !(writeStrKeep j) || c2CoreFmtActiveKeep j) = true := by
    decide
  intro j hj hk
  rw [hlen] at hj
  have hall := List.all_eq_true.mp hsub j (List.mem_range.mpr hj)
  simp only [hk, Bool.not_true, Bool.false_or] at hall
  exact c2_coreFmt_codeLoadedWhere_active_of_rxCode hRx j (by rw [hlen]; exact hj) hall

private theorem c2_fmtWriteSubLink_P_fmt [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits)
    {lr : BitVec 64} (hRet : LsRetAddrFmtWrite lr) :
    CliFmtWriteSubLink fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
      lim (P_fmt lr) c2CoreMpl c2MplAllocCli c2CoreFmtMpl := by
  have hlr : lr.toNat < c2FirstExternStubAddr.toNat :=
    f3LsRetAddr624_lt_firstExternStub hLs hRet.toLsRetAddr624
  have ⟨_, _, hplLs, _⟩ := hLs
  refine
    { linkAlloc := fun k =>
        { plCore := c2CoreMpl_placeable
          clCore := fun m hm =>
            c2_core_codeLoaded_of_rxCode
              (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
          noExtCore0 := noExtern_P_fmt_of_preS5 hlr c2Core_blk0_preS5_chk
          plAlloc := c2MplAllocCli_placeable k
          clAllocWriter := fun m hm =>
            c2MplAllocCli_stringWriter_codeLoaded k ((P_fmt_codeLoaded_iff lr m).mp hm)
          noExtAlloc1 := allocWriter_noExtern_P_fmt hLs hRet k (Or.inl rfl)
          noExtAlloc2 := allocWriter_noExtern_P_fmt hLs hRet k (Or.inr (Or.inl rfl))
          noExtAlloc6 := allocWriter_noExtern_P_fmt hLs hRet k (Or.inr (Or.inr (Or.inl rfl)))
          noExtAlloc7 := allocWriter_noExtern_P_fmt hLs hRet k (Or.inr (Or.inr (Or.inr rfl)))
          panicHandleErr := by
            rw [c2MplAllocCli_handleError_resolve k]
            exact P_fmt_externAt_handleError hlr
          memcpyAll := fun ro => by
            rw [c2MplAllocCli_memcpy_resolve k, wp4MemcpyRealAddr_eq]
            exact c2_budgetMemcpy_f3Lo_ok (P_fmt_svc lr) (P_fmt_cl_f3Lo lr)
              (fun _ => P_fmt_ext_none_of_keepLo hlr) ro
          allocShim := by
            rw [c2MplAllocCli_noAllocShim_resolve k, wp4NoShimV2Addr_eq]
            exact c2_budgetAllocShim_f3Lo_ok (P_fmt_svc lr) (P_fmt_cl_f3Lo lr)
              (fun _ => P_fmt_ext_none_of_keepLo hlr)
          rustAlloc := by
            rw [c2MplAllocCli_rustAlloc_resolve k, wp4RustAllocAddr_eq]
            exact rustBudgetAlloc_of_cliBase
              (c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim
                (P_fmt_svc lr) (P_fmt_cl_f3Lo lr) (fun _ => P_fmt_ext_none_of_keepLo hlr))
          rustRealloc := by
            rw [c2MplAllocCli_rustRealloc_resolve k, wp4RustReallocAddr_eq]
            exact rustBudgetRealloc_of_cliBase
              (c2_realloc_withExecFrozen_ok hMm γ tp brkStart hlim
                (P_fmt_svc lr) (P_fmt_cl_f3Lo lr) (fun _ => P_fmt_ext_none_of_keepLo hlr)) }
      vtEq := c2MplAllocCli_vtable_eq hLs
      plFmt := c2CoreFmtMpl_placeable
      noExtFmtStr := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_str_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtFmtU8 := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU8 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u8_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      plLs := hplLs
      noExtLs := by
        rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
        intro bi hbi hk
        have hbi_cases : bi ∈ ([121, 191, 214, 216, 217, 498, 537] : List Nat) := by
          unfold fmtWriteSubLsKeep at hk
          simp only [cliStringDisplayShimBlocks, decide_eq_true_eq,
            List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide
        have hbiMem : bi ∈ c2FmtWriteInternalIndices :=
          decide_eq_true_eq.mp (List.all_eq_true.mp (by decide :
            (([121, 191, 214, 216, 217, 498, 537] : List Nat).all fun x =>
              decide (x ∈ c2FmtWriteInternalIndices)) = true) bi hbi_cases)
        have hbi624 : bi < 624 := by
          rw [libsignalSessionLib_blocks_length] at hbi; exact hbi
        have hSubMem : bi ∈
            ([78, 121, 170, 191, 214, 215, 216, 217,
              392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat) :=
          decide_eq_true_eq.mp (List.all_eq_true.mp (by decide :
            (([121, 191, 214, 216, 217, 498, 537] : List Nat).all fun x =>
              decide (x ∈ ([78, 121, 170, 191, 214, 215, 216, 217,
                392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat))) = true)
            bi hbi_cases)
        have hLenEq : (libsignalSessionLib.blockLib bi).text.code.length = lsLen bi :=
          Nat.beq_eq.mp (List.all_eq_true.mp c2_lsSub_codeLen_eq_lsLen bi hSubMem)
        exact lsBlock_noExtern_P_fmt hLs c2_disjoint_fmtWrite_ok hj ho hlrEq hnotInt
          hbiMem hbi624 hLenEq
      clLs := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((P_fmt_codeLoaded_iff lr m).mp hm) j hj
      tieFmtWrite := lsρ_eq_resolve_fmtWrite.trans (c2_resolve_fmtWrite_fnAddr hLs)
      tieU8 := lsρ_eq_resolve_u8.trans (c2_resolve_u8DisplayFmt_fnAddr hLs)
      tieStrDisplay := lsρ_eq_resolve_strDisplay.trans (c2_resolve_strDisplayFmt_fnAddr hLs) }

private theorem c2_formatInnerSubLink_P_fmt [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits)
    {lr : BitVec 64} (hRet : LsRetAddrFormatInner lr) :
    CliFormatInnerSubLink fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
      lim (P_fmt lr) c2CoreMpl c2AllocMpl c2CoreFmtMpl := by
  have hlr : lr.toNat < c2FirstExternStubAddr.toNat :=
    f3LsRetAddr624_lt_firstExternStub hLs hRet.toLsRetAddr624
  have ⟨_, _, hplLs, _⟩ := hLs
  have hNoExtLsAll : LibKeepNoExtern libsignalSessionLib formatInnerSubLsKeep lsmpl (P_fmt lr) := by
    rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
    intro bi hbi hk
    have hSubMem : bi ∈
        ([78, 121, 170, 191, 214, 215, 216, 217,
          392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat) := by
      unfold formatInnerSubLsKeep spqrErrorDispKeep at hk
      simp only [cliStringDisplayShimBlocks,
        cliStrRefDisplayShimBlocks, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with (rfl | rfl | rfl | rfl | rfl) |
          (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl |
          (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    have hbiMem : bi ∈ c2FormatInnerInternalIndices :=
      decide_eq_true_eq.mp (List.all_eq_true.mp (by decide :
        (([78, 121, 170, 191, 214, 215, 216, 217,
          392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat).all fun x =>
          decide (x ∈ c2FormatInnerInternalIndices)) = true) bi hSubMem)
    have hbi624 : bi < 624 := by
      rw [libsignalSessionLib_blocks_length] at hbi; exact hbi
    have hLenEq : (libsignalSessionLib.blockLib bi).text.code.length = lsLen bi :=
      Nat.beq_eq.mp (List.all_eq_true.mp c2_lsSub_codeLen_eq_lsLen bi hSubMem)
    exact lsBlock_noExtern_P_fmt hLs c2_disjoint_formatInner_ok hj ho hlrEq hnotInt
      hbiMem hbi624 hLenEq
  refine
    { plCore := c2CoreMpl_placeable
      clCore := fun m hm =>
        c2_core_codeLoaded_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtCore0 := noExtern_P_fmt_of_preS5 hlr c2Core_blk0_preS5_chk
      plAlloc := c2AllocMpl_placeable
      clAllocWriter := fun m hm =>
        c2_alloc_stringWriter_codeLoaded_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtAlloc1 := c2Alloc_seg2_noExtern_P_fmt hlr (by decide)
      noExtAlloc2 := c2Alloc_seg2_noExtern_P_fmt hlr (by decide)
      noExtAlloc6 := c2Alloc_seg2_noExtern_P_fmt hlr (by decide)
      noExtAlloc7 := c2Alloc_seg2_noExtern_P_fmt hlr (by decide)
      panicHandleErr := by
        rw [c2_alloc_handleError_resolve]
        exact P_fmt_externAt_handleError hlr
      memcpyAll := fun ro => by
        rw [c2_alloc_memcpy_resolve, wp4MemcpyRealAddr_eq]
        exact c2_budgetMemcpy_f3Lo_ok (P_fmt_svc lr) (P_fmt_cl_f3Lo lr)
          (fun _ => P_fmt_ext_none_of_keepLo hlr) ro
      allocShim := by
        rw [c2_alloc_noAllocShim_resolve, wp4NoShimV2Addr_eq]
        exact c2_budgetAllocShim_f3Lo_ok (P_fmt_svc lr) (P_fmt_cl_f3Lo lr)
          (fun _ => P_fmt_ext_none_of_keepLo hlr)
      rustAlloc := by
        rw [c2_alloc_rustAlloc_resolve, wp4RustAllocAddr_eq]
        exact rustBudgetAlloc_of_cliBase
          (c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim
            (P_fmt_svc lr) (P_fmt_cl_f3Lo lr) (fun _ => P_fmt_ext_none_of_keepLo hlr))
      rustRealloc := by
        rw [c2_alloc_rustRealloc_resolve, wp4RustReallocAddr_eq]
        exact rustBudgetRealloc_of_cliBase
          (c2_realloc_withExecFrozen_ok hMm γ tp brkStart hlim
            (P_fmt_svc lr) (P_fmt_cl_f3Lo lr) (fun _ => P_fmt_ext_none_of_keepLo hlr))
      clAlloc := fun m hm =>
        c2AllocMpl_codeLoaded_of_c2FmtProg ((P_fmt_codeLoaded_iff lr m).mp hm)
      noExtAlloc3 := c2Alloc_seg2_noExtern_P_fmt hlr (by decide)
      fmtWriteTie := c2_alloc_fmtWriteTie
      plFmt := c2CoreFmtMpl_placeable
      noExtFmtWriteStr := c2CoreFmt_active_noExtern_P_fmt hlr (by decide) (by decide)
      clFmtWriteStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_writeStr_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtFmtU32 := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU32 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u32_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtFmtU64 := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU64 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u64_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtLs := fun bi hbi hspqr =>
        hNoExtLsAll bi hbi (formatInnerSubLsKeep_of_spqr hspqr)
      clLs := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((P_fmt_codeLoaded_iff lr m).mp hm) j hj
      tieWriteStr := lsρ_eq_resolve_writeStr.trans (c2_resolve_writeStr_fnAddr hLs)
      tieFmtWrite := lsρ_eq_resolve_fmtWrite.trans (c2_resolve_fmtWrite_fnAddr hLs)
      tieU32 := lsρ_eq_resolve_u32.trans (c2_resolve_u32DisplayFmt_fnAddr hLs)
      tieU64 := lsρ_eq_resolve_u64.trans (c2_resolve_u64DisplayFmt_fnAddr hLs)
      noExtFmtStr := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_str_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      noExtFmtU8 := fun j hj hk =>
        c2CoreFmt_active_noExtern_P_fmt hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU8 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u8_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((P_fmt_codeLoaded_iff lr m).mp hm))
      plLs := hplLs
      noExtLsAll := hNoExtLsAll
      clLsAll := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((P_fmt_codeLoaded_iff lr m).mp hm) j hj
      tieU8 := lsρ_eq_resolve_u8.trans (c2_resolve_u8DisplayFmt_fnAddr hLs)
      tieStrDisplay := lsρ_eq_resolve_strDisplay.trans (c2_resolve_strDisplayFmt_fnAddr hLs) }

/-! ## 5. Untrapping `Steps (P_fmt lr)` to `StepsUntil c2FmtProg` & `StepsStrictAvoid` -/

private theorem steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all

private theorem steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all

private theorem evalInst_eq_of_svc_eq {P Q : Program} (h : P.svc = Q.svc)
    (inst : Instr) (s : State) : P.evalInst inst s = Q.evalInst inst s := by
  unfold Program.evalInst
  rw [h]

private theorem fetchMem_eq_of_externAt_eq {P Q : Program} {m : Memory} {pc : BitVec 64}
    (h : P.externAt? pc = Q.externAt? pc) :
    P.fetchMem m pc = Q.fetchMem m pc := by
  unfold Program.fetchMem
  rw [h]

private theorem fetchMem_none_of_externAt_some {P : Program} {m : Memory} {pc : BitVec 64}
    {f : State → State} (h : P.externAt? pc = some f) :
    P.fetchMem m pc = none := by
  unfold Program.fetchMem
  simp [h]

private theorem step_running_local {P : Program} {u v : State} (h : Step P u v) :
    u.status = .Running := by
  cases h <;> assumption

private theorem subroutineStop_of_outcome {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (hout : SubroutineOutcome spec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted ∧ (∀ msg, sf.status ≠ .Exception msg) := by
  rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨ec, he, _⟩ | ⟨ho, _⟩
  · refine ⟨Or.inl hret, ?_, ?_⟩
    · rcases hret with ⟨_, _, hrun_sf⟩; intro hh; rw [hh] at hrun_sf; cases hrun_sf
    · rcases hret with ⟨_, _, hrun_sf⟩; intro msg hex; rw [hex] at hrun_sf; cases hrun_sf
  · refine ⟨Or.inr (Or.inl hp), ?_, ?_⟩
    · intro hh; rw [hh] at hp; cases hp
    · intro msg hex; rw [hex] at hp; cases hp
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨ec, he⟩)), ?_, ?_⟩
    · intro hh; rw [hh] at he; cases he
    · intro msg hex; rw [hex] at he; cases he
  · refine ⟨Or.inr (Or.inr (Or.inr ho)), ?_, ?_⟩
    · intro hh; rw [hh] at ho; cases ho
    · intro msg hex; rw [hex] at ho; cases ho

private theorem untrap_P_fmt_to_c2_and_real {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks)
    {s0 s1 sf : State}
    (hs : Steps (P_fmt (s0.readReg64 .lr)) s1 sf)
    (hstop : SubroutineStop s0 sf)
    (hnhalt : sf.status ≠ .Halted)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg) :
    StepsUntil c2FmtProg (SubroutineStop s0) s1 sf ∧
    StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1 sf := by
  let lr := s0.readReg64 .lr
  let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have hsvc_real : P_real.svc = Syscall.standard := rfl
  change Steps (P_fmt lr) s1 sf at hs
  induction hs with
  | refl s => exact ⟨.refl s, .refl s⟩
  | @step sa sb _ h1 hrest ih =>
    have hra : sa.status = .Running := step_running_local h1
    have hns5 : s5Addrs.contains sa.pc = false := by
      cases hs5 : s5Addrs.contains sa.pc
      · rfl
      · exfalso
        have he_s5 := P_fmt_externAt_s5 lr hs5
        cases h1 with
        | halt_unmapped _ _ hnoext => rw [he_s5] at hnoext; cases hnoext
        | extern _ he _ _ =>
          rw [he_s5] at he; injection he with hf; subst hf
          exact hnoex "hit S5" (steps_preserves_exception hrest rfl)
        | extern_fault _ _ _ =>
          exact hnoex _ (steps_preserves_exception hrest rfl)
        | exec _ hfm =>
          rw [fetchMem_none_of_externAt_some he_s5] at hfm; cases hfm
    have hext_untrap : (P_fmt lr).externAt? sa.pc = (c2FmtProgTrap lr).externAt? sa.pc :=
      P_fmt_externAt_of_not_s5 lr hns5
    have hne_lr : sa.pc ≠ lr := by
      intro hpc
      have he_lr : (P_fmt lr).externAt? sa.pc = some c2HaltHook := by
        rw [hext_untrap, hpc]
        exact c2FmtProgTrap_externAt_self lr
      cases h1 with
      | halt_unmapped _ _ hnoext => rw [he_lr] at hnoext; cases hnoext
      | extern _ he _ _ =>
        rw [he_lr] at he; injection he with hf; subst hf
        exact hnhalt (steps_preserves_halted hrest rfl)
      | extern_fault _ _ _ =>
        exact hnoex _ (steps_preserves_exception hrest rfl)
      | exec _ hfm =>
        rw [fetchMem_none_of_externAt_some he_lr] at hfm; cases hfm
    have hnotStop : ¬ SubroutineStop s0 sa := by
      rintro (⟨hpc, _, _⟩ | hp | ⟨_, hex⟩ | ho)
      · exact hne_lr hpc
      · rw [hra] at hp; cases hp
      · rw [hra] at hex; cases hex
      · rw [hra] at ho; cases ho
    have hext_c2 : (P_fmt lr).externAt? sa.pc = c2FmtProg.externAt? sa.pc := by
      rw [hext_untrap]
      exact c2FmtProgTrap_externAt_of_ne hne_lr
    have hext_real : (P_fmt lr).externAt? sa.pc = P_real.externAt? sa.pc := by
      rw [hext_c2]
      exact c2FmtProg_externAt_eq_real hLs mmpl W sa.pc
    obtain ⟨hstep_c2, hstep_real⟩ : Step c2FmtProg sa sb ∧ Step P_real sa sb := by
      cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt (steps_preserves_halted hrest rfl))
      | extern_fault _ _ _ =>
        exact False.elim (hnoex _ (steps_preserves_exception hrest rfl))
      | extern hr he hkf hsym =>
        exact ⟨Step.extern hr (hext_c2.symm.trans he) hkf hsym,
          Step.extern hr (hext_real.symm.trans he) hkf hsym⟩
      | @exec inst hr hfm =>
        have hfm_c2 : c2FmtProg.fetchMem sa.mem sa.pc = some inst :=
          (fetchMem_eq_of_externAt_eq hext_c2).symm.trans hfm
        have hfm_real : P_real.fetchMem sa.mem sa.pc = some inst :=
          (fetchMem_eq_of_externAt_eq hext_real).symm.trans hfm
        have hev_c2 : (P_fmt lr).evalInst inst sa = c2FmtProg.evalInst inst sa :=
          evalInst_eq_of_svc_eq ((P_fmt_svc lr).trans c2FmtProg_svc.symm) inst sa
        have hev_real : (P_fmt lr).evalInst inst sa = P_real.evalInst inst sa :=
          evalInst_eq_of_svc_eq ((P_fmt_svc lr).trans hsvc_real.symm) inst sa
        refine ⟨?_, ?_⟩
        · rw [hev_c2]; exact Step.exec hr hfm_c2
        · rw [hev_real]; exact Step.exec hr hfm_real
    obtain ⟨huntil_rest, havoid_rest⟩ := ih hstop hnhalt hnoex
    exact ⟨.step hnotStop hstep_c2 huntil_rest,
      .step (by rw [hns5]; nofun) hstep_real havoid_rest⟩

/-! ## 6. Rekeying `F3CodeInv`, `spAligned`, & Single-Run Trapped Executions -/

private theorem f3CodeInv_rekey_ls {mpl mpl' mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs' : libsignalSessionLib.LinkedAt cliElfBytes mpl')
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : F3CodeInv mpl mmpl m) :
    F3CodeInv mpl' mmpl m := by
  obtain ⟨inputs, sLoad, hload, hkf⟩ := hInv.fromLoad
  rw [f3PatchedElf_eq_of_linkedAt hLs, ← f3PatchedElf_eq_of_linkedAt hLs'] at hload
  exact (f3CodeOk_of_patchedLoadState hLs' hMm hload).1.of_keepsFrozen hkf

private theorem sp_mod16_iff_spAligned (s : State) :
    s.sp.toNat % 16 = 0 ↔ s.spAligned = true := by
  unfold State.spAligned
  rw [beq_iff_eq]
  have hm : (s.sp &&& 15#64).toNat = s.sp.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod s.sp.toNat 4
  constructor
  · intro h0
    apply BitVec.eq_of_toNat_eq
    rw [hm, h0, BitVec.toNat_ofNat]
  · intro heq
    rw [← hm, heq]
    rfl

private theorem setPC_eq_self {u : State} {target : BitVec 64} (h : u.pc = target) :
    u.setPC target = u := by
  cases u
  dsimp only [State.setPC] at h ⊢
  subst h
  rfl

private theorem activePre_and_run_of_c2FmtGhost_noException {α : Type}
    {roGuard : Memory → Prop} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    {u : State}
    (hImg : c2FmtImgGuard roGuard u)
    (hnoex : ∀ msg, (c2FmtGhost roGuard entryTarget specOf fallback u).status ≠ .Exception msg) :
    ActiveC2FmtPre specOf u ∧
    ∃ (hRun : ActiveC2FmtRun entryTarget specOf u),
      c2FmtGhost roGuard entryTarget specOf fallback u = Classical.choose hRun := by
  classical
  have hAct : ActiveC2FmtPre specOf u := by
    by_contra hNotAct
    apply hnoex "c2FmtGhost: inactive precondition"
    unfold c2FmtGhost
    simp [hImg, hNotAct]
  have hRun : ActiveC2FmtRun entryTarget specOf u := by
    by_contra hNotRun
    apply hnoex "c2FmtGhost: subroutine_ok violated"
    unfold c2FmtGhost
    simp [hImg, hAct, hNotRun]
  refine ⟨hAct, hRun, ?_⟩
  unfold c2FmtGhost
  simp [hImg, hAct, hRun]

private theorem withExecFrozenBudget_pool_intro (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : fineCostModel.σ) (s : State)
    (hfr : ExecFrozen s.mem) :
    (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s ⊢
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mpl tp brkStart)).pool
        (nonZeroEquivLim lim) st s := by
  dsimp only [withExecFrozenBudget]
  rw [fineHookPool_nonZeroEquivLim, sepConj_comm]
  exact Entails.pure_right (fun _ => hfr) (Entails.refl _)

private theorem sat_mono_slot4_of_5 {m : Memory} {P1 P2 P3 Q Q' P5 R : SepProp}
    (h : Q ⊢ Q')
    (hm : m ⊨ (P1 ∗ P2 ∗ P3 ∗ Q ∗ P5) ∗ R) :
    m ⊨ (P1 ∗ P2 ∗ P3 ∗ Q' ∗ P5) ∗ R := by
  have hstep : Q ∗ (P1 ∗ P2 ∗ P3 ∗ P5 ∗ R) ⊢ Q' ∗ (P1 ∗ P2 ∗ P3 ∗ P5 ∗ R) :=
    sepConj_mono_left h
  exact Satisfies.mono
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans hstep (Entails.of_eq (by sep_ac_rfl))))
    hm

private theorem fmtWrite_partA_pre [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr : BitVec 64)
    {s0 : State} (hFr0 : ExecFrozen s0.mem)
    (hRo0 : cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl s0.mem)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFmtWriteProtoAddrCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R) :
    (s0.setPC entryAddr).mem ⊨
      (withRoMemGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs)))).pre (c, st0) (s0.setPC entryAddr) ∗ R := by
  let s1 := s0.setPC entryAddr
  have hpre_s1 : s1.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s1 ∗ R := by
    dsimp only [s1]
    rw [fmtWriteGhostSpecOf_pre_setPC mmpl brkStart lim γ tp (c, st0) s0 entryAddr]
    exact hpre
  have hpre_in1 := (extract_withLsRetFmtWrite hpre_s1).2
  dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec]
    at hpre_in1 ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_in1 ⊢
  refine ⟨hRo0, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  rcases hpre_in1 with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, hEx⟩, hm0⟩
  refine ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen,
    (fitsEnv_nonZeroEquivLim fineCostModel lim st0 _).symm ▸ hFit, hEx⟩, ?_⟩
  rw [withExecFrozenBudget_repAlloc]
  exact sat_mono_slot4_of_5 (withExecFrozenBudget_pool_intro γ mmpl tp brkStart lim st0 s1 hFr0) hm0

private theorem fmtWrite_partB_post [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr : BitVec 64)
    {s0 sf : State}
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFmtWriteProtoAddrCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hout_sub : SubroutineOutcome
      (withRoMemGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs))))
      (c, st0) R (s0.setPC entryAddr) sf) :
    SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf := by
  let A_base := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let s1 := s0.setPC entryAddr
  rcases hout_sub with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpost1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfs, htr⟩, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨evs, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨bs', hp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hw0, hacp1, hfs', htr', hEnv⟩, hm_f⟩
    rw [withExecFrozenBudget_repAlloc] at hm_f
    have hm_drop : sf.mem ⊨
        (CryptoVerification.RustHeap.vecU8 A_base.repAlloc c.v bs' ∗
          VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x2 c.x3
            dotTplBytes c.args ∗
          c.clientSep ∗ A_base.pool lim (fineCostModel.stepEvents evs st0) sf ∗
          stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R :=
      sat_mono_slot4_of_5
        (withExecFrozenBudget_pool_entails γ mmpl tp brkStart lim
          (fineCostModel.stepEvents evs st0) sf)
        hm_f
    have hout1 : SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s1 sf := by
      refine Or.inl ⟨hret1, hcc1, ?_⟩
      dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfs, htr⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨bs', ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hw0, hacp1, hfs', htr', hEnv⟩, hm_drop⟩
    exact fmtWriteGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp (c, st0) R s0 sf
      entryAddr hout1
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem fmtWrite_partC_glue [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr targetFnAddr : BitVec 64) (hEntryEq : entryAddr = targetFnAddr)
    (P_trap : Program)
    {s0 : State} (hFr0 : ExecFrozen s0.mem)
    (hRo0 : cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl s0.mem)
    (hCL_trap : P_trap.CodeLoaded (s0.setPC entryAddr).mem)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFmtWriteProtoAddrCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R)
    (hSubOk : subroutine_ok P_trap targetFnAddr
      (withRoMemGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs))))) :
    ∃ sf : State,
      Steps P_trap (s0.setPC entryAddr) sf ∧
      SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf := by
  have hpre_sub := fmtWrite_partA_pre mmpl brkStart lim entryAddr hFr0 hRo0 γ tp c st0 R hpre
  obtain ⟨sf, hsteps_trap, hout_sub⟩ :=
    reaches_outcome_iff.mp
      (hSubOk.to_outcome (c, st0) R (s0.setPC entryAddr)
        (by rw [State.pc_setPC]; exact hEntryEq)
        hrun hpre_sub hsp)
      hCL_trap
  exact ⟨sf, hsteps_trap, fmtWrite_partB_post mmpl brkStart lim entryAddr γ tp c st0 R hout_sub⟩

private theorem single_fmtWrite_trap_run [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) s0)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFmtWriteProtoAddrCall × fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre x s0 ∗ R) :
    ∃ sf : State,
      StepsUntil c2FmtProg (SubroutineStop s0) (s0.setPC c2FmtWriteAddr) sf ∧
      SubroutineStop s0 sf ∧
      StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (s0.setPC c2FmtWriteAddr) sf := by
  rcases hImg with ⟨hFr0, hRo0, hCL0⟩
  obtain ⟨hRet, _⟩ := extract_withLsRetFmtWrite hpre
  rcases x with ⟨c, st0⟩
  have hL := c2_fmtWriteSubLink_P_fmt hLsLsmpl mmpl hMm γ tp brkStart
    (nonZeroEquivLim_ne_zero lim) hRet
  have hSubOk := cliCoreFmtWrite_protoAddr_ro_ok
    (EnvOf := fun c0 => ExactOrNilEnv c0.exactEvs) hL
  have hEntryEq : c2FmtWriteAddr = coreMultiLib.fnAddr c2CoreMpl coreFmtWriteSym :=
    (c2_resolve_fmtWrite_eq hLsLsmpl).symm.trans (c2_resolve_fmtWrite_fnAddr hLsLsmpl)
  have hCL_trap : (P_fmt (s0.readReg64 .lr)).CodeLoaded (s0.setPC c2FmtWriteAddr).mem := by
    rw [State.mem_setPC]
    exact (P_fmt_codeLoaded_iff (s0.readReg64 .lr) s0.mem).mpr hCL0
  obtain ⟨sf, hsteps_trap, hout_s0⟩ :=
    fmtWrite_partC_glue mmpl brkStart lim c2FmtWriteAddr
      (coreMultiLib.fnAddr c2CoreMpl coreFmtWriteSym) hEntryEq
      (P_fmt (s0.readReg64 .lr)) hFr0 hRo0 hCL_trap hrun hsp γ tp c st0 R hpre hSubOk
  obtain ⟨hstop, hnhalt, hnoex_sf⟩ := subroutineStop_of_outcome hout_s0
  obtain ⟨huntil, havoid⟩ := untrap_P_fmt_to_c2_and_real hLs mmpl W hsteps_trap hstop hnhalt hnoex_sf
  exact ⟨sf, huntil, hstop, havoid⟩

private theorem formatInner_partA_pre [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr : BitVec 64)
    {s0 : State} (hFr0 : ExecFrozen s0.mem)
    (hRo0 : cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl s0.mem)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFormatInnerLsCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R) :
    (s0.setPC entryAddr).mem ⊨
      (withRoMemGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl)
        (withFsTraceExact (cliFormatInnerLsCallSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs)))).pre (c, st0) (s0.setPC entryAddr) ∗ R := by
  let s1 := s0.setPC entryAddr
  have hpre_s1 : s1.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s1 ∗ R := by
    dsimp only [s1]
    rw [formatInnerGhostSpecOf_pre_setPC mmpl brkStart lim γ tp (c, st0) s0 entryAddr]
    exact hpre
  have hpre_in1 := (extract_withLsRetFormatInner hpre_s1).2
  dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec]
    at hpre_in1 ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_in1 ⊢
  refine ⟨hRo0, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  rcases hpre_in1 with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
  refine ⟨⟨hx8, hx0, hx1, hshOk,
    (fitsEnv_nonZeroEquivLim fineCostModel lim st0 _).symm ▸ hFit, hEx⟩, ?_⟩
  exact sat_mono_slot4_of_5 (withExecFrozenBudget_pool_intro γ mmpl tp brkStart lim st0 s1 hFr0) hm0

private theorem formatInner_partB_post [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr : BitVec 64)
    {s0 sf : State}
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFormatInnerLsCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hout_sub : SubroutineOutcome
      (withRoMemGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl)
        (withFsTraceExact (cliFormatInnerLsCallSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs))))
      (c, st0) R (s0.setPC entryAddr) sf) :
    SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf := by
  let A_base := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let s1 := s0.setPC entryAddr
  rcases hout_sub with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpost1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfs, htr⟩, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨evs, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨bs', hp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hacp1, hfs', htr', hEnv⟩, hm_f⟩
    rw [withExecFrozenBudget_repAlloc] at hm_f
    have hm_drop : sf.mem ⊨
        (CryptoVerification.RustHeap.vecU8 A_base.repAlloc c.ret bs' ∗
          VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
          c.clientSep ∗ A_base.pool lim (fineCostModel.stepEvents evs st0) sf ∗
          stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R :=
      sat_mono_slot4_of_5
        (withExecFrozenBudget_pool_entails γ mmpl tp brkStart lim
          (fineCostModel.stepEvents evs st0) sf)
        hm_f
    have hout1 : SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s1 sf := by
      refine Or.inl ⟨hret1, hcc1, ?_⟩
      dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
        cliFormatInnerLsCallSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfs, htr⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨bs', ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hacp1, hfs', htr', hEnv⟩, hm_drop⟩
    exact formatInnerGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp (c, st0) R s0 sf
      entryAddr hout1
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem formatInner_partC_glue [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (entryAddr targetFnAddr : BitVec 64) (hEntryEq : entryAddr = targetFnAddr)
    (P_trap : Program)
    {s0 : State} (hFr0 : ExecFrozen s0.mem)
    (hRo0 : cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl s0.mem)
    (hCL_trap : P_trap.CodeLoaded (s0.setPC entryAddr).mem)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFormatInnerLsCall) (st0 : fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R)
    (hSubOk : subroutine_ok P_trap targetFnAddr
      (withRoMemGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl)
        (withFsTraceExact (cliFormatInnerLsCallSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs))))) :
    ∃ sf : State,
      Steps P_trap (s0.setPC entryAddr) sf ∧
      SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf := by
  have hpre_sub := formatInner_partA_pre mmpl brkStart lim entryAddr hFr0 hRo0 γ tp c st0 R hpre
  obtain ⟨sf, hsteps_trap, hout_sub⟩ :=
    reaches_outcome_iff.mp
      (hSubOk.to_outcome (c, st0) R (s0.setPC entryAddr)
        (by rw [State.pc_setPC]; exact hEntryEq)
        hrun hpre_sub hsp)
      hCL_trap
  exact ⟨sf, hsteps_trap, formatInner_partB_post mmpl brkStart lim entryAddr γ tp c st0 R hout_sub⟩

private theorem single_formatInner_trap_run [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) s0)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFormatInnerLsCall × fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre x s0 ∗ R) :
    ∃ sf : State,
      StepsUntil c2FmtProg (SubroutineStop s0) (s0.setPC c2FormatInnerAddr) sf ∧
      SubroutineStop s0 sf ∧
      StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (s0.setPC c2FormatInnerAddr) sf := by
  rcases hImg with ⟨hFr0, hRo0, hCL0⟩
  obtain ⟨hRet, _⟩ := extract_withLsRetFormatInner hpre
  rcases x with ⟨c, st0⟩
  have hL := c2_formatInnerSubLink_P_fmt hLsLsmpl mmpl hMm γ tp brkStart
    (nonZeroEquivLim_ne_zero lim) hRet
  have hSubOk := cliAllocFormatInner_lsCall_ro_ok
    (EnvOf := fun c0 => ExactOrNilEnv c0.exactEvs) hL
  have hEntryEq : c2FormatInnerAddr = allocMultiLib.fnAddr c2AllocMpl allocFormatInnerSym :=
    (c2_resolve_formatInner_eq hLsLsmpl).symm.trans (c2_resolve_formatInner_fnAddr hLsLsmpl)
  have hCL_trap : (P_fmt (s0.readReg64 .lr)).CodeLoaded (s0.setPC c2FormatInnerAddr).mem := by
    rw [State.mem_setPC]
    exact (P_fmt_codeLoaded_iff (s0.readReg64 .lr) s0.mem).mpr hCL0
  obtain ⟨sf, hsteps_trap, hout_s0⟩ :=
    formatInner_partC_glue mmpl brkStart lim c2FormatInnerAddr
      (allocMultiLib.fnAddr c2AllocMpl allocFormatInnerSym) hEntryEq
      (P_fmt (s0.readReg64 .lr)) hFr0 hRo0 hCL_trap hrun hsp γ tp c st0 R hpre hSubOk
  obtain ⟨hstop, hnhalt, hnoex_sf⟩ := subroutineStop_of_outcome hout_s0
  obtain ⟨huntil, havoid⟩ := untrap_P_fmt_to_c2_and_real hLs mmpl W hsteps_trap hstop hnhalt hnoex_sf
  exact ⟨sf, huntil, hstop, havoid⟩

/-! ## 7. Exported `StepsStrictAvoid` Theorems for `c2FmtWriteGhost` & `c2FormatInnerGhost` -/

/-- `StepsStrictAvoid` of `mlkemSampleNttSyms` for `c2FmtWriteGhost` (`lsFmtWriteSym`). -/
theorem c2_fmtWriteGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsFmtWriteSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2FmtWriteGhost mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (c2FmtWriteGhost mmpl brkStart lim u) := by
  classical
  have hinvLs : F3CodeInv lsmpl mmpl u.mem := f3CodeInv_rekey_ls hLs hLsLsmpl hMm hinv
  have hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) u :=
    ⟨hfr, c2_cliFmtWriteRoGuard hLsLsmpl hinvLs, c2FmtProg_codeLoaded_of_f3CodeInv hLs hinv⟩
  obtain ⟨hAct, hRun, hEq⟩ := activePre_and_run_of_c2FmtGhost_noException hImg hnoex
  change c2FmtWriteGhost mmpl brkStart lim u = Classical.choose hRun at hEq
  rcases hAct with ⟨_, hspMod, γ₀, tp₀, x₀, R₀, hpre₀⟩
  have hsp : u.spAligned = true := (sp_mod16_iff_spAligned u).mp hspMod
  obtain ⟨sf_trap, huntil_trap, hstop_trap, havoid_trap⟩ :=
    single_fmtWrite_trap_run (W := W) hLs hLsLsmpl hMm brkStart lim hImg hrun hsp γ₀ tp₀ x₀ R₀ hpre₀
  have hspec := Classical.choose_spec hRun
  have hstop_choose : SubroutineStop u (Classical.choose hRun) :=
    (subroutineStop_of_outcome (hspec.2.2.2.2.2.2.2 γ₀ tp₀ x₀ R₀ hpre₀)).1
  have hdet : Classical.choose hRun = sf_trap :=
    h2fsgen_stepsUntil_det hspec.1 hstop_choose huntil_trap hstop_trap
  rw [hEq, hdet]
  have hset : u.setPC c2FmtWriteAddr = u :=
    setPC_eq_self (hpc.trans (c2_resolve_fmtWrite_eq hLs))
  rw [hset] at havoid_trap
  refine havoid_trap.mono_bad fun z hz => ?_
  rwa [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hz

/-- `StepsStrictAvoid` of `mlkemSampleNttSyms` for `c2FormatInnerGhost` (`lsFormatInnerSym`). -/
theorem c2_formatInnerGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsFormatInnerSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2FormatInnerGhost mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (c2FormatInnerGhost mmpl brkStart lim u) := by
  classical
  have hinvLs : F3CodeInv lsmpl mmpl u.mem := f3CodeInv_rekey_ls hLs hLsLsmpl hMm hinv
  have hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) u :=
    ⟨hfr, c2_cliFormatInnerRoGuard hLsLsmpl hinvLs, c2FmtProg_codeLoaded_of_f3CodeInv hLs hinv⟩
  obtain ⟨hAct, hRun, hEq⟩ := activePre_and_run_of_c2FmtGhost_noException hImg hnoex
  change c2FormatInnerGhost mmpl brkStart lim u = Classical.choose hRun at hEq
  rcases hAct with ⟨_, hspMod, γ₀, tp₀, x₀, R₀, hpre₀⟩
  have hsp : u.spAligned = true := (sp_mod16_iff_spAligned u).mp hspMod
  obtain ⟨sf_trap, huntil_trap, hstop_trap, havoid_trap⟩ :=
    single_formatInner_trap_run (W := W) hLs hLsLsmpl hMm brkStart lim hImg hrun hsp γ₀ tp₀ x₀ R₀ hpre₀
  have hspec := Classical.choose_spec hRun
  have hstop_choose : SubroutineStop u (Classical.choose hRun) :=
    (subroutineStop_of_outcome (hspec.2.2.2.2.2.2.2 γ₀ tp₀ x₀ R₀ hpre₀)).1
  have hdet : Classical.choose hRun = sf_trap :=
    h2fsgen_stepsUntil_det hspec.1 hstop_choose huntil_trap hstop_trap
  rw [hEq, hdet]
  have hset : u.setPC c2FormatInnerAddr = u :=
    setPC_eq_self (hpc.trans (c2_resolve_formatInner_eq hLs))
  rw [hset] at havoid_trap
  refine havoid_trap.mono_bad fun z hz => ?_
  rwa [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hz

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideFmt
