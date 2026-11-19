/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.HookDischarge.Libc.Memset
import ProofLib.Placed.Transfer
import ProofLib.ProgramReflection
import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Concrete Layout and Subroutine Witnesses for AES-256-CBC

Instantiates `aesEncGhost` and `aesDecGhost` (`AesCbcGhostReplays.lean`) on the concrete
`seg[2]` `.text.lib2` sub-program `aesCbcSubProg` (`f3TrialRxProg` with `Rust.panicked`
installed at the 18 `cliLinkedPanicAddrs` panic entries).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open ProofLib.StdStartup (checkWordsAt decodeWords hasInstrs hasWords_of_wordTree)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng.Proofs
  (HooksUnfetched ProgContainsMallocng memRegion_entails_exists_pointsToBytes memcpySymWords
   memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_ok steps_prog_of_pureMem_outcome)
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.RustStd (checkShimInstrsAt mallocngPlacedCAddrs)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib lsAesDecSym lsAesEncSym)
open LibsignalBinary.Heap
  (AllocEvent BudgetLimits FdsHiFrame FitsEnv RustCliAllocBudget allocMemcpyVmSpec
   zeroBudgetLimits)
open LibsignalBinary.Heap.AesDecErrRoBudget
  (cliAesDecErrStr1Addr cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr
   cliAesDecErrStr2Addr_ne_zero)
open LibsignalBinary.Heap.MuslMemOpsRunsTo
  (BlockExternFree codeLoaded_pureWordsProg_of_hasWords
   subroutine_ok_lift_pureWords_blockExternFree)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (hasShimInstrs_of_wordTree rustAllocShimVm_ret_ok rustHandleErrorPanic_of_extern
   rustHandleErrorPanicSpec)
open LibsignalBinary.Heap.Fine
  (allocMemsetVmSpec f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr
   f3RxWordCount f3StdLayout f3StubAddrs f3StubAzAddr fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (AesDecEnv AesEncEnv aesDecBudgetSpec aesEncBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memset (memset_memsetRegionSpec_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec (decrypt15Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds (decryptPar17Words)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc (encrypt15Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor (dropDecryptorInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
  (AesInitInnerCode aesInitInnerInstrs errnoLocationInstrs getauxvalHwcapInstrs getauxvalInstrsAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit fineHookNoAesRustCliAllocBudget fineHookNoAesRustCliAllocBudgetEntries_thunks
   fineHookNoAesRustCliAllocZeroedBudget_thunk_ok instPoolAesInitSplitFineHook)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand (invExpandedKeys15Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule (expandKey15ReachableInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
  (bitslice4_ok bitsliceInstrs bitslice_rep_ok invBitslice_ok invBitsliceInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
  (invSubBytes_ok invSubBytesInstrs subBytes_ok subBytesInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
  (invMixColumns1_ok invMixColumns1Instrs invMixColumns2_ok invMixColumns2Instrs
   invMixColumns3_ok invMixColumns3Instrs mixColumns1_ok mixColumns1Instrs
   mixColumns3_ok mixColumns3Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
  (memshift32_ok xorColumns_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
  (Aes256KeyScheduleCallees aes256KeySchedule_ok aes256KeyScheduleInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
  (Aes256EncryptCallees aes256Encrypt_ok aes256EncryptInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (Aes256DecryptCallees aes256Decrypt_ok aes256DecryptPrefixInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code (Aes256EncHwAddrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code (Aes256DecHwAddrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt
  (Aes256CbcEncryptCallees Aes256CbcEncryptPanicSyms aes256CbcEncrypt_keepsFs_of_wordTree_ok
   aes256CbcEncryptInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt
  (Aes256CbcDecryptCallees Aes256CbcDecryptPanicSyms aes256CbcDecrypt_keepsFs_of_wordTree_ok
   aes256CbcDecryptInstrs)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecGhost aesDecGhost_rowSpecOk aesDecSpecOf aesEncGhost aesEncGhost_rowSpecOk
   aesEncSpecOf c2AesRconAddr withAesStubRconRO withFsTraceExact withStubPermRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
  (c2_allocZeroed_noAes_withExecFrozen_ok c2_dealloc_noAes_withExecFrozen_ok
   f3PrePanicRxProg f3PrePanicRxProg_codeLoaded_of_f3Trial fineHookPool_nonZeroEquivLim
   fitsEnv_nonZeroEquivLim keepPrePanic nonZeroEquivLim nonZeroEquivLim_ne_zero
   withExecFrozenBudget withExecFrozenBudget_pool_entails)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_libc_eq_of_linkedAt
   f3CliElf_mallocng_linkedAt_unique f3TrialElf f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (cliLinkedPanicAddrs f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr
   isLinkedPanicAddr_false_of_ge isLinkedPanicAddr_false_of_lt isLinkedPanicAddr_false_of_mid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3Trial_allocMemcpyVm_ok f3Trial_allocMemsetVm_ok f3Trial_progContainsMallocng
   f3Trial_rustStdThunkCode f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs f3TrialRxProg
   f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_overrides_none f3TrialRxProg_stubs
   f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2Lib2TextLo c2TimeAddAddr wp4HandleErrorAddr)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. Concrete Addresses, `keepRxSeg`, and `aesCbcSubProg` -/

private theorem f3TrialRxProg_code_len : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

/-- Entry address of `libsignal_session_aes_256_cbc_encrypt` in `seg[2]` (`.text.lib2`,
    `= 0x4ca5d8#64`). -/
abbrev c2AesEncAddr : BitVec 64 := c2TimeAddAddr - 4340#64

/-- Entry address of `libsignal_session_aes_256_cbc_decrypt` in `seg[2]` (`.text.lib2`,
    `= 0x4c97c8#64`). -/
abbrev c2AesDecAddr : BitVec 64 := c2TimeAddAddr - 7940#64

/-- Symbol name of the unreachable OOM-error panic target `alloc::raw_vec::handle_error`. -/
abbrev rustHandleErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

/-- Dummy stub symbol name shared by the 18 linked panic offsets in `aesCbcSubProg`. -/
abbrev c2LinkedPanicStubSym : String := "__c2_linked_panic_stub"

@[expose] def aesCbcPanicExterns (sym : String) : Option (State → State) :=
  if sym == c2LinkedPanicStubSym then some Rust.panicked else none

@[expose] noncomputable def keepRxSeg (pc : BitVec 64) : Bool :=
  decide ((pc - f3TrialRxProg.base).toNat < f3TrialRxProg.code.length)

/-- `seg[2]` RX sub-program matching intermediate `P_pan` on `seg[2]`: installs `Rust.panicked`
    at all `18` `cliLinkedPanicAddrs` in `.text.lib2`. -/
@[expose] noncomputable def aesCbcSubProg : Program :=
  { f3TrialRxProg with
    stubs := cliLinkedPanicAddrs.map fun a => (c2LinkedPanicStubSym, (a - f3RxSegBase).toNat)
    externs := aesCbcPanicExterns }

/-- Compatibility alias (`rfl`) for `aesCbcSubProg`. -/
noncomputable abbrev aesCbcSubProgRaw : Program :=
  aesCbcSubProg

theorem aesCbcSubProg_svc : aesCbcSubProg.svc = Syscall.standard :=
  f3TrialRxProg_svc

theorem aesCbcSubProg_base : aesCbcSubProg.base = f3RxSegBase :=
  f3TrialRxProg_base

theorem aesCbcSubProg_codeLoaded_iff (m : Memory) :
    aesCbcSubProg.CodeLoaded m ↔ f3TrialRxProg.CodeLoaded m := by
  unfold Program.CodeLoaded
  dsimp only [aesCbcSubProg]
  exact Iff.rfl

theorem aesCbcSubProgRaw_svc : aesCbcSubProgRaw.svc = Syscall.standard :=
  aesCbcSubProg_svc

theorem aesCbcSubProgRaw_base : aesCbcSubProgRaw.base = f3RxSegBase :=
  aesCbcSubProg_base

theorem aesCbcSubProgRaw_codeLoaded_iff (m : Memory) :
    aesCbcSubProgRaw.CodeLoaded m ↔ f3TrialRxProg.CodeLoaded m :=
  aesCbcSubProg_codeLoaded_iff m

private theorem sub_toNat_beq_iff_eq (a b base : BitVec 64) :
    ((a - base).toNat == (b - base).toNat) = (a == b) := by
  cases h : a == b with
  | true => rw [beq_iff_eq.mp h, beq_self_eq_true]
  | false =>
    rw [beq_eq_false_iff_ne] at h ⊢
    intro hnat; apply h
    have hbv := BitVec.eq_of_toNat_eq hnat
    have hadd := congrArg (· + base) hbv
    simpa only [BitVec.sub_add_cancel] using hadd

theorem aesCbcSubProg_externAt_eq (pc : BitVec 64) :
    aesCbcSubProg.externAt? pc =
      if isLinkedPanicAddr pc then some Rust.panicked else none := by
  unfold Program.externAt? Program.hookAtOff? aesCbcSubProg isLinkedPanicAddr
  rw [f3TrialRxProg_symbols, f3TrialRxProg_base]
  dsimp only [List.findSome?]
  rw [Option.or_none]
  have haux : ∀ (xs : List (BitVec 64)),
      ((xs.map fun a => (c2LinkedPanicStubSym, (a - f3RxSegBase).toNat)).findSome? fun s =>
        if s.2 == (pc - f3RxSegBase).toNat then aesCbcPanicExterns s.1 else none) =
      if xs.contains pc then some Rust.panicked else none := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons, List.findSome?_cons, List.contains_cons, sub_toNat_beq_iff_eq]
      cases h : a == pc with
      | true =>
        rw [beq_iff_eq.mp h, beq_self_eq_true]
        rfl
      | false =>
        have hsym : (pc == a) = false := by
          rw [beq_eq_false_iff_ne] at h ⊢; exact Ne.symm h
        simp only [hsym, Bool.false_eq_true, Bool.false_or, ↓reduceIte]
        exact ih
  exact haux cliLinkedPanicAddrs

theorem aesCbcSubProg_externAt_handleError :
    aesCbcSubProg.externAt? wp4HandleErrorAddr = some Rust.panicked := by
  rw [aesCbcSubProg_externAt_eq]
  have h : isLinkedPanicAddr wp4HandleErrorAddr = true := by decide
  rw [h]; rfl

theorem aesCbcSubProgRaw_externAt_handleError :
    aesCbcSubProgRaw.externAt? wp4HandleErrorAddr = some Rust.panicked :=
  aesCbcSubProg_externAt_handleError

theorem aesCbcSubProg_externAt_aesEnc :
    aesCbcSubProg.externAt? c2AesEncAddr = none := by
  rw [aesCbcSubProg_externAt_eq, isLinkedPanicAddr_false_of_mid (by decide) (by decide)]
  rfl

theorem aesCbcSubProg_externAt_aesDec :
    aesCbcSubProg.externAt? c2AesDecAddr = none := by
  rw [aesCbcSubProg_externAt_eq, isLinkedPanicAddr_false_of_mid (by decide) (by decide)]
  rfl

theorem aesCbcSubProg_externAt_cases {pc : BitVec 64} {f : State → State}
    (he : aesCbcSubProg.externAt? pc = some f) :
    f = Rust.panicked ∧ isLinkedPanicAddr pc = true := by
  rw [aesCbcSubProg_externAt_eq] at he
  cases h : isLinkedPanicAddr pc with
  | true => rw [h] at he; injection he with hf; exact ⟨hf.symm, rfl⟩
  | false => rw [h] at he; cases he

theorem aesCbcSubProg_externAt_none_of_not_panic {pc : BitVec 64}
    (hnp : isLinkedPanicAddr pc = false) :
    aesCbcSubProg.externAt? pc = none := by
  rw [aesCbcSubProg_externAt_eq, hnp]; rfl

theorem keepRxSeg_eq_lt (pc : BitVec 64) :
    keepRxSeg pc = decide ((pc - f3RxSegBase).toNat < 4 * f3RxWordCount) := by
  unfold keepRxSeg
  rw [f3TrialRxProg_base, f3TrialRxProg_code_len]

theorem keepRxSeg_aesEnc : keepRxSeg c2AesEncAddr = true := by
  rw [keepRxSeg_eq_lt]; decide

theorem keepRxSeg_aesDec : keepRxSeg c2AesDecAddr = true := by
  rw [keepRxSeg_eq_lt]; decide

theorem keepRxSeg_eq_progKeep : keepRxSeg = progKeep f3TrialRxProg := rfl

theorem c2_aesCbcSubProg_subslice :
    checkProgCodeSubslice f3TrialRxProg aesCbcSubProg = true := by
  have hb : aesCbcSubProg.base = f3TrialRxProg.base := rfl
  have hc : aesCbcSubProg.code = f3TrialRxProg.code := rfl
  have halign : f3TrialRxProg.base.toNat % 4 = 0 := by rw [f3TrialRxProg_base]; decide
  have hbound : f3TrialRxProg.base.toNat + f3TrialRxProg.code.length ≤ 2 ^ 64 := by
    rw [f3TrialRxProg_base, f3TrialRxProg_code_len]; decide
  unfold checkProgCodeSubslice
  dsimp only
  rw [hb, hc, BitVec.sub_self, BitVec.toNat_zero]
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq, beq_iff_eq,
    Nat.zero_add, List.drop_zero, List.take_length]
  exact ⟨⟨⟨⟨halign, hbound⟩, BitVec.add_zero _⟩, Nat.le_refl _⟩, trivial⟩

/-! ## 2. `mallocng` Containment & `keepRxSeg` Disjointness -/

theorem c2_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

private theorem c2_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem c2_mng_fnAddr_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (name : String) :
    mallocngLib.fnAddr mmpl name = mallocngLib.fnAddr f3MallocngMpl name := by
  unfold MultiPlacedLib.fnAddr
  cases hlk : lookupBlockSym name mallocngLib.blocks with
  | none =>
    exact (f3CliElf_mallocng_linkedAt_unique hMm).1 0 (Nat.zero_lt_succ 23)
  | some p =>
    rcases p with ⟨i, _⟩
    dsimp only
    rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 i (lookupBlockSym_lt hlk)]

private theorem c2_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [c2_mng_fnAddr_eq mmpl hMm]

theorem c2_mng_libc_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    (mallocngAddrsOfPlacement mmpl).libc = f3StdLayout.libcAddr :=
  f3CliElf_mallocng_libc_eq_of_linkedAt hMm

theorem c2_progContainsMallocng_f3TrialRxProg (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := c2_mng_placeable mmpl hMm
  have hIn1 := c2_mng_inElf mmpl hMm
  have hPl2 := mallocngLib_in_f3TrialElf.1
  have hIn2 := mallocngLib_in_f3TrialElf.2.1
  have hF3 := f3Trial_progContainsMallocng
  refine VerifiedLibraries.Mallocng.Proofs.ProgContainsMultiLib.of_noExterns hPl1 f3TrialRxProg_svc
    (fun m hPm i hi => ?_) f3TrialRxProg_no_ext
  have hcl_f3 := hF3.codeLoaded m hPm i hi
  have hbase_i : mmpl.base i = f3MallocngMpl.base i :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 i hi
  have hbase_prog : (mallocngLib.blockProgram mmpl i).base =
      (mallocngLib.blockProgram f3MallocngMpl i).base := hbase_i
  have hcode_mmpl : (mallocngLib.blockProgram mmpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hcode_f3 : (mallocngLib.blockProgram f3MallocngMpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement f3MallocngMpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hlen1 : (mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hlen2 : (mallocngLib.blocks[i].patched
      (mallocngLib.blockPlacement f3MallocngMpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl2.blocks_ok i hi).len_aligned
  have hcode_prog : (mallocngLib.blockProgram mmpl i).code =
      (mallocngLib.blockProgram f3MallocngMpl i).code := by
    rw [hcode_mmpl, hcode_f3]
    refine List.ext_getElem (hlen1.trans hlen2.symm) (fun k hk1 hk2 => ?_)
    obtain ⟨_, hc1, _⟩ := hIn1.blocks i hi k hk1
    obtain ⟨_, hc2, _⟩ := hIn2.blocks i hi k hk2
    rw [hbase_i] at hc1
    exact (Prod.mk.inj (Option.some.inj (hc1.symm.trans hc2))).2
  rw [Program.codeLoaded_iff] at hcl_f3 ⊢
  rwa [hbase_prog, hcode_prog]

theorem c2_keepRxSeg_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → keepRxSeg a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((c2_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable mmpl hMm) (c2_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have hhi_rx : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3RxWordCount := by decide
    have hrx_nat : f3RxSegBase.toNat < 2 ^ 64 := BitVec.isLt f3RxSegBase
    have hsub_nat : (a - f3RxSegBase).toNat = a.toNat - f3RxSegBase.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    rw [keepRxSeg_eq_lt]
    exact decide_eq_true (by omega)

theorem c2_mallocng_lt_writeLo (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true →
      decide ((a - f3RxSegBase).toNat < 0x5798) = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((c2_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable mmpl hMm) (c2_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have hhi_lo : f3MngCodeHi ≤ f3RxSegBase.toNat + 0x5798 := by decide
    have hrx_nat : f3RxSegBase.toNat < 2 ^ 64 := BitVec.isLt f3RxSegBase
    have hsub_nat : (a - f3RxSegBase).toNat = a.toNat - f3RxSegBase.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    exact decide_eq_true (by omega)

theorem c2_aesEncGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsAesEncSym
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  aesEncGhost_rowSpecOk keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim

theorem c2_aesDecGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsAesDecSym
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  aesDecGhost_rowSpecOk keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim

theorem c2_aesCbc_hKeep [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr) :
    keepRxSeg lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hRet
  have hstub_le : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  have hrx_hi : f3RxSegBase.toNat + 4 * f3RxWordCount < 2 ^ 64 := by decide
  rw [keepRxSeg_eq_lt, decide_eq_false_iff_not]
  intro hlt_rx
  have hl_lt : lr.toNat < f3RxSegBase.toNat := Nat.lt_of_lt_of_le hlt hstub_le
  have hwrap : (lr - f3RxSegBase).toNat = 2 ^ 64 + lr.toNat - f3RxSegBase.toNat := by
    rw [BitVec.toNat_sub]
    omega
  omega

theorem c2_aesCbc_hlr_ne_stub [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hRet : LsRetAddr624 lr)
    (pc : BitVec 64) (f : State → State)
    (he : aesCbcSubProg.externAt? pc = some f) :
    pc ≠ lr := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hRet
  obtain ⟨_, hp⟩ := aesCbcSubProg_externAt_cases he
  have hge : c2FirstExternStubAddr.toNat ≤ pc.toNat := by
    unfold isLinkedPanicAddr cliLinkedPanicAddrs at hp
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro heq; rw [← heq] at hlt; omega

/-! ## 3. `WordTree` Code Certificates on `aesCbcSubProgRaw` (`seg[2]`) -/

abbrev c2Memshift32Addr : BitVec 64 := c2AesDecAddr - 13420#64
abbrev c2XorColumnsAddr : BitVec 64 := c2AesDecAddr - 13104#64
abbrev c2InvBitsliceAddr : BitVec 64 := c2AesDecAddr - 12304#64
abbrev c2InvSubBytesAddr : BitVec 64 := c2AesDecAddr - 11612#64
abbrev c2MixColumns1Addr : BitVec 64 := c2AesDecAddr - 11032#64
abbrev c2MixColumns3Addr : BitVec 64 := c2AesDecAddr - 10552#64
abbrev c2Aes256DecryptAddr : BitVec 64 := c2AesDecAddr - 10072#64
abbrev c2Aes256EncryptAddr : BitVec 64 := c2AesDecAddr - 8992#64
abbrev c2InvMixColumns1Addr : BitVec 64 := c2AesDecAddr - 7760#64
abbrev c2InvMixColumns2Addr : BitVec 64 := c2AesDecAddr - 7204#64
abbrev c2InvMixColumns3Addr : BitVec 64 := c2AesDecAddr - 6808#64
abbrev c2Aes256KeyScheduleAddr : BitVec 64 := c2AesDecAddr - 6252#64
abbrev c2BitsliceAddr : BitVec 64 := c2AesDecAddr - 4212#64
abbrev c2SubBytesAddr : BitVec 64 := c2AesDecAddr - 3520#64

abbrev c2AesStorageAddr : BitVec 64 := f3StdLayout.brkStart - 8160#64
abbrev c2AesInitInnerAddr : BitVec 64 := c2AesDecAddr - 2992#64
abbrev c2AesDropDecryptorAddr : BitVec 64 := c2AesDecAddr - 2956#64
abbrev c2AesHwDecryptPar17Addr : BitVec 64 := c2AesDecAddr - 2736#64
abbrev c2AesHwDecryptAddr : BitVec 64 := c2AesDecAddr - 724#64
abbrev c2AesHwEncryptAddr : BitVec 64 := c2AesDecAddr - 568#64
abbrev c2AesExpandKeyAddr : BitVec 64 := c2AesDecAddr - 412#64
abbrev c2AesInvExpandedKeysAddr : BitVec 64 := c2AesDecAddr - 120#64
abbrev c2AesGetauxvalHwcapAddr : BitVec 64 := c2TimeAddAddr - 612#64

abbrev c2AesEncHwAddrs : Aes256EncHwAddrs where
  storageAddr := c2AesStorageAddr
  initInnerAddr := c2AesInitInnerAddr
  getauxvalHwcapAddr := c2AesGetauxvalHwcapAddr
  getauxvalAddr := f3StdLayout.getauxvalAddr
  errnoLocationAddr := f3StdLayout.errnoLocationAddr
  expandKeyAddr := c2AesExpandKeyAddr
  invExpandedKeysAddr := c2AesInvExpandedKeysAddr
  rconAddr := c2AesRconAddr
  hwEncryptAddr := c2AesHwEncryptAddr
  dropDecryptorAddr := c2AesDropDecryptorAddr

abbrev c2AesDecHwAddrs : Aes256DecHwAddrs where
  storageAddr := c2AesStorageAddr
  initInnerAddr := c2AesInitInnerAddr
  getauxvalHwcapAddr := c2AesGetauxvalHwcapAddr
  getauxvalAddr := f3StdLayout.getauxvalAddr
  errnoLocationAddr := f3StdLayout.errnoLocationAddr
  expandKeyAddr := c2AesExpandKeyAddr
  invExpandAddr := c2AesInvExpandedKeysAddr
  rconAddr := c2AesRconAddr
  relaxRcon := false
  hwDecryptAddr := c2AesHwDecryptAddr
  hwDecryptPar17Addr := c2AesHwDecryptPar17Addr
  dropDecryptorAddr := c2AesDropDecryptorAddr

abbrev c2DecPanic0Sym : BitVec 64 := cliAesDecErrStr2Addr - 264#64
abbrev c2DecPanic0Target : BitVec 64 := c2Lib2TextLo + 5212#64

@[expose] def c2AesEncPanicSyms : Aes256CbcEncryptPanicSyms where
  msgPtr := cliAesDecErrStr2Addr - 128#64
  errPtr := cliAesDecErrStr2Addr - 32#64
  locPtr := cliAesDecErrStr2Addr - 88#64
  unwrapFailedAddr := c2Lib2TextLo + 2752#64

@[expose] def c2AesDecPanicSyms : Aes256CbcDecryptPanicSyms where
  panicMsgAddr := cliAesDecErrStr2Addr + 68#64
  panicLocAddr := cliAesDecErrStr2Addr + 128#64
  panicAddr := c2Lib2TextLo + 3076#64
  sliceLocAddr := cliAesDecErrStr2Addr - 64#64
  sliceIndexFailAddr := c2Lib2TextLo + 4652#64
  addOverflowLocAddr := cliAesDecErrStr2Addr - 152#64
  panicAddOverflowAddr := c2Lib2TextLo + 5128#64
  subOverflowLocAddr := cliAesDecErrStr2Addr - 240#64
  panicSubOverflowAddr := c2Lib2TextLo + 5212#64

theorem aesCbcSubProg_code : aesCbcSubProg.code = f3TrialRxWordTree.toBytes :=
  f3TrialRxWordTree_eq

theorem aesCbcSubProgRaw_code : aesCbcSubProgRaw.code = f3TrialRxWordTree.toBytes :=
  f3TrialRxWordTree_eq

theorem aesCbcSubProgRaw_hookAtOff_none {off : Nat}
    (hband : off < 0x479798 - 0x474000 ∨
      (0x47ac2c - 0x474000 ≤ off ∧ off < 0x4cb070 - 0x474000) ∨
      (0x4cb0e4 - 0x474000 ≤ off ∧ off < 4 * f3RxWordCount)) :
    aesCbcSubProgRaw.hookAtOff? off = none := by
  have hwc : f3RxWordCount = 90112 := rfl
  have hoff64 : off < 2 ^ 64 := by omega
  let pc : BitVec 64 := f3RxSegBase + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = 0x474000 + off := by
    dsimp only [pc]
    have hrx : f3RxSegBase.toNat = 0x474000 := rfl
    rw [BitVec.toNat_add, hrx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64,
      Nat.mod_eq_of_lt (by omega)]
  have hsub : (pc - f3RxSegBase).toNat = off := by
    have hbv : pc - f3RxSegBase = BitVec.ofNat 64 off := by dsimp only [pc]; bv_omega
    rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
  have hext_eq : aesCbcSubProg.externAt? pc = aesCbcSubProgRaw.hookAtOff? off := by
    unfold Program.externAt?
    rw [aesCbcSubProg_base, hsub]
  rw [← hext_eq]
  rcases hband with hlt | ⟨hlo, hhi⟩ | ⟨hge, _⟩
  · exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt (by omega))
  · exact aesCbcSubProg_externAt_none_of_not_panic
      (isLinkedPanicAddr_false_of_mid (by omega) (by omega))
  · exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_ge (by omega))

theorem aesCbcSubProg_hookAtOff_none {off : Nat}
    (hband : off < 0x479798 - 0x474000 ∨
      (0x47ac2c - 0x474000 ≤ off ∧ off < 0x4cb070 - 0x474000) ∨
      (0x4cb0e4 - 0x474000 ≤ off ∧ off < 4 * f3RxWordCount)) :
    aesCbcSubProg.hookAtOff? off = none :=
  aesCbcSubProgRaw_hookAtOff_none hband

theorem hasInstrs_aesCbcSubProgRaw_of_check {addr : BitVec 64} {instrs : List Instr}
    (hchk : checkShimInstrsAt f3RxSegBase f3TrialRxWordTree addr instrs = true)
    (hfit : (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 0x479798 - 0x474000 ∨
      (0x47ac2c - 0x474000 ≤ (addr - f3RxSegBase).toNat ∧
        (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 0x4cb070 - 0x474000) ∨
      (0x4cb0e4 - 0x474000 ≤ (addr - f3RxSegBase).toNat ∧
        (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 4 * f3RxWordCount)) :
    hasInstrs aesCbcSubProgRaw addr instrs := by
  have hchk' : checkShimInstrsAt aesCbcSubProgRaw.base f3TrialRxWordTree addr instrs = true := by
    rwa [aesCbcSubProgRaw_base]
  refine hasShimInstrs_of_wordTree f3RxWordCount aesCbcSubProgRaw_code f3TrialRxWordTree_size
    (fun i hi => ?_) hchk'
  rw [aesCbcSubProgRaw_base]
  exact aesCbcSubProgRaw_hookAtOff_none (by omega)

theorem hasInstrs_aesCbcSubProg_of_check {addr : BitVec 64} {instrs : List Instr}
    (hchk : checkShimInstrsAt f3RxSegBase f3TrialRxWordTree addr instrs = true)
    (hfit : (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 0x479798 - 0x474000 ∨
      (0x47ac2c - 0x474000 ≤ (addr - f3RxSegBase).toNat ∧
        (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 0x4cb070 - 0x474000) ∨
      (0x4cb0e4 - 0x474000 ≤ (addr - f3RxSegBase).toNat ∧
        (addr - f3RxSegBase).toNat + 4 * instrs.length ≤ 4 * f3RxWordCount) := by
      exact of_decide_eq_true (by rfl_kernel)) :
    hasInstrs aesCbcSubProg addr instrs :=
  hasInstrs_aesCbcSubProgRaw_of_check hchk hfit

set_option maxRecDepth 4000000 in
theorem c2_memshift32_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2Memshift32Addr
      LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers.memshift32ReachableInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_xorColumns_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2XorColumnsAddr
      LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers.xorColumnsReachableInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invBitslice_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2InvBitsliceAddr invBitsliceInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invSubBytes_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2InvSubBytesAddr invSubBytesInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_mixColumns1_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2MixColumns1Addr mixColumns1Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_mixColumns3_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2MixColumns3Addr mixColumns3Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invMixColumns1_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2InvMixColumns1Addr invMixColumns1Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invMixColumns2_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2InvMixColumns2Addr invMixColumns2Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invMixColumns3_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2InvMixColumns3Addr invMixColumns3Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_bitslice_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2BitsliceAddr bitsliceInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_subBytes_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2SubBytesAddr subBytesInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_keySchedule_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2Aes256KeyScheduleAddr
      (aes256KeyScheduleInstrs c2Aes256KeyScheduleAddr f3StdLayout.memsetAddr c2BitsliceAddr
        c2Memshift32Addr c2SubBytesAddr c2XorColumnsAddr f3StdLayout.memcpyAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_aes256Encrypt_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2Aes256EncryptAddr
      (aes256EncryptInstrs c2Aes256EncryptAddr c2BitsliceAddr c2SubBytesAddr
        c2MixColumns1Addr c2MixColumns3Addr c2InvBitsliceAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_aes256Decrypt_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2Aes256DecryptAddr
      (aes256DecryptPrefixInstrs c2Aes256DecryptAddr c2BitsliceAddr c2InvSubBytesAddr
        c2InvMixColumns1Addr c2InvMixColumns2Addr c2InvMixColumns3Addr c2InvBitsliceAddr
        c2DecPanic0Sym false c2DecPanic0Target) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_noShimV2_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree f3NoShimV2Addr [.ret (.gpr 30#5)] = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_initInner_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesInitInnerAddr
      (aesInitInnerInstrs c2AesInitInnerAddr c2AesGetauxvalHwcapAddr c2AesStorageAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_getauxvalHwcap_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesGetauxvalHwcapAddr
      (getauxvalHwcapInstrs c2AesGetauxvalHwcapAddr f3StdLayout.getauxvalAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_getauxval_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree f3StdLayout.getauxvalAddr
      (getauxvalInstrsAt f3StdLayout.getauxvalAddr f3StdLayout.libcAddr
        f3StdLayout.errnoLocationAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_errnoLocation_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree f3StdLayout.errnoLocationAddr
      errnoLocationInstrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_expandKey15_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesExpandKeyAddr
      (expandKey15ReachableInstrs c2AesExpandKeyAddr c2AesRconAddr false) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_invExpandedKeys15_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesInvExpandedKeysAddr
      invExpandedKeys15Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_hwEncrypt15_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesHwEncryptAddr
      encrypt15Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_hwDecrypt15_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesHwDecryptAddr
      decrypt15Instrs = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_hwDecryptPar17_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesHwDecryptPar17Addr
      (decodeWords decryptPar17Words) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_dropDecryptor_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesDropDecryptorAddr
      (dropDecryptorInstrs c2AesDropDecryptorAddr c2AesStorageAddr) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_aes256CbcEncrypt_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesEncAddr
      (aes256CbcEncryptInstrs c2AesEncAddr c2AesEncHwAddrs c2Aes256KeyScheduleAddr
        c2Aes256EncryptAddr f3NoShimV2Addr f3StubAzAddr f3StdLayout.memcpyAddr
        f3StdLayout.memsetAddr wp4HandleErrorAddr c2AesEncPanicSyms) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2_aes256CbcDecrypt_chk :
    checkShimInstrsAt f3RxSegBase f3TrialRxWordTree c2AesDecAddr
      (aes256CbcDecryptInstrs c2AesDecAddr c2AesDecHwAddrs c2Aes256KeyScheduleAddr
        c2Aes256DecryptAddr f3NoShimV2Addr f3StubAzAddr f3StubAddrs.dealloc
        f3StdLayout.memcpyAddr wp4HandleErrorAddr cliAesDecErrStr1Addr cliAesDecErrStr2Addr
        c2AesDecPanicSyms false false) = true := by
  rfl_kernel

/-! ## 4. Direct `aesCbcSubProgRaw` Subroutines (`memcpy`, `memset`, `handle_error`, `withExecFrozenBudget` Allocators) -/

theorem aesCbcSubProg_codeLoaded_f3PrePanic {m : Memory}
    (hCL : aesCbcSubProg.CodeLoaded m) :
    f3PrePanicRxProg.CodeLoaded m :=
  f3PrePanicRxProg_codeLoaded_of_f3Trial ((aesCbcSubProg_codeLoaded_iff m).mp hCL)

theorem aesCbcSubProg_externAt_none_of_keepPrePanic {pc : BitVec 64}
    (hk : keepPrePanic pc = true) :
    aesCbcSubProg.externAt? pc = none := by
  unfold keepPrePanic at hk
  rw [decide_eq_true_eq] at hk
  have hlo : f3RxSegBase.toNat = 0x474000 := rfl
  have hlen : 4 * PrePanicMngLift.f3PrePanicWordCount = 0x5798 := rfl
  have hlt : pc.toNat < 0x479798 := by
    by_contra hge
    have hsub : (pc - f3RxSegBase).toNat = pc.toNat - f3RxSegBase.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    omega
  exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt hlt)

theorem aesCbcSubProgRaw_blockExternFree {addr : BitVec 64} {len : Nat}
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + len ≤ 0x479798) :
    BlockExternFree aesCbcSubProgRaw addr len := by
  intro a ha
  have ha_off : (a - addr).toNat < len := ha
  have heq_a : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have ht : (addr + BitVec.ofNat 64 (a - addr).toNat).toNat = addr.toNat + (a - addr).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [heq_a] at ht
  exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt (by omega))

private theorem f3Trial_memcpy_hasWords :
    f3TrialRxProg.hasWords f3StdLayout.memcpyAddr memcpySymWords := by
  have hoff_lt : (f3StdLayout.memcpyAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memcpySymWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memcpyAddr - f3RxSegBase).toNat memcpySymWords = true)

private theorem allocMemcpyVm_len_le_2pow63_local {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

theorem c2_memcpy_aesCbcSubProgRaw_ok :
    subroutine_ok aesCbcSubProgRaw f3StdLayout.memcpyAddr allocMemcpyVmSpec := by
  have hcl_pure : ∀ m : Memory, aesCbcSubProgRaw.CodeLoaded m →
      (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords
      ((aesCbcSubProgRaw_codeLoaded_iff m).mp hm) f3Trial_memcpy_hasWords (by decide)
  have hlen_w : 4 * memcpySymWords.length = 396 := by rfl_kernel
  have hext : BlockExternFree aesCbcSubProgRaw f3StdLayout.memcpyAddr (4 * memcpySymWords.length) :=
    aesCbcSubProgRaw_blockExternFree (by decide) (by rw [hlen_w]; decide)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpyVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := allocMemcpyVm_len_le_2pow63_local (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt))) hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_blockExternFree
    (P := aesCbcSubProgRaw)
    (memcpy_pureWords_ok f3StdLayout.memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    aesCbcSubProgRaw_svc
    (memcpy_allInstrs_noSvc_noMsr f3StdLayout.memcpyAddr)
    hcl_pure hext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
      rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

private theorem f3Trial_memset_hasWords :
    f3TrialRxProg.hasWords f3StdLayout.memsetAddr memsetWords := by
  have hoff_lt : (f3StdLayout.memsetAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memsetWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memsetWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memsetAddr - f3RxSegBase).toNat memsetWords = true)

private theorem pureWordsProg_hasWords_memset_local (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).hasWords entry memsetWords :=
  pureWordsProg_hasWords
    (Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble (4 * memsetWords.length) (2 ^ 64) = true))
    (by rfl_kernel : ((List.range memsetWords.length).all fun i =>
      (pureWordsProg 0#64 memsetWords).readWordOff (4 * i) == memsetWords[i]?) = true)

private theorem pureWordsProg_noSvcMsr_memset_local (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  (by rfl_kernel :
    (pureWordsProg 0#64 memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)

theorem c2_memset_aesCbcSubProgRaw_ok :
    subroutine_ok aesCbcSubProgRaw f3StdLayout.memsetAddr allocMemsetVmSpec := by
  let memsetAddr := f3StdLayout.memsetAddr
  let prog₀ := pureWordsProg memsetAddr memsetWords
  have hpure : subroutine_ok prog₀ memsetAddr
      { ProofLib.memsetRegionSpec with
        post := fun x s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab⌝ ∗
            ProofLib.memsetRegionSpec.post x s0 sf } := by
    apply subroutine_ok_of_steps_outcome
    intro x R s0 hpc hrun hpre hsp hL
    obtain ⟨sf, hsteps, hout⟩ :=
      subroutine_ok_elim_steps_outcome
        (memset_memsetRegionSpec_ok (pureWordsProg_hasWords_memset_local memsetAddr))
        x R s0 hpc hrun hpre hsp hL
    have horc : sf.oracle = s0.oracle :=
      Steps.oracle_eq_of_standard rfl
        (fun pc => by
          simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?])
        hsteps
    have hsym : sf.symtab = s0.symtab := hsteps.symtab_eq
    refine ⟨sf, hsteps, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨horc, hsym⟩, hpost⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  have hcl_pure : ∀ m : Memory, aesCbcSubProgRaw.CodeLoaded m → prog₀.CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords
      ((aesCbcSubProgRaw_codeLoaded_iff m).mp hm) f3Trial_memset_hasWords (by decide)
  have hlen_w : 4 * memsetWords.length = 260 := by rfl_kernel
  have hext : BlockExternFree aesCbcSubProgRaw memsetAddr (4 * memsetWords.length) :=
    aesCbcSubProgRaw_blockExternFree (by decide) (by dsimp [memsetAddr]; rw [hlen_w]; decide)
  have hlift := subroutine_ok_lift_pureWords_blockExternFree
    (P := aesCbcSubProgRaw)
    hpure aesCbcSubProgRaw_svc (pureWordsProg_noSvcMsr_memset_local memsetAddr)
    hcl_pure hext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ptr, c, n⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemsetVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hn_nat : (s0.readReg64 .x2).toNat = n := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine hlift.mono_outcome (ptr, c, n) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [ProofLib.memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hn_nat, Nat.le_of_lt hlt⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [ProofLib.memsetRegionSpec, allocMemsetVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym⟩ =>
        Entails.pure_left fun hx0f => ?_
      obtain ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩ := hpf
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem c2_shim_aesCbcSubProgRaw_ok :
    subroutine_ok aesCbcSubProgRaw f3NoShimV2Addr
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec :=
  rustAllocShimVm_ret_ok (hasInstrs_aesCbcSubProgRaw_of_check c2_noShimV2_chk (by decide))

theorem c2_handleError_aesCbcSubProgRaw_ok :
    subroutine_ok aesCbcSubProgRaw wp4HandleErrorAddr rustHandleErrorPanicSpec :=
  rustHandleErrorPanic_of_extern aesCbcSubProgRaw_externAt_handleError

private theorem c2_allocZeroed_noAes_withExecFrozen_aesCbc_ok (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits) :
    subroutine_ok aesCbcSubProg f3StubAzAddr
      (LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt.rustAllocZeroedBudgetSpecBase
        fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  c2_allocZeroed_noAes_withExecFrozen_ok hMm γ tp brkStart hlim
    aesCbcSubProg_svc (fun _ => aesCbcSubProg_codeLoaded_f3PrePanic)
    (fun _ => aesCbcSubProg_externAt_none_of_keepPrePanic)

private theorem c2_dealloc_noAes_withExecFrozen_aesCbc_ok (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits) :
    subroutine_ok aesCbcSubProg f3StubAddrs.dealloc
      (LibsignalBinary.Heap.rustCliDeallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  c2_dealloc_noAes_withExecFrozen_ok hMm γ tp brkStart hlim
    aesCbcSubProg_svc (fun _ => aesCbcSubProg_codeLoaded_f3PrePanic)
    (fun _ => aesCbcSubProg_externAt_none_of_keepPrePanic)

/-! ## 5. Top-Level `c2_aesEnc_subroutineOk` and `c2_aesDec_subroutineOk` -/

private theorem c2_aesInitInnerCode_aesCbcSubProg (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    AesInitInnerCode aesCbcSubProg c2AesInitInnerAddr c2AesGetauxvalHwcapAddr
      f3StdLayout.getauxvalAddr f3StdLayout.errnoLocationAddr
      (mallocngAddrsOfPlacement mmpl).libc c2AesStorageAddr where
  initInner_code := hasInstrs_aesCbcSubProg_of_check c2_initInner_chk
  getauxvalHwcap_code := hasInstrs_aesCbcSubProg_of_check c2_getauxvalHwcap_chk
  getauxval_code := by
    rw [c2_mng_libc_eq mmpl hMm]
    exact hasInstrs_aesCbcSubProg_of_check c2_getauxval_chk
  errnoLocation_code := hasInstrs_aesCbcSubProg_of_check c2_errnoLocation_chk

private theorem c2_ksCallees_aesCbcSubProg :
    Aes256KeyScheduleCallees aesCbcSubProg f3StdLayout.memsetAddr c2BitsliceAddr
      c2Memshift32Addr c2SubBytesAddr c2XorColumnsAddr f3StdLayout.memcpyAddr where
  memset_ok := c2_memset_aesCbcSubProgRaw_ok
  bitslice_ok := bitslice_rep_ok (hasInstrs_aesCbcSubProg_of_check c2_bitslice_chk)
  memshift32_ok := memshift32_ok aesCbcSubProgRaw c2Memshift32Addr
    (hasInstrs_aesCbcSubProg_of_check c2_memshift32_chk)
  subBytes_ok := subBytes_ok (hasInstrs_aesCbcSubProg_of_check c2_subBytes_chk)
  xorColumns_ok := xorColumns_ok aesCbcSubProgRaw c2XorColumnsAddr
    (hasInstrs_aesCbcSubProg_of_check c2_xorColumns_chk)
  memcpy_ok := c2_memcpy_aesCbcSubProgRaw_ok

theorem c2_decBlockCallees_aesCbcSubProgRaw :
    Aes256DecryptCallees aesCbcSubProgRaw c2BitsliceAddr c2InvSubBytesAddr
      c2InvMixColumns1Addr c2InvMixColumns2Addr c2InvMixColumns3Addr c2InvBitsliceAddr where
  bitslice_ok := bitslice4_ok (hasInstrs_aesCbcSubProg_of_check c2_bitslice_chk)
  invSubBytes_ok := invSubBytes_ok (hasInstrs_aesCbcSubProg_of_check c2_invSubBytes_chk)
  invMixColumns1_ok := invMixColumns1_ok (hasInstrs_aesCbcSubProg_of_check c2_invMixColumns1_chk)
  invMixColumns2_ok := invMixColumns2_ok (hasInstrs_aesCbcSubProg_of_check c2_invMixColumns2_chk)
  invMixColumns3_ok := invMixColumns3_ok (hasInstrs_aesCbcSubProg_of_check c2_invMixColumns3_chk)
  invBitslice_ok := invBitslice_ok (hasInstrs_aesCbcSubProg_of_check c2_invBitslice_chk)

theorem c2_aesDecCallees_aesCbcSubProg
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits) :
    Aes256CbcDecryptCallees fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart))
      lim aesCbcSubProg c2AesDecHwAddrs c2Aes256KeyScheduleAddr c2Aes256DecryptAddr
      f3NoShimV2Addr f3StubAzAddr f3StubAddrs.dealloc f3StdLayout.memcpyAddr wp4HandleErrorAddr :=
  Aes256CbcDecryptCallees.of_hasInstrs
    (c2_aesInitInnerCode_aesCbcSubProg mmpl hMm)
    (hasInstrs_aesCbcSubProg_of_check c2_expandKey15_chk)
    (hasInstrs_aesCbcSubProg_of_check c2_invExpandedKeys15_chk)
    (hasInstrs_aesCbcSubProg_of_check c2_hwDecryptPar17_chk)
    (hasInstrs_aesCbcSubProg_of_check c2_hwDecrypt15_chk)
    (hasInstrs_aesCbcSubProg_of_check c2_dropDecryptor_chk)
    (hasInstrs_aesCbcSubProg_of_check c2_keySchedule_chk)
    c2_ksCallees_aesCbcSubProg
    (hasInstrs_aesCbcSubProg_of_check c2_aes256Decrypt_chk)
    c2_decBlockCallees_aesCbcSubProgRaw
    c2_shim_aesCbcSubProgRaw_ok
    (c2_allocZeroed_noAes_withExecFrozen_aesCbc_ok mmpl hMm γ tp f3StdLayout.brkStart hlim)
    (c2_dealloc_noAes_withExecFrozen_aesCbc_ok mmpl hMm γ tp f3StdLayout.brkStart hlim)
    c2_memcpy_aesCbcSubProgRaw_ok
    c2_handleError_aesCbcSubProgRaw_ok

theorem c2_aesEnc_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok aesCbcSubProg c2AesEncAddr
      (withAesStubRconRO aesCbcSubProg
        (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hCal : Aes256CbcEncryptCallees fineCostModel A' lim' aesCbcSubProg c2AesEncHwAddrs
      c2Aes256KeyScheduleAddr c2Aes256EncryptAddr f3NoShimV2Addr f3StubAzAddr
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr wp4HandleErrorAddr :=
    Aes256CbcEncryptCallees.of_hasInstrs lim'
      (c2_aesInitInnerCode_aesCbcSubProg mmpl hMm)
      (hasInstrs_aesCbcSubProg_of_check c2_expandKey15_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_invExpandedKeys15_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_hwEncrypt15_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_dropDecryptor_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_keySchedule_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_aes256Encrypt_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_bitslice_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_memshift32_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_subBytes_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_xorColumns_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_mixColumns1_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_mixColumns3_chk)
      (hasInstrs_aesCbcSubProg_of_check c2_invBitslice_chk)
      (c2_allocZeroed_noAes_withExecFrozen_aesCbc_ok mmpl hMm γ tp f3StdLayout.brkStart hlim')
      ⟨c2_shim_aesCbcSubProgRaw_ok, c2_memcpy_aesCbcSubProgRaw_ok, c2_handleError_aesCbcSubProgRaw_ok⟩
      c2_memset_aesCbcSubProgRaw_ok
  have hRaw := aes256CbcEncrypt_keepsFs_of_wordTree_ok (fnAddr := c2AesEncAddr)
    A' lim' f3RxWordCount aesCbcSubProgRaw_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesCbcSubProg_base]
      have hlo : 0x47ac2c - 0x474000 ≤ (c2AesEncAddr - f3RxSegBase).toNat := by decide
      have hfit : (c2AesEncAddr - f3RxSegBase).toNat + 4 * 595 ≤ 0x4cb070 - 0x474000 := by decide
      exact aesCbcSubProg_hookAtOff_none (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    c2_aes256CbcEncrypt_chk
    hCal
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, aesEncSpecOf,
    withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hfr⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs
          (aesEncBudgetSpec CryptoGames.AES256.aes256Enc fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesEncBudgetSpec, LibsignalBinary.Heap.SpecBudget.aesCallPreBudget, A', A0,
      withExecFrozenBudget, lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesEncBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, aesEncSpecOf,
      withLsRet, aesEncBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono_left
              (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf)))))
      hpost
  · dsimp only [withRoData, LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesEncBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem c2_aesDec_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok aesCbcSubProg c2AesDecAddr
      (withAesStubRconRO aesCbcSubProg
        (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hCal := c2_aesDecCallees_aesCbcSubProg mmpl hMm γ tp hlim'
  have hRaw := aes256CbcDecrypt_keepsFs_of_wordTree_ok (fnAddr := c2AesDecAddr)
    A' lim' f3RxWordCount aesCbcSubProgRaw_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesCbcSubProg_base]
      have hlo : 0x47ac2c - 0x474000 ≤ (c2AesDecAddr - f3RxSegBase).toNat := by decide
      have hfit : (c2AesDecAddr - f3RxSegBase).toNat + 4 * 900 ≤ 0x4cb070 - 0x474000 := by decide
      exact aesCbcSubProg_hookAtOff_none (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    c2_aes256CbcDecrypt_chk
    hCal cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, aesDecSpecOf,
    withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hfr⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs
          (aesDecBudgetSpec CryptoGames.AES256.aes256Dec fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesDecBudgetSpec, LibsignalBinary.Heap.SpecBudget.aesCallPreBudget, A', A0,
      withExecFrozenBudget, lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesDecBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, aesDecSpecOf,
      withLsRet, aesDecBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono_left
              (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf)))))
      hpost
  · dsimp only [withRoData, LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs,
      aesDecBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
