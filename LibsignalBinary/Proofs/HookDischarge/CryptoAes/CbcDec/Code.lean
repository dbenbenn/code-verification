/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
public import ProofLib.StdStartup.StdDetect
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords

/-!
# Instruction Sequence & Callee Contracts for `aes_256_cbc_decrypt` (`900` Instructions)

Placement-generic `900`-instruction sequence (`aes256CbcDecryptInstrs`), `266`-instruction hardware
loop slice (`cbcDecHwLoopInstrs` + `hasInstrs_hwLoop_of_full`), `HwLoopContract` join interface, and
`Aes256CbcDecryptCallees` over `[PoolAesInitSplit A hw.storageAddr]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (adrpOff decodeWords hasInstrs pageLo12)
open CryptoGames.CBC (bytesToBlock blockToBytesLE chunks16 cbcDecryptBlocks)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpecBase
   rustCliDeallocBudgetSpecBase)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved adrpAddPair adrpAddPair_length hasInstrs_prefix)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
  (aes256KeyScheduleInstrs Aes256KeyScheduleCallees aes256KeyScheduleSpec aes256KeySchedule_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (aes256DecryptPrefixInstrs Aes256DecryptCallees aes256DecryptSpec aes256Decrypt_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (armv8ExpandKey armv8InvExpandedKeys roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode (AesInitInnerCode)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit aesInitInnerSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule
  (expandKey15ReachableInstrs expandKey15RegionSpec expandKey15_region_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (invExpandedKeys15Instrs invExpandedKeys15RegionSpec invExpandedKeys15_region_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec
  (decrypt15Instrs decrypt15InplaceSpec decrypt15_inplace_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
  (decryptPar17InplaceBytesSpec decryptPar17_inplace_bytes_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds (decryptPar17Words)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor
  (dropDecryptorInstrs dropDecryptorSpec dropDecryptor_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcPrologueWords cbcPostStorageAdrpWords cbcStorageCheckWords cbcPostSoftKsWords
   cbcFastRejectWords cbcPostInitWords cbcPreInvExpandWords cbcHwCopyEkWords
   cbcSroaCopy960Words cbcSroaCopy952Words cbcSroaStage968Words cbcPreAllocWords
   cbcPostAllocWords cbcLoopDispatchWords
   hwSetupWords hwPar17InitWords hwPar17PreMc1Words hwPar17PreMc2Words hwPar17PreDecWords
   hwPar17Xor0AWords hwPar17Xor0BWords hwPar17XorLoopAWords hwPar17XorLoopBWords
   hwPar17PostMcWords hwPar17TailWords hwRemSetupWords hwRemPreDecWords
   hwRemPostAWords hwRemPostBWords hwRemExitWords
   cbcBadKeyIvWords cbcRetEpilogueWords cbcSoftQuadSetupWords cbcSoftQuadPre1Words
   cbcSoftQuadPre2Words cbcSoftQuadPost1aWords cbcSoftQuadPost1bWords cbcSoftQuadPost2Words
   cbcSoftQuadPost3Words cbcSoftQuadPost4Words cbcSoftQuadPost5Words cbcSoftTailSetupWords
   cbcSoftTailPreWords cbcSoftTailPost1Words cbcSoftTailPost2Words cbcUnpadWords
   cbcErrDeallocArgsWords cbcErrRetPreWords cbcErrRetPostWords cbcOkPreDropWords
   cbcOkRetWords cbcPanic1MidWords cbcSlicePanicMidWords cbcHandleErrPreWords)

/-! ## 1. Relocation Structures & `266`/`900`-Instruction Sequences -/

/-- Hardware AES-256 (`aes::armv8`) and `cpufeatures` target addresses for `aes_256_cbc_decrypt`. -/
structure Aes256DecHwAddrs where
  storageAddr : BitVec 64
  initInnerAddr : BitVec 64
  getauxvalHwcapAddr : BitVec 64 := 0#64
  getauxvalAddr : BitVec 64 := 0#64
  errnoLocationAddr : BitVec 64 := 0#64
  expandKeyAddr : BitVec 64
  invExpandAddr : BitVec 64
  rconAddr : BitVec 64
  relaxRcon : Bool := false
  hwDecryptAddr : BitVec 64
  hwDecryptPar17Addr : BitVec 64
  dropDecryptorAddr : BitVec 64

/-- Relocation parameters for the 4 unreachable cold panic tails (`+0xdbc..+0xe0c`). -/
structure Aes256CbcDecryptPanicSyms where
  panicMsgAddr : BitVec 64
  panicMsgRelax : Bool := false
  panicLocAddr : BitVec 64
  panicLocRelax : Bool := false
  panicAddr : BitVec 64
  sliceLocAddr : BitVec 64
  sliceLocRelax : Bool := false
  sliceIndexFailAddr : BitVec 64
  addOverflowLocAddr : BitVec 64
  addOverflowLocRelax : Bool := false
  panicAddOverflowAddr : BitVec 64
  subOverflowLocAddr : BitVec 64
  subOverflowLocRelax : Bool := false
  panicSubOverflowAddr : BitVec 64

/-- Unrelocated template instance of `Aes256CbcDecryptPanicSyms` at `fnAddr`. -/
@[expose] def Aes256CbcDecryptPanicSyms.template (fnAddr : BitVec 64 := 0#64) :
    Aes256CbcDecryptPanicSyms where
  panicMsgAddr := (fnAddr + 0xdbc#64) &&& 0xfffffffffffff000#64
  panicLocAddr := (fnAddr + 0xdc4#64) &&& 0xfffffffffffff000#64
  panicAddr := fnAddr + 0xdd0#64
  sliceLocAddr := (fnAddr + 0xdd4#64) &&& 0xfffffffffffff000#64
  sliceIndexFailAddr := fnAddr + 0xde8#64
  addOverflowLocAddr := (fnAddr + 0xdec#64) &&& 0xfffffffffffff000#64
  panicAddOverflowAddr := fnAddr + 0xdf4#64
  subOverflowLocAddr := (fnAddr + 0xe04#64) &&& 0xfffffffffffff000#64
  panicSubOverflowAddr := fnAddr + 0xe0c#64

/-- Exact `266`-instruction `STORAGE == 1` hardware CBC decryption loop slice
    (`fnAddr + 0x1d4#64 .. fnAddr + 0x5fc#64`). -/
@[expose] def cbcDecHwLoopInstrs
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) : List Instr :=
  List.flatten
    [ decodeWords hwSetupWords, decodeWords hwPar17InitWords, decodeWords hwPar17PreMc1Words,
      [.bl (memcpyAddr - (fnAddr + 0x228#64))], decodeWords hwPar17PreMc2Words,
      [.bl (memcpyAddr - (fnAddr + 0x238#64))], decodeWords hwPar17PreDecWords,
      [.bl (hwDecryptPar17Addr - (fnAddr + 0x248#64))],
      decodeWords hwPar17Xor0AWords, decodeWords hwPar17Xor0BWords,
      decodeWords hwPar17XorLoopAWords, decodeWords hwPar17XorLoopBWords,
      decodeWords hwPar17PostMcWords, [.bl (memcpyAddr - (fnAddr + 0x478#64))],
      decodeWords hwPar17TailWords, decodeWords hwRemSetupWords, decodeWords hwRemPreDecWords,
      [.bl (hwDecryptAddr - (fnAddr + 0x4d8#64))],
      decodeWords hwRemPostAWords, decodeWords hwRemPostBWords, decodeWords hwRemExitWords ]

theorem cbcDecHwLoopInstrs_length
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) :
    (cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr).length = 266 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [cbcDecHwLoopInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  rfl

/-- Prefix `117` instructions (`fnAddr + 0x000#64 .. fnAddr + 0x1d4#64`) before `cbcDecHwLoopInstrs`. -/
@[expose] def cbcDecPrologInstrs
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (keyScheduleAddr shimAddr allocZeroedAddr memcpyAddr errStr1Addr : BitVec 64)
    (errStr1Relax : Bool := false) : List Instr :=
  List.flatten
    [ decodeWords cbcPrologueWords,
      [.adr true (.gpr 19#5) (adrpOff (fnAddr + 0x040#64) hw.storageAddr)],
      decodeWords cbcPostStorageAdrpWords,
      [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 hw.storageAddr))],
      decodeWords cbcStorageCheckWords,
      [.bl (keyScheduleAddr - (fnAddr + 0x070#64))],
      decodeWords cbcPostSoftKsWords,
      adrpAddPair (.gpr 10#5) (fnAddr + 0x07c#64) errStr1Addr errStr1Relax,
      decodeWords cbcFastRejectWords,
      [.bl (hw.initInnerAddr - (fnAddr + 0x098#64))],
      decodeWords cbcPostInitWords,
      [.bl (hw.expandKeyAddr - (fnAddr + 0x0ac#64))],
      decodeWords cbcPreInvExpandWords,
      [.bl (hw.invExpandAddr - (fnAddr + 0x0bc#64))],
      decodeWords cbcHwCopyEkWords,
      [.bl (memcpyAddr - (fnAddr + 0x13c#64))],
      decodeWords cbcSroaCopy960Words,
      [.bl (memcpyAddr - (fnAddr + 0x154#64))],
      decodeWords cbcSroaCopy952Words,
      [.bl (memcpyAddr - (fnAddr + 0x170#64))],
      decodeWords cbcSroaStage968Words,
      [.bl (memcpyAddr - (fnAddr + 0x18c#64)),
       .bl (shimAddr - (fnAddr + 0x190#64))],
      decodeWords cbcPreAllocWords,
      [.bl (allocZeroedAddr - (fnAddr + 0x19c#64))],
      decodeWords cbcPostAllocWords,
      [.bl (memcpyAddr - (fnAddr + 0x1bc#64)),
       .ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 hw.storageAddr))],
      decodeWords cbcLoopDispatchWords ]

theorem cbcDecPrologInstrs_length
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (keyScheduleAddr shimAddr allocZeroedAddr memcpyAddr errStr1Addr : BitVec 64)
    (errStr1Relax : Bool) :
    (cbcDecPrologInstrs fnAddr hw keyScheduleAddr shimAddr allocZeroedAddr memcpyAddr
      errStr1Addr errStr1Relax).length = 117 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [cbcDecPrologInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    adrpAddPair_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  rfl

/-- Suffix `517` instructions (`fnAddr + 0x5fc#64 .. fnAddr + 0xe10#64`) after `cbcDecHwLoopInstrs`. -/
@[expose] def cbcDecPostHwInstrs
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (decryptAddr deallocAddr handleErrorAddr errStr2Addr : BitVec 64)
    (panics : Aes256CbcDecryptPanicSyms := Aes256CbcDecryptPanicSyms.template fnAddr)
    (errStr2Relax : Bool := false) : List Instr :=
  List.flatten
    [ [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 hw.storageAddr))],
      decodeWords cbcBadKeyIvWords,
      decodeWords cbcRetEpilogueWords,
      decodeWords cbcSoftQuadSetupWords,
      decodeWords cbcSoftQuadPre1Words,
      decodeWords cbcSoftQuadPre2Words,
      [.bl (decryptAddr - (fnAddr + 0x7e8#64))],
      decodeWords cbcSoftQuadPost1aWords,
      decodeWords cbcSoftQuadPost1bWords,
      decodeWords cbcSoftQuadPost2Words,
      decodeWords cbcSoftQuadPost3Words,
      decodeWords cbcSoftQuadPost4Words,
      decodeWords cbcSoftQuadPost5Words,
      decodeWords cbcSoftTailSetupWords,
      decodeWords cbcSoftTailPreWords,
      [.bl (decryptAddr - (fnAddr + 0xc04#64))],
      decodeWords cbcSoftTailPost1Words,
      decodeWords cbcSoftTailPost2Words,
      decodeWords cbcUnpadWords,
      [.bl (hw.dropDecryptorAddr - (fnAddr + 0xd64#64))],
      decodeWords cbcErrDeallocArgsWords,
      [.bl (deallocAddr - (fnAddr + 0xd74#64))],
      decodeWords cbcErrRetPreWords,
      adrpAddPair (.gpr 9#5) (fnAddr + 0xd80#64) errStr2Addr errStr2Relax,
      decodeWords cbcErrRetPostWords,
      decodeWords cbcOkPreDropWords,
      [.bl (hw.dropDecryptorAddr - (fnAddr + 0xda8#64))],
      decodeWords cbcOkRetWords,
      adrpAddPair (.gpr 0#5) (fnAddr + 0xdbc#64) panics.panicMsgAddr panics.panicMsgRelax,
      adrpAddPair (.gpr 2#5) (fnAddr + 0xdc4#64) panics.panicLocAddr panics.panicLocRelax,
      decodeWords cbcPanic1MidWords,
      [.bl (panics.panicAddr - (fnAddr + 0xdd0#64))],
      adrpAddPair (.gpr 3#5) (fnAddr + 0xdd4#64) panics.sliceLocAddr panics.sliceLocRelax,
      decodeWords cbcSlicePanicMidWords,
      [.bl (panics.sliceIndexFailAddr - (fnAddr + 0xde8#64))],
      adrpAddPair (.gpr 0#5) (fnAddr + 0xdec#64) panics.addOverflowLocAddr panics.addOverflowLocRelax,
      [.bl (panics.panicAddOverflowAddr - (fnAddr + 0xdf4#64))],
      decodeWords cbcHandleErrPreWords,
      [.bl (handleErrorAddr - (fnAddr + 0xe00#64))],
      adrpAddPair (.gpr 0#5) (fnAddr + 0xe04#64) panics.subOverflowLocAddr panics.subOverflowLocRelax,
      [.bl (panics.panicSubOverflowAddr - (fnAddr + 0xe0c#64))] ]

theorem cbcDecPostHwInstrs_length
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (decryptAddr deallocAddr handleErrorAddr errStr2Addr : BitVec 64)
    (panics : Aes256CbcDecryptPanicSyms) (errStr2Relax : Bool) :
    (cbcDecPostHwInstrs fnAddr hw decryptAddr deallocAddr handleErrorAddr
      errStr2Addr panics errStr2Relax).length = 517 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [cbcDecPostHwInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    adrpAddPair_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  rfl

/-- Relocation-patched `900`-instruction sequence of `signal_crypto::aes_cbc::aes_256_cbc_decrypt`
    (`autodetect::Aes256`, hardware + `Fixslice64`). -/
@[expose] def aes256CbcDecryptInstrs
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64)
    (panics : Aes256CbcDecryptPanicSyms := Aes256CbcDecryptPanicSyms.template fnAddr)
    (errStr1Relax : Bool := false) (errStr2Relax : Bool := false) : List Instr :=
  cbcDecPrologInstrs fnAddr hw keyScheduleAddr shimAddr allocZeroedAddr memcpyAddr
    errStr1Addr errStr1Relax ++
  cbcDecHwLoopInstrs fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr ++
  cbcDecPostHwInstrs fnAddr hw decryptAddr deallocAddr handleErrorAddr
    errStr2Addr panics errStr2Relax

theorem aes256CbcDecryptInstrs_length
    (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64)
    (panics : Aes256CbcDecryptPanicSyms) (errStr1Relax errStr2Relax : Bool) :
    (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
      errStr1Relax errStr2Relax).length = 900 := by
  simp only [aes256CbcDecryptInstrs, List.length_append, cbcDecPrologInstrs_length,
    cbcDecHwLoopInstrs_length, cbcDecPostHwInstrs_length]

theorem hasInstrs_split {P : Program} {a : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P a (xs ++ ys)) :
    hasInstrs P a xs ∧ hasInstrs P (a + BitVec.ofNat 64 (4 * xs.length)) ys := by
  refine ⟨hasInstrs_prefix h, fun i hi => ?_⟩
  have hall := h (xs.length + i) (by rw [List.length_append]; omega)
  have hget : (xs ++ ys)[xs.length + i]'(by rw [List.length_append]; omega) = ys[i] := by
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
  have ha : a + BitVec.ofNat 64 (4 * (xs.length + i)) =
      a + BitVec.ofNat 64 (4 * xs.length) + BitVec.ofNat 64 (4 * i) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hget, ha] at hall
  exact hall

/-- Extract `hasInstrs P (fnAddr + 0x1d4#64) (cbcDecHwLoopInstrs ...)` from the full
    `900`-instruction `aes256CbcDecryptInstrs` assumption. -/
theorem hasInstrs_hwLoop_of_full {P : Program}
    {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax)) :
    hasInstrs P (fnAddr + 0x1d4#64)
      (cbcDecHwLoopInstrs fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr) := by
  unfold aes256CbcDecryptInstrs at hCode
  rw [List.append_assoc] at hCode
  have hTail := (hasInstrs_split hCode).2
  rw [cbcDecPrologInstrs_length] at hTail
  exact hasInstrs_prefix hTail

/-! ## 2. Callee Contract Bundle (`Aes256CbcDecryptCallees`) & `HwLoopContract` -/

/-- Unplaced conditional-OOM contract for `__rust_alloc_zeroed(size, align)`. -/
abbrev rustAllocZeroedBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpecBase M A lim true

/-- Bundle of `subroutine_ok` contracts for all subroutines called by `aes_256_cbc_decrypt`,
    splitting `(hw.storageAddr ↦₈ _)` out of `A.pool` via `[hSplit : PoolAesInitSplit A hw.storageAddr]`. -/
structure Aes256CbcDecryptCallees (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : Program) (hw : Aes256DecHwAddrs)
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    (keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr : BitVec 64) : Prop where
  initInner_ok : subroutine_ok P hw.initInnerAddr (aesInitInnerSpec M hSplit.base hw.storageAddr lim)
  expandKey_ok : subroutine_ok P hw.expandKeyAddr (expandKey15RegionSpec hw.rconAddr)
  invExpand_ok : subroutine_ok P hw.invExpandAddr invExpandedKeys15RegionSpec
  hwDecryptPar17_ok : subroutine_ok P hw.hwDecryptPar17Addr decryptPar17InplaceBytesSpec
  hwDecrypt_ok : subroutine_ok P hw.hwDecryptAddr decrypt15InplaceSpec
  dropDecryptor_ok : subroutine_ok P hw.dropDecryptorAddr (dropDecryptorSpec hw.storageAddr)
  keySchedule_ok : subroutine_ok P keyScheduleAddr aes256KeyScheduleSpec
  decrypt_ok : subroutine_ok P decryptAddr aes256DecryptSpec
  shim_ok : subroutine_ok P shimAddr rustAllocShimVmSpec
  allocZeroed_ok : subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase M hSplit.base lim)
  dealloc_ok : subroutine_ok P deallocAddr (rustCliDeallocBudgetSpecBase M hSplit.base lim)
  memcpy_ok : subroutine_ok P memcpyAddr allocMemcpyVmSpec
  handleError_ok : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec

/-- Construct `Aes256CbcDecryptCallees` from `hasInstrs` on all `Armv8` and `Fixslice64`
    subroutines plus allocator/libc contracts on `hSplit.base`. -/
theorem Aes256CbcDecryptCallees.of_hasInstrs {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr
     memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr
     invSubBytesAddr invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr
     decPanic0Sym : BitVec 64}
    {decPanic0Relax : Bool} {decPanic0Target : BitVec 64}
    (hInitCode : AesInitInnerCode P hw.initInnerAddr hw.getauxvalHwcapAddr hw.getauxvalAddr
      hw.errnoLocationAddr hSplit.libcAddr hw.storageAddr)
    (hExpCode : hasInstrs P hw.expandKeyAddr
      (expandKey15ReachableInstrs hw.expandKeyAddr hw.rconAddr hw.relaxRcon))
    (hInvExpCode : hasInstrs P hw.invExpandAddr invExpandedKeys15Instrs)
    (hPar17Code : hasInstrs P hw.hwDecryptPar17Addr (decodeWords decryptPar17Words))
    (hHwDecCode : hasInstrs P hw.hwDecryptAddr decrypt15Instrs)
    (hDropCode : hasInstrs P hw.dropDecryptorAddr
      (dropDecryptorInstrs hw.dropDecryptorAddr hw.storageAddr))
    (hKsCode : hasInstrs P keyScheduleAddr
      (aes256KeyScheduleInstrs keyScheduleAddr memsetAddr bitsliceAddr memshift32Addr
        subBytesAddr xorColumnsAddr memcpyAddr))
    (hKsCal : Aes256KeyScheduleCallees P memsetAddr bitsliceAddr memshift32Addr
      subBytesAddr xorColumnsAddr memcpyAddr)
    (hDecCode : hasInstrs P decryptAddr
      (aes256DecryptPrefixInstrs decryptAddr bitsliceAddr invSubBytesAddr
        invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr
        decPanic0Sym decPanic0Relax decPanic0Target))
    (hDecCal : Aes256DecryptCallees P bitsliceAddr invSubBytesAddr
      invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr)
    (hShim : subroutine_ok P shimAddr rustAllocShimVmSpec)
    (hAllocZeroed : subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase M hSplit.base lim))
    (hDealloc : subroutine_ok P deallocAddr (rustCliDeallocBudgetSpecBase M hSplit.base lim))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hHandleErr : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec) :
    Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr where
  initInner_ok := hSplit.initInner_ok lim hInitCode
  expandKey_ok := expandKey15_region_subroutine_ok hExpCode
  invExpand_ok := invExpandedKeys15_region_subroutine_ok hInvExpCode
  hwDecryptPar17_ok := decryptPar17_inplace_bytes_subroutine_ok hPar17Code
  hwDecrypt_ok := decrypt15_inplace_subroutine_ok hHwDecCode
  dropDecryptor_ok := dropDecryptor_subroutine_ok hDropCode
  keySchedule_ok := aes256KeySchedule_ok hKsCode hKsCal
  decrypt_ok := aes256Decrypt_ok hDecCode hDecCal
  shim_ok := hShim
  allocZeroed_ok := hAllocZeroed
  dealloc_ok := hDealloc
  memcpy_ok := hMemcpy
  handleError_ok := hHandleErr

/-- Abstract CPS `SepWP` contract for the `266`-instruction `STORAGE == 1` hardware CBC decryption
    loop slice (`fnAddr + 0x1d4#64 -> fnAddr + 0xd20#64`), proved independently in `CbcDec/HwLoop*`. -/
@[expose] def HwLoopContract (P : Program)
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) : Prop :=
  hasInstrs P (fnAddr + 0x1d4#64)
    (cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr) →
  subroutine_ok P memcpyAddr allocMemcpyVmSpec →
  subroutine_ok P hwDecryptPar17Addr decryptPar17InplaceBytesSpec →
  subroutine_ok P hwDecryptAddr decrypt15InplaceSpec →
  ∀ (target_pc sp outBuf : BitVec 64) (x : AesCall) (Rest : SepProp) (s : State)
    (post : State → SepProp → Prop) (oom : State → SepProp),
    0 < x.input.length →
    x.input.length % 16 = 0 →
    x.input.length < 2 ^ 40 →
    x.key.length = 32 →
    x.iv.length = 16 →
    outBuf ≠ 0#64 →
    s.pc = fnAddr + 0x1d4#64 →
    s.status = .Running →
    s.sp = sp →
    sp &&& 15#64 = 0#64 →
    s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.input.length / 16) →
    s.readReg64 (.gpr 24#5) = sp + 0x4b0#64 →
    s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 x.input.length →
    (∀ sf : State,
      sf.pc = fnAddr + 0xd20#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (x.input.length / 16) →
      sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (x.input.length / 16)) ∗
         ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 x.input.length) ∗
         ((sp + 0x028#64) ↦₆₄ outBuf) ∗
         ((sp + 0x030#64) ↦₆₄ x.inA) ∗
         memRegion (sp + 0x0e0#64) 8 ∗
         memRegion (sp + 0x4b0#64) 0x110 ∗
         memRegion (sp + 0x870#64) 0x110 ∗
         memRegion (sp + 0xa50#64) 0x10 ∗
         roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey x.key)) ∗
         memRegion (sp + 0xf00#64) 16 ∗
         (x.inA ↦ₛ x.input) ∗
         (outBuf ↦ₛ
           (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 x.key))
             (bytesToBlock x.iv) (chunks16 x.input)).flatMap blockToBytesLE) ∗
         stackAt sp allocHookStack ∗ Rest)
        post oom) →
    SepWP P target_pc s
      (((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (x.input.length / 16)) ∗
       ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 x.input.length) ∗
       ((sp + 0x028#64) ↦₆₄ outBuf) ∗
       ((sp + 0x030#64) ↦₆₄ x.inA) ∗
       memRegion (sp + 0x0e0#64) 8 ∗
       memRegion (sp + 0x4b0#64) 0x110 ∗
       memRegion (sp + 0x870#64) 0x110 ∗
       memRegion (sp + 0xa50#64) 0x10 ∗
       roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey x.key)) ∗
       ((sp + 0xf00#64) ↦ₛ x.iv) ∗
       (x.inA ↦ₛ x.input) ∗
       memRegion outBuf x.input.length ∗
       stackAt sp allocHookStack ∗ Rest)
      post oom

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
