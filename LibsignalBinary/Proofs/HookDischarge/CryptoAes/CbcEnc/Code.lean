/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor

/-!
# Relocated Instruction Sequence & Callee Bundle for `aes_256_cbc_encrypt` (`CbcEnc.Code`)

Placement-generic `595`-instruction model (`584` reachable + `11` unreachable `unwrap_failed` tail)
and callee-contract bundle for `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (`aes::autodetect::Aes256`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code

open Arm64 ProofLib
open ProofLib.StdStartup (adrpOff decodeWords hasInstrs pageLo12)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec RustStdAllocAuxEntries)
open LibsignalBinary.Heap.Fine (allocMemsetVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (adrpAddPair adrpAddPair_length hasInstrs_prefix)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
  (Aes256KeyScheduleCallees aes256KeyScheduleInstrs aes256KeyScheduleSpec aes256KeySchedule_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
  (Aes256EncryptCallees aes256EncryptInstrs aes256EncryptSpec aes256Encrypt_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
  (bitsliceInstrs invBitsliceInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode (subBytesInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
  (mixColumns1Instrs mixColumns3Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
  (memshift32ReachableInstrs xorColumnsReachableInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode (AesInitInnerCode)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit aesInitInnerSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule
  (expandKey15ReachableInstrs expandKey15RegionSpec expandKey15_region_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (invExpandedKeys15Instrs invExpandedKeys15RegionSpec invExpandedKeys15_region_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
  (encrypt15Instrs encrypt15InplaceSpec encrypt15_inplace_subroutine_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor
  (dropDecryptorInstrs dropDecryptorSpec dropDecryptor_subroutine_ok)

/-! ## 1. Relocation Address Bundles -/

/-- Hardware `aes::armv8` & `cpufeatures` relocation targets for `aes_256_cbc_encrypt`. -/
structure Aes256EncHwAddrs where
  storageAddr : BitVec 64
  initInnerAddr : BitVec 64
  getauxvalHwcapAddr : BitVec 64
  getauxvalAddr : BitVec 64
  errnoLocationAddr : BitVec 64
  expandKeyAddr : BitVec 64
  invExpandedKeysAddr : BitVec 64
  rconAddr : BitVec 64
  hwEncryptAddr : BitVec 64
  dropDecryptorAddr : BitVec 64

/-- Relocation parameters for the unreachable `unwrap_failed` panic tail (`[584..594]`). -/
structure Aes256CbcEncryptPanicSyms where
  msgPtr : BitVec 64
  errPtr : BitVec 64
  locPtr : BitVec 64
  unwrapFailedAddr : BitVec 64
  relaxMsg : Bool := false
  relaxErr : Bool := false
  relaxLoc : Bool := false

/-- Default zero-page template instance of `Aes256CbcEncryptPanicSyms` at `fnAddr`. -/
@[expose] def Aes256CbcEncryptPanicSyms.template
    (fnAddr : BitVec 64 := 0#64) : Aes256CbcEncryptPanicSyms where
  msgPtr := (fnAddr + 0x928#64) &&& 0xfffffffffffff000#64
  errPtr := (fnAddr + 0x930#64) &&& 0xfffffffffffff000#64
  locPtr := (fnAddr + 0x938#64) &&& 0xfffffffffffff000#64
  unwrapFailedAddr := fnAddr + 0x948#64

/-! ## 2. Machine-Code Word Segments (`595` Instructions) -/

@[expose] def encPrologWords : List (BitVec 32) := [
   0xa9ba7bfd#32, 0xa9016ffc#32, 0xa90267fa#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32, 0x910003fd#32,
   0xd14007ff#32, 0xf81407ff#32, 0xf100807f#32, 0xaa0803f3#32, 0x540045c1#32]
@[expose] def encSave45Words : List (BitVec 32) := [0xaa0503f5#32, 0xaa0403f4#32]
@[expose] def encDisp0Words : List (BitVec 32) := [
   0xaa0103f7#32, 0xaa0003f6#32, 0x7100051f#32, 0x54003c60#32, 0x7103fd1f#32, 0x54003ba0#32]
@[expose] def encSwKsPreWords : List (BitVec 32) := [0x911043e8#32, 0xaa0203e0#32]
@[expose] def encSwKsMcWords : List (BitVec 32) := [0x913243e0#32, 0x911043e1#32, 0x52807802#32]
@[expose] def encSwIvChkWords : List (BitVec 32) := [0xf10042bf#32, 0x540040e1#32]
@[expose] def encJoinMc1Words : List (BitVec 32) := [0x912303e0#32, 0x911043e1#32, 0x52807802#32]
@[expose] def encJoinMc2Words : List (BitVec 32) := [0x3dc00280#32, 0x910103e0#32, 0x912303e1#32, 0x52807a02#32, 0x3d8323e0#32]
@[expose] def encSizeCalcWords : List (BitVec 32) := [0x927ceaf9#32, 0xb1004334#32, 0x54004324#32]
@[expose] def encAllocArgsWords : List (BitVec 32) := [0xaa1403e0#32, 0x52800021#32, 0x52800038#32]
@[expose] def encPostAllocWords : List (BitVec 32) := [
   0xb4004280#32, 0xeb1402ff#32, 0x540042a8#32, 0xaa0003f5#32, 0x913243e0#32, 0x912303e1#32, 0x52807a02#32,
   0x913243f8#32, 0x913243fa#32]
@[expose] def encPadMcWords : List (BitVec 32) := [
   0xd344fefb#32, 0x92400ef7#32, 0x911f43e0#32, 0x8b1902c1#32, 0xaa1703e2#32, 0xf903efff#32, 0xf903ebff#32,
   0x911f43fc#32]
@[expose] def encPadMsWords : List (BitVec 32) := [0x52800208#32, 0x8b170380#32, 0xcb170101#32, 0xaa0103e2#32]
@[expose] def encSpillTailWords : List (BitVec 32) := [
   0x395f43e9#32, 0x395f47e8#32, 0x8b1902b7#32, 0x290023e9#32, 0x395f4be9#32, 0x395f4fe8#32, 0x290123e9#32,
   0x395f53e9#32, 0x395f57e8#32, 0x290223e9#32, 0x395f5be9#32, 0x395f5fe8#32, 0x290323e9#32, 0x395f63e9#32,
   0x395f67e8#32, 0x290423e9#32, 0x395f6be9#32, 0x395f6fe8#32, 0x290523e9#32, 0x395f73e9#32, 0x395f77e8#32,
   0x290623e9#32, 0x395f7be9#32, 0x395f7fe8#32, 0x290723e9#32]
@[expose] def encLoopDispWords : List (BitVec 32) := [0x7100051f#32, 0x540009e1#32]
@[expose] def encHwLoopHdrWords : List (BitVec 32) := [0xb40019bb#32, 0xaa1503f9#32]
@[expose] def encHwLoopPreAWords : List (BitVec 32) := [
   0x3cc106c0#32, 0x394f0308#32, 0x394f070a#32, 0x394f0f0d#32, 0x913243e0#32, 0x3d81f7e0#32, 0x394f0b0b#32,
   0x911f43e1#32, 0x395f43e9#32, 0x395f47ec#32, 0x911f43e2#32, 0x395f4bee#32, 0x394f370f#32, 0x395f77f0#32,
   0x4a080128#32, 0x395f4fe9#32, 0x4a0a018a#32, 0x391f43e8#32, 0x394f1308#32, 0x4a0b01cb#32, 0x391f47ea#32,
   0x395f53ea#32, 0x4a0d0129#32, 0x391f4fe9#32, 0x394f1709#32, 0x395f6fec#32, 0x4a080148#32, 0x395f57ea#32,
   0x391f4beb#32, 0x391f53e8#32, 0x394f2f0b#32, 0x394f330d#32, 0x4a090148#32, 0x394f1b09#32, 0x395f5bea#32,
   0x391f57e8#32]
@[expose] def encHwLoopPreBWords : List (BitVec 32) := [
   0x395f73ee#32, 0x4a090148#32, 0x394f1f09#32, 0x395f5fea#32, 0x391f5be8#32, 0x4a090148#32, 0x394f2309#32,
   0x395f63ea#32, 0x391f5fe8#32, 0x4a090148#32, 0x394f2709#32, 0x395f67ea#32, 0x391f63e8#32, 0x4a090148#32,
   0x394f2b09#32, 0x395f6bea#32, 0x391f67e8#32, 0x4a0d01c8#32, 0x4a090149#32, 0x4a0b018a#32, 0x391f73e8#32,
   0x391f6be9#32, 0x394f3b09#32, 0x394f3f08#32, 0x391f6fea#32, 0x395f7bea#32, 0x395f7fec#32, 0x4a0f020b#32,
   0x4a090149#32, 0x4a080188#32, 0x391f77eb#32, 0x391f7be9#32, 0x391f7fe8#32]
@[expose] def encHwLoopPostWords : List (BitVec 32) := [
   0x3dc1f7e0#32, 0xf100077b#32, 0x3d80f340#32, 0x3c810720#32, 0x54fff6c1#32, 0x14000080#32]
@[expose] def encSwLoopCbzWords : List (BitVec 32) := [0xb4000ffb#32]
@[expose] def encSwLoopInitWords : List (BitVec 32) := [
   0x394f0309#32, 0x394f070a#32, 0xd10153bc#32, 0x394f0b08#32, 0x394f0f0b#32, 0x91001ed6#32, 0x394f130c#32,
   0x394f170d#32, 0x91001eb9#32, 0x394f1b0e#32, 0x394f1f0f#32, 0x394f2310#32, 0x394f2703#32, 0x394f2b02#32,
   0x394f2f01#32, 0x394f3300#32, 0x394f3712#32, 0x394f3b11#32, 0x394f3f04#32]
@[expose] def encSwLoopPreAWords : List (BitVec 32) := [
   0x385f92c5#32, 0x385fa2c6#32, 0x6f00e400#32, 0x4a0900a9#32, 0x385fb2c5#32, 0x4a0a00ca#32, 0x390f7309#32,
   0x385fc2c9#32, 0x4a0800a8#32, 0x390f770a#32, 0x385fd2ca#32, 0x4a0b0129#32, 0x390f7b08#32, 0x385fe2c8#32,
   0x390f7f09#32, 0x385ff2c9#32, 0x4a0c014a#32, 0x4a0d0108#32, 0x390f830a#32, 0x394002ca#32, 0x4a0e0129#32,
   0x390f8708#32, 0x394006c8#32, 0x390f8b09#32, 0x39400ac9#32, 0x4a0f014a#32, 0x4a100108#32]
@[expose] def encSwLoopPreBWords : List (BitVec 32) := [
   0x390f8f0a#32, 0x39400eca#32, 0x4a030129#32, 0x390f9308#32, 0x394012c8#32, 0x390f9709#32, 0x394016c9#32,
   0x4a02014a#32, 0x4a010108#32, 0x390f9b0a#32, 0x39401aca#32, 0x4a000129#32, 0x390f9f08#32, 0x39401ec8#32,
   0x390fa309#32, 0x394022c9#32, 0x4a12014a#32, 0x4a110108#32, 0x913243e0#32, 0xd10153a1#32, 0x4a040129#32,
   0x390fab08#32, 0x911f43e8#32, 0x390fa70a#32, 0x390faf09#32, 0xad010380#32, 0x3c810380#32]
@[expose] def encSwLoopOutWords : List (BitVec 32) := [
   0x395f43e9#32, 0x395f47ea#32, 0xf100077b#32, 0x395f4be8#32, 0x395f4feb#32, 0x910042d6#32, 0x395f53ec#32,
   0x395f57ed#32, 0x395f5bee#32, 0x395f5fef#32, 0x395f63f0#32, 0x395f67e3#32, 0x395f6be2#32, 0x395f6fe1#32,
   0x395f73e0#32, 0x395f77f2#32, 0x395f7bf1#32, 0x395f7fe4#32]
@[expose] def encSwLoopCtWords : List (BitVec 32) := [
   0x381f9329#32, 0x381fa32a#32, 0x381fb328#32, 0x381fc32b#32, 0x381fd32c#32, 0x381fe32d#32, 0x381ff32e#32,
   0x3900032f#32, 0x39000730#32, 0x39000b23#32, 0x39000f22#32, 0x39001321#32, 0x39001720#32, 0x39001b32#32,
   0x39001f31#32, 0x39002324#32, 0x91004339#32]
@[expose] def encSwLoopPrevWords : List (BitVec 32) := [
   0x390f0309#32, 0x390f070a#32, 0x390f0b08#32, 0x390f0f0b#32, 0x390f130c#32, 0x390f170d#32, 0x390f1b0e#32,
   0x390f1f0f#32, 0x390f2310#32, 0x390f2703#32, 0x390f2b02#32, 0x390f2f01#32, 0x390f3300#32, 0x390f3712#32,
   0x390f3b11#32, 0x390f3f04#32, 0x54fff2c1#32]
@[expose] def encTailDispWords : List (BitVec 32) := [0x7100051f#32, 0x540008e1#32]
@[expose] def encHwTailPreAWords : List (BitVec 32) := [
   0x29402fea#32, 0x394f0308#32, 0x394f0709#32, 0x913243e0#32, 0x911f43e1#32, 0x911f43e2#32, 0x4a0a0108#32,
   0x4a0b0129#32, 0x394f0b0a#32, 0x391f43e8#32, 0x394f0f08#32, 0x391f47e9#32, 0x294127eb#32, 0x4a0b014a#32,
   0x394f130b#32, 0x4a090108#32, 0x394f1709#32, 0x391f4bea#32, 0x391f4fe8#32, 0xb94013e8#32, 0x394f1b0a#32,
   0x4a080168#32, 0x391f53e8#32, 0xb94017e8#32, 0x4a080128#32, 0x394f1f09#32, 0x391f57e8#32, 0xb9401be8#32,
   0x4a080148#32, 0x394f230a#32, 0x391f5be8#32, 0xb9401fe8#32, 0x4a080128#32, 0x394f2709#32, 0x391f5fe8#32]
@[expose] def encHwTailPreBWords : List (BitVec 32) := [
   0xb94023e8#32, 0x4a080148#32, 0x394f2b0a#32, 0x391f63e8#32, 0xb94027e8#32, 0x4a080128#32, 0x394f2f09#32,
   0x391f67e8#32, 0xb9402be8#32, 0x4a080148#32, 0x394f330a#32, 0x391f6be8#32, 0xb9402fe8#32, 0x4a080128#32,
   0x394f3709#32, 0x391f6fe8#32, 0xb94033e8#32, 0x4a080148#32, 0x394f3b0a#32, 0x391f73e8#32, 0xb94037e8#32,
   0x4a080128#32, 0x394f3f09#32, 0x391f77e8#32, 0xb9403be8#32, 0x4a080148#32, 0x391f7be8#32, 0xb9403fe8#32,
   0x4a080128#32, 0x391f7fe8#32]
@[expose] def encHwTailPostWords : List (BitVec 32) := [0x3dc1f7e0#32, 0x3d80f340#32, 0x3d8002e0#32, 0x14000071#32]
@[expose] def encSwTailPreAWords : List (BitVec 32) := [
   0x29402fea#32, 0x394f0308#32, 0x394f0709#32, 0x6f00e400#32, 0x294133ed#32, 0x4a0a0108#32, 0xd10153aa#32,
   0x4a0b0129#32, 0x39000148#32, 0x394f0b08#32, 0x394f130b#32, 0x39000549#32, 0x394f0f09#32, 0x913243e0#32,
   0x4a0d0108#32, 0xd10153a1#32, 0xad010140#32, 0x4a0c0129#32, 0x39000948#32, 0x394f170c#32, 0x39000d49#32,
   0x294227e8#32, 0x4a080168#32, 0x394f1b0b#32, 0x3d800540#32, 0x4a090189#32, 0x39001148#32, 0x394f1f0c#32,
   0x39001549#32, 0x294327e8#32, 0x4a080168#32, 0x394f230b#32, 0x4a090189#32, 0x39001948#32, 0x394f270c#32,
   0x39001d49#32]
@[expose] def encSwTailPreBWords : List (BitVec 32) := [
   0x294427e8#32, 0x4a080168#32, 0x394f2b0b#32, 0x4a090189#32, 0x39002148#32, 0x394f2f0c#32, 0x39002549#32,
   0x294527e8#32, 0x4a080168#32, 0x394f330b#32, 0x4a090189#32, 0x39002948#32, 0x394f370c#32, 0x39002d49#32,
   0x294627e8#32, 0x4a080168#32, 0x394f3b0b#32, 0x4a090189#32, 0x39003148#32, 0x394f3f0c#32, 0x39003549#32,
   0x294727e8#32, 0x4a080168#32, 0x4a090189#32, 0x39003948#32, 0x911f43e8#32, 0x39003d49#32]
@[expose] def encSwTailOutWords : List (BitVec 32) := [
   0x395f43e8#32, 0x395f47e9#32, 0x395f4bea#32, 0x395f4feb#32, 0x395f53ec#32, 0x395f57ed#32, 0x395f5bee#32,
   0x395f5fef#32, 0x395f63f0#32, 0x395f67f1#32, 0x395f6bf2#32, 0x395f6fe0#32, 0x395f73e1#32, 0x395f77e2#32,
   0x395f7be3#32, 0x395f7fe4#32]
@[expose] def encSwTailPrevWords : List (BitVec 32) := [
   0x390f0308#32, 0x390f0709#32, 0x390f0b0a#32, 0x390f0f0b#32, 0x390f130c#32, 0x390f170d#32, 0x390f1b0e#32,
   0x390f1f0f#32, 0x390f2310#32, 0x390f2711#32, 0x390f2b12#32, 0x390f2f00#32, 0x390f3301#32, 0x390f3702#32,
   0x390f3b03#32, 0x390f3f04#32]
@[expose] def encSwTailCtWords : List (BitVec 32) := [
   0x390002e8#32, 0x390006e9#32, 0x39000aea#32, 0x39000eeb#32, 0x390012ec#32, 0x390016ed#32, 0x39001aee#32,
   0x39001eef#32, 0x390022f0#32, 0x390026f1#32, 0x39002af2#32, 0x39002ee0#32, 0x390032e1#32, 0x390036e2#32,
   0x39003ae3#32, 0x39003ee4#32]
@[expose] def encDropArgWords : List (BitVec 32) := [0x913243e0#32]
@[expose] def encWriteVecWords : List (BitVec 32) := [0xa9005674#32, 0xf9000a74#32, 0x1400004a#32]
@[expose] def encInitSaveWords : List (BitVec 32) := [0xaa0203f8#32]
@[expose] def encInitPostWords : List (BitVec 32) := [0xaa1803e2#32, 0x3607c420#32]
@[expose] def encHwKsArgsWords : List (BitVec 32) := [0x911f43e0#32, 0xaa0203e1#32]
@[expose] def encHwInvArgsWords : List (BitVec 32) := [0x913243e8#32, 0x911f43e1#32, 0x9103c100#32]
@[expose] def encHwCopyEkWords : List (BitVec 32) := [
   0x3dc227e0#32, 0x3dc22be1#32, 0x911043e0#32, 0x3dc22fe2#32, 0x913243e1#32, 0x52803c02#32, 0x3d8357e0#32,
   0x3dc217e0#32, 0x3d835be1#32, 0x3dc21be1#32, 0x3d8347e0#32, 0x3dc21fe0#32, 0x3d835fe2#32, 0x3dc223e2#32,
   0x3d834fe0#32, 0x3dc20be0#32, 0x3d834be1#32, 0x3dc207e1#32, 0x3d833be0#32, 0x3dc20fe0#32, 0x3d8353e2#32,
   0x3dc213e2#32, 0x3d833fe0#32, 0x3dc1fbe0#32, 0x3d8337e1#32, 0x3dc1f7e1#32, 0x3d8343e2#32, 0x3dc203e2#32,
   0x3d832be0#32, 0x3dc1ffe0#32, 0x3d8327e1#32, 0x3d8333e2#32, 0x3d832fe0#32]
@[expose] def encHwMc2ArgsWords : List (BitVec 32) := [0x913243e0#32, 0x911043e1#32, 0x52807802#32]
@[expose] def encHwIvChkWords : List (BitVec 32) := [0xf10042bf#32, 0x54ffbf60#32]
@[expose] def encDeadErrWords : List (BitVec 32) := [
   0x7100051f#32, 0x54000161#32, 0xaa1f03e9#32, 0x913243e8#32, 0xf903ebe8#32, 0xaa0903ea#32, 0x91000529#32,
   0xf107813f#32, 0x382a691f#32, 0x54ffff81#32, 0x911f43e8#32, 0x14000008#32, 0x913243ea#32, 0x52807808#32,
   0xaa0a03e9#32, 0xf800853f#32, 0xf1002108#32, 0xaa0903ea#32, 0x54ffffa1#32, 0x92800008#32, 0xf9000268#32]
@[expose] def encEpilogueWords : List (BitVec 32) := [
   0x914007ff#32, 0x910303ff#32, 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa94267fa#32, 0xa9416ffc#32,
   0xa8c67bfd#32, 0xd65f03c0#32]
@[expose] def encDeadMiWords : List (BitVec 32) := [0xaa1f03f8#32]
@[expose] def encPanicArgsWords : List (BitVec 32) := [0xaa1803e0#32, 0xaa1403e1#32]
@[expose] def encPanicPreWords : List (BitVec 32) := [0x910103e0#32]
@[expose] def encPanicSetupWords : List (BitVec 32) := [0xd10047a2#32, 0x528004a1#32]

/-- Reachable `584`-instruction prefix (`[0..583]`, `+0x000..+0x91c`) of `aes_256_cbc_encrypt`. -/
@[expose] def aes256CbcEncryptReachableInstrs (fnAddr : BitVec 64) (hw : Aes256EncHwAddrs)
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64) : List Instr :=
  List.flatten [
    decodeWords encPrologWords, [.adr true (.gpr 25#5) (adrpOff (fnAddr + 0x030#64) hw.storageAddr)], decodeWords encSave45Words,
    [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 25#5) (pageLo12 hw.storageAddr))], decodeWords encDisp0Words, decodeWords encSwKsPreWords,
    [.bl (keyScheduleAddr - (fnAddr + 0x060#64))], decodeWords encSwKsMcWords, [.bl (memcpyAddr - (fnAddr + 0x070#64))],
    decodeWords encSwIvChkWords, decodeWords encJoinMc1Words, [.bl (memcpyAddr - (fnAddr + 0x088#64))],
    decodeWords encJoinMc2Words, [.bl (memcpyAddr - (fnAddr + 0x0a0#64))], decodeWords encSizeCalcWords,
    [.bl (shimAddr - (fnAddr + 0x0b0#64))], decodeWords encAllocArgsWords, [.bl (allocZeroedAddr - (fnAddr + 0x0c0#64))],
    decodeWords encPostAllocWords, [.bl (memcpyAddr - (fnAddr + 0x0e8#64))], decodeWords encPadMcWords,
    [.bl (memcpyAddr - (fnAddr + 0x10c#64))], decodeWords encPadMsWords, [.bl (memsetAddr - (fnAddr + 0x120#64))],
    decodeWords encSpillTailWords, [.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x188#64) hw.storageAddr)], [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 hw.storageAddr))],
    decodeWords encLoopDispWords, decodeWords encHwLoopHdrWords, decodeWords encHwLoopPreAWords,
    decodeWords encHwLoopPreBWords, [.bl (hw.hwEncryptAddr - (fnAddr + 0x2b4#64))], decodeWords encHwLoopPostWords,
    decodeWords encSwLoopCbzWords, decodeWords encSwLoopInitWords, decodeWords encSwLoopPreAWords,
    decodeWords encSwLoopPreBWords, [.bl (encryptAddr - (fnAddr + 0x3f8#64))], decodeWords encSwLoopOutWords,
    decodeWords encSwLoopCtWords, decodeWords encSwLoopPrevWords, [.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x4cc#64) hw.storageAddr)],
    [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 hw.storageAddr))], decodeWords encTailDispWords, decodeWords encHwTailPreAWords,
    decodeWords encHwTailPreBWords, [.bl (hw.hwEncryptAddr - (fnAddr + 0x5e0#64))], decodeWords encHwTailPostWords,
    decodeWords encSwTailPreAWords, decodeWords encSwTailPreBWords, [.bl (encryptAddr - (fnAddr + 0x6f0#64))],
    decodeWords encSwTailOutWords, decodeWords encSwTailPrevWords, decodeWords encSwTailCtWords,
    decodeWords encDropArgWords, [.bl (hw.dropDecryptorAddr - (fnAddr + 0x7b8#64))], decodeWords encWriteVecWords,
    decodeWords encInitSaveWords, [.bl (hw.initInnerAddr - (fnAddr + 0x7cc#64))], decodeWords encInitPostWords,
    decodeWords encHwKsArgsWords, [.bl (hw.expandKeyAddr - (fnAddr + 0x7e0#64))], decodeWords encHwInvArgsWords,
    [.bl (hw.invExpandedKeysAddr - (fnAddr + 0x7f0#64))], decodeWords encHwCopyEkWords, [.bl (memcpyAddr - (fnAddr + 0x878#64))],
    decodeWords encHwMc2ArgsWords, [.bl (memcpyAddr - (fnAddr + 0x888#64))], decodeWords encHwIvChkWords,
    [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 25#5) (pageLo12 hw.storageAddr))], decodeWords encDeadErrWords, decodeWords encEpilogueWords,
    decodeWords encDeadMiWords, decodeWords encPanicArgsWords, [.bl (handleErrorAddr - (fnAddr + 0x91c#64))] ]

/-- Unreachable `11`-instruction `unwrap_failed` panic tail (`[584..594]`, `+0x920..+0x948`). -/
@[expose] def aes256CbcEncryptPanicTail
    (fnAddr dropDecryptorAddr : BitVec 64) (p : Aes256CbcEncryptPanicSyms) : List Instr :=
  decodeWords encPanicPreWords ++
  [ .bl (dropDecryptorAddr - (fnAddr + 0x924#64)) ] ++
  adrpAddPair (.gpr 0#5) (fnAddr + 0x928#64) p.msgPtr p.relaxMsg ++
  adrpAddPair (.gpr 3#5) (fnAddr + 0x930#64) p.errPtr p.relaxErr ++
  adrpAddPair (.gpr 4#5) (fnAddr + 0x938#64) p.locPtr p.relaxLoc ++
  decodeWords encPanicSetupWords ++
  [ .bl (p.unwrapFailedAddr - (fnAddr + 0x948#64)) ]

/-- Complete `595`-instruction relocated sequence of `aes_256_cbc_encrypt` (`+0x000..+0x948`). -/
@[expose] def aes256CbcEncryptInstrs (fnAddr : BitVec 64) (hw : Aes256EncHwAddrs)
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64)
    (p : Aes256CbcEncryptPanicSyms := Aes256CbcEncryptPanicSyms.template fnAddr) : List Instr :=
  aes256CbcEncryptReachableInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
    allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr ++
  aes256CbcEncryptPanicTail fnAddr hw.dropDecryptorAddr p

private theorem length_decodeWords (ws : List (BitVec 32)) :
    (decodeWords ws).length = ws.length := by simp [decodeWords]

theorem aes256CbcEncryptReachableInstrs_length (fnAddr : BitVec 64) (hw : Aes256EncHwAddrs)
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64) :
    (aes256CbcEncryptReachableInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr).length = 584 := by
  simp only [aes256CbcEncryptReachableInstrs, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, length_decodeWords]; decide

theorem aes256CbcEncryptInstrs_length (fnAddr : BitVec 64) (hw : Aes256EncHwAddrs)
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64)
    (p : Aes256CbcEncryptPanicSyms) :
    (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p).length = 595 := by
  dsimp only [aes256CbcEncryptInstrs, aes256CbcEncryptPanicTail]
  rw [List.length_append, aes256CbcEncryptReachableInstrs_length]
  simp only [List.length_append, List.length_singleton, length_decodeWords, adrpAddPair_length]; rfl

/-! ## 3. Pre-Split Basic-Block Fetch Bundle (`CbcEncCode`) -/

private theorem hasInstrs_split0 {P : Program} {fnAddr : BitVec 64} (off2 : BitVec 64)
    {xs ys : List Instr} (h : hasInstrs P fnAddr (xs ++ ys))
    (hoff : BitVec.ofNat 64 (4 * xs.length) = off2) :
    hasInstrs P fnAddr xs ∧ hasInstrs P (fnAddr + off2) ys := by
  refine ⟨hasInstrs_prefix h, fun i hi => ?_⟩
  have h1 := h (xs.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
  simp only [Nat.add_sub_cancel_left] at h1
  have had : fnAddr + off2 + BitVec.ofNat 64 (4 * i) =
      fnAddr + BitVec.ofNat 64 (4 * (xs.length + i)) := by
    rw [← hoff, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  rwa [had]

private theorem hasInstrs_split_next {P : Program} {fnAddr off1 : BitVec 64} (off2 : BitVec 64)
    {xs ys : List Instr} (h : hasInstrs P (fnAddr + off1) (xs ++ ys))
    (hoff : off1 + BitVec.ofNat 64 (4 * xs.length) = off2) :
    hasInstrs P (fnAddr + off1) xs ∧ hasInstrs P (fnAddr + off2) ys := by
  refine ⟨hasInstrs_prefix h, fun i hi => ?_⟩
  have h1 := h (xs.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
  simp only [Nat.add_sub_cancel_left] at h1
  have had : fnAddr + off2 + BitVec.ofNat 64 (4 * i) =
      fnAddr + off1 + BitVec.ofNat 64 (4 * (xs.length + i)) := by
    rw [← hoff, ← BitVec.add_assoc fnAddr off1, BitVec.add_assoc _ _ (BitVec.ofNat 64 (4 * i)),
      ← BitVec.ofNat_add, Nat.mul_add]
  rwa [had]

private theorem hasInstrs_singleton {P : Program} {a : BitVec 64} {inst : Instr}
    (h : hasInstrs P a [inst]) : P.fetch a = some inst := by
  simpa using h 0 (by simp)

/-- Pre-split fetch obligations for the reachable `584`-instruction prefix of `aes_256_cbc_encrypt`. -/
structure CbcEncCode (P : Program) (fnAddr : BitVec 64) (hw : Aes256EncHwAddrs)
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64) : Prop where
  segProlog : hasInstrs P fnAddr (decodeWords encPrologWords)
  adrp_st0 : P.fetch (fnAddr + 0x030#64) = some (.adr true (.gpr 25#5) (adrpOff (fnAddr + 0x030#64) hw.storageAddr))
  segSave45 : hasInstrs P (fnAddr + 0x034#64) (decodeWords encSave45Words)
  ldrb_st0 : P.fetch (fnAddr + 0x03c#64) = some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 25#5) (pageLo12 hw.storageAddr)))
  segDisp0 : hasInstrs P (fnAddr + 0x040#64) (decodeWords encDisp0Words)
  segSwKsPre : hasInstrs P (fnAddr + 0x058#64) (decodeWords encSwKsPreWords)
  bl_ks : P.fetch (fnAddr + 0x060#64) = some (.bl (keyScheduleAddr - (fnAddr + 0x060#64)))
  segSwKsMc : hasInstrs P (fnAddr + 0x064#64) (decodeWords encSwKsMcWords)
  bl_swMc : P.fetch (fnAddr + 0x070#64) = some (.bl (memcpyAddr - (fnAddr + 0x070#64)))
  segSwIvChk : hasInstrs P (fnAddr + 0x074#64) (decodeWords encSwIvChkWords)
  segJoinMc1 : hasInstrs P (fnAddr + 0x07c#64) (decodeWords encJoinMc1Words)
  bl_joinMc1 : P.fetch (fnAddr + 0x088#64) = some (.bl (memcpyAddr - (fnAddr + 0x088#64)))
  segJoinMc2 : hasInstrs P (fnAddr + 0x08c#64) (decodeWords encJoinMc2Words)
  bl_joinMc2 : P.fetch (fnAddr + 0x0a0#64) = some (.bl (memcpyAddr - (fnAddr + 0x0a0#64)))
  segSizeCalc : hasInstrs P (fnAddr + 0x0a4#64) (decodeWords encSizeCalcWords)
  bl_shim : P.fetch (fnAddr + 0x0b0#64) = some (.bl (shimAddr - (fnAddr + 0x0b0#64)))
  segAllocArgs : hasInstrs P (fnAddr + 0x0b4#64) (decodeWords encAllocArgsWords)
  bl_alloc : P.fetch (fnAddr + 0x0c0#64) = some (.bl (allocZeroedAddr - (fnAddr + 0x0c0#64)))
  segPostAlloc : hasInstrs P (fnAddr + 0x0c4#64) (decodeWords encPostAllocWords)
  bl_postMc : P.fetch (fnAddr + 0x0e8#64) = some (.bl (memcpyAddr - (fnAddr + 0x0e8#64)))
  segPadMc : hasInstrs P (fnAddr + 0x0ec#64) (decodeWords encPadMcWords)
  bl_padMc : P.fetch (fnAddr + 0x10c#64) = some (.bl (memcpyAddr - (fnAddr + 0x10c#64)))
  segPadMs : hasInstrs P (fnAddr + 0x110#64) (decodeWords encPadMsWords)
  bl_padMs : P.fetch (fnAddr + 0x120#64) = some (.bl (memsetAddr - (fnAddr + 0x120#64)))
  segSpillTail : hasInstrs P (fnAddr + 0x124#64) (decodeWords encSpillTailWords)
  adrp_st1 : P.fetch (fnAddr + 0x188#64) = some (.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x188#64) hw.storageAddr))
  ldrb_st1 : P.fetch (fnAddr + 0x18c#64) = some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 hw.storageAddr)))
  segLoopDisp : hasInstrs P (fnAddr + 0x190#64) (decodeWords encLoopDispWords)
  segHwLoopHdr : hasInstrs P (fnAddr + 0x198#64) (decodeWords encHwLoopHdrWords)
  segHwLoopPreA : hasInstrs P (fnAddr + 0x1a0#64) (decodeWords encHwLoopPreAWords)
  segHwLoopPreB : hasInstrs P (fnAddr + 0x230#64) (decodeWords encHwLoopPreBWords)
  bl_hwLoopEnc : P.fetch (fnAddr + 0x2b4#64) = some (.bl (hw.hwEncryptAddr - (fnAddr + 0x2b4#64)))
  segHwLoopPost : hasInstrs P (fnAddr + 0x2b8#64) (decodeWords encHwLoopPostWords)
  segSwLoopCbz : hasInstrs P (fnAddr + 0x2d0#64) (decodeWords encSwLoopCbzWords)
  segSwLoopInit : hasInstrs P (fnAddr + 0x2d4#64) (decodeWords encSwLoopInitWords)
  segSwLoopPreA : hasInstrs P (fnAddr + 0x320#64) (decodeWords encSwLoopPreAWords)
  segSwLoopPreB : hasInstrs P (fnAddr + 0x38c#64) (decodeWords encSwLoopPreBWords)
  bl_swLoopEnc : P.fetch (fnAddr + 0x3f8#64) = some (.bl (encryptAddr - (fnAddr + 0x3f8#64)))
  segSwLoopOut : hasInstrs P (fnAddr + 0x3fc#64) (decodeWords encSwLoopOutWords)
  segSwLoopCt : hasInstrs P (fnAddr + 0x444#64) (decodeWords encSwLoopCtWords)
  segSwLoopPrev : hasInstrs P (fnAddr + 0x488#64) (decodeWords encSwLoopPrevWords)
  adrp_st2 : P.fetch (fnAddr + 0x4cc#64) = some (.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x4cc#64) hw.storageAddr))
  ldrb_st2 : P.fetch (fnAddr + 0x4d0#64) = some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 hw.storageAddr)))
  segTailDisp : hasInstrs P (fnAddr + 0x4d4#64) (decodeWords encTailDispWords)
  segHwTailPreA : hasInstrs P (fnAddr + 0x4dc#64) (decodeWords encHwTailPreAWords)
  segHwTailPreB : hasInstrs P (fnAddr + 0x568#64) (decodeWords encHwTailPreBWords)
  bl_hwTailEnc : P.fetch (fnAddr + 0x5e0#64) = some (.bl (hw.hwEncryptAddr - (fnAddr + 0x5e0#64)))
  segHwTailPost : hasInstrs P (fnAddr + 0x5e4#64) (decodeWords encHwTailPostWords)
  segSwTailPreA : hasInstrs P (fnAddr + 0x5f4#64) (decodeWords encSwTailPreAWords)
  segSwTailPreB : hasInstrs P (fnAddr + 0x684#64) (decodeWords encSwTailPreBWords)
  bl_swTailEnc : P.fetch (fnAddr + 0x6f0#64) = some (.bl (encryptAddr - (fnAddr + 0x6f0#64)))
  segSwTailOut : hasInstrs P (fnAddr + 0x6f4#64) (decodeWords encSwTailOutWords)
  segSwTailPrev : hasInstrs P (fnAddr + 0x734#64) (decodeWords encSwTailPrevWords)
  segSwTailCt : hasInstrs P (fnAddr + 0x774#64) (decodeWords encSwTailCtWords)
  segDropArg : hasInstrs P (fnAddr + 0x7b4#64) (decodeWords encDropArgWords)
  bl_drop : P.fetch (fnAddr + 0x7b8#64) = some (.bl (hw.dropDecryptorAddr - (fnAddr + 0x7b8#64)))
  segWriteVec : hasInstrs P (fnAddr + 0x7bc#64) (decodeWords encWriteVecWords)
  segInitSave : hasInstrs P (fnAddr + 0x7c8#64) (decodeWords encInitSaveWords)
  bl_init : P.fetch (fnAddr + 0x7cc#64) = some (.bl (hw.initInnerAddr - (fnAddr + 0x7cc#64)))
  segInitPost : hasInstrs P (fnAddr + 0x7d0#64) (decodeWords encInitPostWords)
  segHwKsArgs : hasInstrs P (fnAddr + 0x7d8#64) (decodeWords encHwKsArgsWords)
  bl_hwExp : P.fetch (fnAddr + 0x7e0#64) = some (.bl (hw.expandKeyAddr - (fnAddr + 0x7e0#64)))
  segHwInvArgs : hasInstrs P (fnAddr + 0x7e4#64) (decodeWords encHwInvArgsWords)
  bl_hwInv : P.fetch (fnAddr + 0x7f0#64) = some (.bl (hw.invExpandedKeysAddr - (fnAddr + 0x7f0#64)))
  segHwCopyEk : hasInstrs P (fnAddr + 0x7f4#64) (decodeWords encHwCopyEkWords)
  bl_hwMc1 : P.fetch (fnAddr + 0x878#64) = some (.bl (memcpyAddr - (fnAddr + 0x878#64)))
  segHwMc2Args : hasInstrs P (fnAddr + 0x87c#64) (decodeWords encHwMc2ArgsWords)
  bl_hwMc2 : P.fetch (fnAddr + 0x888#64) = some (.bl (memcpyAddr - (fnAddr + 0x888#64)))
  segHwIvChk : hasInstrs P (fnAddr + 0x88c#64) (decodeWords encHwIvChkWords)
  ldrb_stErr : P.fetch (fnAddr + 0x894#64) = some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 25#5) (pageLo12 hw.storageAddr)))
  segDeadErr : hasInstrs P (fnAddr + 0x898#64) (decodeWords encDeadErrWords)
  segEpilogue : hasInstrs P (fnAddr + 0x8ec#64) (decodeWords encEpilogueWords)
  segDeadMi : hasInstrs P (fnAddr + 0x910#64) (decodeWords encDeadMiWords)
  segPanicArgs : hasInstrs P (fnAddr + 0x914#64) (decodeWords encPanicArgsWords)
  bl_handleErr : P.fetch (fnAddr + 0x91c#64) = some (.bl (handleErrorAddr - (fnAddr + 0x91c#64)))

theorem CbcEncCode.of_hasInstrs {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    (hc : hasInstrs P fnAddr
      (aes256CbcEncryptReachableInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)) :
    CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr := by
  simp only [aes256CbcEncryptReachableInstrs, List.flatten_cons, List.flatten_nil, List.append_nil] at hc
  rcases hasInstrs_split0 0x030#64 hc rfl with ⟨h0, hc⟩; rcases hasInstrs_split_next 0x034#64 hc rfl with ⟨h1, hc⟩
  rcases hasInstrs_split_next 0x03c#64 hc rfl with ⟨h2, hc⟩; rcases hasInstrs_split_next 0x040#64 hc rfl with ⟨h3, hc⟩
  rcases hasInstrs_split_next 0x058#64 hc rfl with ⟨h4, hc⟩; rcases hasInstrs_split_next 0x060#64 hc rfl with ⟨h5, hc⟩
  rcases hasInstrs_split_next 0x064#64 hc rfl with ⟨h6, hc⟩; rcases hasInstrs_split_next 0x070#64 hc rfl with ⟨h7, hc⟩
  rcases hasInstrs_split_next 0x074#64 hc rfl with ⟨h8, hc⟩; rcases hasInstrs_split_next 0x07c#64 hc rfl with ⟨h9, hc⟩
  rcases hasInstrs_split_next 0x088#64 hc rfl with ⟨h10, hc⟩; rcases hasInstrs_split_next 0x08c#64 hc rfl with ⟨h11, hc⟩
  rcases hasInstrs_split_next 0x0a0#64 hc rfl with ⟨h12, hc⟩; rcases hasInstrs_split_next 0x0a4#64 hc rfl with ⟨h13, hc⟩
  rcases hasInstrs_split_next 0x0b0#64 hc rfl with ⟨h14, hc⟩; rcases hasInstrs_split_next 0x0b4#64 hc rfl with ⟨h15, hc⟩
  rcases hasInstrs_split_next 0x0c0#64 hc rfl with ⟨h16, hc⟩; rcases hasInstrs_split_next 0x0c4#64 hc rfl with ⟨h17, hc⟩
  rcases hasInstrs_split_next 0x0e8#64 hc rfl with ⟨h18, hc⟩; rcases hasInstrs_split_next 0x0ec#64 hc rfl with ⟨h19, hc⟩
  rcases hasInstrs_split_next 0x10c#64 hc rfl with ⟨h20, hc⟩; rcases hasInstrs_split_next 0x110#64 hc rfl with ⟨h21, hc⟩
  rcases hasInstrs_split_next 0x120#64 hc rfl with ⟨h22, hc⟩; rcases hasInstrs_split_next 0x124#64 hc rfl with ⟨h23, hc⟩
  rcases hasInstrs_split_next 0x188#64 hc rfl with ⟨h24, hc⟩; rcases hasInstrs_split_next 0x18c#64 hc rfl with ⟨h25, hc⟩
  rcases hasInstrs_split_next 0x190#64 hc rfl with ⟨h26, hc⟩; rcases hasInstrs_split_next 0x198#64 hc rfl with ⟨h27, hc⟩
  rcases hasInstrs_split_next 0x1a0#64 hc rfl with ⟨h28, hc⟩; rcases hasInstrs_split_next 0x230#64 hc rfl with ⟨h29, hc⟩
  rcases hasInstrs_split_next 0x2b4#64 hc rfl with ⟨h30, hc⟩; rcases hasInstrs_split_next 0x2b8#64 hc rfl with ⟨h31, hc⟩
  rcases hasInstrs_split_next 0x2d0#64 hc rfl with ⟨h32, hc⟩; rcases hasInstrs_split_next 0x2d4#64 hc rfl with ⟨h33, hc⟩
  rcases hasInstrs_split_next 0x320#64 hc rfl with ⟨h34, hc⟩; rcases hasInstrs_split_next 0x38c#64 hc rfl with ⟨h35, hc⟩
  rcases hasInstrs_split_next 0x3f8#64 hc rfl with ⟨h36, hc⟩; rcases hasInstrs_split_next 0x3fc#64 hc rfl with ⟨h37, hc⟩
  rcases hasInstrs_split_next 0x444#64 hc rfl with ⟨h38, hc⟩; rcases hasInstrs_split_next 0x488#64 hc rfl with ⟨h39, hc⟩
  rcases hasInstrs_split_next 0x4cc#64 hc rfl with ⟨h40, hc⟩; rcases hasInstrs_split_next 0x4d0#64 hc rfl with ⟨h41, hc⟩
  rcases hasInstrs_split_next 0x4d4#64 hc rfl with ⟨h42, hc⟩; rcases hasInstrs_split_next 0x4dc#64 hc rfl with ⟨h43, hc⟩
  rcases hasInstrs_split_next 0x568#64 hc rfl with ⟨h44, hc⟩; rcases hasInstrs_split_next 0x5e0#64 hc rfl with ⟨h45, hc⟩
  rcases hasInstrs_split_next 0x5e4#64 hc rfl with ⟨h46, hc⟩; rcases hasInstrs_split_next 0x5f4#64 hc rfl with ⟨h47, hc⟩
  rcases hasInstrs_split_next 0x684#64 hc rfl with ⟨h48, hc⟩; rcases hasInstrs_split_next 0x6f0#64 hc rfl with ⟨h49, hc⟩
  rcases hasInstrs_split_next 0x6f4#64 hc rfl with ⟨h50, hc⟩; rcases hasInstrs_split_next 0x734#64 hc rfl with ⟨h51, hc⟩
  rcases hasInstrs_split_next 0x774#64 hc rfl with ⟨h52, hc⟩; rcases hasInstrs_split_next 0x7b4#64 hc rfl with ⟨h53, hc⟩
  rcases hasInstrs_split_next 0x7b8#64 hc rfl with ⟨h54, hc⟩; rcases hasInstrs_split_next 0x7bc#64 hc rfl with ⟨h55, hc⟩
  rcases hasInstrs_split_next 0x7c8#64 hc rfl with ⟨h56, hc⟩; rcases hasInstrs_split_next 0x7cc#64 hc rfl with ⟨h57, hc⟩
  rcases hasInstrs_split_next 0x7d0#64 hc rfl with ⟨h58, hc⟩; rcases hasInstrs_split_next 0x7d8#64 hc rfl with ⟨h59, hc⟩
  rcases hasInstrs_split_next 0x7e0#64 hc rfl with ⟨h60, hc⟩; rcases hasInstrs_split_next 0x7e4#64 hc rfl with ⟨h61, hc⟩
  rcases hasInstrs_split_next 0x7f0#64 hc rfl with ⟨h62, hc⟩; rcases hasInstrs_split_next 0x7f4#64 hc rfl with ⟨h63, hc⟩
  rcases hasInstrs_split_next 0x878#64 hc rfl with ⟨h64, hc⟩; rcases hasInstrs_split_next 0x87c#64 hc rfl with ⟨h65, hc⟩
  rcases hasInstrs_split_next 0x888#64 hc rfl with ⟨h66, hc⟩; rcases hasInstrs_split_next 0x88c#64 hc rfl with ⟨h67, hc⟩
  rcases hasInstrs_split_next 0x894#64 hc rfl with ⟨h68, hc⟩; rcases hasInstrs_split_next 0x898#64 hc rfl with ⟨h69, hc⟩
  rcases hasInstrs_split_next 0x8ec#64 hc rfl with ⟨h70, hc⟩; rcases hasInstrs_split_next 0x910#64 hc rfl with ⟨h71, hc⟩
  rcases hasInstrs_split_next 0x914#64 hc rfl with ⟨h72, hc⟩; rcases hasInstrs_split_next 0x91c#64 hc rfl with ⟨h73, hc⟩
  exact ⟨
    h0, hasInstrs_singleton h1, h2, hasInstrs_singleton h3, h4, h5,
    hasInstrs_singleton h6, h7, hasInstrs_singleton h8, h9, h10, hasInstrs_singleton h11,
    h12, hasInstrs_singleton h13, h14, hasInstrs_singleton h15, h16, hasInstrs_singleton h17,
    h18, hasInstrs_singleton h19, h20, hasInstrs_singleton h21, h22, hasInstrs_singleton h23,
    h24, hasInstrs_singleton h25, hasInstrs_singleton h26, h27, h28, h29,
    h30, hasInstrs_singleton h31, h32, h33, h34, h35,
    h36, hasInstrs_singleton h37, h38, h39, h40, hasInstrs_singleton h41,
    hasInstrs_singleton h42, h43, h44, h45, hasInstrs_singleton h46, h47,
    h48, h49, hasInstrs_singleton h50, h51, h52, h53,
    h54, hasInstrs_singleton h55, h56, h57, hasInstrs_singleton h58, h59,
    h60, hasInstrs_singleton h61, h62, hasInstrs_singleton h63, h64, hasInstrs_singleton h65,
    h66, hasInstrs_singleton h67, h68, hasInstrs_singleton h69, h70, h71,
    h72, h73, hasInstrs_singleton hc⟩

/-! ## 4. Callee Contract Bundle (`Aes256CbcEncryptCallees`) -/

/-- Callee contract bundle for `signal_crypto::aes_cbc::aes_256_cbc_encrypt`. -/
structure Aes256CbcEncryptCallees (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : Program) (hw : Aes256EncHwAddrs)
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    (keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64) : Prop where
  initInner_ok : subroutine_ok P hw.initInnerAddr (aesInitInnerSpec M hSplit.base hw.storageAddr lim)
  expandKey_ok : subroutine_ok P hw.expandKeyAddr (expandKey15RegionSpec hw.rconAddr)
  invExpandedKeys_ok : subroutine_ok P hw.invExpandedKeysAddr invExpandedKeys15RegionSpec
  hwEncrypt_ok : subroutine_ok P hw.hwEncryptAddr encrypt15InplaceSpec
  dropDecryptor_ok : subroutine_ok P hw.dropDecryptorAddr (dropDecryptorSpec hw.storageAddr)
  keySchedule_ok : subroutine_ok P keyScheduleAddr aes256KeyScheduleSpec
  encrypt_ok : subroutine_ok P encryptAddr aes256EncryptSpec
  shim_ok : subroutine_ok P shimAddr rustAllocShimVmSpec
  allocZeroed_ok : subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase M hSplit.base lim)
  memcpy_ok : subroutine_ok P memcpyAddr allocMemcpyVmSpec
  memset_ok : subroutine_ok P memsetAddr allocMemsetVmSpec
  handleError_ok : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec

/-- Construct `Aes256CbcEncryptCallees` from `Armv8` & `Fixslice64` `hasInstrs` / `AesInitInnerCode`
    witnesses plus `hSplit.base` `allocZeroed` and `RustStd` auxiliary contracts. -/
theorem Aes256CbcEncryptCallees.of_hasInstrs {M : AllocCostModel} {A : RustCliAllocBudget M}
    (lim : BudgetLimits) {P : Program} {hw : Aes256EncHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr] {relaxRcon : Bool}
    {keyScheduleAddr encryptAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr
      mixColumns1Addr mixColumns3Addr invBitsliceAddr
      shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    (hInitInner : AesInitInnerCode P hw.initInnerAddr hw.getauxvalHwcapAddr
      hw.getauxvalAddr hw.errnoLocationAddr hSplit.libcAddr hw.storageAddr)
    (hExpandKey : hasInstrs P hw.expandKeyAddr
      (expandKey15ReachableInstrs hw.expandKeyAddr hw.rconAddr relaxRcon))
    (hInvExpand : hasInstrs P hw.invExpandedKeysAddr invExpandedKeys15Instrs)
    (hHwEnc : hasInstrs P hw.hwEncryptAddr encrypt15Instrs)
    (hDrop : hasInstrs P hw.dropDecryptorAddr
      (dropDecryptorInstrs hw.dropDecryptorAddr hw.storageAddr))
    (hKs : hasInstrs P keyScheduleAddr
      (aes256KeyScheduleInstrs keyScheduleAddr memsetAddr bitsliceAddr memshift32Addr
        subBytesAddr xorColumnsAddr memcpyAddr))
    (hEnc : hasInstrs P encryptAddr
      (aes256EncryptInstrs encryptAddr bitsliceAddr subBytesAddr
        mixColumns1Addr mixColumns3Addr invBitsliceAddr))
    (hBitslice : hasInstrs P bitsliceAddr bitsliceInstrs)
    (hMemshift32 : hasInstrs P memshift32Addr memshift32ReachableInstrs)
    (hSubBytes : hasInstrs P subBytesAddr subBytesInstrs)
    (hXorColumns : hasInstrs P xorColumnsAddr xorColumnsReachableInstrs)
    (hMix1 : hasInstrs P mixColumns1Addr mixColumns1Instrs)
    (hMix3 : hasInstrs P mixColumns3Addr mixColumns3Instrs)
    (hInvBitslice : hasInstrs P invBitsliceAddr invBitsliceInstrs)
    (hAllocZeroed : subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase M hSplit.base lim))
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr where
  initInner_ok := hSplit.initInner_ok lim hInitInner
  expandKey_ok := expandKey15_region_subroutine_ok hExpandKey
  invExpandedKeys_ok := invExpandedKeys15_region_subroutine_ok hInvExpand
  hwEncrypt_ok := encrypt15_inplace_subroutine_ok hHwEnc
  dropDecryptor_ok := dropDecryptor_subroutine_ok hDrop
  keySchedule_ok := aes256KeySchedule_ok hKs
    (Aes256KeyScheduleCallees.of_hasInstrs hMemset hBitslice hMemshift32
      hSubBytes hXorColumns hAux.memcpy_ok)
  encrypt_ok := aes256Encrypt_ok hEnc
    (Aes256EncryptCallees.of_hasInstrs hBitslice hSubBytes hMix1 hMix3 hInvBitslice)
  shim_ok := hAux.shim_ok
  allocZeroed_ok := hAllocZeroed
  memcpy_ok := hAux.memcpy_ok
  memset_ok := hMemset
  handleError_ok := hAux.handleError_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
