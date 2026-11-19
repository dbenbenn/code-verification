/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Configurations, Slot Maps, & Row States (`Seg2Defs`)

1. `B28`/`B29` call specs on `B07`, `KCfg` instances (`cfgA..cfgD`), and 25-lane `KSlot` tables.
2. `RejSiteConfig` instances (`rejCfgInit3`, `rejCfgExtra1`) and `FetchesInstrsAt` certificates.
3. `MemAHeaderOk`, `RowCalleeGprs`, `RowExtraState`, `RowMidState`, `RowExitState`, and
   `MultiLaneSampled`/`MultiLaneSlots`/`BTreeMem` spatial bridges.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemMemcpySpec
  mlkemMemsetSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok
  blk29_memset_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakAbsorb
  keccakPermuteN
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake128BlockAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE
  packHalfwordsLE_length
  packHalfwordsLE_replicate_zero
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled
  MultiLaneSepFrom
  MultiLaneSlots
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (
  RejVariant
  checkWordsAtTree
  fetchesInstrsAt_of_wordTree
  rejInnerInstrs
  rejInnerWords
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig
  rejOuterInstrs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv
  MultiLaneXofInv
  allLanesDone
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq
  blk07_tree_size
  blkLib07
  blkPC07
  blkPl07
  blkPlaceable07
  blkTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree
  KCfg
  KSlot
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem
  BTreeMemFrom
  BTreeMem_entails_memRegion
  KCfgValid
  blk07NoRelocInRange
  btreeBytesFrom
  bytesToBTree9
  checkInstrsAt07
  fetchesInstrsAt_blk07_range
  pointsToBytes_eq_btreeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)

/-! ## 1. `B28`/`B29` Call Specs, `KCfg` Instances, & 25-Lane `KSlot` Maps -/

@[expose] def rcSym : String :=
  "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"

theorem blk28_memcpy_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk28_memcpy_ok

theorem blk29_memset_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk29_memset_ok

@[expose] def cfgA : KCfg := { offA := 144, lenA := 286, offB := 28848, lenB := 0 }
@[expose] def cfgB : KCfg := { offA := 144, lenA := 286, offB := 28848, lenB := 252 }
@[expose] def cfgC : KCfg := { offA := 144, lenA := 286, offB := 26768, lenB := 84 }
@[expose] def cfgD : KCfg := { offA := 2560, lenA := 272, offB := 26768, lenB := 0 }

theorem cfgA_valid : KCfgValid cfgA := by decide
theorem cfgB_valid : KCfgValid cfgB := by decide
theorem cfgC_valid : KCfgValid cfgC := by decide
theorem cfgD_valid : KCfgValid cfgD := by decide

@[expose] def slotsL1 : List KSlot :=
  [.vreg 0, .vreg 24, .vreg 29, .vreg 5, .vreg 14,
   .vreg 19, .vreg 23, .spillQ 1664, .vreg 12, .vreg 11,
   .vreg 21, .vreg 22, .vreg 27, .vreg 9, .vreg 15,
   .vreg 13, .vreg 31, .vreg 30, .vreg 26, .vreg 7,
   .vreg 25, .vreg 28, .vreg 8, .vreg 17, .vreg 20]

@[expose] def slotsL2 : List KSlot :=
  [.vreg 6, .vreg 23, .vreg 28, .vreg 8, .spillQ 1904,
   .vreg 20, .vreg 22, .spillQ 1488, .vreg 9, .spillQ 1520,
   .vreg 15, .vreg 14, .vreg 30, .vreg 26, .vreg 12,
   .vreg 25, .vreg 29, .vreg 4, .vreg 11, .vreg 17,
   .vreg 16, .vreg 27, .vreg 31, .vreg 18, .vreg 19]

@[expose] def slotsFa8_01 : List KSlot :=
  [.spillQ 784, .spillQ 1536, .spillQ 1552, .spillQ 2048, .spillQ 1712,
   .spillQ 1008, .spillQ 1056, .spillQ 1664, .spillQ 1568, .spillQ 1584,
   .spillQ 976, .spillQ 1040, .spillQ 1072, .spillQ 1680, .spillQ 1088,
   .spillQ 960, .spillQ 992, .spillQ 1024, .spillQ 800, .spillQ 1696,
   .spillQ 816, .spillQ 1248, .spillQ 2192, .spillQ 2032, .spillQ 2352]

@[expose] def slotsFa8_23 : List KSlot :=
  [.spillQ 688, .spillQ 1472, .spillQ 736, .spillQ 768, .spillQ 1904,
   .spillQ 720, .spillQ 752, .spillQ 1488, .spillQ 1504, .spillQ 1520,
   .spillQ 848, .spillQ 896, .spillQ 912, .spillQ 944, .spillQ 1648,
   .spillQ 832, .spillQ 864, .spillQ 880, .spillQ 928, .spillQ 1632,
   .spillQ 704, .spillQ 1232, .spillQ 1728, .spillQ 2016, .spillQ 2320]

@[expose] def slotsL3 : List KSlot :=
  [.vreg 14, .vreg 2, .vreg 7, .vreg 31, .spillQ 1616,
   .vreg 18, .vreg 23, .vreg 29, .vreg 8, .vreg 9,
   .vreg 20, .vreg 26, .vreg 30, .vreg 15, .vreg 12,
   .vreg 11, .vreg 25, .vreg 13, .vreg 10, .vreg 6,
   .vreg 24, .vreg 27, .vreg 19, .vreg 16, .vreg 17]

@[expose] def slotsL4 : List KSlot :=
  [.vreg 6, .vreg 8, .vreg 7, .vreg 4, .vreg 23,
   .vreg 18, .vreg 14, .vreg 22, .vreg 29, .vreg 9,
   .vreg 11, .vreg 10, .vreg 24, .vreg 15, .vreg 12,
   .vreg 30, .vreg 25, .vreg 13, .vreg 21, .vreg 26,
   .vreg 28, .vreg 27, .vreg 19, .vreg 16, .vreg 17]

@[expose] def slotsL5 : List KSlot :=
  [.vreg 14, .vreg 15, .vreg 9, .spillQ 1600, .spillQ 2000,
   .vreg 18, .vreg 22, .vreg 11, .spillQ 1888, .spillQ 1984,
   .vreg 29, .vreg 13, .vreg 12, .vreg 25, .vreg 10,
   .vreg 31, .vreg 20, .vreg 28, .vreg 27, .vreg 17,
   .vreg 30, .vreg 23, .vreg 21, .vreg 26, .vreg 16]

@[expose] def slotsL6 : List KSlot :=
  [.vreg 2, .vreg 5, .vreg 11, .spillQ 2208, .spillQ 2384,
   .spillQ 2224, .spillQ 2272, .spillQ 1952, .vreg 8, .vreg 1,
   .vreg 12, .vreg 14, .spillQ 1776, .spillQ 2240, .vreg 7,
   .spillQ 1920, .vreg 3, .vreg 6, .vreg 24, .vreg 29,
   .vreg 31, .vreg 15, .vreg 4, .vreg 26, .vreg 16]

@[expose] def slotsMidInit01 : List KSlot :=
  [.vreg 1, .vreg 8, .vreg 15, .spillQ 2336, .spillQ 2416,
   .spillQ 1744, .spillQ 1824, .spillQ 2160, .spillQ 1216, .spillQ 2304,
   .spillQ 1184, .spillQ 1200, .vreg 26, .spillQ 2176, .spillQ 1872,
   .spillQ 2080, .vreg 17, .vreg 16, .vreg 28, .spillQ 2144,
   .vreg 5, .spillQ 1248, .vreg 0, .spillQ 2032, .spillQ 2352]

@[expose] def slotsMidInit23 : List KSlot :=
  [.spillQ 1168, .spillQ 2128, .spillQ 2064, .spillQ 2208, .spillQ 2384,
   .spillQ 2224, .vreg 30, .spillQ 1952, .spillQ 1968, .spillQ 2368,
   .spillQ 2112, .spillQ 2000, .vreg 2, .vreg 20, .spillQ 2288,
   .spillQ 1920, .spillQ 1936, .spillQ 1760, .spillQ 1792, .vreg 21,
   .vreg 18, .spillQ 1232, .spillQ 1728, .spillQ 2016, .spillQ 2320]

@[expose] def slotsMidExtra01 : List KSlot :=
  [.spillQ 1136, .spillQ 2096, .spillQ 2400, .spillQ 2336, .spillQ 2416,
   .spillQ 1744, .spillQ 1824, .spillQ 2160, .spillQ 1216, .spillQ 2304,
   .spillQ 1184, .spillQ 1200, .spillQ 1840, .spillQ 2176, .spillQ 1872,
   .spillQ 2080, .spillQ 1152, .spillQ 1808, .spillQ 1856, .spillQ 2144,
   .spillQ 1120, .spillQ 1248, .spillQ 2192, .spillQ 2032, .spillQ 2352]

@[expose] def slotsMidExtra23 : List KSlot :=
  [.vreg 21, .spillQ 2128, .spillQ 2064, .spillQ 2208, .spillQ 2384,
   .spillQ 2224, .vreg 30, .spillQ 1952, .vreg 4, .spillQ 2368,
   .spillQ 2112, .vreg 27, .vreg 2, .vreg 20, .vreg 7,
   .vreg 1, .vreg 26, .spillQ 1760, .vreg 17, .vreg 19,
   .vreg 18, .vreg 23, .spillQ 1728, .vreg 10, .vreg 31]

@[expose] def slotsInv01 : List KSlot :=
  [.vreg 1, .vreg 8, .vreg 15, .spillQ 2336, .vreg 3,
   .spillQ 1744, .spillQ 1824, .vreg 22, .vreg 9, .vreg 7,
   .vreg 4, .vreg 25, .vreg 26, .vreg 14, .spillQ 1872,
   .spillQ 2080, .vreg 17, .vreg 16, .vreg 28, .spillQ 2144,
   .vreg 5, .vreg 29, .vreg 0, .vreg 6, .vreg 13]

@[expose] def slotsInv23 : List KSlot :=
  [.spillQ 1168, .spillQ 2128, .spillQ 2064, .spillQ 2208, .spillQ 2384,
   .spillQ 2224, .vreg 30, .spillQ 1952, .spillQ 1968, .spillQ 2368,
   .spillQ 2112, .spillQ 2000, .vreg 2, .vreg 20, .vreg 11,
   .spillQ 1920, .spillQ 1936, .spillQ 1760, .spillQ 1792, .vreg 21,
   .vreg 18, .vreg 31, .vreg 23, .spillQ 2016, .spillQ 2320]

@[expose] def slotsL7 : List KSlot :=
  [.vreg 1, .vreg 5, .vreg 15, .vreg 11, .vreg 3,
   .vreg 2, .vreg 27, .vreg 22, .vreg 9, .vreg 31,
   .vreg 4, .vreg 25, .vreg 26, .vreg 14, .vreg 17,
   .spillQ 2080, .vreg 12, .vreg 16, .vreg 28, .vreg 23,
   .vreg 10, .vreg 29, .vreg 24, .vreg 6, .vreg 13]

@[expose] def slotsL8 : List KSlot :=
  [.vreg 21, .spillQ 2128, .spillQ 2064, .spillQ 2208, .spillQ 2384,
   .spillQ 2224, .vreg 28, .vreg 15, .vreg 16, .spillQ 2368,
   .spillQ 2112, .vreg 27, .vreg 22, .vreg 26, .vreg 7,
   .vreg 24, .vreg 17, .vreg 10, .vreg 14, .vreg 25,
   .vreg 18, .vreg 9, .vreg 23, .vreg 19, .vreg 20]

/-! ## 2. `RejSiteConfig` Instances (`rejCfgInit3`, `rejCfgExtra1`) & Fetch Certificates -/

@[expose] def rejCfgInit3 : RejSiteConfig :=
  { v := .varB
    nLanes := 4
    nChunks := 21
    slotStride := 544
    rIdx := .x8
    rSqPtr := .x9
    rPrevIdx := .x10
    rSampArr := .x26
    rSlotStride := .x27
    rSlotsBase := .x19 }

@[expose] def rejCfgExtra1 : RejSiteConfig :=
  { v := .varB
    nLanes := 4
    nChunks := 7
    slotStride := 544
    rIdx := .x10
    rSqPtr := .x8
    rPrevIdx := .x9
    rSampArr := .x26
    rSlotStride := .x27
    rSlotsBase := .x19 }

theorem rejCfgInit3_valid : rejCfgInit3.Valid := by decide
theorem rejCfgExtra1_valid : rejCfgExtra1.Valid := by decide

private theorem chk_rejInit3_outer : checkInstrsAt07 2417 (rejOuterInstrs rejCfgInit3) = true := by
  decide +kernel

private theorem chk_rejInit3_inner :
    checkWordsAtTree blkTree07 blkLib07 (0x25c4 + 44) (rejInnerWords .varB) = true := by
  decide +kernel

private theorem chk_rejExtra1_outer : checkInstrsAt07 3289 (rejOuterInstrs rejCfgExtra1) = true := by
  decide +kernel

private theorem chk_rejExtra1_inner :
    checkWordsAtTree blkTree07 blkLib07 (0x3364 + 44) (rejInnerWords .varB) = true := by
  decide +kernel

theorem fetches_rejInit3_outer [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC07.rebase b (fun _ => none)) (b + 0x25c4#64) 0
      (rejOuterInstrs rejCfgInit3) :=
  fetchesInstrsAt_blk07_range (b := b) (wSite := 2417) (baseIdx := 0) (wHi := 2430)
    (by decide +kernel) (by decide) (by decide) chk_rejInit3_outer

theorem fetches_rejInit3_inner [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC07.rebase b (fun _ => none)) (b + 0x25c4#64) 11
      (rejInnerInstrs .varB) :=
  fetchesInstrsAt_of_wordTree blk07_code_eq blk07_tree_size blkPlaceable07
    (siteOff := 0x25c4) (b := b) (X := fun _ => none) (v := .varB)
    (by decide) (by decide) (by decide) chk_rejInit3_inner

theorem fetches_rejExtra1_outer [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC07.rebase b (fun _ => none)) (b + 0x3364#64) 0
      (rejOuterInstrs rejCfgExtra1) :=
  fetchesInstrsAt_blk07_range (b := b) (wSite := 3289) (baseIdx := 0) (wHi := 3302)
    (by decide +kernel) (by decide) (by decide) chk_rejExtra1_outer

theorem fetches_rejExtra1_inner [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC07.rebase b (fun _ => none)) (b + 0x3364#64) 11
      (rejInnerInstrs .varB) :=
  fetchesInstrsAt_of_wordTree blk07_code_eq blk07_tree_size blkPlaceable07
    (siteOff := 0x3364) (b := b) (X := fun _ => none) (v := .varB)
    (by decide) (by decide) (by decide) chk_rejExtra1_inner

/-! ## 3. Row Header, Callee GPRs, Row Loop States, & Spatial Bridges -/

@[expose] def MemAHeaderOk (sp : BitVec 64) (rho : List (BitVec 8)) (tA : BTree (BitVec 64) 9) : Prop :=
  tA.get 0 = 0x00000000001f0300#64 ∧
  tA.get 1 = 0#64 ∧
  tA.get 2 = 0x00000000001f0200#64 ∧
  tA.get 3 = 0#64 ∧
  tA.get 4 = 0x00000000001f0100#64 ∧
  tA.get 5 = 0#64 ∧
  tA.get 7 = sp + 26779#64 ∧
  tA.get 8 = sp + 28859#64 ∧
  tA.get 9 = sp + 29112#64 ∧
  tA.get 14 = 0xffffffffff0000ff#64 ∧
  tA.get 15 = 0xffffffffffffffff#64 ∧
  tA.get 16 = rhoW rho 3 ∧
  tA.get 17 = rhoW rho 3 ∧
  tA.get 18 = rhoW rho 2 ∧
  tA.get 19 = rhoW rho 2 ∧
  tA.get 20 = rhoW rho 1 ∧
  tA.get 21 = rhoW rho 1 ∧
  tA.get 22 = rhoW rho 0 ∧
  tA.get 23 = rhoW rho 0

@[expose] def RowCalleeGprs (sp rcBase : BitVec 64) (row : Nat) (s : State) : Prop :=
  s.readReg64 .x19 = sp + 2560#64 ∧
  s.readReg64 .x20 = BitVec.ofNat 64 row ∧
  s.readReg64 .x21 = rcBase ∧
  s.readReg64 .x22 = sp + 26768#64 ∧
  s.readReg64 .x23 = sp + 26779#64 ∧
  s.readReg64 .x24 = sp + 27032#64 ∧
  s.readReg64 .x25 = 256#64 ∧
  s.readReg64 .x26 = sp + 24720#64 ∧
  s.readReg64 .x27 = 544#64 ∧
  s.readReg64 .fp = sp + 33008#64

@[expose] def RowExtraState [MlKemPlacement] (b sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (extra : Nat) (st : State) (P : SepProp) : Prop :=
  st.pc = b + 0x29ac#64 ∧
  st.status = .Running ∧
  st.sp = sp ∧
  st.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl st.mem ∧
  MlKemRoOk mlkemMpl st.mem ∧
  RowCalleeGprs sp rcBase row st ∧
  st.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  ∃ (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk sp rho tA ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC st tA (slotsInv01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC st tA (slotsInv23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64)) ∧
    MultiLaneXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    (P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 24720#64) 4 sampled ∗
      MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
      memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗
      Rest)

@[expose] def RowMidState [MlKemPlacement] (sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (extra : Nat) (sm : State) (Pm : SepProp) : Prop :=
  sm.sp = sp ∧
  sm.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
  MlKemRoOk mlkemMpl sm.mem ∧
  RowCalleeGprs sp rcBase row sm ∧
  sm.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  sm.readReg64 .x10 = 0#64 ∧
  sm.readReg64 .x8 = sp + 26779#64 ∧
  ∃ (tA tB : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk sp rho tA ∧
    (∀ c, c < 4 → btreeBytesFrom (21 * c) 21 tB = shake128BlockAt (rowSeed rho row c) (extra + 3)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC sm tA (slotsMidExtra01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC sm tA (slotsMidExtra23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64)) ∧
    MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      BTreeMem (sp + 26768#64) 84 tB ∗
      MultiLaneSampled (sp + 24720#64) 4 sampled ∗
      MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
      memRegion (sp + 28848#64) 2016 ∗
      Rest)

@[expose] def RowExitState [MlKemPlacement] (sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  sf.sp = sp ∧
  sf.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  RowCalleeGprs sp rcBase row sf ∧
  sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  ∃ (extra : Nat) (tA : BTree (BitVec 64) 9)
    (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk sp rho tA ∧
    MultiLaneXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    allLanesDone 4 (fun c => rowSeed rho row c) extra = true ∧
    (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 24720#64) 4 sampled ∗
      MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
      memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗
      Rest)


@[expose] def slotBytes4 (hws : Nat → List (BitVec 16)) : List (BitVec 8) :=
  packHalfwordsLE (hws 0) ++ packHalfwordsLE (hws 1) ++
    packHalfwordsLE (hws 2) ++ packHalfwordsLE (hws 3)

theorem slotBytes4_length {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (h3 : (hws 3).length = 272) :
    (slotBytes4 hws).length = 2176 := by
  simp [slotBytes4, packHalfwordsLE_length, h0, h1, h2, h3]

theorem slotBytes4_drop_take {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (h3 : (hws 3).length = 272)
    {c : Nat} (hc : c < 4) :
    ((slotBytes4 hws).drop (544 * c)).take 512 = (packHalfwordsLE (hws c)).take 512 := by
  have l0 : (packHalfwordsLE (hws 0)).length = 544 := by simp [packHalfwordsLE_length, h0]
  have l1 : (packHalfwordsLE (hws 1)).length = 544 := by simp [packHalfwordsLE_length, h1]
  have l2 : (packHalfwordsLE (hws 2)).length = 544 := by simp [packHalfwordsLE_length, h2]
  have l3 : (packHalfwordsLE (hws 3)).length = 544 := by simp [packHalfwordsLE_length, h3]
  unfold slotBytes4
  rw [List.append_assoc, List.append_assoc]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · simp [List.take_append_of_le_length (by omega : 512 ≤ (packHalfwordsLE (hws 0)).length)]
  · rw [show 544 * 1 = (packHalfwordsLE (hws 0)).length from l0.symm,
      List.drop_left, List.take_append_of_le_length (by omega)]
  · rw [show 544 * 2 = (packHalfwordsLE (hws 0)).length + (packHalfwordsLE (hws 1)).length by omega,
      ← List.drop_drop, List.drop_left, List.drop_left,
      List.take_append_of_le_length (by omega)]
  · rw [show 544 * 3 = (packHalfwordsLE (hws 0)).length +
        ((packHalfwordsLE (hws 1)).length + (packHalfwordsLE (hws 2)).length) by omega,
      ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left, List.drop_left]

theorem multiLaneSlots4_eq_pointsToBytes (ptr : BitVec 64) {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (_h3 : (hws 3).length = 272) :
    MultiLaneSlots ptr 544 4 hws = (ptr ↦ₛ slotBytes4 hws) := by
  have hp0 : ptr + BitVec.ofNat 64 (544 * 0) = ptr := BitVec.add_zero ptr
  have hp1 : ptr + BitVec.ofNat 64 (544 * 1) = ptr + 544#64 := rfl
  have hp2 : ptr + BitVec.ofNat 64 (544 * 2) = (ptr + 544#64) + 544#64 := by bv_omega
  have hp3 : ptr + BitVec.ofNat 64 (544 * 3) = ((ptr + 544#64) + 544#64) + 544#64 := by bv_omega
  unfold slotBytes4
  simp only [MultiLaneSlots, MultiLaneSepFrom, hp0, hp1, hp2, hp3, sepConj_emp,
    List.append_assoc, pointsToBytes_append, packHalfwordsLE_length, h0, h1, h2]

theorem memset2176_eq_multiLaneSlots4 (ptr : BitVec 64) :
    (ptr ↦ₛ List.replicate 2176 0#8) =
      MultiLaneSlots ptr 544 4 (fun _ => List.replicate 272 0#16) := by
  rw [multiLaneSlots4_eq_pointsToBytes ptr
    (List.length_replicate ..) (List.length_replicate ..)
    (List.length_replicate ..) (List.length_replicate ..)]
  unfold slotBytes4
  rw [packHalfwordsLE_replicate_zero, ← List.replicate_add, ← List.replicate_add,
    ← List.replicate_add]

theorem multiLaneSlots4_eq_btreeMem272 (ptr : BitVec 64) {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (h3 : (hws 3).length = 272) :
    MultiLaneSlots ptr 544 4 hws = BTreeMem ptr 272 (bytesToBTree9 (slotBytes4 hws)) := by
  rw [multiLaneSlots4_eq_pointsToBytes ptr h0 h1 h2 h3]
  exact pointsToBytes_eq_btreeMem 272 ptr (slotBytes4_length h0 h1 h2 h3) (by decide)

theorem btreeMem4_zero_eq_multiLaneSampled4 (ptr : BitVec 64) {t : BTree (BitVec 64) 9}
    (h0 : t.get 0 = 0#64) (h1 : t.get 1 = 0#64) (h2 : t.get 2 = 0#64) (h3 : t.get 3 = 0#64) :
    BTreeMem ptr 4 t = MultiLaneSampled ptr 4 (fun _ => 0) := by
  have hp0 : ptr + BitVec.ofNat 64 (8 * 0) = ptr := BitVec.add_zero ptr
  have hp1 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
  have hp2 : ptr + BitVec.ofNat 64 (8 * 2) = (ptr + 8#64) + 8#64 := by bv_omega
  have hp3 : ptr + BitVec.ofNat 64 (8 * 3) = ((ptr + 8#64) + 8#64) + 8#64 := by bv_omega
  simp only [BTreeMem, BTreeMemFrom, MultiLaneSampled, MultiLaneSepFrom,
    h0, h1, h2, h3, hp0, hp1, hp2, hp3]

theorem multiLaneSampled4_entails_memRegion32 (ptr : BitVec 64) (sampled : Nat → Nat) :
    MultiLaneSampled ptr 4 sampled ⊢ memRegion ptr 32 := by
  have heq : MultiLaneSampled ptr 4 sampled =
      BTreeMem ptr 4 (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (sampled i))) := by
    have hg0 : (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (sampled i))).get 0 =
        BitVec.ofNat 64 (sampled 0) := BTree.get_ofFn 9 _ 0 (by decide)
    have hg1 : (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (sampled i))).get 1 =
        BitVec.ofNat 64 (sampled 1) := BTree.get_ofFn 9 _ 1 (by decide)
    have hg2 : (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (sampled i))).get 2 =
        BitVec.ofNat 64 (sampled 2) := BTree.get_ofFn 9 _ 2 (by decide)
    have hg3 : (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (sampled i))).get 3 =
        BitVec.ofNat 64 (sampled 3) := BTree.get_ofFn 9 _ 3 (by decide)
    have hp0 : ptr + BitVec.ofNat 64 (8 * 0) = ptr := BitVec.add_zero ptr
    have hp1 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
    have hp2 : ptr + BitVec.ofNat 64 (8 * 2) = (ptr + 8#64) + 8#64 := by bv_omega
    have hp3 : ptr + BitVec.ofNat 64 (8 * 3) = ((ptr + 8#64) + 8#64) + 8#64 := by bv_omega
    simp only [MultiLaneSampled, MultiLaneSepFrom, BTreeMem, BTreeMemFrom,
      hg0, hg1, hg2, hg3, hp0, hp1, hp2, hp3]
  rw [heq]
  exact BTreeMem_entails_memRegion ptr 4 _

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
