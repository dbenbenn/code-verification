/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedOddSites
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge

/-!
# `decapsulate_compressed_key` (`B04`) — `Seg5` Invariants, `TreeMem` Bridges, & Entry (`Seg5Init`)

Defines `Seg5RegInv`, `Seg5ConstWordsInv`, `Seg5LoopState`, `Seg5RowDone`, `TreeMem (sp + 144#64) 264`
entry/exit spatial bridges, `+0x4058 → +0x40d4 → +0x436c` prologue, and `+0x436c → +0x4390`
(`B29` `memset`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 150000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel
  fetch_rebase_ldst128Lo12_site mbase mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl
  resolve_blk29 resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk SepWP.roDataAt_intro cst16_0_vec cst16_1_vec cst16_2_vec
  mlkemData02Bytes_length mlkemData03Bytes_length mlkemData04Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState packLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE packHalfwordsLE_replicate_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (RejSiteConfig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepStore128 Vec128At VecRangeMem bytesToVecNat pointsToBytes_eq_vecRangeMem step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KSlot)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem TreeMem_eq_pointsToWords64 btreeOfWords btreeOfWords_get
  memRegion_entails_exists_treeMem treeMem_entails_memRegion treeMem_join treeMem_split zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  rhoW rowPermState rowSeeds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (slotHoldsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (fetchWordTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  InSeg5Word04 fetch_blk04_seg5 inv01Slots inv2Slots)

/-! ## 1. Configurations, Register Invariants, & Row State Predicates -/

@[expose] def cfgInit04 : KCfg := { offA := 144, lenA := 264, offB := 22400, lenB := 189 }
@[expose] def cfgClamp04 : KCfg := { offA := 144, lenA := 264, offB := 19168, lenB := 3 }
@[expose] def cfgExtra04 : KCfg := { offA := 144, lenA := 264, offB := 20704, lenB := 63 }
theorem cfgInit04_wf : KCfgWf cfgInit04 := by unfold KCfgWf cfgInit04; decide
theorem cfgClamp04_wf : KCfgWf cfgClamp04 := by unfold KCfgWf cfgClamp04; decide
theorem cfgExtra04_wf : KCfgWf cfgExtra04 := by unfold KCfgWf cfgExtra04; decide

@[expose] def cfgRejInit3_04 : RejSiteConfig :=
  { v := .varA, nLanes := 3, nChunks := 21, slotStride := 544,
    rIdx := .x9, rSqPtr := .x10, rPrevIdx := .x11,
    rSampArr := .x23, rSlotStride := .x21, rSlotsBase := .gpr 27#5 }
@[expose] def cfgRejExtra1_04 : RejSiteConfig :=
  { v := .varA, nLanes := 3, nChunks := 7, slotStride := 544,
    rIdx := .x11, rSqPtr := .x9, rPrevIdx := .x10,
    rSampArr := .x23, rSlotStride := .x21, rSlotsBase := .gpr 27#5 }
theorem cfgRejInit3_04_valid : cfgRejInit3_04.Valid := by decide +kernel
theorem cfgRejExtra1_04_valid : cfgRejExtra1_04.Valid := by decide +kernel

@[expose] def Seg5RegInv [MlKemPlacement] (sp fpVal : BitVec 64) (s : State) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧ s.readReg64 .fp = fpVal ∧
  s.readReg64 .x20 = sp + 23704#64 ∧ s.readReg64 .x21 = 544#64 ∧
  s.readReg64 .x22 = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ∧
  s.readReg64 .x23 = sp + 19168#64 ∧ s.readReg64 .x24 = sp + 20715#64 ∧
  s.readReg64 .x25 = 256#64 ∧ s.readReg64 .x26 = sp + 20704#64 ∧
  s.readReg64 .x27 = sp + 5680#64 ∧ s.readReg64 .x28 = sp + 20968#64

@[expose] def Seg5ConstWordsInv (sp : BitVec 64) (rho : List (BitVec 8))
    (tA : BTree (BitVec 64) 9) : Prop :=
  tA.get 0 = 0x001f0200#64 ∧ tA.get 1 = 0#64 ∧
  tA.get 2 = 0x001f0100#64 ∧ tA.get 3 = 0#64 ∧
  tA.get 5 = sp + 22411#64 ∧ tA.get 6 = sp + 13392#64 ∧ tA.get 7 = sp + 22664#64 ∧
  tA.get 38 = 0xffffffffff0000ff#64 ∧ tA.get 39 = 0xffffffffffffffff#64 ∧
  tA.get 40 = rhoW rho 3 ∧ tA.get 41 = rhoW rho 3 ∧
  tA.get 42 = rhoW rho 2 ∧ tA.get 43 = rhoW rho 2 ∧
  tA.get 44 = rhoW rho 1 ∧ tA.get 45 = rhoW rho 1 ∧
  tA.get 46 = rhoW rho 0 ∧ tA.get 47 = rhoW rho 0

@[expose] def Seg5LoopState [MlKemPlacement] (b sp fpVal : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (extra : Nat) (s : State) (P : SepProp) : Prop :=
  s.pc = b + BitVec.ofNat 64 (4 * 6390) ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  Seg5RegInv sp fpVal s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x19 = BitVec.ofNat 64 row ∧
  ∃ (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    Seg5ConstWordsInv sp rho tA ∧
    (∀ idx, idx < 25 →
      slotHolds cfgClamp04 s tA (inv01Slots.getD idx (.vreg 0))
        ((rowPermState rho row 0 (extra + 2)).getD idx 0#64)
        ((rowPermState rho row 1 (extra + 2)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHoldsLo cfgClamp04 s tA (inv2Slots.getD idx (.vreg 0))
        ((rowPermState rho row 2 (extra + 2)).getD idx 0#64)) ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (P ⊢ TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
      MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗
      MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F)

@[expose] def Seg5RowDone [MlKemPlacement] (b sp fpVal : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (s : State) (P : SepProp) : Prop :=
  s.pc = b + BitVec.ofNat 64 (4 * 4150) ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  Seg5RegInv sp fpVal s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x19 = BitVec.ofNat 64 row ∧
  ∃ (extra : Nat) (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    allLanesDone 3 (rowSeeds rho row) extra = true ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    Seg5ConstWordsInv sp rho tA ∧
    (P ⊢ TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
      MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗ F)

theorem multiLaneSampled3_eq_treeMem04 (sp : BitVec 64) (sampled : Nat → Nat)
    (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = BitVec.ofNat 64 (sampled 0)) (h1 : t.get 1 = BitVec.ofNat 64 (sampled 1))
    (h2 : t.get 2 = BitVec.ofNat 64 (sampled 2)) :
    MultiLaneSampled (sp + 19168#64) 3 sampled = TreeMem (sp + 19168#64) 3 t := by
  rw [TreeMem_eq_pointsToWords64]
  change MultiLaneSepFrom
      (fun i s => (sp + 19168#64 + BitVec.ofNat 64 (8 * i)) ↦₆₄ BitVec.ofNat 64 s) 0 3 sampled =
    pointsToWords64 (sp + 19168#64) [t.get 0, t.get 1, t.get 2]
  rw [h0, h1, h2]
  simp only [MultiLaneSepFrom, pointsToWords64_cons, pointsToWords64_nil,
    sepConj_emp, BitVec.add_assoc]; rfl

theorem replicate1632_eq_multiLaneSlots0_04 (sp : BitVec 64) :
    ((sp + 5680#64) ↦ₛ List.replicate 1632 0#8) =
      MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) := by
  have h544 : packHalfwordsLE (List.replicate 272 0#16) = List.replicate 544 0#8 :=
    packHalfwordsLE_replicate_zero 272
  have hsplit : List.replicate 1632 (0#8) =
      List.replicate 544 0#8 ++ (List.replicate 544 0#8 ++ List.replicate 544 0#8) := by
    rw [← List.replicate_add, ← List.replicate_add]
  rw [hsplit, pointsToBytes_append, pointsToBytes_append]
  simp only [MultiLaneSlots, MultiLaneSepFrom, h544, List.length_replicate,
    sepConj_emp, BitVec.add_assoc]; rfl

/-! ## 2. `TreeMem (sp + 144#64) 264` Spatial Bridges & Branch Step Helpers -/

private theorem vec128At_dup64 (a : BitVec 64) (w : BitVec 64) :
    Vec128At a (w ++ w) = (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ w) := by
  unfold Vec128At
  have h0 : (w ++ w).extractLsb' 0 64 = w := by bv_bits
  have h1 : (w ++ w).extractLsb' 64 64 = w := by bv_bits
  rw [h0, h1]

private theorem lo8_eq_treeMem04 (sp w4 : BitVec 64) (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = 0x001f0200#64) (h1 : t.get 1 = 0#64)
    (h2 : t.get 2 = 0x001f0100#64) (h3 : t.get 3 = 0#64) (h4 : t.get 4 = w4)
    (h5 : t.get 5 = sp + 22411#64) (h6 : t.get 6 = sp + 13392#64)
    (h7 : t.get 7 = sp + 22664#64) :
    Vec128At (sp + 144#64) 0x000000000000000000000000001f0200#128 ∗
      Vec128At (sp + 160#64) 0x000000000000000000000000001f0100#128 ∗
      ((sp + 176#64) ↦₆₄ w4) ∗
      ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗
      ((sp + 200#64) ↦₆₄ (sp + 22664#64)) =
      TreeMem (sp + 144#64) 8 t := by
  rw [TreeMem_eq_pointsToWords64]
  change _ = pointsToWords64 (sp + 144#64)
    [t.get 0, t.get 1, t.get 2, t.get 3, t.get 4, t.get 5, t.get 6, t.get 7]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  unfold Vec128At
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc]
  rfl

private theorem mid10_eq_treeMem04 (sp : BitVec 64) (rho : List (BitVec 8)) (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = 0xffffffffff0000ff#64) (h1 : t.get 1 = 0xffffffffffffffff#64)
    (h2 : t.get 2 = rhoW rho 3) (h3 : t.get 3 = rhoW rho 3)
    (h4 : t.get 4 = rhoW rho 2) (h5 : t.get 5 = rhoW rho 2)
    (h6 : t.get 6 = rhoW rho 1) (h7 : t.get 7 = rhoW rho 1)
    (h8 : t.get 8 = rhoW rho 0) (h9 : t.get 9 = rhoW rho 0) :
    Vec128At (sp + 448#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
      Vec128At (sp + 464#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
      Vec128At (sp + 480#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
      Vec128At (sp + 496#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
      Vec128At (sp + 512#64) (packLane64 rho 0 ++ packLane64 rho 0) =
      TreeMem (sp + 448#64) 10 t := by
  rw [TreeMem_eq_pointsToWords64]
  change _ = pointsToWords64 (sp + 448#64)
    [t.get 0, t.get 1, t.get 2, t.get 3, t.get 4, t.get 5, t.get 6, t.get 7, t.get 8, t.get 9]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    vec128At_dup64 (sp + 464#64), vec128At_dup64 (sp + 480#64),
    vec128At_dup64 (sp + 496#64), vec128At_dup64 (sp + 512#64)]
  unfold Vec128At rhoW
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc]
  rfl

theorem entry_treeMem04_join (sp w4 : BitVec 64) (rho : List (BitVec 8))
    (tMid tHi : BTree (BitVec 64) 9) :
    ∃ tA : BTree (BitVec 64) 9,
      Seg5ConstWordsInv sp rho tA ∧
      Vec128At (sp + 144#64) 0x000000000000000000000000001f0200#128 ∗
        Vec128At (sp + 160#64) 0x000000000000000000000000001f0100#128 ∗
        ((sp + 176#64) ↦₆₄ w4) ∗
        ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
        ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗
        ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
        TreeMem (sp + 208#64) 30 tMid ∗
        Vec128At (sp + 448#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
        Vec128At (sp + 464#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
        Vec128At (sp + 480#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
        Vec128At (sp + 496#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
        Vec128At (sp + 512#64) (packLane64 rho 0 ++ packLane64 rho 0) ∗
        TreeMem (sp + 528#64) 216 tHi =
      TreeMem (sp + 144#64) 264 tA := by
  let ws0 : List (BitVec 64) :=
    [0x001f0200#64, 0#64, 0x001f0100#64, 0#64, w4, sp + 22411#64, sp + 13392#64, sp + 22664#64]
  let ws2 : List (BitVec 64) :=
    [0xffffffffff0000ff#64, 0xffffffffffffffff#64, rhoW rho 3, rhoW rho 3,
     rhoW rho 2, rhoW rho 2, rhoW rho 1, rhoW rho 1, rhoW rho 0, rhoW rho 0]
  let t0 := btreeOfWords 0 ws0 zeroTree9
  let t2 := btreeOfWords 0 ws2 zeroTree9
  have hlen0 : ws0.length = 8 := rfl
  have hlen2 : ws2.length = 10 := rfl
  have ht0 : ∀ i, i < 8 → t0.get i = ws0.getD i 0#64 := fun i hi => by
    simpa [Nat.zero_add] using btreeOfWords_get 0 ws0 zeroTree9 i (by omega) (by omega)
  have ht2 : ∀ i, i < 10 → t2.get i = ws2.getD i 0#64 := fun i hi => by
    simpa [Nat.zero_add] using btreeOfWords_get 0 ws2 zeroTree9 i (by omega) (by omega)
  let t01 := BTree.ofFn 9 fun i => if i < 8 then ws0.getD i 0#64 else tMid.get (i - 8)
  let t012 := BTree.ofFn 9 fun i => if i < 38 then t01.get i else ws2.getD (i - 38) 0#64
  let tA := BTree.ofFn 9 fun i => if i < 48 then t012.get i else tHi.get (i - 48)
  have hget0 : ∀ i, i < 8 → tA.get i = ws0.getD i 0#64 := fun i hi => by
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp only [show i < 48 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp only [show i < 38 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp only [hi, ↓reduceIte]
  have hget2 : ∀ i, i < 10 → tA.get (38 + i) = ws2.getD i 0#64 := fun i hi => by
    rw [BTree.get_ofFn 9 _ (38 + i) (by omega)]; simp only [show 38 + i < 48 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ (38 + i) (by omega)]
    simp only [show ¬(38 + i < 38) by omega, ↓reduceIte, show 38 + i - 38 = i by omega]
  refine ⟨tA, ⟨hget0 0 (by decide), hget0 1 (by decide), hget0 2 (by decide), hget0 3 (by decide),
    hget0 5 (by decide), hget0 6 (by decide), hget0 7 (by decide),
    hget2 0 (by decide), hget2 1 (by decide), hget2 2 (by decide), hget2 3 (by decide),
    hget2 4 (by decide), hget2 5 (by decide), hget2 6 (by decide), hget2 7 (by decide),
    hget2 8 (by decide), hget2 9 (by decide)⟩, ?_⟩
  have hL0 := lo8_eq_treeMem04 sp w4 t0
    (ht0 0 (by decide)) (ht0 1 (by decide)) (ht0 2 (by decide)) (ht0 3 (by decide))
    (ht0 4 (by decide)) (ht0 5 (by decide)) (ht0 6 (by decide)) (ht0 7 (by decide))
  have hL2 := mid10_eq_treeMem04 sp rho t2
    (ht2 0 (by decide)) (ht2 1 (by decide)) (ht2 2 (by decide)) (ht2 3 (by decide))
    (ht2 4 (by decide)) (ht2 5 (by decide)) (ht2 6 (by decide)) (ht2 7 (by decide))
    (ht2 8 (by decide)) (ht2 9 (by decide))
  have hJ1 : TreeMem (sp + 144#64) 8 t0 ∗ TreeMem (sp + 208#64) 30 tMid =
      TreeMem (sp + 144#64) 38 t01 := by
    rw [show sp + 208#64 = (sp + 144#64) + BitVec.ofNat 64 (8 * 8) by bv_omega]
    exact treeMem_join (n1 := 8) (n2 := 30) (t := t01)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi, ht0 i hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (8 + i) (by omega)]
        simp [show ¬(8 + i < 8) by omega, show 8 + i - 8 = i by omega])
  have hJ2 : TreeMem (sp + 144#64) 38 t01 ∗ TreeMem (sp + 448#64) 10 t2 =
      TreeMem (sp + 144#64) 48 t012 := by
    rw [show sp + 448#64 = (sp + 144#64) + BitVec.ofNat 64 (8 * 38) by bv_omega]
    exact treeMem_join (n1 := 38) (n2 := 10) (t := t012)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (38 + i) (by omega)]
        simp [show ¬(38 + i < 38) by omega, show 38 + i - 38 = i by omega, ht2 i hi])
  have hJ3 : TreeMem (sp + 144#64) 48 t012 ∗ TreeMem (sp + 528#64) 216 tHi =
      TreeMem (sp + 144#64) 264 tA := by
    rw [show sp + 528#64 = (sp + 144#64) + BitVec.ofNat 64 (8 * 48) by bv_omega]
    exact treeMem_join (n1 := 48) (n2 := 216) (t := tA)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (48 + i) (by omega)]
        simp [show ¬(48 + i < 48) by omega, show 48 + i - 48 = i by omega])
  rw [← hJ3, ← hJ2, ← hJ1, ← hL2, ← hL0]
  apply sepProp_ext <;> sep_frame

theorem exit_treeMem04_entails (sp : BitVec 64) (tA : BTree (BitVec 64) 9) :
    TreeMem (sp + 144#64) 264 tA ⊢ memRegion (sp + 144#64) 2112 :=
  treeMem_entails_memRegion (ptr := sp + 144#64) (len := 264) tA (by decide)

theorem step_b_seg5 [MlKemPlacement] {b tgt : BitVec 64} {w : Nat} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hin : InSeg5Word04 w) (hfw : fetchWordTree04 w = some (.b disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : SepWP (blkPC04.rebase b (fun _ => none)) tgt
      (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s P post oom := by
  refine SepWP.step_pure hpc hrun (fetch_blk04_seg5 hin hfw)
    (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl hnext
  rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hpc]

theorem step_bCond_seg5 [MlKemPlacement] {b tgt : BitVec 64} {w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hin : InSeg5Word04 w) (hfw : fetchWordTree04 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk04_seg5 hin hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk04_seg5 hin hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]

/-! ## 3. `+0x4058 → +0x436c` Prologue & `+0x436c → +0x4390` (`B29` `memset`) -/

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x4058 → 0x40d8, 0x436c → 0x4390]
gen_placed_odd_sites blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x4058 → 0x40d8]

@[simp, arm64_norm]
private theorem blkPC04_ldst128_cst16_0 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 16568) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.0")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := 16568)
    (r := { off := 16568, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16568)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4142) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC04_ldst128_cst16_1 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 16580) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.1")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := 16580)
    (r := { off := 16580, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16580)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4145) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC04_ldst128_cst16_2 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 16588) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 10))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.2")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := 16588)
    (r := { off := 16588, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16588)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4147) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  readLE_8_eq_packLane64)

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

private theorem blk29_memset_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk29_memset_ok

attribute [local wp_norm ↓ high] exec_simdMovi_2d_0
attribute [local irreducible] blkPC04 blkLib04 mlkemMultiLib TreeMem MultiLaneSlots packLane64

private theorem seq_roOk [MlKemPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => MlKemRoOk mlkemMpl sm.mem → SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        MlKemRoOk mlkemMpl sm.mem ∧ (MlKemRoOk mlkemMpl sm.mem → SepWP prog target sm Pm post))
      (Φ := MlKemRoOk mlkemMpl) (fun _ _ hr hkf => hr.of_keepsFrozen hkf) hro h
      (fun _ _ _ _ hr hk => ⟨hr, hk⟩))
    (fun _ _ _ _ ⟨hr, hk⟩ => hk hr)

private theorem orr_11_sp_add (sp off out : BitVec 64)
    (hsp : (sp &&& 15#64 == 0#64) = true) (hoff : (off &&& 15#64 == 0#64) = true)
    (hout : off + 11#64 = out) :
    ((sp + off) ||| 11#64) = sp + out := by
  have hsp0 : sp &&& 15#64 = 0#64 := of_decide_eq_true hsp
  have hoff0 : off &&& 15#64 = 0#64 := of_decide_eq_true hoff
  subst hout
  have hal : (sp + off) &&& 15#64 = 0#64 := by bv_bits
  have hdisj : (sp + off) &&& 11#64 = 0#64 := by
    have h15 : (15#64 &&& 11#64 : BitVec 64) = 11#64 := by decide
    rw [← h15, ← BitVec.and_assoc, hal]; decide
  rw [(BitVec.add_eq_or_of_and_eq_zero (sp + off) 11#64 hdisj).symm, BitVec.add_assoc]

@[simp] private theorem extractLsb64_lo_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
@[simp] private theorem extractLsb64_hi_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
@[simp] private theorem truncate64_append (hi lo : BitVec 64) :
    (hi ++ lo).truncate 64 = lo := by bv_bits

private theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1
  rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

abbrev offSeg5Entry : BitVec 64 := BitVec.ofNat 64 (4 * 4118)
abbrev offSeg5Mid : BitVec 64 := BitVec.ofNat 64 (4 * 4139)
abbrev offSeg5Memset : BitVec 64 := BitVec.ofNat 64 (4 * 4315)
abbrev offSeg5Body : BitVec 64 := BitVec.ofNat 64 (4 * 4324)

private theorem seg5_prologue_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal dkA : BitVec 64) (dk rho : List (BitVec 8)) (Rest : SepProp)
    (hdk : dk.length = 2400) (hrho_def : (dk.drop 2304).take 32 = rho)
    (hpc : s.pc = b + offSeg5Entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hfp : s.readReg64 .fp = fpVal) (hx9 : s.readReg64 .x9 = dkA) (hx10 : s.readReg64 .x10 = 11#64)
    (hx23 : s.readReg64 .x23 = sp + 16384#64) (hx26 : s.readReg64 .x26 = sp + 20704#64)
    (hx27 : s.readReg64 .x27 = sp + 5680#64) (hx28 : s.readReg64 .x28 = sp + 20968#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5Mid) s
      (memRegion (sp + 184#64) 8 ∗ memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ Rest)
      (fun s1 P1 =>
        Seg5RegInv sp fpVal s1 ∧ s1.readReg64 .x8 = 0#64 ∧
        s1.readVReg128 0#5 = packLane64 rho 24 ++ packLane64 rho 24 ∧
        s1.readVReg128 2#5 = packLane64 rho 16 ++ packLane64 rho 16 ∧
        (P1 ⊢ ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
          Vec128At (sp + 496#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
          Vec128At (sp + 512#64) (packLane64 rho 0 ++ packLane64 rho 0) ∗
          (dkA ↦ₛ dk) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have _horr22400 := orr_11_sp_add sp 22400#64 22411#64 hal_sp (by decide) rfl
  have _horr20704 := orr_11_sp_add sp 20704#64 20715#64 hal_sp (by decide) rfl
  have hrho_len : rho.length = 32 := by rw [← hrho_def]; simp [hdk]
  have hdk_split : (dkA ↦ₛ dk) =
      (dkA ↦ₛ dk.take 2304) ∗ ((dkA + 2304#64) ↦ₛ rho) ∗ ((dkA + 2336#64) ↦ₛ dk.drop 2336) := by
    have h1 : dk = dk.take 2304 ++ dk.drop 2304 := (List.take_append_drop 2304 dk).symm
    have h2 : dk.drop 2304 = rho ++ dk.drop 2336 := by
      rw [← hrho_def, show (2336 : Nat) = 2304 + 32 from rfl, ← List.drop_drop]
      exact (List.take_append_drop 32 (dk.drop 2304)).symm
    conv_lhs => rw [h1, h2]
    rw [pointsToBytes_append, pointsToBytes_append,
      show (dk.take 2304).length = 2304 by simp [hdk], hrho_len,
      show dkA + BitVec.ofNat 64 2304 = dkA + 2304#64 by rfl,
      show (dkA + 2304#64) + BitVec.ofNat 64 32 = dkA + 2336#64 by bv_omega]
  have o496_8 : sp + 496#64 + 8#64 = sp + 504#64 := by clear *- ; bv_omega
  have o496_16 : sp + 496#64 + 16#64 = sp + 512#64 := by clear *- ; bv_omega
  have o496_24 : sp + 496#64 + 24#64 = sp + 520#64 := by clear *- ; bv_omega
  have o512_8 : sp + 512#64 + 8#64 = sp + 520#64 := by clear *- ; bv_omega
  have odk8 : dkA + 2304#64 + 8#64 = dkA + 2312#64 := by clear *- ; bv_omega
  have odk16 : dkA + 2304#64 + 16#64 = dkA + 2320#64 := by clear *- ; bv_omega
  have odk24 : dkA + 2304#64 + 24#64 = dkA + 2328#64 := by clear *- ; bv_omega
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 184#64)); intro c184
  sep_frame_apply (sepWP_elim_region32 (a := sp + 496#64)); intro d0 d1 d2 d3
  rw [hdk_split, ← vec2_cells_eq_bytes (dkA + 2304#64) hrho_len]
  generalize hv0 : bytesToVecNat rho 0 = qv0
  generalize hv1 : bytesToVecNat rho 1 = qv1
  simp only [o496_8, o496_16, o496_24, odk8, odk16, odk24]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp [hfp], by wp_norm_lhs, by simp, by wp_norm_lhs,
      by wp_norm_lhs, by simp, by simp,
      by simp [hx26], by simp [hx27], by simp [hx28]⟩,
      by simp, ?_, ?_, ?_⟩
  · subst hv1; dsimp only [bytesToVecNat]; simp [readLE_8_eq_packLane64]
  · subst hv1; dsimp only [bytesToVecNat]; simp [readLE_8_eq_packLane64]
  · subst hv0 hv1
    simp only [o512_8.symm, odk8.symm, odk16.symm, odk24.symm]
    rw [vec2_cells_eq_bytes (dkA + 2304#64) hrho_len, ← hdk_split]
    dsimp only [Vec128At, bytesToVecNat]
    simp only [truncate64_append, extractLsb64_lo_append, extractLsb64_hi_append,
      o496_8, o512_8,
      Nat.mul_zero, Nat.zero_add, readLE_8_eq_packLane64]
    sep_frame

theorem seg5_prologue [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal dkA : BitVec 64) (dk : List (BitVec 8)) (Rest : SepProp)
    (hdk : dk.length = 2400)
    (hpc : s.pc = b + offSeg5Entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hfp : s.readReg64 .fp = fpVal) (hx9 : s.readReg64 .x9 = dkA) (hx10 : s.readReg64 .x10 = 11#64)
    (hx23 : s.readReg64 .x23 = sp + 16384#64) (hx26 : s.readReg64 .x26 = sp + 20704#64)
    (hx27 : s.readReg64 .x27 = sp + 5680#64) (hx28 : s.readReg64 .x28 = sp + 20968#64)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let rho := (dk.drop 2304).take 32
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5Memset) s
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ Rest)
      (fun s2 P2 =>
        Seg5RegInv sp fpVal s2 ∧ s2.readReg64 .x8 = 0#64 ∧
        (P2 ⊢ Vec128At (sp + 144#64) 0x000000000000000000000000001f0200#128 ∗
          Vec128At (sp + 160#64) 0x000000000000000000000000001f0100#128 ∗
          ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
          Vec128At (sp + 448#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
          Vec128At (sp + 464#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
          Vec128At (sp + 480#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
          Vec128At (sp + 496#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
          Vec128At (sp + 512#64) (packLane64 rho 0 ++ packLane64 rho 0) ∗
          (dkA ↦ₛ dk) ∗ Rest)) := by
  intro rho
  generalize hrho_def : (dk.drop 2304).take 32 = rho0
  change SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5Memset) s
    (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
      memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
      memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ Rest)
    (fun s2 P2 =>
      Seg5RegInv sp fpVal s2 ∧ s2.readReg64 .x8 = 0#64 ∧
      (P2 ⊢ Vec128At (sp + 144#64) 0x000000000000000000000000001f0200#128 ∗
        Vec128At (sp + 160#64) 0x000000000000000000000000001f0100#128 ∗
        ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
        Vec128At (sp + 448#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
        Vec128At (sp + 464#64) (packLane64 ((dk.drop 2304).take 32) 24 ++ packLane64 ((dk.drop 2304).take 32) 24) ∗
        Vec128At (sp + 480#64) (packLane64 ((dk.drop 2304).take 32) 16 ++ packLane64 ((dk.drop 2304).take 32) 16) ∗
        Vec128At (sp + 496#64) (packLane64 ((dk.drop 2304).take 32) 8 ++ packLane64 ((dk.drop 2304).take 32) 8) ∗
        Vec128At (sp + 512#64) (packLane64 ((dk.drop 2304).take 32) 0 ++ packLane64 ((dk.drop 2304).take 32) 0) ∗
        (dkA ↦ₛ dk) ∗ Rest))
  rw [hrho_def]
  let midRest := memRegion (sp + 144#64) 32 ∗ memRegion (sp + 448#64) 16 ∗
    memRegion (sp + 464#64) 32 ∗ Rest
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 184#64) 8 ∗ memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ midRest)
    (by dsimp only [midRest]; sep_frame) ?_
  refine seq_roOk (mid := b + offSeg5Mid) hro ?_
  refine SepWP.mono
    (seg5_prologue_a hb hbase s sp fpVal dkA dk rho0 midRest hdk hrho_def hpc hrun hsp hsp_al
      hfp hx9 hx10 hx23 hx26 hx27 hx28) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hreg1, hx8_1, hq0_1, hq2_1, hP1⟩ hro1
  rcases hreg1 with ⟨hsp1, hsp_al1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  subst hbase
  have o144_8 : sp + 144#64 + 8#64 = sp + 152#64 := by clear *- ; bv_omega
  have o144_16 : sp + 144#64 + 16#64 = sp + 160#64 := by clear *- ; bv_omega
  have o144_24 : sp + 144#64 + 24#64 = sp + 168#64 := by clear *- ; bv_omega
  have o160_8 : sp + 160#64 + 8#64 = sp + 168#64 := by clear *- ; bv_omega
  have o448_8 : sp + 448#64 + 8#64 = sp + 456#64 := by clear *- ; bv_omega
  have o464_8 : sp + 464#64 + 8#64 = sp + 472#64 := by clear *- ; bv_omega
  have o464_16 : sp + 464#64 + 16#64 = sp + 480#64 := by clear *- ; bv_omega
  have o464_24 : sp + 464#64 + 24#64 = sp + 488#64 := by clear *- ; bv_omega
  have o480_8 : sp + 480#64 + 8#64 = sp + 488#64 := by clear *- ; bv_omega
  let Tail := ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
    Vec128At (sp + 496#64) (packLane64 rho0 8 ++ packLane64 rho0 8) ∗
    Vec128At (sp + 512#64) (packLane64 rho0 0 ++ packLane64 rho0 0) ∗ (dkA ↦ₛ dk) ∗ Rest
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 144#64) 32 ∗ memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗ Tail)
    (Entails.trans hP1 (by dsimp only [midRest, Tail]; sep_frame)) ?_
  rw [memRegion_split' (b := sp + 448#64) (b' := sp + 456#64) (n := 8) (k := (8 : Nat)) rfl o448_8.symm (by decide)]
  sep_frame_apply (sepWP_elim_region32 (a := sp + 144#64)); intro c144 c152 c160 c168
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 448#64)); intro c448
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 456#64)); intro c456
  sep_frame_apply (sepWP_elim_region32 (a := sp + 464#64)); intro d0 d1 d2 d3
  simp only [o144_8, o144_16, o144_24, o464_8, o464_16, o464_24]
  refine seq_roOk (mid := blkPl04.base + BitVec.ofNat 64 16568) hro1 ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro2 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of]) hro2.cst16_0 mlkemData02Bytes_length cst16_0_vec (by wp_norm_lhs) ?_
  refine seq_roOk (mid := blkPl04.base + BitVec.ofNat 64 16580) (by simpa using hro2) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro3 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of]) hro3.cst16_1 mlkemData03Bytes_length cst16_1_vec (by wp_norm_lhs) ?_
  refine seq_roOk (mid := blkPl04.base + BitVec.ofNat 64 16588) (by simpa using hro3) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro4 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of]) hro4.cst16_2 mlkemData04Bytes_length cst16_2_vec (by wp_norm_lhs) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp1], spAligned_of_sp_eq hsp_al1 hsp1 (by simp [hsp1]),
      by simp [hfp1], by simp [hx20_1], by simp [hx21_1], by simp [hx22_1],
      by simp [hx23_1], by simp [hx24_1], by simp [hx25_1], by simp [hx26_1],
      by simp [hx27_1], by simp [hx28_1]⟩, by simp [hx8_1], ?_⟩
  dsimp only [Tail, Vec128At]
  simp only [extractLsb64_lo_append, extractLsb64_hi_append,
    o144_8, o160_8, o448_8, o464_8, o480_8,
    show (0x000000000000000000000000001f0200#128).extractLsb' 0 64 = 0x00000000001f0200#64 by decide,
    show (0x000000000000000000000000001f0200#128).extractLsb' 64 64 = 0#64 by decide,
    show (0x000000000000000000000000001f0100#128).extractLsb' 0 64 = 0x00000000001f0100#64 by decide,
    show (0x000000000000000000000000001f0100#128).extractLsb' 64 64 = 0#64 by decide,
    show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 0 64 = 0xffffffffff0000ff#64 by decide,
    show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 64 64 = 0xffffffffffffffff#64 by decide]
  sep_frame

theorem seg5_row_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (row : Nat) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Memset) (hrun : s.status = .Running)
    (hreg : Seg5RegInv sp fpVal s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 row)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5Body) s
      (memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 19168#64) 24 ∗ Rest)
      (fun sf Pf => Seg5RegInv sp fpVal sf ∧ sf.readReg64 .x19 = BitVec.ofNat 64 row ∧
        (Pf ⊢ MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨hsp, hal, hfp, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hal
  rw [memRegion_split' (b := sp + 19168#64) (b' := sp + 19176#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19176#64) (b' := sp + 19184#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 19168#64)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 19176#64)); intro c1
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 19184#64)); intro c2
  have hv0 : ((sp + 19168#64) ↦₆₄ c0) ∗ ((sp + 19176#64) ↦₆₄ c1) = Vec128At (sp + 19168#64) (c1 ++ c0) := by
    unfold Vec128At; simp
  refine SepWP.congr_pre (P1 := memRegion (sp + 5680#64) 1632 ∗ ((sp + 19184#64) ↦₆₄ c2) ∗
      Vec128At (sp + 19168#64) (c1 ++ c0) ∗ Rest) (by rw [← hv0]; apply sepProp_ext <;> sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 5
  apply SepWP.step_str64 (wb := none) (ea := sp + 19184#64)
  · wp_norm_lhs
  · simp [hrun]
  · wp_norm_lhs
  · simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp]
  · simp [evalAddrMode, hsp]
  · rfl
  · exact (SepStore64.here rfl).left.right
  · wp_norm_lhs
  intro m1
  wp_step
  apply step_strQ128 (wb := none) (ea := sp + 19168#64) (val := 0#128)
  · wp_norm_lhs
  · simp [hrun]
  · wp_norm_lhs
  · simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp]
  · simp [evalAddrMode, hsp]
  · simp
  · exact (SepStore128.vec128At rfl).left.right.right
  · wp_norm_lhs
  intro m2
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  intro _hcl2
  wp_call (blk29_memset_04 blkPl04.base) (sp + 5680#64, 0#8, 1632)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) ‹_›
    ⟨⟨hsp_sf, spAligned_of_sp_eq hal hsp hsp_sf,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*],
      by simp [*]⟩, by simp [*], ?_⟩
  rw [replicate1632_eq_multiLaneSlots0_04 sp]
  have hsamp0 : Vec128At (sp + 19168#64) 0#128 ∗ ((sp + 19184#64) ↦₆₄ 0#64) =
      MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) := by
    unfold Vec128At MultiLaneSampled
    simp only [MultiLaneSepFrom, sepConj_emp, sepConj_assoc, BitVec.add_assoc]; rfl
  rw [← hsamp0]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init
