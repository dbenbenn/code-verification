/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge

/-!
# `generate_keypair_compressed` (`B05`): `Seg2` invariants, `TreeMem` bridges, and entry

Defines `Seg2RegInv`, `Seg2ConstWordsInv`, `Seg2LoopState`, `Seg2RowMid`, `Seg2RowDone`, and
`Seg2RowExit`; proves `TreeMem (sp + 64#64) 268` entry/exit spatial bridges and clamp/branch
decision lemmas; and steps `+0x02b8 → +0x02dc` (`B29` `memset`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk SepWP.roDataAt_intro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState packLane64 shake128BlockAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (keccakF1600_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  clampSampled packHalfwordsLE packHalfwordsLE_replicate_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (RejSiteConfig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (Vec128At)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  cell_entails_memRegion8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  Seg2ConstSlots sepWP_elim_cell8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KSlot fetchWordTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem TreeMem_eq_pointsToWords64 btreeOfWords btreeOfWords_get fetch_blk05_seg2
  memRegion_entails_exists_treeMem treeMem_entails_memRegion treeMem_join treeMem_split zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf condHolds_HI_255 setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  inv01Slots inv2Slots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  rhoW rowPermState rowPermState_succ rowPermState_zero rowSeeds)

/-! ## 1. Configurations, Register Invariants, & Row State Predicates -/

@[expose] def cfgInit : KCfg := { offA := 64, lenA := 268, offB := 9984, lenB := 189 }
@[expose] def cfgClamp : KCfg := { offA := 64, lenA := 268, offB := 29024, lenB := 3 }
@[expose] def cfgExtra : KCfg := { offA := 64, lenA := 268, offB := 27840, lenB := 63 }
@[expose] def cfgShift : KCfg := { offA := 17376, lenA := 204, offB := 0, lenB := 0 }
theorem cfgInit_wf : KCfgWf cfgInit := by unfold KCfgWf cfgInit; decide
theorem cfgClamp_wf : KCfgWf cfgClamp := by unfold KCfgWf cfgClamp; decide
theorem cfgExtra_wf : KCfgWf cfgExtra := by unfold KCfgWf cfgExtra; decide
theorem cfgShift_wf : KCfgWf cfgShift := by unfold KCfgWf cfgShift; decide
@[expose] def cfgRejInit3 : RejSiteConfig :=
  { v := .varB, nLanes := 3, nChunks := 21, slotStride := 544,
    rIdx := .x8, rSqPtr := .x9, rPrevIdx := .x10,
    rSampArr := .x21, rSlotStride := .gpr 27#5, rSlotsBase := .x19 }
@[expose] def cfgRejExtra1 : RejSiteConfig :=
  { v := .varB, nLanes := 3, nChunks := 7, slotStride := 544,
    rIdx := .x10, rSqPtr := .x8, rPrevIdx := .x9,
    rSampArr := .x21, rSlotStride := .gpr 27#5, rSlotsBase := .x19 }
theorem cfgRejInit3_valid : cfgRejInit3.Valid := by decide +kernel
theorem cfgRejExtra1_valid : cfgRejExtra1.Valid := by decide +kernel

@[expose] def Seg2BaseRegInv [MlKemPlacement] (sp fpVal : BitVec 64) (s : State) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧ s.readReg64 .fp = fpVal ∧
  s.readReg64 .x19 = sp + 17376#64 ∧ s.readReg64 .x21 = sp + 29024#64 ∧
  s.readReg64 .x24 = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ∧
  s.readReg64 .x26 = sp + 27840#64 ∧ s.readReg64 .x27 = 544#64 ∧ s.readReg64 .x28 = sp + 28104#64

@[expose] def Seg2RegInv [MlKemPlacement] (sp fpVal : BitVec 64) (s : State) : Prop :=
  Seg2BaseRegInv sp fpVal s ∧ s.readReg64 .x20 = sp + 27851#64 ∧ s.readReg64 .x23 = 256#64

@[expose] def Seg2ConstWordsInv (sp : BitVec 64) (rho : List (BitVec 8))
    (tA : BTree (BitVec 64) 9) : Prop :=
  tA.get 0 = 0x001f0200#64 ∧ tA.get 1 = 0#64 ∧
  tA.get 2 = 0x001f0100#64 ∧ tA.get 3 = 0#64 ∧
  tA.get 5 = sp + 27851#64 ∧ tA.get 6 = sp + 9995#64 ∧
  tA.get 7 = sp + 11288#64 ∧ tA.get 8 = sp + 10248#64 ∧
  tA.get 9 = sp + 8416#64 ∧
  tA.get 36 = 0xffffffffff0000ff#64 ∧ tA.get 37 = 0xffffffffffffffff#64 ∧
  tA.get 38 = rhoW rho 3 ∧ tA.get 39 = rhoW rho 3 ∧
  tA.get 40 = rhoW rho 2 ∧ tA.get 41 = rhoW rho 2 ∧
  tA.get 42 = rhoW rho 1 ∧ tA.get 43 = rhoW rho 1 ∧
  tA.get 44 = rhoW rho 0 ∧ tA.get 45 = rhoW rho 0

@[expose] def slotHoldsLo (cfg : KCfg) (s : State) (tA : BTree (BitVec 64) 9)
    (sl : KSlot) (vLo : BitVec 64) : Prop :=
  ∃ vHi, slotHolds cfg s tA sl vLo vHi

@[expose] def Seg2LoopState [MlKemPlacement] (b sp fpVal : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (extra : Nat) (s : State) (P : SepProp) : Prop :=
  s.pc = b + 0x2300#64 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  Seg2RegInv sp fpVal s ∧
  s.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x22 = BitVec.ofNat 64 row ∧
  ∃ (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    Seg2ConstWordsInv sp rho tA ∧
    (∀ idx, idx < 25 →
      slotHolds cfgClamp s tA (inv01Slots.getD idx (.vreg 0))
        ((rowPermState rho row 0 (extra + 2)).getD idx 0#64)
        ((rowPermState rho row 1 (extra + 2)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHoldsLo cfgClamp s tA (inv2Slots.getD idx (.vreg 0))
        ((rowPermState rho row 2 (extra + 2)).getD idx 0#64)) ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (P ⊢ TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
      MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ memRegion (sp + 27840#64) 504 ∗
      MultiLaneSampled (sp + 29024#64) 3 sampled ∗ F)

@[expose] def Seg2RowDone [MlKemPlacement] (b sp fpVal : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (s : State) (P : SepProp) : Prop :=
  s.pc = b + 0x3048#64 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  Seg2RegInv sp fpVal s ∧
  s.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x22 = BitVec.ofNat 64 row ∧
  ∃ (extra : Nat) (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    allLanesDone 3 (rowSeeds rho row) extra = true ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    Seg2ConstWordsInv sp rho tA ∧
    (P ⊢ TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
      MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ memRegion (sp + 27840#64) 504 ∗
      memRegion (sp + 29024#64) 24 ∗ F)

theorem rowPermState_size {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col n : Nat) :
    (rowPermState rho row col n).size = 25 := by
  cases n with
  | zero => rw [rowPermState_zero hrho row col]; exact keccakF1600_size _
  | succ k => rw [← rowPermState_succ]; exact keccakF1600_size _

theorem keccakRc_intro [MlKemPlacement] {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog target_pc s
      (((mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29") ↦ᵣ
        mlkemData01Bytes) ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.roDataAt_intro hro.keccakRc (by decide +kernel) h

theorem multiLaneSampled3_eq_treeMem (sp : BitVec 64) (sampled : Nat → Nat)
    (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = BitVec.ofNat 64 (sampled 0)) (h1 : t.get 1 = BitVec.ofNat 64 (sampled 1))
    (h2 : t.get 2 = BitVec.ofNat 64 (sampled 2)) :
    MultiLaneSampled (sp + 29024#64) 3 sampled = TreeMem (sp + 29024#64) 3 t := by
  rw [TreeMem_eq_pointsToWords64]
  change MultiLaneSepFrom
      (fun i s => (sp + 29024#64 + BitVec.ofNat 64 (8 * i)) ↦₆₄ BitVec.ofNat 64 s) 0 3 sampled =
    pointsToWords64 (sp + 29024#64) [t.get 0, t.get 1, t.get 2]
  rw [h0, h1, h2]
  simp only [MultiLaneSepFrom, pointsToWords64_cons, pointsToWords64_nil,
    sepConj_emp, BitVec.add_assoc]; rfl

theorem replicate1632_eq_multiLaneSlots0 (sp : BitVec 64) :
    ((sp + 17376#64) ↦ₛ List.replicate 1632 0#8) =
      MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) := by
  have h544 : packHalfwordsLE (List.replicate 272 0#16) = List.replicate 544 0#8 :=
    packHalfwordsLE_replicate_zero 272
  have hsplit : List.replicate 1632 (0#8) =
      List.replicate 544 0#8 ++ (List.replicate 544 0#8 ++ List.replicate 544 0#8) := by
    rw [← List.replicate_add, ← List.replicate_add]
  rw [hsplit, pointsToBytes_append, pointsToBytes_append]
  simp only [MultiLaneSlots, MultiLaneSepFrom, h544, List.length_replicate,
    sepConj_emp, BitVec.add_assoc]; rfl

/-! ## 2. `TreeMem (sp + 64#64) 268` Entry/Exit Spatial Bridges & Clamp/Branch Helpers -/

private theorem vec128At_dup64 (a : BitVec 64) (w : BitVec 64) :
    Vec128At a (w ++ w) = (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ w) := by
  unfold Vec128At
  have h0 : (w ++ w).extractLsb' 0 64 = w := by bv_bits
  have h1 : (w ++ w).extractLsb' 64 64 = w := by bv_bits
  rw [h0, h1]

private theorem lo10_eq_treeMem (sp w4 : BitVec 64) (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = 0x001f0200#64) (h1 : t.get 1 = 0#64)
    (h2 : t.get 2 = 0x001f0100#64) (h3 : t.get 3 = 0#64) (h4 : t.get 4 = w4)
    (h5 : t.get 5 = sp + 27851#64) (h6 : t.get 6 = sp + 9995#64)
    (h7 : t.get 7 = sp + 11288#64) (h8 : t.get 8 = sp + 10248#64)
    (h9 : t.get 9 = sp + 8416#64) :
    Vec128At (sp + 64#64) 0x000000000000000000000000001f0200#128 ∗
      Vec128At (sp + 80#64) 0x000000000000000000000000001f0100#128 ∗
      ((sp + 96#64) ↦₆₄ w4) ∗
      ((sp + 104#64) ↦₆₄ (sp + 27851#64)) ∗
      ((sp + 112#64) ↦₆₄ (sp + 9995#64)) ∗
      ((sp + 120#64) ↦₆₄ (sp + 11288#64)) ∗
      ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) =
      TreeMem (sp + 64#64) 10 t := by
  rw [TreeMem_eq_pointsToWords64]
  change _ = pointsToWords64 (sp + 64#64)
    [t.get 0, t.get 1, t.get 2, t.get 3, t.get 4, t.get 5, t.get 6, t.get 7, t.get 8, t.get 9]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  unfold Vec128At
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc]
  rfl

private theorem mid10_eq_treeMem (sp : BitVec 64) (rho : List (BitVec 8)) (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = 0xffffffffff0000ff#64) (h1 : t.get 1 = 0xffffffffffffffff#64)
    (h2 : t.get 2 = rhoW rho 3) (h3 : t.get 3 = rhoW rho 3)
    (h4 : t.get 4 = rhoW rho 2) (h5 : t.get 5 = rhoW rho 2)
    (h6 : t.get 6 = rhoW rho 1) (h7 : t.get 7 = rhoW rho 1)
    (h8 : t.get 8 = rhoW rho 0) (h9 : t.get 9 = rhoW rho 0) :
    Vec128At (sp + 352#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
      Vec128At (sp + 368#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
      Vec128At (sp + 384#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
      Vec128At (sp + 400#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
      Vec128At (sp + 416#64) (packLane64 rho 0 ++ packLane64 rho 0) =
      TreeMem (sp + 352#64) 10 t := by
  rw [TreeMem_eq_pointsToWords64]
  change _ = pointsToWords64 (sp + 352#64)
    [t.get 0, t.get 1, t.get 2, t.get 3, t.get 4, t.get 5, t.get 6, t.get 7, t.get 8, t.get 9]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    vec128At_dup64 (sp + 368#64), vec128At_dup64 (sp + 384#64),
    vec128At_dup64 (sp + 400#64), vec128At_dup64 (sp + 416#64)]
  unfold Vec128At rhoW
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc]
  rfl

theorem entry_treeMem_join (sp w4 : BitVec 64) (rho : List (BitVec 8))
    (tMid tHi : BTree (BitVec 64) 9) :
    ∃ tA : BTree (BitVec 64) 9,
      Seg2ConstWordsInv sp rho tA ∧
      Seg2ConstSlots sp rho ∗ ((sp + 96#64) ↦₆₄ w4) ∗ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
        TreeMem (sp + 144#64) 26 tMid ∗ TreeMem (sp + 432#64) 222 tHi =
      ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        TreeMem (sp + 64#64) 268 tA := by
  let ws0 : List (BitVec 64) :=
    [0x001f0200#64, 0#64, 0x001f0100#64, 0#64, w4, sp + 27851#64,
     sp + 9995#64, sp + 11288#64, sp + 10248#64, sp + 8416#64]
  let ws2 : List (BitVec 64) :=
    [0xffffffffff0000ff#64, 0xffffffffffffffff#64, rhoW rho 3, rhoW rho 3,
     rhoW rho 2, rhoW rho 2, rhoW rho 1, rhoW rho 1, rhoW rho 0, rhoW rho 0]
  let t0 := btreeOfWords 0 ws0 zeroTree9
  let t2 := btreeOfWords 0 ws2 zeroTree9
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  have hlen0 : ws0.length = 10 := rfl
  have hlen2 : ws2.length = 10 := rfl
  have ht0 : ∀ i, i < 10 → t0.get i = ws0.getD i 0#64 := fun i hi => by
    simpa [Nat.zero_add] using btreeOfWords_get 0 ws0 zeroTree9 i (by omega) (by omega)
  have ht2 : ∀ i, i < 10 → t2.get i = ws2.getD i 0#64 := fun i hi => by
    simpa [Nat.zero_add] using btreeOfWords_get 0 ws2 zeroTree9 i (by omega) (by omega)
  let t01 := BTree.ofFn 9 fun i => if i < 10 then ws0.getD i 0#64 else tMid.get (i - 10)
  let t012 := BTree.ofFn 9 fun i => if i < 36 then t01.get i else ws2.getD (i - 36) 0#64
  let tA := BTree.ofFn 9 fun i => if i < 46 then t012.get i else tHi.get (i - 46)
  have hget0 : ∀ i, i < 10 → tA.get i = ws0.getD i 0#64 := fun i hi => by
    rw [BTree.get_ofFn 9 _ i (by omega)]
    simp only [show i < 46 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ i (by omega)]
    simp only [show i < 36 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ i (by omega)]
    simp only [hi, ↓reduceIte]
  have hget2 : ∀ i, i < 10 → tA.get (36 + i) = ws2.getD i 0#64 := fun i hi => by
    rw [BTree.get_ofFn 9 _ (36 + i) (by omega)]
    simp only [show 36 + i < 46 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ (36 + i) (by omega)]
    simp only [show ¬(36 + i < 36) by omega, ↓reduceIte, show 36 + i - 36 = i by omega]
  refine ⟨tA, ⟨hget0 0 (by decide), hget0 1 (by decide), hget0 2 (by decide), hget0 3 (by decide),
    hget0 5 (by decide), hget0 6 (by decide), hget0 7 (by decide), hget0 8 (by decide),
    hget0 9 (by decide), hget2 0 (by decide), hget2 1 (by decide), hget2 2 (by decide),
    hget2 3 (by decide), hget2 4 (by decide), hget2 5 (by decide), hget2 6 (by decide),
    hget2 7 (by decide), hget2 8 (by decide), hget2 9 (by decide)⟩, ?_⟩
  have hL0 := lo10_eq_treeMem sp w4 t0
    (ht0 0 (by decide)) (ht0 1 (by decide)) (ht0 2 (by decide)) (ht0 3 (by decide))
    (ht0 4 (by decide)) (ht0 5 (by decide)) (ht0 6 (by decide)) (ht0 7 (by decide))
    (ht0 8 (by decide)) (ht0 9 (by decide))
  have hL2 := mid10_eq_treeMem sp rho t2
    (ht2 0 (by decide)) (ht2 1 (by decide)) (ht2 2 (by decide)) (ht2 3 (by decide))
    (ht2 4 (by decide)) (ht2 5 (by decide)) (ht2 6 (by decide)) (ht2 7 (by decide))
    (ht2 8 (by decide)) (ht2 9 (by decide))
  have hJ1 : TreeMem (sp + 64#64) 10 t0 ∗ TreeMem (sp + 144#64) 26 tMid =
      TreeMem (sp + 64#64) 36 t01 := by
    rw [show sp + 144#64 = (sp + 64#64) + BitVec.ofNat 64 (8 * 10) by bv_omega]
    exact treeMem_join (n1 := 10) (n2 := 26) (t := t01)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi, ht0 i hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (10 + i) (by omega)]
        simp [show ¬(10 + i < 10) by omega, show 10 + i - 10 = i by omega])
  have hJ2 : TreeMem (sp + 64#64) 36 t01 ∗ TreeMem (sp + 352#64) 10 t2 =
      TreeMem (sp + 64#64) 46 t012 := by
    rw [show sp + 352#64 = (sp + 64#64) + BitVec.ofNat 64 (8 * 36) by bv_omega]
    exact treeMem_join (n1 := 36) (n2 := 10) (t := t012)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (36 + i) (by omega)]
        simp [show ¬(36 + i < 36) by omega, show 36 + i - 36 = i by omega, ht2 i hi])
  have hJ3 : TreeMem (sp + 64#64) 46 t012 ∗ TreeMem (sp + 432#64) 222 tHi =
      TreeMem (sp + 64#64) 268 tA := by
    rw [show sp + 432#64 = (sp + 64#64) + BitVec.ofNat 64 (8 * 46) by bv_omega]
    exact treeMem_join (n1 := 46) (n2 := 222) (t := tA)
      (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
      (fun i hi => by
        rw [BTree.get_ofFn 9 _ (46 + i) (by omega)]
        simp [show ¬(46 + i < 46) by omega, show 46 + i - 46 = i by omega])
  unfold Seg2ConstSlots
  rw [← hJ3, ← hJ2, ← hJ1, ← hL2, ← hL0]
  apply sepProp_ext <;> sep_frame

theorem exit_treeMem_entails (sp : BitVec 64) (tA : BTree (BitVec 64) 9)
    (h9 : tA.get 9 = sp + 8416#64) :
    TreeMem (sp + 64#64) 268 tA ⊢
      memRegion (sp + 64#64) 72 ∗ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
        memRegion (sp + 144#64) 2064 := by
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  let tHi := BTree.ofFn 9 fun i => tA.get (10 + i)
  have hsp1 := treeMem_split (ptr := sp + 64#64) (n1 := 10) (n2 := 258) (t := tA) (t2 := tHi)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)])
  rw [show sp + 64#64 + BitVec.ofNat 64 (8 * 10) = sp + 144#64 by bv_omega] at hsp1
  let t9 := BTree.ofFn 9 fun i => tA.get (9 + i)
  have hsp0 := treeMem_split (ptr := sp + 64#64) (n1 := 9) (n2 := 1) (t := tA) (t2 := t9)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)])
  rw [show sp + 64#64 + BitVec.ofNat 64 (8 * 9) = sp + 136#64 by bv_omega] at hsp0
  have ht9 : TreeMem (sp + 136#64) 1 t9 = ((sp + 136#64) ↦₆₄ (sp + 8416#64)) := by
    rw [TreeMem_eq_pointsToWords64]
    change pointsToWords64 (sp + 136#64) [t9.get 0] = _
    have hg0 : t9.get 0 = sp + 8416#64 := by
      simp [t9, BTree.get_ofFn 9 _ 0 (by decide), h9]
    rw [hg0, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]
  rw [hsp1, hsp0, ht9]
  exact Entails.trans (sepConj_mono
    (sepConj_mono_left (treeMem_entails_memRegion (ptr := sp + 64#64) (len := 9) tA (by decide)))
    (treeMem_entails_memRegion (ptr := sp + 144#64) (len := 258) tHi (by decide))) (by sep_frame)

private theorem selHi255_fin :
    ∀ s : Fin 272,
      (if 255#64 < BitVec.ofNat 64 s.val then 256#64 else BitVec.ofNat 64 s.val) =
        BitVec.ofNat 64 (clampSampled s.val) := by
  decide +kernel

theorem selHi255_of_le271 {s : Nat} (hs : s ≤ 271) :
    (if 255#64 < BitVec.ofNat 64 s then 256#64 else BitVec.ofNat 64 s) =
      BitVec.ofNat 64 (clampSampled s) := selHi255_fin ⟨s, by omega⟩

private theorem condCC_256_fin :
    ∀ s : Fin 272,
      ConditionHolds .CC (AddWithCarry64 (BitVec.ofNat 64 s.val) (~~~256#64) true).2 =
        decide (s.val < 256) := by
  decide +kernel

theorem condCC_256_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .CC (AddWithCarry64 (BitVec.ofNat 64 s) (~~~256#64) true).2 =
      decide (s < 256) := condCC_256_fin ⟨s, by omega⟩

private theorem condCS_256_fin :
    ∀ s : Fin 272,
      ConditionHolds .CS (AddWithCarry64 (BitVec.ofNat 64 s.val) (~~~256#64) true).2 =
        decide (256 ≤ s.val) := by
  decide +kernel

theorem condCS_256_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .CS (AddWithCarry64 (BitVec.ofNat 64 s) (~~~256#64) true).2 =
      decide (256 ≤ s) := condCS_256_fin ⟨s, by omega⟩

theorem condHI_255_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .HI (AddWithCarry64 (BitVec.ofNat 64 s) (~~~255#64) true).2 =
      decide (256 ≤ s) := by
  rw [condHolds_HI_255]
  have hmod : (BitVec.ofNat 64 s).toNat = s := Nat.mod_eq_of_lt (by omega)
  simp [BitVec.lt_def, hmod]; omega

theorem raw_sampled_le271 {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawXofInv N seeds extra sampled hws) {i : Nat} (hi : i < N) :
    sampled i ≤ 271 := by
  rcases (hraw i hi).2.1 with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega

theorem step_b_seg2 [MlKemPlacement] {b tgt : BitVec 64} {w : Nat} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlo : 183 ≤ w) (hhi : w < 3297) (hfw : fetchWordTree05 w = some (.b disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : SepWP (blkPC05.rebase b (fun _ => none)) tgt
      (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom) :
    SepWP (blkPC05.rebase b (fun _ => none)) tgt s P post oom := by
  refine SepWP.step_pure hpc hrun (fetch_blk05_seg2 hlo hhi hfw)
    (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl hnext
  rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hpc]

theorem step_bCond_seg2 [MlKemPlacement] {b tgt : BitVec 64} {w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlo : 183 ≤ w) (hhi : w < 3297) (hfw : fetchWordTree05 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC05.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC05.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC05.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk05_seg2 hlo hhi hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk05_seg2 hlo hhi hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]

/-! ## 3. `+0x02a8` Row Header & `+0x02b8 → +0x02dc` (`B29` `memset`) -/

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x02a8 → 0x02dc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local wp_norm ↓ high] exec_simdMovi_2d_0
attribute [local irreducible] blkLib05 TreeMem MultiLaneSlots

private theorem spAligned_of_eq {s1 s2 : State} {sp : BitVec 64}
    (hal : s1.spAligned = true) (h1 : s1.sp = sp) (h2 : s2.sp = sp) :
    s2.spAligned = true := by
  simpa [State.spAligned, h1, h2] using hal

theorem seg2_row_header_lt3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp fpVal : BitVec 64) (row : Nat) (tA : BTree (BitVec 64) 9) (Rest : SepProp)
    (hrow : row < 3) (ht5 : tA.get 5 = sp + 27851#64)
    (hpc : s.pc = b + 0x02a8#64) (hrun : s.status = .Running)
    (hreg : Seg2BaseRegInv sp fpVal s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 row) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) s
      (TreeMem (sp + 64#64) 268 tA ∗ Rest)
      (fun sf Pf => Seg2RegInv sp fpVal sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 row ∧
        (Pf ⊢ TreeMem (sp + 64#64) 268 tA ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨hsp, hal, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩
  have hload : SepLoad64 (sp + 104#64) (TreeMem (sp + 64#64) 268 tA ∗ Rest) (sp + 27851#64) := by
    rw [← ht5]
    exact BTreeMem.sepLoad64_treeMem (ptr := sp + 64#64) (len := 268) (idx := 5)
      (t := tA) (F := Rest) (by decide) (by decide) rfl (by bv_omega)
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hal
  refine SepWP.step_ldr64 (wb := none) (ea := sp + 104#64)
    (by wp_norm_lhs) hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) hload (by wp_norm_lhs) ?_
  wp_steps 2
  have hne3 : BitVec.ofNat 64 row ≠ 3#64 := by
    rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> decide
  refine SepWP.step_pure (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (s' := (((((s.writeReg64 (Reg.gpr 20#5) (sp + 27851#64)).writeReg64 (Reg.gpr 23#5) 256#64).setPState
      (subsPState64 (BitVec.ofNat 64 row) 3#64)).setPC (blkPl05.base + 692#64)).advancePC))
    (by simp [Program.evalInst, execInstWithSvc, State.setPC, hne3]) rfl ?_
  refine SepWP.done (by simp [State.advancePC, State.setPC, BitVec.add_assoc]) (by simp [hrun])
    ⟨⟨⟨by simp [hsp], spAligned_of_eq hal hsp (by simp [hsp]),
      by simp [hfp], by simp [hx19], by simp [hx21], by simp [hx24],
      by simp [hx26], by simp [hx27], by simp [hx28]⟩, by simp, by simp⟩,
      by simp [hx1], Entails.refl _⟩

/-- Offset `+0x3480` (`13440` B, entry to Segment 3) expressed without unary `Nat.mul` or 4-hex literals. -/
@[expose] def offSeg3Entry : BitVec 64 := 6720#64 + 6720#64

theorem seg2_row_header_eq3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp fpVal : BitVec 64) (tA : BTree (BitVec 64) 9) (Rest : SepProp)
    (ht5 : tA.get 5 = sp + 27851#64)
    (hpc : s.pc = b + 0x02a8#64) (hrun : s.status = .Running)
    (hreg : Seg2BaseRegInv sp fpVal s) (hx1 : s.readReg64 .x1 = 3#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offSeg3Entry) s
      (TreeMem (sp + 64#64) 268 tA ∗ Rest)
      (fun sf Pf => Seg2RegInv sp fpVal sf ∧ (Pf ⊢ TreeMem (sp + 64#64) 268 tA ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨hsp, hal, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩
  have hload : SepLoad64 (sp + 104#64) (TreeMem (sp + 64#64) 268 tA ∗ Rest) (sp + 27851#64) := by
    rw [← ht5]
    exact BTreeMem.sepLoad64_treeMem (ptr := sp + 64#64) (len := 268) (idx := 5)
      (t := tA) (F := Rest) (by decide) (by decide) rfl (by bv_omega)
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hal
  refine SepWP.step_ldr64 (wb := none) (ea := sp + 104#64)
    (by wp_norm_lhs) hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) hload (by wp_norm_lhs) ?_
  wp_steps 2
  have hpc_eq : blkPl05.base + 692#64 + 12748#64 = blkPl05.base + offSeg3Entry := by
    unfold offSeg3Entry; bv_omega
  refine SepWP.step_pure (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (s' := (((((s.writeReg64 (Reg.gpr 20#5) (sp + 27851#64)).writeReg64 (Reg.gpr 23#5) 256#64).setPState
      (subsPState64 3#64 3#64)).setPC (blkPl05.base + offSeg3Entry))))
    (by simp [Program.evalInst, execInstWithSvc, State.setPC, hpc_eq])
    (by simp [State.setPC]) ?_
  refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
    ⟨⟨⟨by simp [hsp], spAligned_of_eq hal hsp (by simp [hsp]),
      by simp [hfp], by simp [hx19], by simp [hx21], by simp [hx24],
      by simp [hx26], by simp [hx27], by simp [hx28]⟩, by simp, by simp⟩,
      Entails.refl _⟩

theorem seg2_row_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp fpVal : BitVec 64) (row : Nat) (Rest : SepProp)
    (hpc : s.pc = b + 0x02b8#64) (hrun : s.status = .Running)
    (hreg : Seg2RegInv sp fpVal s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 row)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02dc#64) s
      (memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 29024#64) 24 ∗ Rest)
      (fun sf Pf => Seg2RegInv sp fpVal sf ∧ sf.readReg64 .x22 = BitVec.ofNat 64 row ∧
        (Pf ⊢ MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨⟨hsp, hal, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩, hx20, hx23⟩
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hal
  rw [memRegion_split' (b := sp + 29024#64) (b' := sp + 29040#64) (n := 16) (k := (8 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.congr_pre (P1 := memRegion (sp + 29024#64) 16 ∗ memRegion (sp + 29040#64) 8 ∗
      memRegion (sp + 17376#64) 1632 ∗ Rest) (by apply sepProp_ext <;> sep_frame) ?_
  sep_frame_apply (Seg1Prologue.sepWP_elim_vec128 (a := sp + 29024#64)); intro v0
  refine SepWP.congr_pre (P1 := memRegion (sp + 29040#64) 8 ∗ Vec128At (sp + 29024#64) v0 ∗
      memRegion (sp + 17376#64) 1632 ∗ Rest) (by apply sepProp_ext <;> sep_frame) ?_
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 29040#64)); intro c2
  refine SepWP.congr_pre (P1 := memRegion (sp + 17376#64) 1632 ∗ ((sp + 29040#64) ↦₆₄ c2) ∗
      Vec128At (sp + 29024#64) v0 ∗ Rest) (by apply sepProp_ext <;> sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 6
  apply SepWP.step_str64 (wb := none) (ea := sp + 29040#64)
  · wp_norm_lhs
  · simp [hrun]
  · wp_norm_lhs
  · simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp]
  · simp [evalAddrMode, hsp]
  · rfl
  · exact (SepStore64.here rfl).left.right
  · wp_norm_lhs
  intro m1
  apply Encaps2.VecMem.step_strQ128 (wb := none) (ea := sp + 29024#64) (val := 0#128)
  · wp_norm_lhs
  · simp [hrun]
  · wp_norm_lhs
  · simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp]
  · simp [evalAddrMode, hsp]
  · simp
  · exact (Encaps2.VecMem.SepStore128.vec128At rfl).left.right.right
  · wp_norm_lhs
  intro m2
  wp_step
  wp_mlkem_call blk29_memset_ok (sp + 17376#64, 0#8, (1632 : Nat))
  refine SepWP.done (by wp_norm_lhs) ‹_›
    ⟨⟨⟨hsp_sf.trans (by simp [hsp]), spAligned_of_eq hal hsp (hsp_sf.trans (by simp [hsp])),
      Eq.trans ‹_› (by simp [hfp]), Eq.trans ‹_› (by simp [hx19]), Eq.trans ‹_› (by simp [hx21]),
      Eq.trans ‹_› (by simp [hx24]), Eq.trans ‹_› (by simp [hx26]), Eq.trans ‹_› (by simp [hx27]),
      Eq.trans ‹_› (by simp [hx28])⟩, Eq.trans ‹_› (by simp [hx20]), Eq.trans ‹_› (by simp [hx23])⟩,
      ‹_›, ?_⟩
  rw [replicate1632_eq_multiLaneSlots0 sp]
  have hsamp0 : Vec128At (sp + 29024#64) 0#128 ∗ ((sp + 29040#64) ↦₆₄ 0#64) =
      MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) := by
    unfold Vec128At MultiLaneSampled
    simp only [MultiLaneSepFrom, sepConj_emp, sepConj_assoc, BitVec.add_assoc]; rfl
  rw [← hsamp0]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
