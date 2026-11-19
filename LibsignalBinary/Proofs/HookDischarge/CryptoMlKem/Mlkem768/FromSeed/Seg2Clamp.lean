/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg

/-!
# `generate_keypair_compressed` (`B05`): `Seg2` symbolic entry builder and clamp dispatch

Shared symbolic entry state constructor (`mkSegState` / `mkSegEnv`) for `Seg2` ranges and proofs of
both post-`rej_sample` clamp/branch dispatchers (`+0x2290 → +0x2300 / +0x3048` for `init3` and
`+0x2f7c → +0x2300 / +0x3048` for `extra1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (blkLib05 blkPC05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem btreeOfWords btreeOfWords_get treeMem_entails_memRegion zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KStateMatches KSpatial matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep (
  sepWP_of_runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  btree_ext_get readSlot slotHolds slotValid vreg128_repack writeSlot)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  inv01Slots inv2Slots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  eval_checked_pstate eval_checked_slot rhoW rowPermState rowSeeds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2ConstWordsInv Seg2LoopState Seg2RegInv Seg2RowDone cfgClamp cfgClamp_wf
  condCC_256_of_le271 condCS_256_of_le271 condHI_255_of_le271 keccakRc_intro
  multiLaneSampled3_eq_treeMem raw_sampled_le271 selHi255_of_le271 slotHoldsLo
  step_bCond_seg2 step_b_seg2)

attribute [local irreducible] keccakF1600 blkLib05

/-! ## 1. Pre-Clamp Slot Tables (`+0x2290` & `+0x2f7c`) & Symbolic Entry State Builder -/

@[expose] def preClamp01Slots : List KSlot :=
  [.vreg 19, .vreg 15, .spillQ 1984, .spillQ 2128, .vreg 16, .vreg 31, .spillQ 1184, .vreg 30, .vreg 12, .vreg 28,
   .vreg 24, .vreg 14, .vreg 9, .vreg 25, .vreg 29, .spillQ 1072, .vreg 23, .spillQ 1168, .vreg 27, .vreg 26,
   .spillQ 1040, .spillQ 1216, .spillQ 1824, .spillQ 2144, .spillQ 2080]

@[expose] def preClamp2Slots : List KSlot :=
  [.vreg 7, .vreg 1, .spillQ 1760, .spillQ 2176, .spillQ 2096, .vreg 2, .spillQ 1744, .vreg 3, .spillQ 1872, .spillQ 2016,
   .spillQ 1680, .spillQ 1888, .vreg 5, .spillQ 1856, .spillQ 2000, .vreg 22, .spillQ 1712, .spillQ 1520, .spillQ 1552, .vreg 13,
   .vreg 8, .spillQ 1200, .spillQ 1968, .spillQ 2064, .spillQ 2112]

@[expose] def preExtra01Slots : List KSlot :=
  [.spillQ 1056, .spillQ 1792, .spillQ 1984, .spillQ 2128, .spillQ 2192, .spillQ 1664, .spillQ 1184, .spillQ 1840, .spillQ 1920, .spillQ 1952,
   .spillQ 1088, .spillQ 1120, .spillQ 1136, .spillQ 1152, .spillQ 1936, .spillQ 1072, .spillQ 1104, .spillQ 1168, .spillQ 2032, .spillQ 2048,
   .spillQ 1040, .spillQ 1216, .spillQ 1824, .spillQ 2144, .spillQ 2080]

@[expose] def preExtra2Slots : List KSlot :=
  [.vreg 7, .vreg 1, .spillQ 1760, .spillQ 2176, .spillQ 2096, .vreg 2, .vreg 18, .vreg 27, .vreg 16, .vreg 0,
   .spillQ 1680, .vreg 15, .vreg 21, .vreg 30, .vreg 4, .vreg 22, .vreg 24, .vreg 25, .spillQ 1552, .vreg 5,
   .vreg 8, .vreg 31, .vreg 17, .vreg 10, .vreg 20]

@[expose] def constMemAIdxs : List Nat :=
  [0, 1, 2, 3, 5, 6, 7, 8, 9, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]

@[expose] def constMemAExpr (i : Nat) : KExpr :=
  if i == 0 then .const64 0x001f0200#64 else if i == 1 then .const64 0#64
  else if i == 2 then .const64 0x001f0100#64 else if i == 3 then .const64 0#64
  else if i == 5 then .spAdd 27851#64 else if i == 6 then .spAdd 9995#64
  else if i == 7 then .spAdd 11288#64 else if i == 8 then .spAdd 10248#64
  else if i == 9 then .spAdd 8416#64
  else if i == 36 then .const64 0xffffffffff0000ff#64
  else if i == 37 then .const64 0xffffffffffffffff#64
  else if i == 38 || i == 39 then .var 106
  else if i == 40 || i == 41 then .var 105
  else if i == 42 || i == 43 then .var 104
  else if i == 44 || i == 45 then .var 103
  else .var (300 + i)

@[expose] def segGprExpr (g : Nat) : KExpr :=
  if g == 1 then .var 101
  else if g == 19 then .spAdd 17376#64
  else if g == 20 then .spAdd 27851#64
  else if g == 21 then .spAdd 29024#64
  else if g == 22 then .var 100
  else if g == 23 then .const64 256#64
  else if g == 24 then .rcAdd 0#64
  else if g == 26 then .spAdd 27840#64
  else if g == 27 then .const64 544#64
  else if g == 28 then .spAdd 28104#64
  else if g == 29 then .var 102
  else .var (200 + g)

@[expose] def mkSegBaseState (hasConsts : Bool) : KState :=
  { vregs := BTree.ofFn 5 fun vr => (.var (110 + 2 * vr), .var (110 + 2 * vr + 1))
    gprs := BTree.ofFn 5 segGprExpr
    memA := BTree.ofFn 9 fun i => if hasConsts then constMemAExpr i else .var (300 + i)
    memB := BTree.ofFn 9 fun i => .var (900 + i)
    pstate := none }

@[expose] def writeSlotsPair (cfg : KCfg) (offLo offHi : Nat) : Nat → List KSlot → KState → KState
  | _, [], st => st
  | idx, sl :: rest, st =>
      writeSlotsPair cfg offLo offHi (idx + 1) rest
        (writeSlot cfg st sl (.var (offLo + idx), .var (offHi + idx)))

@[expose] def mkSegState (cfg : KCfg) (hasConsts : Bool) (slots01 slots2 : List KSlot) : KState :=
  writeSlotsPair cfg 50 75 0 slots2 (writeSlotsPair cfg 0 25 0 slots01 (mkSegBaseState hasConsts))

@[expose] def mkSegEnv [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat) (rho : List (BitVec 8))
    (k0 k1 k2 : KeccakState) (k2Hi : Nat → BitVec 64) (s : State) (tA tB : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp
    rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    rLoop := 0
    vars := fun id =>
      if id < 25 then k0.getD id 0#64
      else if id < 50 then k1.getD (id - 25) 0#64
      else if id < 75 then k2.getD (id - 50) 0#64
      else if id < 100 then k2Hi (id - 75)
      else if id == 100 then BitVec.ofNat 64 row
      else if id == 101 then s.readReg64 .x1
      else if id == 102 then fpVal
      else if id == 103 then rhoW rho 0
      else if id == 104 then rhoW rho 1
      else if id == 105 then rhoW rho 2
      else if id == 106 then rhoW rho 3
      else if id < 174 then
        let k := id - 110
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 }

private theorem writeSlot_preserves {cfg : KCfg} {env : KEnv} {st : KState} {s : State}
    {tA : BTree (BitVec 64) 9} {sl : KSlot} {p : KExpr × KExpr}
    (hm : KStateMatches env st s) (htA : st.memA.map (evalKExpr env) = tA)
    (hsl : slotHolds cfg s tA sl (evalKExpr env p.1) (evalKExpr env p.2)) :
    KStateMatches env (writeSlot cfg st sl p) s ∧
      (writeSlot cfg st sl p).memA.map (evalKExpr env) = tA ∧
      (writeSlot cfg st sl p).memB = st.memB := by
  cases sl with
  | vreg r =>
      rcases hsl with ⟨hr, hv⟩; refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpstate⟩, htA, rfl⟩
      intro vr; simp only [writeSlot]; rw [BTree.get_set _ r p hr vr.toNat vr.isLt]
      by_cases heq : vr.toNat = r
      · have hvr : vr = BitVec.ofNat 5 r := BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hr])
        subst hvr; simpa [heq] using hv
      · simp [heq]; exact hm.hvregs vr
  | spillQ off =>
      rcases hsl with ⟨hidx, hlo, hhi⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩, ?_, rfl⟩
      apply btree_ext_get; intro j hj
      simp only [writeSlot, BTree.get_map]
      rw [BTree.get_set _ _ _ hidx j hj]
      by_cases h1 : j = (off - cfg.offA) / 8 + 1
      · subst h1; simpa using hhi.symm
      · simp only [h1, ↓reduceIte]; rw [BTree.get_set _ _ _ (by omega) j hj]
        by_cases h0 : j = (off - cfg.offA) / 8
        · subst h0; simpa using hlo.symm
        · simp only [h0, ↓reduceIte]; rw [← htA, BTree.get_map]

private theorem mkSegEnv_var_ge110 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {rho : List (BitVec 8)} {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64}
    {s : State} {tA tB : BTree (BitVec 64) 9} {id : Nat} (hid : 110 ≤ id) :
    (mkSegEnv sp fpVal row rho k0 k1 k2 k2Hi s tA tB).vars id =
      if id < 174 then
        let k := id - 110
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 := by
  simp only [mkSegEnv, show ¬(id < 25) by omega, show ¬(id < 50) by omega,
    show ¬(id < 75) by omega, show ¬(id < 100) by omega,
    beq_false_of_ne (show id ≠ 100 by omega), beq_false_of_ne (show id ≠ 101 by omega),
    beq_false_of_ne (show id ≠ 102 by omega), beq_false_of_ne (show id ≠ 103 by omega),
    beq_false_of_ne (show id ≠ 104 by omega), beq_false_of_ne (show id ≠ 105 by omega),
    beq_false_of_ne (show id ≠ 106 by omega), Bool.false_eq_true, ↓reduceIte]

private theorem mkSegBaseState_matches [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {rho : List (BitVec 8)} {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64}
    {s : State} {tA tB : BTree (BitVec 64) 9} {hasConsts : Bool}
    (hreg : Seg2RegInv sp fpVal s) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : hasConsts = true → Seg2ConstWordsInv sp rho tA) :
    let env := mkSegEnv sp fpVal row rho k0 k1 k2 k2Hi s tA tB
    KStateMatches env (mkSegBaseState hasConsts) s ∧
      (mkSegBaseState hasConsts).memA.map (evalKExpr env) = tA ∧
      (mkSegBaseState hasConsts).memB.map (evalKExpr env) = tB := by
  intro env
  rcases hreg with ⟨⟨hsp, hspA, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩, hx20, hx23⟩
  refine ⟨⟨hsp, hspA, ?_, ?_, fun _ _ h => nomatch h⟩, ?_, ?_⟩
  · intro vr
    simp only [mkSegBaseState]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
    have hlt := vr.isLt
    simp only [evalKExpr, env, mkSegEnv_var_ge110 (show 110 ≤ 110 + 2 * vr.toNat by omega),
      mkSegEnv_var_ge110 (show 110 ≤ 110 + 2 * vr.toNat + 1 by omega),
      show 110 + 2 * vr.toNat < 174 by omega, show 110 + 2 * vr.toNat + 1 < 174 by omega,
      ↓reduceIte, show (110 + 2 * vr.toNat - 110) / 2 = vr.toNat by omega,
      show ((110 + 2 * vr.toNat - 110) % 2 == 0) = true from beq_iff_eq.mpr (by omega),
      show (110 + 2 * vr.toNat + 1 - 110) / 2 = vr.toNat by omega,
      show ((110 + 2 * vr.toNat + 1 - 110) % 2 == 0) = false from beq_false_of_ne (by omega),
      Bool.false_eq_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g hg31
    simp only [mkSegBaseState]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
    have hlt := g.isLt
    by_cases h1 : g = 1#5; · subst h1; rfl
    by_cases h19 : g = 19#5; · subst h19; exact hx19
    by_cases h20 : g = 20#5; · subst h20; exact hx20
    by_cases h21 : g = 21#5; · subst h21; exact hx21
    by_cases h22 : g = 22#5; · subst h22; exact hx22
    by_cases h23 : g = 23#5; · subst h23; exact hx23
    by_cases h24 : g = 24#5; · subst h24; simpa [segGprExpr, evalKExpr, env, mkSegEnv] using hx24
    by_cases h26 : g = 26#5; · subst h26; exact hx26
    by_cases h27 : g = 27#5; · subst h27; exact hx27
    by_cases h28 : g = 28#5; · subst h28; exact hx28
    by_cases h29 : g = 29#5; · subst h29; exact hfp
    have hne : ∀ c : Fin 32, g ≠ BitVec.ofNat 5 c.1 → (g.toNat == c.1) = false := fun c hc =>
      beq_false_of_ne fun he => hc (BitVec.eq_of_toNat_eq (by simp [he]))
    simp only [segGprExpr, hne ⟨1, by decide⟩ h1, hne ⟨19, by decide⟩ h19, hne ⟨20, by decide⟩ h20,
      hne ⟨21, by decide⟩ h21, hne ⟨22, by decide⟩ h22, hne ⟨23, by decide⟩ h23,
      hne ⟨24, by decide⟩ h24, hne ⟨26, by decide⟩ h26, hne ⟨27, by decide⟩ h27,
      hne ⟨28, by decide⟩ h28, hne ⟨29, by decide⟩ h29, Bool.false_eq_true, ↓reduceIte,
      evalKExpr, env, mkSegEnv_var_ge110 (show 110 ≤ 200 + g.toNat by omega),
      show ¬(200 + g.toNat < 174) by omega, show 200 + g.toNat < 232 by omega,
      show 200 + g.toNat - 200 = g.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · apply btree_ext_get; intro j hj
    simp only [BTree.get_map, mkSegBaseState]; rw [BTree.get_ofFn 9 _ j hj]
    cases hasConsts with
    | false =>
        simp [evalKExpr, env, mkSegEnv_var_ge110 (show 110 ≤ 300 + j by omega),
          show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
          show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
    | true =>
        rcases htA rfl with ⟨c0, c1, c2, c3, c5, c6, c7, c8, c9, c36, c37,
          c38, c39, c40, c41, c42, c43, c44, c45⟩
        by_cases hj10 : j < 10
        · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [constMemAExpr, evalKExpr, env, mkSegEnv, c0, c1, c2, c3, c5, c6, c7, c8, c9]
        · by_cases hj36 : 36 ≤ j ∧ j < 46
          · rcases (show j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 by omega) with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [constMemAExpr, evalKExpr, env, mkSegEnv, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45]
          · have hne : ∀ c, c ≠ j → (j == c) = false := fun _ hc => beq_false_of_ne hc.symm
            simp only [↓reduceIte, constMemAExpr, hne 0 (by omega), hne 1 (by omega), hne 2 (by omega),
              hne 3 (by omega), hne 5 (by omega), hne 6 (by omega), hne 7 (by omega), hne 8 (by omega),
              hne 9 (by omega), hne 36 (by omega), hne 37 (by omega), hne 38 (by omega), hne 39 (by omega),
              hne 40 (by omega), hne 41 (by omega), hne 42 (by omega), hne 43 (by omega),
              hne 44 (by omega), hne 45 (by omega), Bool.false_or, Bool.false_eq_true,
              evalKExpr, env, mkSegEnv_var_ge110 (show 110 ≤ 300 + j by omega),
              show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
              show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
  · apply btree_ext_get; intro j hj
    simp only [BTree.get_map, mkSegBaseState]; rw [BTree.get_ofFn 9 _ j hj]
    simp [evalKExpr, env, mkSegEnv_var_ge110 (show 110 ≤ 900 + j by omega),
      show ¬(900 + j < 174) by omega, show ¬(900 + j < 232) by omega,
      show ¬(900 + j < 812) by omega, show 900 + j < 1412 by omega, show 900 + j - 900 = j by omega]

private theorem writeSlotsPair_matches {cfg : KCfg} {env : KEnv} {offLo offHi : Nat}
    {fLo fHi : Nat → BitVec 64} {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hvLo : ∀ k, k < 25 → evalKExpr env (.var (offLo + k)) = fLo k)
    (hvHi : ∀ k, k < 25 → evalKExpr env (.var (offHi + k)) = fHi k)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length ≤ 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (fLo (k + j)) (fHi (k + j))) →
      KStateMatches env st s → st.memA.map (evalKExpr env) = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsPair cfg offLo offHi k rem st) s ∧
        (writeSlotsPair cfg offLo offHi k rem st).memA.map (evalKExpr env) = tA ∧
        (writeSlotsPair cfg offLo offHi k rem st).memB = mB0 := by
  induction rem with
  | nil => intro _ _ _ _ hm htA hmB; exact ⟨hm, htA, hmB⟩
  | cons sl rest ih =>
      intro k st hsum hsl hm htA hmB
      have hlen : (sl :: rest).length = rest.length + 1 := rfl
      have hk : k < 25 := by omega
      have hsl0 : slotHolds cfg s tA sl
          (evalKExpr env (.var (offLo + k))) (evalKExpr env (.var (offHi + k))) := by
        rw [hvLo k hk, hvHi k hk]
        simpa only [List.getD_cons_zero, Nat.add_zero] using hsl 0 (by omega)
      rcases writeSlot_preserves (p := (.var (offLo + k), .var (offHi + k))) hm htA hsl0
        with ⟨hm1, htA1, hmB1⟩
      exact ih (k + 1) _ (by omega)
        (fun j hj => by
          have hj1 := hsl (j + 1) (by omega)
          rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega] at hj1
          exact hj1)
        hm1 htA1 (hmB1.trans hmB)

theorem mkSegState_matches [MlKemPlacement] {cfg : KCfg} {hasConsts : Bool}
    {slots01 slots2 : List KSlot} {sp fpVal : BitVec 64} {row : Nat} {rho : List (BitVec 8)}
    {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64} {s : State} {tA tB : BTree (BitVec 64) 9}
    (hl01 : slots01.length ≤ 25) (hl2 : slots2.length ≤ 25)
    (hreg : Seg2RegInv sp fpVal s) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : hasConsts = true → Seg2ConstWordsInv sp rho tA)
    (hs01 : ∀ idx, idx < slots01.length →
      slotHolds cfg s tA (slots01.getD idx (.vreg 0)) (k0.getD idx 0#64) (k1.getD idx 0#64))
    (hs2 : ∀ idx, idx < slots2.length →
      slotHolds cfg s tA (slots2.getD idx (.vreg 0)) (k2.getD idx 0#64) (k2Hi idx)) :
    let env := mkSegEnv sp fpVal row rho k0 k1 k2 k2Hi s tA tB
    let st := mkSegState cfg hasConsts slots01 slots2
    KStateMatches env st s ∧ st.memA.map (evalKExpr env) = tA ∧ st.memB.map (evalKExpr env) = tB := by
  intro env st
  rcases mkSegBaseState_matches (k0 := k0) (k1 := k1) (k2 := k2) (k2Hi := k2Hi)
    (tA := tA) (tB := tB) hreg hx22 htA with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 → evalKExpr env (.var (0 + k)) = k0.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, env, mkSegEnv, hk]
  have hv1 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = k1.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv, show ¬(25 + k < 25) by omega,
      show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  have hv2 : ∀ k, k < 25 → evalKExpr env (.var (50 + k)) = k2.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv, show ¬(50 + k < 25) by omega,
      show ¬(50 + k < 50) by omega, show 50 + k < 75 by omega, show 50 + k - 50 = k by omega]
  have hv2Hi : ∀ k, k < 25 → evalKExpr env (.var (75 + k)) = k2Hi k := fun k hk => by
    simp [evalKExpr, env, mkSegEnv, show ¬(75 + k < 25) by omega,
      show ¬(75 + k < 50) by omega, show ¬(75 + k < 75) by omega,
      show 75 + k < 100 by omega, show 75 + k - 75 = k by omega]
  rcases writeSlotsPair_matches (cfg := cfg) hv0 hv1 slots01 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs01 j hj) hm0 htA0 rfl with ⟨hm1, htA1, hmB1⟩
  rcases writeSlotsPair_matches (cfg := cfg) hv2 hv2Hi slots2 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs2 j hj) hm1 htA1 rfl with ⟨hm2, htA2, hmB2⟩
  exact ⟨hm2, htA2, by dsimp only [st, mkSegState]; rw [hmB2, hmB1, htB0]⟩

/-! ## 2. Clamp Post-State Checker & `+0x2290` / `+0x2f7c` Dispatchers -/

@[expose] def checkSegRegGprs (st : KState) (eX1 : KExpr) : Bool :=
  (st.gprs.get 1).beq eX1 &&
  (st.gprs.get 19).beq (.spAdd 17376#64) &&
  (st.gprs.get 20).beq (.spAdd 27851#64) &&
  (st.gprs.get 21).beq (.spAdd 29024#64) &&
  (st.gprs.get 22).beq (.var 100) &&
  (st.gprs.get 23).beq (.const64 256#64) &&
  (st.gprs.get 24).beq (.rcAdd 0#64) &&
  (st.gprs.get 26).beq (.spAdd 27840#64) &&
  (st.gprs.get 27).beq (.const64 544#64) &&
  (st.gprs.get 28).beq (.spAdd 28104#64) &&
  (st.gprs.get 29).beq (.var 102)

@[expose] def checkConstWordsMemA (st : KState) : Bool :=
  constMemAIdxs.all fun i => (st.memA.get i).beq (constMemAExpr i)

@[expose] def checkClampEnd (st : KState) (checkInvSlots : Bool) : Bool :=
  checkSegRegGprs st (.var 101) &&
  checkConstWordsMemA st &&
  (st.memB.get 0).beq (.selHi255 (.var 900) (.const64 256#64) (.var 900)) &&
  (st.memB.get 1).beq (.selHi255 (.var 901) (.const64 256#64) (.var 901)) &&
  (st.memB.get 2).beq (.selHi255 (.var 902) (.const64 256#64) (.var 902)) &&
  (!checkInvSlots ||
    (((List.range 25).all fun idx =>
        let sl := inv01Slots.getD idx (.vreg 0)
        slotValid cfgClamp sl &&
          (readSlot cfgClamp st sl).1.beq (.var idx) &&
          (readSlot cfgClamp st sl).2.beq (.var (25 + idx))) &&
     ((List.range 25).all fun idx =>
        let sl := inv2Slots.getD idx (.vreg 0)
        slotValid cfgClamp sl &&
          (readSlot cfgClamp st sl).1.beq (.var (50 + idx)))))

theorem eq_some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o <;> simp_all

theorem sepWP_drop_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {A Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s (A ∗ Q) post oom := by
  unfold SepWP at h ⊢; intro R hm
  exact h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm))

theorem with_frozen_env [MlKemPlacement] {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf =>
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem → post sf Pf)) :
    SepWP prog tgt s P post :=
  SepWP.mono_frozen (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
    ⟨hcl, hro⟩ h (fun _ _ _ _ ⟨hc, hr⟩ hp => hp hc hr)

theorem extract_segRegInv [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat} {eX1 : KExpr}
    {env : KEnv} {st : KState} {sf : State}
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv100 : env.vars 100 = BitVec.ofNat 64 row) (hv102 : env.vars 102 = fpVal)
    (hchk : checkSegRegGprs st eX1 = true) :
    Seg2RegInv sp fpVal sf ∧ sf.readReg64 .x1 = evalKExpr env eX1 ∧
      sf.readReg64 .x22 = BitVec.ofNat 64 row := by
  simp only [checkSegRegGprs, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g19⟩, g20⟩, g21⟩, g22⟩, g23⟩, g24⟩, g26⟩, g27⟩, g28⟩, g29⟩
  have rg : ∀ (g : Fin 32), g.1 ≠ 31 → ∀ {e : KExpr}, (st.gprs.get g.1).beq e = true →
      sf.readReg64 (.gpr (BitVec.ofNat 5 g.1)) = evalKExpr env e := by
    intro g hg e hb
    have r := hm.hgprs (BitVec.ofNat 5 g.1) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt g.2]; have := g.2; omega)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt g.2, KExpr.beq_eq_true hb] at r
    exact r
  refine ⟨⟨⟨hm.hsp.trans hsp, hm.hsp_al, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
    rg ⟨1, by decide⟩ (by decide) g1, ?_⟩
  · simpa [evalKExpr, hv102] using rg ⟨29, by decide⟩ (by decide) g29
  · simpa [evalKExpr, hsp] using rg ⟨19, by decide⟩ (by decide) g19
  · simpa [evalKExpr, hsp] using rg ⟨21, by decide⟩ (by decide) g21
  · simpa [evalKExpr, hrc] using rg ⟨24, by decide⟩ (by decide) g24
  · simpa [evalKExpr, hsp] using rg ⟨26, by decide⟩ (by decide) g26
  · simpa [evalKExpr] using rg ⟨27, by decide⟩ (by decide) g27
  · simpa [evalKExpr, hsp] using rg ⟨28, by decide⟩ (by decide) g28
  · simpa [evalKExpr, hsp] using rg ⟨20, by decide⟩ (by decide) g20
  · simpa [evalKExpr] using rg ⟨23, by decide⟩ (by decide) g23
  · simpa [evalKExpr, hv100] using rg ⟨22, by decide⟩ (by decide) g22

theorem extract_constWords {sp : BitVec 64} {rho : List (BitVec 8)} {env : KEnv} {st : KState}
    (hsp : env.sp = sp)
    (hv103 : env.vars 103 = rhoW rho 0) (hv104 : env.vars 104 = rhoW rho 1)
    (hv105 : env.vars 105 = rhoW rho 2) (hv106 : env.vars 106 = rhoW rho 3)
    (hchk : checkConstWordsMemA st = true) :
    Seg2ConstWordsInv sp rho (st.memA.map (evalKExpr env)) := by
  have hc : ∀ (i : Nat), i ∈ constMemAIdxs →
      (st.memA.map (evalKExpr env)).get i = evalKExpr env (constMemAExpr i) := fun i hi => by
    have hb := (List.all_eq_true.mp hchk) i hi
    rw [BTree.get_map, KExpr.beq_eq_true hb]
  exact ⟨hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
    (hc 5 (by decide)).trans (by simp [constMemAExpr, evalKExpr, hsp]),
    (hc 6 (by decide)).trans (by simp [constMemAExpr, evalKExpr, hsp]),
    (hc 7 (by decide)).trans (by simp [constMemAExpr, evalKExpr, hsp]),
    (hc 8 (by decide)).trans (by simp [constMemAExpr, evalKExpr, hsp]),
    (hc 9 (by decide)).trans (by simp [constMemAExpr, evalKExpr, hsp]),
    hc 36 (by decide), hc 37 (by decide),
    (hc 38 (by decide)).trans hv106, (hc 39 (by decide)).trans hv106,
    (hc 40 (by decide)).trans hv105, (hc 41 (by decide)).trans hv105,
    (hc 42 (by decide)).trans hv104, (hc 43 (by decide)).trans hv104,
    (hc 44 (by decide)).trans hv103, (hc 45 (by decide)).trans hv103⟩

theorem exprVarsOk_true : ∀ e : KExpr, Seg2Base.exprVarsOk (fun _ => true) e = true := by
  intro e; induction e <;> simp_all [Seg2Base.exprVarsOk]

theorem kexprBeq_refl : ∀ e : KExpr, e.beq e = true := by
  intro e; induction e <;> simp_all [KExpr.beq]

theorem finish_clamp_branch [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row extra : Nat} {F : SepProp}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    {env : KEnv} {st : KState} {sf : State}
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) extra sampled hws)
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv100 : env.vars 100 = BitVec.ofNat 64 row)
    (hv101 : env.vars 101 = BitVec.ofNat 64 (row + 1))
    (hv102 : env.vars 102 = fpVal)
    (hv103 : env.vars 103 = rhoW rho 0) (hv104 : env.vars 104 = rhoW rho 1)
    (hv105 : env.vars 105 = rhoW rho 2) (hv106 : env.vars 106 = rhoW rho 3)
    (hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64)
    (hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64)
    (hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64)
    (hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0))
    (hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1))
    (hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2))
    (isExit : Bool) (hdone : allLanesDone 3 (rowSeeds rho row) extra = isExit)
    (hpc : sf.pc = if isExit then b + 0x3048#64 else b + 0x2300#64)
    (hrun : sf.status = .Running)
    (hchk : checkClampEnd st (!isExit) = true) :
    let FF := memRegion (sp + 9984#64) 1512 ∗
      MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ memRegion (sp + 27840#64) 504 ∗ F
    SepWP (blkPC05.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) extra then b + 0x3048#64 else b + 0x2300#64)
      sf (KSpatial cfgClamp env st FF)
      (fun sOut POut => mlkemMultiLib.CodeLoaded mlkemMpl sOut.mem → MlKemRoOk mlkemMpl sOut.mem →
        if allLanesDone 3 (rowSeeds rho row) extra then Seg2RowDone b sp fpVal rho row F sOut POut
        else Seg2LoopState b sp fpVal rho row F extra sOut POut) := by
  intro FF; rw [hdone]
  simp only [checkClampEnd, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hregC, hconstC⟩, hm0⟩, hm1⟩, hm2⟩, hslotsC⟩
  rcases extract_segRegInv hm hsp hrc hv100 hv102 hregC with ⟨hreg, hx1, hx22⟩
  rw [evalKExpr, hv101] at hx1
  have htA := extract_constWords hsp hv103 hv104 hv105 hv106 hconstC
  have hclamp : MultiLaneXofInv 3 (rowSeeds rho row) extra (fun i => clampSampled (sampled i)) hws :=
    hraw.clamp
  have htB : ∀ i, i < 3 →
      (st.memB.map (evalKExpr env)).get i = BitVec.ofNat 64 (clampSampled (sampled i)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [BTree.get_map, KExpr.beq_eq_true hm0, evalKExpr, evalKExpr, evalKExpr, hb0]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [BTree.get_map, KExpr.beq_eq_true hm1, evalKExpr, evalKExpr, evalKExpr, hb1]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [BTree.get_map, KExpr.beq_eq_true hm2, evalKExpr, evalKExpr, evalKExpr, hb2]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
  have hsampMem : TreeMem (sp + 29024#64) 3 (st.memB.map (evalKExpr env)) =
      MultiLaneSampled (sp + 29024#64) 3 (fun i => clampSampled (sampled i)) :=
    (multiLaneSampled3_eq_treeMem sp _ _
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide))).symm
  apply sepWP_drop_left
  cases isExit with
  | true =>
      simp only [↓reduceIte] at hpc ⊢
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx1, hx22, extra,
        st.memA.map (evalKExpr env), fun i => clampSampled (sampled i), hws, hdone, hclamp, htA, ?_⟩
      dsimp only [cfgClamp, FF]
      rw [hsp, show sp + BitVec.ofNat 64 64 = sp + 64#64 from rfl,
        show sp + BitVec.ofNat 64 29024 = sp + 29024#64 from rfl]
      exact Entails.trans (by sep_frame : _ ⊢ TreeMem (sp + 29024#64) 3 (st.memB.map (evalKExpr env)) ∗
          (TreeMem (sp + 64#64) 268 (st.memA.map (evalKExpr env)) ∗
            memRegion (sp + 9984#64) 1512 ∗ MultiLaneSlots (sp + 17376#64) 544 3 hws ∗
            memRegion (sp + 27840#64) 504 ∗ F))
        (Entails.trans (sepConj_mono_left
          (treeMem_entails_memRegion (ptr := sp + 29024#64) (len := 3) (st.memB.map (evalKExpr env)) (by decide)))
          (by sep_frame))
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
      simp only [Bool.not_false, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hslotsC
      rcases hslotsC with ⟨hs01, hs2⟩
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx1, hx22,
        st.memA.map (evalKExpr env), fun i => clampSampled (sampled i), hws, htA, ?_, ?_, hclamp, ?_⟩
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs01) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        have hsl := eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1.1 _ _ hi.1.2 hi.2 rfl rfl
        simpa [evalKExpr, hv0 idx hidx, hv1 idx hidx] using hsl
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs2) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        refine ⟨evalKExpr env (readSlot cfgClamp st (inv2Slots.getD idx (.vreg 0))).2, ?_⟩
        have hsl := eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1 (.var (50 + idx))
          (readSlot cfgClamp st (inv2Slots.getD idx (.vreg 0))).2
          hi.2 (kexprBeq_refl _) rfl (exprVarsOk_true _)
        simpa [evalKExpr, hv2 idx hidx] using hsl
      · dsimp only [cfgClamp, FF]
        rw [hsp, show sp + BitVec.ofNat 64 64 = sp + 64#64 from rfl,
          show sp + BitVec.ofNat 64 29024 = sp + 29024#64 from rfl, hsampMem]
        sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
