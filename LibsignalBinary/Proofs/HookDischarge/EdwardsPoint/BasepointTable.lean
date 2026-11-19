/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `EdwardsBasepointTable` Machine-Code Proofs

Machine-code proofs in `dalekCliMultiLib` for:
- `<LookupTable<AffineNielsPoint>>::select` (`B09`, 191 insns, stack 192)
- `<EdwardsBasepointTable as BasepointTable>::mul_base` (`B26`, 167 insns, stack 1680)
- `<&Scalar as Mul<&EdwardsBasepointTable>>::mul` (`B27`, 4 insns, stack 1680)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.BasepointTable

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul fpNeg EdExtPoint edExtZero)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase dalekCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes fe51_one fe51OneBytes ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded scalarRadix16Digits scalarRadix16Digits_length
  Fe51MulOk ScalarAsRadix16Ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  readLE_slice_eq fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edAddAffineNiels edDouble4
  fe51AffineNielsBoundedAt fe51LookupTable8Bounded edTableEntryAt edSelectAffineNiels
  fe51BasepointTable32Bounded fe51BasepointTable32Bounded_mono
  edMulBaseStep edMulBaseStepAt edMulBaseLoopWith edMulBaseLoop edMulBase
  EdwardsPointMulByPow2_4Ok EdwardsPointAddAffineNielsOk
  LookupTableAffineNielsSelectOk EdwardsBasepointTableMulBaseOk ScalarMulBasepointTableOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add write64_length_eq
  readLE_write64_self' readLE_write64_ne readLE_append_left readLE_append_right
  pointsToBytesRO_take_drop fold_fe51ValOfBytes edAsExtended_of_append4
  fe51_mul_post_props fe51Reduce_bounded fe51Reduce_val_mod fe51Neg_val_mod
  sepWP_abstract_bytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_split_stack_callee sepWP_merge_stack_callee)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (fe51LimbsBoundedAt_mono)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  readLE_cons8 fe51OneBytes_length
  fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24
  ed25519BasepointTableBytes_length)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (black_box_u8_ok)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 09 dalekCliMultiLib DalekCliPlacement 191 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl09_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl09.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 26 dalekCliMultiLib DalekCliPlacement 167 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl26_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl26.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 27 dalekCliMultiLib DalekCliPlacement 4 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl27_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl27.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

/-! ## 1. `<LookupTable<AffineNielsPoint>>::select` (`B09`) Private Helpers -/

private theorem sbfx_getLsbD_7 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 r)).getLsbD 7 = x.getLsbD 7 := by subst h; simp

private theorem sxtb_low8 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 r) >>> 0 &&& 255#64 = BitVec.zeroExtend 64 x := by
  subst h; ext i hi
  have h255 := (by decide : ∀ k (hk : k < 64), (255#64)[k] = decide (k < 8)) i hi
  by_cases h8 : i < 8
  · simp [h255, h8, show i < 32 by omega]
  · simp [h255, h8]

private theorem sbfx_bit7 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 r) >>> 7 &&& 1#64 = BitVec.zeroExtend 64 x >>> 7 &&& 1#64 := by
  subst h; ext i hi
  have h1 := (by decide : ∀ k (hk : k < 64), (1#64)[k] = decide (k = 0)) i hi
  by_cases hi0 : i = 0 <;> simp [h1, hi0]

private theorem and_255_of_zeroExtend8_ite (r : BitVec 64) (c : Bool)
    (h : BitVec.zeroExtend 8 r = if c then 1#8 else 0#8) :
    r &&& 255#64 = if c then 1#64 else 0#64 := by
  have h255 : r &&& 255#64 = BitVec.zeroExtend 64 (BitVec.zeroExtend 8 r) := by
    ext i hi
    have hm := (by decide : ∀ k (hk : k < 64), (255#64)[k] = decide (k < 8)) i hi
    simp [hm, Bool.and_comm]; rfl
  rw [h255, h]; cases c <;> rfl

private theorem neg_ite_one_zero (c : Bool) :
    -(if c then 1#64 else 0#64) = if c then 18446744073709551615#64 else 0#64 := by cases c <;> rfl
private theorem sub_one_ite_one_zero (c : Bool) :
    (if c then 1#64 else 0#64) - 1#64 = if c then 0#64 else 18446744073709551615#64 := by cases c <;> rfl
private def sel64 (c : Bool) (t f : BitVec 64) : BitVec 64 := if c then t else f
private theorem and_allOnes_64 (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  ext i hi; simp [(by decide : ∀ k (hk : k < 64), (18446744073709551615#64)[k] = true) i hi]
private theorem sel64_and_allOnes_zero (x : BitVec 64) (c : Bool) :
    x &&& (if c then 18446744073709551615#64 else 0#64) = sel64 c x 0#64 := by cases c <;> simp [sel64, and_allOnes_64]
private theorem and_ite_zero_allOnes (x : BitVec 64) (c : Bool) :
    x &&& (if c then 0#64 else 18446744073709551615#64) = if c then 0#64 else x := by cases c <;> simp [and_allOnes_64]
private theorem sel64_or_left (c : Bool) (x y : BitVec 64) :
    sel64 c x 0#64 ||| (if c then 0#64 else y) = sel64 c x y := by cases c <;> simp [sel64]
private theorem xor_and_sel64_lhs (a b : BitVec 64) (c : Bool) :
    sel64 c (a ^^^ b) 0#64 ^^^ a = sel64 c b a := by cases c <;> simp [sel64]; ext i hi; simp; cases a[i] <;> cases b[i] <;> rfl
private theorem xor_and_sel64_rhs (a b : BitVec 64) (c : Bool) :
    sel64 c (a ^^^ b) 0#64 ^^^ b = sel64 c a b := by cases c <;> simp [sel64]
private theorem eq_of_eq_rhs {α : Type} {lhs rhs1 rhs2 : α} (h1 : lhs = rhs1) (h2 : rhs1 = rhs2) : lhs = rhs2 := h1.trans h2

private theorem ubfx_high32_sign (v : BitVec 64) (x : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 32 32
      (v &&& 4294967295#64 ||| BitVec.zeroExtend 64 (BitVec.setWidth 32
        (BitVec.zeroExtend 64 x ||| (if x.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&&
          18446744073709551360#64)) <<< 32)) >>> 7 &&& 1#64) =
    if x.getLsbD 7 = true then 1#8 else 0#8 := by
  have hex : ∀ (a : BitVec 64) (b : BitVec 32),
      BitVec.extractLsb' 32 32 (a &&& 4294967295#64 ||| BitVec.zeroExtend 64 b <<< 32) = b := by
    intro a b; ext i hi
    have hmask : (4294967295#64)[32 + i]'(by omega) = false := by revert i hi; decide
    simp [hi, show ¬ (32 + i < 32) by omega, show 32 + i < 64 by omega]
    intro _ h; rw [hmask] at h; contradiction
  rw [hex]; revert x; decide

private def HoldEq {α : Type} (a b : α) : Prop := a = b
private theorem hold_reg {lhs rhs : BitVec 64} (h : lhs = rhs) : ∃ v, HoldEq v rhs ∧ lhs = v := ⟨rhs, rfl, h⟩

private theorem hold_stack7 {prog : Program} {target_pc : BitVec 64} {s : State}
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 F : SepProp}
    {p104 p112 p120 p128 p136 p144 p152 v104 v112 v120 v128 v136 v144 v152 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ u104 u112 u120 u128 u136 u144 u152,
      HoldEq u104 v104 → HoldEq u112 v112 → HoldEq u120 v120 → HoldEq u128 v128 →
      HoldEq u136 v136 → HoldEq u144 v144 → HoldEq u152 v152 →
      SepWP prog target_pc s (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗
        (p104 ↦₆₄ u104) ∗ (p112 ↦₆₄ u112) ∗ (p120 ↦₆₄ u120) ∗ (p128 ↦₆₄ u128) ∗
        (p136 ↦₆₄ u136) ∗ (p144 ↦₆₄ u144) ∗ (p152 ↦₆₄ u152) ∗ F) post oom) :
    SepWP prog target_pc s (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗
      (p104 ↦₆₄ v104) ∗ (p112 ↦₆₄ v112) ∗ (p120 ↦₆₄ v120) ∗ (p128 ↦₆₄ v128) ∗
      (p136 ↦₆₄ v136) ∗ (p144 ↦₆₄ v144) ∗ (p152 ↦₆₄ v152) ∗ F) post oom :=
  h v104 v112 v120 v128 v136 v144 v152 rfl rfl rfl rfl rfl rfl rfl

private theorem getLsbD_7_eq_msb (x : BitVec 8) : x.getLsbD 7 = x.msb := by revert x; decide

private theorem fe51Bounds_hold_chain4 {c4 c3 c2 c1 : Bool} {B : Nat} {u0 u1 u2 u3 u4
    a4_0 a4_1 a4_2 a4_3 a4_4 a3_0 a3_1 a3_2 a3_3 a3_4 a2_0 a2_1 a2_2 a2_3 a2_4 a1_0 a1_1 a1_2 a1_3 a1_4 b0 b1 b2 b3 b4 : BitVec 64}
    (h0 : HoldEq u0 (sel64 c4 a4_0 (sel64 c3 a3_0 (sel64 c2 a2_0 (sel64 c1 a1_0 b0)))))
    (h1 : HoldEq u1 (sel64 c4 a4_1 (sel64 c3 a3_1 (sel64 c2 a2_1 (sel64 c1 a1_1 b1)))))
    (h2 : HoldEq u2 (sel64 c4 a4_2 (sel64 c3 a3_2 (sel64 c2 a2_2 (sel64 c1 a1_2 b2)))))
    (h3 : HoldEq u3 (sel64 c4 a4_3 (sel64 c3 a3_3 (sel64 c2 a2_3 (sel64 c1 a1_3 b3)))))
    (h4 : HoldEq u4 (sel64 c4 a4_4 (sel64 c3 a3_4 (sel64 c2 a2_4 (sel64 c1 a1_4 b4)))))
    (ha4 : a4_0.toNat < B ∧ a4_1.toNat < B ∧ a4_2.toNat < B ∧ a4_3.toNat < B ∧ a4_4.toNat < B)
    (ha3 : a3_0.toNat < B ∧ a3_1.toNat < B ∧ a3_2.toNat < B ∧ a3_3.toNat < B ∧ a3_4.toNat < B)
    (ha2 : a2_0.toNat < B ∧ a2_1.toNat < B ∧ a2_2.toNat < B ∧ a2_3.toNat < B ∧ a2_4.toNat < B)
    (ha1 : a1_0.toNat < B ∧ a1_1.toNat < B ∧ a1_2.toNat < B ∧ a1_3.toNat < B ∧ a1_4.toNat < B)
    (hb : b0.toNat < B ∧ b1.toNat < B ∧ b2.toNat < B ∧ b3.toNat < B ∧ b4.toNat < B) :
    u0.toNat < B ∧ u1.toNat < B ∧ u2.toNat < B ∧ u3.toNat < B ∧ u4.toNat < B := by
  rw [h0, h1, h2, h3, h4]; cases c4 <;> cases c3 <;> cases c2 <;> cases c1 <;> assumption

private theorem fe51Val_hold_chain4 {c4 c3 c2 c1 : Bool} {u0 u1 u2 u3 u4
    a4_0 a4_1 a4_2 a4_3 a4_4 a3_0 a3_1 a3_2 a3_3 a3_4 a2_0 a2_1 a2_2 a2_3 a2_4 a1_0 a1_1 a1_2 a1_3 a1_4 b0 b1 b2 b3 b4 : BitVec 64}
    (h0 : HoldEq u0 (sel64 c4 a4_0 (sel64 c3 a3_0 (sel64 c2 a2_0 (sel64 c1 a1_0 b0)))))
    (h1 : HoldEq u1 (sel64 c4 a4_1 (sel64 c3 a3_1 (sel64 c2 a2_1 (sel64 c1 a1_1 b1)))))
    (h2 : HoldEq u2 (sel64 c4 a4_2 (sel64 c3 a3_2 (sel64 c2 a2_2 (sel64 c1 a1_2 b2)))))
    (h3 : HoldEq u3 (sel64 c4 a4_3 (sel64 c3 a3_3 (sel64 c2 a2_3 (sel64 c1 a1_3 b3)))))
    (h4 : HoldEq u4 (sel64 c4 a4_4 (sel64 c3 a3_4 (sel64 c2 a2_4 (sel64 c1 a1_4 b4))))) :
    fe51Val u0 u1 u2 u3 u4 =
      if c4 then fe51Val a4_0 a4_1 a4_2 a4_3 a4_4 else if c3 then fe51Val a3_0 a3_1 a3_2 a3_3 a3_4
      else if c2 then fe51Val a2_0 a2_1 a2_2 a2_3 a2_4 else if c1 then fe51Val a1_0 a1_1 a1_2 a1_3 a1_4
      else fe51Val b0 b1 b2 b3 b4 := by
  rw [h0, h1, h2, h3, h4]; cases c4 <;> cases c3 <;> cases c2 <;> cases c1 <;> rfl

private theorem writeSelectEpilogue_spec (bs table_bs : List (BitVec 8)) (x : BitVec 8)
    (yp0 yp1 yp2 yp3 yp4 ym0 ym1 ym2 ym3 ym4 d0 d1 d2 d3 d4 : BitVec 64) (hbs : bs.length = 120)
    (hyp_b : yp0.toNat < 2 ^ 53 ∧ yp1.toNat < 2 ^ 53 ∧ yp2.toNat < 2 ^ 53 ∧ yp3.toNat < 2 ^ 53 ∧ yp4.toNat < 2 ^ 53)
    (hym_b : ym0.toNat < 2 ^ 53 ∧ ym1.toNat < 2 ^ 53 ∧ ym2.toNat < 2 ^ 53 ∧ ym3.toNat < 2 ^ 53 ∧ ym4.toNat < 2 ^ 53)
    (hd_b : d0.toNat < 2 ^ 53 ∧ d1.toNat < 2 ^ 53 ∧ d2.toNat < 2 ^ 53 ∧ d3.toNat < 2 ^ 53 ∧ d4.toNat < 2 ^ 53)
    (hyp_v : fe51Val yp0 yp1 yp2 yp3 yp4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 840 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 720
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 600 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 480
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 360 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 240
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 120 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 0 else 1)
    (hym_v : fe51Val ym0 ym1 ym2 ym3 ym4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 880 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 760
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 640 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 520
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 400 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 280
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 160 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 40 else 1)
    (hd_v : fe51Val d0 d1 d2 d3 d4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 920 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 800
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 680 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 560
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 440 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 320
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 200 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 80 else 0) :
    let s := x.getLsbD 7
    let res_bs :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 bs
        0 (sel64 s ym0 yp0)) 8 (sel64 s ym1 yp1)) 32 (sel64 s ym4 yp4))
        40 (sel64 s yp0 ym0)) 48 (sel64 s yp1 ym1)) 56 (sel64 s yp2 ym2))
        16 (sel64 s ym2 yp2)) 24 (sel64 s ym3 yp3)) 64 (sel64 s yp3 ym3))
        72 (sel64 s yp4 ym4))
        80 (sel64 s ((36028797018963664#64 - d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 ((36028797018963952#64 - d4) >>> 51)) * 19#64) d0))
        88 (sel64 s ((36028797018963952#64 - d1 &&& 2251799813685247#64) + (36028797018963664#64 - d0) >>> 51) d1))
        96 (sel64 s ((36028797018963952#64 - d2 &&& 2251799813685247#64) + (36028797018963952#64 - d1) >>> 51) d2))
        104 (sel64 s ((36028797018963952#64 - d3 &&& 2251799813685247#64) + (36028797018963952#64 - d2) >>> 51) d3))
        112 (sel64 s ((36028797018963952#64 - d4 &&& 2251799813685247#64) + (36028797018963952#64 - d3) >>> 51) d4)
    res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
      (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
        edSelectAffineNiels table_bs x := by
  intro s res_bs; haveI : HasLenGe bs 120 := ⟨by omega⟩
  have hlen : res_bs.length = 120 := by dsimp only [res_bs]; simp only [write64_length_eq, hbs]; decide
  have ⟨hr0, hr1, hr2, hr3, hr4⟩ := fe51Reduce_bounded (36028797018963664#64 - d0) (36028797018963952#64 - d1)
    (36028797018963952#64 - d2) (36028797018963952#64 - d3) (36028797018963952#64 - d4)
  have hred_b := And.intro (Nat.lt_trans hr0 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr1 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr2 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr3 (by decide : 2 ^ 52 < 2 ^ 53))
               (Nat.lt_trans hr4 (by decide : 2 ^ 52 < 2 ^ 53)))))
  have hbnd : fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) := by
    dsimp only [res_bs, fe51AffineNielsBoundedAt, fe51LimbsBoundedAt]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    cases s <;> simp only [sel64, ↓ite_true, Bool.false_eq_true, ↓ite_false]
    · exact ⟨hyp_b, hym_b, hd_b⟩
    · exact ⟨hym_b, hyp_b, hred_b⟩
  have hval : (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
      if x.msb then (fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fpNeg (fe51Val d0 d1 d2 d3 d4 % p25519))
      else (fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val d0 d1 d2 d3 d4 % p25519) := by
    dsimp only [res_bs, s, fe51ValAt]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    rw [getLsbD_7_eq_msb x]; cases x.msb <;> simp only [sel64, ↓ite_true, Bool.false_eq_true, ↓ite_false]
    rw [fe51Reduce_val_mod, fe51Neg_val_mod d0 d1 d2 d3 d4 ⟨by omega, by omega, by omega, by omega, by omega⟩]
  have hsel : (fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val d0 d1 d2 d3 d4 % p25519) =
      if x == 8#8 || x == -8#8 then edTableEntryAt table_bs 7 else if x == 7#8 || x == -7#8 then edTableEntryAt table_bs 6
      else if x == 6#8 || x == -6#8 then edTableEntryAt table_bs 5 else if x == 5#8 || x == -5#8 then edTableEntryAt table_bs 4
      else if x == 4#8 || x == -4#8 then edTableEntryAt table_bs 3 else if x == 3#8 || x == -3#8 then edTableEntryAt table_bs 2
      else if x == 2#8 || x == -2#8 then edTableEntryAt table_bs 1 else if x == 1#8 || x == -1#8 then edTableEntryAt table_bs 0
      else (1, 1, 0) := by
    rw [hyp_v, hym_v, hd_v]
    cases (x == 8#8 || x == -8#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 7#8 || x == -7#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 6#8 || x == -6#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 5#8 || x == -5#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 4#8 || x == -4#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 3#8 || x == -3#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 2#8 || x == -2#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 1#8 || x == -1#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> rfl
  refine ⟨hlen, hbnd, ?_⟩; rw [hval]; unfold edSelectAffineNiels; rw [← hsel]

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_frame)
    (hoff : off = off' + 8 := by decide) (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (h : SepWP prog tpc s (memRegion (sp - BitVec.ofNat 64 off) n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  have ha : sp - BitVec.ofNat 64 off + 8#64 = sp - BitVec.ofNat 64 off' := by
    change sp - BitVec.ofNat 64 off + BitVec.ofNat 64 8 = sp - BitVec.ofNat 64 off'
    rw [sub_ofNat64_add sp off 8 (by omega), show off - 8 = off' by omega]
  rw [← ha] at hP; exact SepWP.head_region (sp - BitVec.ofNat 64 off) n m hnm hb hP h

local syntax "close_cells_sub " term:max num num num : tactic
macro_rules
  | `(tactic| close_cells_sub $sp $off $n $k) => do
    let (off, n, k) := (off.getNat, n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then
      let offLit := Lean.Syntax.mkNumLit (toString off)
      `(tactic| apply SepWP.last_region ($sp - BitVec.ofNat 64 $offLit))
    else
      let (offLit, off'Lit, nLit, n'Lit, k'Lit) := (Lean.Syntax.mkNumLit (toString off), Lean.Syntax.mkNumLit (toString (off - 8)),
        Lean.Syntax.mkNumLit (toString n), Lean.Syntax.mkNumLit (toString (n - 8)), Lean.Syntax.mkNumLit (toString (k - 1)))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem lookup_table_affine_niels_select_tail [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl09 b) (hbase : dalekCliPl09.base = b)
    (R : SepProp) (s0 sf : State) (a_1 a v_sp176_lo : BitVec 64)
    (a_2 : BitVec 8) (a_3 a_rest_1 : List (BitVec 8))
    (d2_4 d1_4 yp0_4 ym1_4 ym0_4 d0_4 d4_4 d3_4 ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4 : BitVec 64)
    {oom : State → SepProp}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (h_4 : a_3.length = 120)
    (h : fe51LookupTable8Bounded a_rest_1 (2 ^ 53))
    (hpc_sf : sf.pc = b + 136#64) (hrun_sf : sf.status = ExecStatus.Running)
    (hsp_sf : sf.sp = s0.sp - 176#64)
    (h_5 : sf.readReg64 (Reg.gpr 19#5) = d2_4) (h_6 : sf.readReg64 (Reg.gpr 20#5) = d1_4)
    (h_7 : sf.readReg64 (Reg.gpr 21#5) = yp0_4) (h_8 : sf.readReg64 (Reg.gpr 22#5) = ym1_4)
    (h_9 : sf.readReg64 (Reg.gpr 23#5) = ym0_4) (h_10 : sf.readReg64 (Reg.gpr 24#5) = d0_4)
    (h_11 : sf.readReg64 (Reg.gpr 25#5) = a + 536#64) (h_12 : sf.readReg64 (Reg.gpr 26#5) = 5#64)
    (h_13 : sf.readReg64 (Reg.gpr 27#5) = d4_4) (h_14 : sf.readReg64 (Reg.gpr 28#5) = d3_4)
    (hcs_sf : sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl sf.mem)
    (hpost : BitVec.zeroExtend 8 (sf.readReg64 (Reg.gpr 0#5)) = if (a_2 == 5#8 || a_2 == -5#8) then 1#8 else 0#8)
    (hyp4_b : yp0_4.toNat < 2 ^ 53 ∧ yp1_4.toNat < 2 ^ 53 ∧ yp2_4.toNat < 2 ^ 53 ∧ yp3_4.toNat < 2 ^ 53 ∧ yp4_4.toNat < 2 ^ 53)
    (hym4_b : ym0_4.toNat < 2 ^ 53 ∧ ym1_4.toNat < 2 ^ 53 ∧ ym2_4.toNat < 2 ^ 53 ∧ ym3_4.toNat < 2 ^ 53 ∧ ym4_4.toNat < 2 ^ 53)
    (hd4_b : d0_4.toNat < 2 ^ 53 ∧ d1_4.toNat < 2 ^ 53 ∧ d2_4.toNat < 2 ^ 53 ∧ d3_4.toNat < 2 ^ 53 ∧ d4_4.toNat < 2 ^ 53)
    (hyp4_v : fe51Val yp0_4 yp1_4 yp2_4 yp3_4 yp4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 360 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 240
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 120 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 0 else 1)
    (hym4_v : fe51Val ym0_4 ym1_4 ym2_4 ym3_4 ym4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 400 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 280
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 160 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 40 else 1)
    (hd4_v : fe51Val d0_4 d1_4 d2_4 d3_4 d4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 440 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 320
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 200 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 80 else 0) :
    SepWP (dalekCliPC09.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf
      (memRegion (s0.sp - 176#64 - 16#64) 16 ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗ (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗ (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗ (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗ (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 104#64) ↦₆₄ ym4_4 ∗ (s0.sp - 112#64) ↦₆₄ ym3_4 ∗ (s0.sp - 120#64) ↦₆₄ yp3_4 ∗ (s0.sp - 128#64) ↦₆₄ yp4_4 ∗
        (s0.sp - 136#64) ↦₆₄ ym2_4 ∗ (s0.sp - 144#64) ↦₆₄ yp1_4 ∗ (s0.sp - 152#64) ↦₆₄ yp2_4 ∗ (s0.sp - 160#64) ↦₆₄
          (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 >>> 7 &&& 1#64 |||
              (if a_2.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64)) <<< 32 |||
            BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 >>> 7 &&& 1#64 |||
              (if a_2.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64) +
              BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 |||
                (if a_2.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64))) ∗
        (s0.sp - 168#64) ↦₆₄ a_1 ∗ (s0.sp - 176#64) ↦₆₄ (v_sp176_lo &&& 4294967295#64 |||
          BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 |||
            (if a_2.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64)) <<< 32) ∗
        a ↦ᵣ a_rest_1 ∗ a_1 ↦ₛ a_3)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (a ↦ᵣ a_rest_1 ∗ stackFrame sf 192 ∗
        ∃∗ res_bs, a_1 ↦ₛ res_bs ∗ ⌜res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
          (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
            edSelectAffineNiels a_rest_1 a_2⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  have htab_len : a_rest_1.length = 960 := h.1
  haveI : HasLenGe a_3 120 := ⟨by omega⟩; haveI : HasLenGe a_rest_1 960 := ⟨by omega⟩
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 6#8 || a_2 == -6#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 7#8 || a_2 == -7#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 8#8 || a_2 == -8#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if a_2.getLsbD 7 then 1#8 else 0#8 := eq_of_eq_rhs hpost (ubfx_high32_sign _ a_2)
  rcases hold_reg h_5 with ⟨d2, hd2, h_5⟩; rcases hold_reg h_6 with ⟨d1, hd1, h_6⟩; rcases hold_reg h_7 with ⟨yp0, hyp0, h_7⟩
  rcases hold_reg h_8 with ⟨ym1, hym1, h_8⟩; rcases hold_reg h_9 with ⟨ym0, hym0, h_9⟩; rcases hold_reg h_10 with ⟨d0, hd0, h_10⟩
  rcases hold_reg h_13 with ⟨d4, hd4, h_13⟩; rcases hold_reg h_14 with ⟨d3, hd3, h_14⟩
  apply hold_stack7; intro ym4 ym3 yp3 yp4 ym2 yp1 yp2 hym4 hym3 hyp3 hyp4 hym2 hyp1 hyp2
  wp_steps; simp only [and_255_of_zeroExtend8_ite _ _ hpost, neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left, xor_and_sel64_lhs, xor_and_sel64_rhs]; clear hpost
  apply sepWP_abstract_bytes a_1
    (fun res_bs => res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
      (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) = edSelectAffineNiels a_rest_1 a_2)
  · rcases h with ⟨_, _, _, _, _, ⟨hb4_0, hb4_40, hb4_80⟩, ⟨hb5_0, hb5_40, hb5_80⟩, ⟨hb6_0, hb6_40, hb6_80⟩, ⟨hb7_0, hb7_40, hb7_80⟩⟩
    exact writeSelectEpilogue_spec a_3 a_rest_1 a_2 yp0 yp1 yp2 yp3 yp4 ym0 ym1 ym2 ym3 ym4 d0 d1 d2 d3 d4 h_4
      (fe51Bounds_hold_chain4 hyp0 hyp1 hyp2 hyp3 hyp4 hb7_0 hb6_0 hb5_0 hb4_0 hyp4_b)
      (fe51Bounds_hold_chain4 hym0 hym1 hym2 hym3 hym4 hb7_40 hb6_40 hb5_40 hb4_40 hym4_b)
      (fe51Bounds_hold_chain4 hd0 hd1 hd2 hd3 hd4 hb7_80 hb6_80 hb5_80 hb4_80 hd4_b)
      (by rw [fe51Val_hold_chain4 hyp0 hyp1 hyp2 hyp3 hyp4, hyp4_v]; rfl)
      (by rw [fe51Val_hold_chain4 hym0 hym1 hym2 hym3 hym4, hym4_v]; rfl)
      (by rw [fe51Val_hold_chain4 hd0 hd1 hd2 hd3 hd4, hd4_v]; rfl)
  intro res_bs ⟨hres_len, ⟨hb0, hb40, hb80⟩, hres_val⟩
  have hres_bnd : fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) := ⟨hb0, hb40, hb80⟩
  unpack_fe51_at hb0; unpack_fe51_at hb40; unpack_fe51_at hb80
  close_cells_sub s0.sp 176 176 22; apply sepWP_merge_stack_callee 16 176; wp_done

/-! ## 2. `<EdwardsBasepointTable as BasepointTable>::mul_base` (`B26`) Private Helpers -/

private def checkWordsBounded (bs : List (BitVec 8)) (bound : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 => match bs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      decide ((pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat < bound) && checkWordsBounded rest bound rem
    | _ => false

private theorem of_checkWordsBounded {bs : List (BitVec 8)} {bound rem k : Nat}
    (h : checkWordsBounded bs bound rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (8 * k) 8).toNat < bound := by
  induction rem generalizing bs k with
  | zero => omega
  | succ rem ih =>
    unfold checkWordsBounded at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; rcases k with _ | k
    · rw [Nat.mul_zero, ← ByteSlice.pack64_eq_readLE_8]; exact h.1
    · rw [show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]; exact ih h.2 (by omega)

private theorem checkWordsBounded_ed25519BasepointTable :
    checkWordsBounded ed25519BasepointTableBytes (2 ^ 52) 3840 = true := by decide +kernel

private theorem ed25519BasepointTableBytes_bounded :
    fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52) := by
  refine ⟨ed25519BasepointTableBytes_length, fun i hi => ?_⟩
  have hlen : (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960).length = 960 := by
    change ((ed25519BasepointTableBytes.drop (960 * i)).take 960).length = 960
    simp only [List.length_take, List.length_drop, ed25519BasepointTableBytes_length]; omega
  have hlimb (j : Nat) (hj : j < 120) :
      (ByteSlice.readLE (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) (8 * j) 8).toNat < 2 ^ 52 := by
    rw [readLE_slice_eq ed25519BasepointTableBytes (960 * i) 960 (8 * j) (by rw [decide_eq_true_eq]; omega),
        show 960 * i + 8 * j = 8 * (120 * i + j) by omega]
    exact of_checkWordsBounded checkWordsBounded_ed25519BasepointTable (by omega)
  have hentry (e : Nat) (he : e < 8) :
      fe51AffineNielsBoundedAt (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) (120 * e) (2 ^ 52) :=
    ⟨⟨by simpa [show 120 * e = 8 * (15 * e) by omega] using hlimb (15 * e) (by omega),
      by simpa [show 120 * e + 8 = 8 * (15 * e + 1) by omega] using hlimb (15 * e + 1) (by omega),
      by simpa [show 120 * e + 16 = 8 * (15 * e + 2) by omega] using hlimb (15 * e + 2) (by omega),
      by simpa [show 120 * e + 24 = 8 * (15 * e + 3) by omega] using hlimb (15 * e + 3) (by omega),
      by simpa [show 120 * e + 32 = 8 * (15 * e + 4) by omega] using hlimb (15 * e + 4) (by omega)⟩,
     ⟨by simpa [show 120 * e + 40 = 8 * (15 * e + 5) by omega] using hlimb (15 * e + 5) (by omega),
      by simpa [show 120 * e + 40 + 8 = 8 * (15 * e + 6) by omega] using hlimb (15 * e + 6) (by omega),
      by simpa [show 120 * e + 40 + 16 = 8 * (15 * e + 7) by omega] using hlimb (15 * e + 7) (by omega),
      by simpa [show 120 * e + 40 + 24 = 8 * (15 * e + 8) by omega] using hlimb (15 * e + 8) (by omega),
      by simpa [show 120 * e + 40 + 32 = 8 * (15 * e + 9) by omega] using hlimb (15 * e + 9) (by omega)⟩,
     ⟨by simpa [show 120 * e + 80 = 8 * (15 * e + 10) by omega] using hlimb (15 * e + 10) (by omega),
      by simpa [show 120 * e + 80 + 8 = 8 * (15 * e + 11) by omega] using hlimb (15 * e + 11) (by omega),
      by simpa [show 120 * e + 80 + 16 = 8 * (15 * e + 12) by omega] using hlimb (15 * e + 12) (by omega),
      by simpa [show 120 * e + 80 + 24 = 8 * (15 * e + 13) by omega] using hlimb (15 * e + 13) (by omega),
      by simpa [show 120 * e + 80 + 32 = 8 * (15 * e + 14) by omega] using hlimb (15 * e + 14) (by omega)⟩⟩
  exact ⟨hlen, by simpa using hentry 0 (by decide), by simpa using hentry 1 (by decide),
    by simpa using hentry 2 (by decide), by simpa using hentry 3 (by decide),
    by simpa using hentry 4 (by decide), by simpa using hentry 5 (by decide),
    by simpa using hentry 6 (by decide), by simpa using hentry 7 (by decide)⟩

attribute [local irreducible] fe51LookupTable8Bounded

private theorem pointsToBytesRO_split3 (a : BitVec 64) (bs : List (BitVec 8)) (off len : Nat)
    (h : off + len ≤ bs.length) :
    (a ↦ᵣ bs) =
      ((a + BitVec.ofNat 64 off) ↦ᵣ ProofLib.ByteSlice.slice bs off len) ∗
      ((a ↦ᵣ bs.take off) ∗ ((a + BitVec.ofNat 64 (off + len)) ↦ᵣ bs.drop (off + len))) := by
  rw [pointsToBytesRO_take_drop a off bs (by omega),
      pointsToBytesRO_take_drop (a + BitVec.ofNat 64 off) len (bs.drop off) (by simp; omega),
      List.drop_drop]
  have hadd : a + BitVec.ofNat 64 off + BitVec.ofNat 64 len = a + BitVec.ofNat 64 (off + len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadd]
  unfold ProofLib.ByteSlice.slice
  sep_ac_rfl

private theorem mul_base_init_post (dst : List (BitVec 8)) (hdst : dst.length = 160) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 32 0#64) 72 0#64) 120 0#64) 128 0#64) 136 0#64) 144 0#64)
        40 (ByteSlice.readLE fe51OneBytes 0 8)) 48 (ByteSlice.readLE fe51OneBytes 8 8)) 0 0#64) 8 0#64) 16 0#64) 24 0#64)
        56 (ByteSlice.readLE fe51OneBytes 16 8)) 64 (ByteSlice.readLE fe51OneBytes 24 8)) 112 0#64)
        80 (ByteSlice.readLE fe51OneBytes 0 8)) 88 (ByteSlice.readLE fe51OneBytes 8 8))
        96 (ByteSlice.readLE fe51OneBytes 16 8)) 104 (ByteSlice.readLE fe51OneBytes 24 8)) 152 0#64
    fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero := by
  haveI : HasLenGe dst 160 := ⟨by omega⟩
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes edExtZero
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne,
    write64_length_eq, hdst, fe51One_readLE_0, fe51One_readLE_8, fe51One_readLE_16, fe51One_readLE_24]
  decide +kernel

private theorem copy160_point4_post (dst src : List (BitVec 8)) (P : EdExtPoint) (bound : Nat)
    (hdst : dst.length = 160) (hsrc_b : fe51Point4Bounded src bound) (hsrc_v : edExtOfBytes src = P) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 96 (ByteSlice.readLE src 96 8)) 104 (ByteSlice.readLE src 104 8)) 112 (ByteSlice.readLE src 112 8)) 120 (ByteSlice.readLE src 120 8))
        128 (ByteSlice.readLE src 128 8)) 136 (ByteSlice.readLE src 136 8)) 144 (ByteSlice.readLE src 144 8)) 152 (ByteSlice.readLE src 152 8))
        32 (ByteSlice.readLE src 32 8)) 40 (ByteSlice.readLE src 40 8)) 48 (ByteSlice.readLE src 48 8)) 56 (ByteSlice.readLE src 56 8))
        64 (ByteSlice.readLE src 64 8)) 72 (ByteSlice.readLE src 72 8)) 80 (ByteSlice.readLE src 80 8)) 88 (ByteSlice.readLE src 88 8))
        0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8)) 16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)
    fe51Point4Bounded buf bound ∧ edExtOfBytes buf = P := by
  haveI : HasLenGe dst 160 := ⟨by omega⟩; obtain ⟨_, h0, h40, h80, h120⟩ := hsrc_b
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne, write64_length_eq, hdst]
  exact ⟨⟨rfl, h0, h40, h80, h120⟩, hsrc_v⟩

private theorem sepWP_resize_callee (sp0 : BitVec 64) (low k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 912 := by decide) (hf : Full = memRegion (sp0 - 1680#64) 912 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp0 - 768#64 - BitVec.ofNat 64 k) k ∗ stackAt (sp0 - 768#64 - BitVec.ofNat 64 k) low) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp0 - 1680#64 = (sp0 - 768#64) - 912#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, haddr]; change SepWP prog target_pc s (stackAt (sp0 - 768#64) 912 ∗ P) post oom
  rw [← hsum, stackAt_region (sp0 - 768#64) low k (by omega), sepConj_comm (stackAt _ _) (memRegion _ _)]; exact hnext

private theorem sepWP_unresize_callee (sp0 : BitVec 64) (low k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 912 := by decide)
    (hf : Full = (memRegion (sp0 - 768#64 - BitVec.ofNat 64 k) k ∗ stackAt (sp0 - 768#64 - BitVec.ofNat 64 k) low) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp0 - 1680#64) 912 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : (sp0 - 768#64) - 912#64 = sp0 - 1680#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp0 - 768#64) low k (by omega), hsum]
  change SepWP prog target_pc s (memRegion ((sp0 - 768#64) - 912#64) 912 ∗ P) post oom; rw [haddr]; exact hnext

private theorem sepWP_split_ro_slice (table : BitVec 64) (table_bs : List (BitVec 8)) (i : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < 32) (htab : table_bs.length = 30720) (hf : Full = (table ↦ᵣ table_bs) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ProofLib.ByteSlice.slice table_bs (960 * i) 960) ∗
      ((table ↦ᵣ table_bs.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ table_bs.drop (960 * i + 960)))) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsToBytesRO_split3 table table_bs (960 * i) 960 (by omega)]; exact hnext

private theorem sepWP_unsplit_ro_slice (table : BitVec 64) (table_bs : List (BitVec 8)) (i : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < 32) (htab : table_bs.length = 30720)
    (hf : Full = (((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ProofLib.ByteSlice.slice table_bs (960 * i) 960) ∗
       ((table ↦ᵣ table_bs.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ table_bs.drop (960 * i + 960)))) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((table ↦ᵣ table_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, ← pointsToBytesRO_split3 table table_bs (960 * i) 960 (by omega)]; exact hnext

private theorem sepWP_split4_completed_376 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 376#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 52) := by assumption) (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 53) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54) := by assumption) (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 52) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) → fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y → fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s ((((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let b0 := bs.take 40; let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let b1 := d1.take 40; let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  let b2 := d2.take 40; let b3 := d2.drop 40
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hd1]
  have hb2_l : b2.length = 40 := by simp [b2, hd2]
  have hb3_l : b3.length = 40 := by simp [b3, hd2]
  have hs0 : ((sp - 376#64) ↦ₛ bs) = ((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 376 40]
  have hs1 : ((sp - 336#64) ↦ₛ d1) = ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 336 40]
  have hs2 : ((sp - 296#64) ↦ₛ d2) = ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 296 40]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    have e0 : b0 ++ d1 = bs := List.take_append_drop 40 bs; have e1 : b1 ++ d2 = d1 := List.take_append_drop 40 d1
    have e2 : b2 ++ b3 = d2 := List.take_append_drop 40 d2; rw [e2, e1, e0]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, show off - 40 - 40 = off - 80 by omega, readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l, show off - 40 - 40 - 40 = off - 120 by omega]
  have h0' := fe51LimbsBoundedAt_mono h0 (b2 := 2 ^ 54); have h40' := fe51LimbsBoundedAt_mono h40 (b2 := 2 ^ 54)
  have h120' := fe51LimbsBoundedAt_mono h120 (b2 := 2 ^ 54); unfold fe51LimbsBoundedAt at h0' h40' h80 h120'
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0' h40' h80 h120'
  have hval' : edExtOfBytes bs = ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
      fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub,
      fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, fold_fe51ValOfBytes b3]
  rw [hval] at hval'; rw [hf, hs0, hs1, hs2]
  exact hnext b0 b1 b2 b3 hb0_l hb1_l hb2_l hb3_l ⟨hb0_l, h0'⟩ ⟨hb1_l, h40'⟩ ⟨hb2_l, h80⟩ ⟨hb3_l, h120'⟩
    (congrArg EdExtPoint.X hval').symm (congrArg EdExtPoint.Y hval').symm
    (congrArg EdExtPoint.Z hval').symm (congrArg EdExtPoint.T hval').symm

private theorem sepWP_merge4_stack_376 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption) (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 → SepWP prog target_pc s (((sp - 376#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 296#64 + BitVec.ofNat 64 b2.length = sp - 256#64 := by rw [h2]; exact sub_ofNat64_add sp 296 40
  have ha1 : sp - 336#64 + BitVec.ofNat 64 b1.length = sp - 296#64 := by rw [h1]; exact sub_ofNat64_add sp 336 40
  have ha0' : sp - 376#64 + BitVec.ofNat 64 b0.length = sp - 336#64 := by rw [h0]; exact sub_ofNat64_add sp 376 40
  have hm : ((sp - 376#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0', pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

private theorem sepWP_split4_stack_536 (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 536#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8), b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s ((((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 536#64) ↦ₛ bs) = ((sp - 536#64) ↦ₛ bs.take 40) ∗ ((sp - 496#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 536 40]
  have hs1 : ((sp - 496#64) ↦ₛ d1) = ((sp - 496#64) ↦ₛ d1.take 40) ∗ ((sp - 456#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 496 40]
  have hs2 : ((sp - 456#64) ↦ₛ d2) = ((sp - 456#64) ↦ₛ d2.take 40) ∗ ((sp - 416#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 456 40]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40) (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

private theorem sepWP_merge4_stack_536 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (Q : List (BitVec 8) → Prop)
    (hf : Full = (((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption) (h2 : b2.length = 40 := by assumption)
    (hQ : Q (b0 ++ (b1 ++ (b2 ++ b3))))
    (hnext : ∀ res_bs : List (BitVec 8), Q res_bs → SepWP prog target_pc s (((sp - 536#64) ↦ₛ res_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 456#64 + BitVec.ofNat 64 b2.length = sp - 416#64 := by rw [h2]; exact sub_ofNat64_add sp 456 40
  have ha1 : sp - 496#64 + BitVec.ofNat 64 b1.length = sp - 456#64 := by rw [h1]; exact sub_ofNat64_add sp 496 40
  have ha0 : sp - 536#64 + BitVec.ofNat 64 b0.length = sp - 496#64 := by rw [h0]; exact sub_ofNat64_add sp 536 40
  have hm : ((sp - 536#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) hQ

private def mulBaseLoopPre (sp0 table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)) (F : SepProp) : SepProp :=
  memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
  ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs) ∗ F

private theorem sepWP_fold_mulBaseLoopPre (sp0 table : BitVec 64)
    {table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
      ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs)) ∗ F := by sep_frame)
    (hnext : SepWP prog target_pc s (mulBaseLoopPre sp0 table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : mulBaseLoopPre sp0 table table_bs digits acc_bs ext_bs comp_bs niels_bs F =
      (memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
       ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs)) ∗ F := by
    unfold mulBaseLoopPre; sep_ac_rfl
  rw [hf, ← hm]; exact hnext

private theorem even_getLsbD_0 {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i)).getLsbD 0 = false :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val)).getLsbD 0 = false) ⟨i, hi⟩
private theorem odd_getLsbD_0 {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i + 1)).getLsbD 0 = true :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1)).getLsbD 0 = true) ⟨i, hi⟩
private theorem ofNat_2i_add_1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) + 1#64 = BitVec.ofNat 64 (2 * k.val + 1)) ⟨i, hi⟩
private theorem ofNat_2i1_add_1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i + 1) + 1#64 = BitVec.ofNat 64 (2 * (i + 1)) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val + 1) + 1#64 = BitVec.ofNat 64 (2 * (k.val + 1))) ⟨i, hi⟩
private theorem ule_64_2i1 {i : Nat} (hi : i < 32) : (64#64).ule (BitVec.ofNat 64 (2 * i + 1)) = false :=
  (by decide : ∀ k : Fin 32, (64#64).ule (BitVec.ofNat 64 (2 * k.val + 1)) = false) ⟨i, hi⟩
private theorem ule_64_2i {i : Nat} (hi : i < 32) : (64#64).ule (BitVec.ofNat 64 (2 * i)) = false :=
  (by decide : ∀ k : Fin 32, (64#64).ule (BitVec.ofNat 64 (2 * k.val)) = false) ⟨i, hi⟩
private theorem lsr_2i1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i + 1) >>> 1 = BitVec.ofNat 64 i :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val + 1) >>> 1 = BitVec.ofNat 64 k.val) ⟨i, hi⟩
private theorem lsr_2i {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i) >>> 1 = BitVec.ofNat 64 i :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) >>> 1 = BitVec.ofNat 64 k.val) ⟨i, hi⟩
private theorem mul_960_ofNat {i : Nat} (hi : i < 32) : BitVec.ofNat 64 i * 960#64 = BitVec.ofNat 64 (960 * i) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 k.val * 960#64 = BitVec.ofNat 64 (960 * k.val)) ⟨i, hi⟩

private theorem pc_odd_end (b : BitVec 64) {i : Nat} (hi : i < 32) :
    (if (BitVec.ofNat 64 (2 * i + 1) + 1#64 != 64#64) = true then b + 152#64 else b + 316#64) =
      if i == 31 then b + 316#64 else b + 152#64 := by
  have h : (BitVec.ofNat 64 (2 * i + 1) + 1#64 != 64#64) = !(i == 31) :=
    (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1) + 1#64 != 64#64) = !(k.val == 31)) ⟨i, hi⟩
  rw [h]; cases (i == 31) <;> simp

private theorem pc_even_end (b : BitVec 64) {i : Nat} (hi : i < 32) :
    (if (BitVec.ofNat 64 (2 * i + 1) + 1#64 == 64#64) = true then b + 580#64 else b + 416#64) =
      if i == 31 then b + 580#64 else b + 416#64 := by
  have h : (BitVec.ofNat 64 (2 * i + 1) + 1#64 == 64#64) = (i == 31) :=
    (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1) + 1#64 == 64#64) = (k.val == 31)) ⟨i, hi⟩
  rw [h]

private structure MulBaseLoopRegs [DalekCliPlacement]
    (s0 s : State) (out table r22 r24 r26 pc_val x23_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 768#64
  hx19 : s.readReg64 (Reg.gpr 19#5) = out
  hx20 : s.readReg64 (Reg.gpr 20#5) = table
  hx21 : s.readReg64 (Reg.gpr 21#5) = s0.sp - 536#64
  hx22 : s.readReg64 (Reg.gpr 22#5) = r22
  hx23 : s.readReg64 (Reg.gpr 23#5) = x23_val
  hx24 : s.readReg64 (Reg.gpr 24#5) = r24
  hx25 : s.readReg64 (Reg.gpr 25#5) = 960#64
  hx26 : s.readReg64 (Reg.gpr 26#5) = r26
  hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5)
  hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5)
  hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem

private abbrev MulBaseOddRegs [DalekCliPlacement]
    (s0 s : State) (out table pc_val x23_val : BitVec 64) : Prop :=
  MulBaseLoopRegs s0 s out table (s0.sp - 768#64) (s0.sp - 376#64) (s0.readReg64 (Reg.gpr 26#5)) pc_val x23_val

private abbrev MulBaseEvenRegs [DalekCliPlacement]
    (s0 s : State) (out table pc_val x23_val : BitVec 64) : Prop :=
  MulBaseLoopRegs s0 s out table (s0.sp - 376#64) (s0.sp - 536#64) (s0.sp - 768#64) pc_val x23_val

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_base_odd_iter [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl26 b) (hbase : dalekCliPl26.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (i : Nat) (hi : i < 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseOddRegs s0 s out table (b + 152#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseOddRegs s0 sf' out table (if i == 31 then b + 316#64 else b + 152#64) (BitVec.ofNat 64 (2 * (i + 1))) →
      fe51Point4Bounded acc' (2 ^ 52) → edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc →
      ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold mulBaseLoopPre
  wp_sym_steps 1; simp only [even_getLsbD_0 hi, beq_self_eq_true, ↓ite_true]
  wp_sym_steps 3; simp only [ofNat_2i_add_1 hi]
  wp_sym_steps 4; simp only [ule_64_2i1 hi, Bool.false_eq_true, ↓ite_false]
  wp_sym_steps 3; simp only [lsr_2i1 hi, mul_960_ofNat hi]
  apply sepWP_resize_callee s0.sp 720 192; apply sepWP_split_ro_slice table table_bs i hi htab_len
  have htab_i := htab_bnd i hi; wp_steps; wp_dalek_call hSelect; clean_prev_sf
  apply sepWP_unsplit_ro_slice table table_bs i hi htab_len; apply sepWP_unresize_callee s0.sp 720 192
  have hniels_w_len : w.length = 120 := by assumption
  obtain ⟨hsel_0, hsel_40, hsel_80⟩ : fe51AffineNielsBoundedAt w 0 (2 ^ 53) := by assumption
  have hsel_val : (fe51ValAt w 0 % p25519, fe51ValAt w 40 % p25519, fe51ValAt w 80 % p25519) =
      edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960) (digits.getD (2 * i + 1) 0#8) := by
    assumption
  have hacc_len : acc_bs.length = 160 := hacc_b.1
  have hacc_0 := fe51LimbsBoundedAt_mono hacc_b.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_0
  have hacc_40 := fe51LimbsBoundedAt_mono hacc_b.2.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_40
  have hacc_80 : fe51LimbsBoundedAt acc_bs 80 (2 ^ 52) := hacc_b.2.2.2.1; unpack_fe51_at hacc_80
  have hacc_120 := fe51LimbsBoundedAt_mono hacc_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at hacc_120
  have hsel_0' := fe51LimbsBoundedAt_mono hsel_0 (b2 := 2 ^ 54); unpack_fe51_at hsel_0'
  have hsel_40' := fe51LimbsBoundedAt_mono hsel_40 (b2 := 2 ^ 54); unpack_fe51_at hsel_40'
  have hsel_80' := fe51LimbsBoundedAt_mono hsel_80 (b2 := 2 ^ 54); unpack_fe51_at hsel_80'
  wp_sym_steps 3; apply sepWP_resize_callee s0.sp 384 528; wp_steps; wp_dalek_call hAdd; clean_prev_sf
  apply sepWP_unresize_callee s0.sp 384 528
  let C := edAddAffineNiels acc (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519)
  have hadd_val : edExtOfBytes w_1 = edAddAffineNiels (edExtOfBytes acc_bs)
      (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519) := by assumption
  have hc_val : edExtOfBytes w_1 = C := by rw [hadd_val, hacc_v]
  apply sepWP_split4_completed_376 s0.sp C
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_536 s0.sp; intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee s0.sp 688 224
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_2 (fpMul C.X C.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_3 (fpMul C.Y C.Z)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_4 (fpMul C.Z C.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_5 (fpMul C.X C.Y)
  apply sepWP_unresize_callee s0.sp 688 224
  apply sepWP_merge4_stack_376 s0.sp; intro comp' hcomp'_len
  apply sepWP_merge4_stack_536 s0.sp
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ := edAsExtended_of_append4 w_2 w_3 w_4 w_5 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    refine ⟨⟨hl, hb0, hb1, hb2, hb3⟩, ?_⟩; rw [hv]; unfold edMulBaseStep; rw [← hsel_val]
  intro ext' ⟨hext'_b, hext'_v⟩
  clear_dead_vars [w_1, c0, c1, c2, c3, e0, e1, e2, e3, w_2, w_3, w_4, w_5]
  have hext'_len : ext'.length = 160 := hext'_b.1; haveI : HasLenGe acc_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 13
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
    (hQ := copy160_point4_post acc_bs ext' _ (2 ^ 52) hacc_len hext'_b hext'_v)
  intro acc' ⟨hacc'_b, hacc'_v⟩
  have hperm : ((s0.sp - 704#64) ↦ₛ acc' ∗ (s0.sp - 536#64) ↦ₛ ext' ∗ (s0.sp - 376#64) ↦ₛ comp' ∗
      memRegion (s0.sp - 1680#64) 912 ∗ (s0.sp - 216#64) ↦ₛ w ∗ table ↦ᵣ table_bs ∗ (s0.sp - 768#64) ↦ₛ digits ∗ F) =
      mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' w F := by unfold mulBaseLoopPre; sep_ac_rfl
  rw [hperm]
  refine hnext _ acc' ext' comp' w ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_copy⟩
    hacc'_b hacc'_v hext'_len hcomp'_len hniels_w_len
  · simp only [State.pc_setMem, State.pc_setPC, pc_odd_end b hi]
  · simp only [arm64_norm, ofNat_2i1_add_1 hi]

private theorem loop_zero_eq {i : Nat} (h : i + 0 = 32) : i = 32 := h
private theorem loop_succ_lt {i rem' : Nat} (h : i + (rem' + 1) = 32) : i < 32 := by omega
private theorem loop_succ_add {i rem' : Nat} (h : i + (rem' + 1) = 32) : (i + 1) + rem' = 32 := by omega
private theorem loop_succ_cond {i rem' : Nat} (h : i + (rem' + 1) = 32) : (i == 31) = (rem' == 0) := by
  cases h0 : (rem' == 0)
  · simp only [beq_eq_false_iff_ne, ne_eq] at h0 ⊢; omega
  · simp only [beq_iff_eq] at h0 ⊢; omega

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_base_even_iter [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl26 b) (hbase : dalekCliPl26.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (i : Nat) (hi : i < 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseEvenRegs s0 s out table (b + 416#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseEvenRegs s0 sf' out table (if i == 31 then b + 580#64 else b + 416#64) (BitVec.ofNat 64 (2 * (i + 1))) →
      fe51Point4Bounded acc' (2 ^ 52) → edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc →
      ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold mulBaseLoopPre
  wp_sym_steps 1; simp only [even_getLsbD_0 hi]
  wp_sym_steps 3; simp only [ule_64_2i hi, Bool.false_eq_true, ↓ite_false]
  wp_sym_steps 3; simp only [lsr_2i hi, mul_960_ofNat hi]
  apply sepWP_resize_callee s0.sp 720 192; apply sepWP_split_ro_slice table table_bs i hi htab_len
  have htab_i := htab_bnd i hi; wp_steps; wp_dalek_call hSelect; clean_prev_sf
  apply sepWP_unsplit_ro_slice table table_bs i hi htab_len; apply sepWP_unresize_callee s0.sp 720 192
  have hniels_w_len : w.length = 120 := by assumption
  obtain ⟨hsel_0, hsel_40, hsel_80⟩ : fe51AffineNielsBoundedAt w 0 (2 ^ 53) := by assumption
  have hsel_val : (fe51ValAt w 0 % p25519, fe51ValAt w 40 % p25519, fe51ValAt w 80 % p25519) =
      edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960) (digits.getD (2 * i) 0#8) := by
    assumption
  have hacc_len : acc_bs.length = 160 := hacc_b.1
  have hacc_0 := fe51LimbsBoundedAt_mono hacc_b.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_0
  have hacc_40 := fe51LimbsBoundedAt_mono hacc_b.2.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_40
  have hacc_80 : fe51LimbsBoundedAt acc_bs 80 (2 ^ 52) := hacc_b.2.2.2.1; unpack_fe51_at hacc_80
  have hacc_120 := fe51LimbsBoundedAt_mono hacc_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at hacc_120
  have hsel_0' := fe51LimbsBoundedAt_mono hsel_0 (b2 := 2 ^ 54); unpack_fe51_at hsel_0'
  have hsel_40' := fe51LimbsBoundedAt_mono hsel_40 (b2 := 2 ^ 54); unpack_fe51_at hsel_40'
  have hsel_80' := fe51LimbsBoundedAt_mono hsel_80 (b2 := 2 ^ 54); unpack_fe51_at hsel_80'
  wp_sym_steps 3; apply sepWP_resize_callee s0.sp 384 528; wp_steps; wp_dalek_call hAdd; clean_prev_sf
  apply sepWP_unresize_callee s0.sp 384 528
  let C := edAddAffineNiels acc (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519)
  have hadd_val : edExtOfBytes w_1 = edAddAffineNiels (edExtOfBytes acc_bs)
      (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519) := by assumption
  have hc_val : edExtOfBytes w_1 = C := by rw [hadd_val, hacc_v]
  apply sepWP_split4_completed_376 s0.sp C
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_536 s0.sp; intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee s0.sp 688 224
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_2 (fpMul C.X C.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_3 (fpMul C.Y C.Z)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_4 (fpMul C.Z C.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_5 (fpMul C.X C.Y)
  apply sepWP_unresize_callee s0.sp 688 224
  apply sepWP_merge4_stack_376 s0.sp; intro comp' hcomp'_len
  apply sepWP_merge4_stack_536 s0.sp
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ := edAsExtended_of_append4 w_2 w_3 w_4 w_5 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    refine ⟨⟨hl, hb0, hb1, hb2, hb3⟩, ?_⟩; rw [hv]; unfold edMulBaseStep; simp only [Nat.add_zero]; rw [← hsel_val]
  intro ext' ⟨hext'_b, hext'_v⟩
  clear_dead_vars [w_1, c0, c1, c2, c3, e0, e1, e2, e3, w_2, w_3, w_4, w_5]
  have hext'_len : ext'.length = 160 := hext'_b.1; haveI : HasLenGe acc_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 13; simp only [ofNat_2i_add_1 hi]
  wp_sym_steps 1; simp only [odd_getLsbD_0 hi, beq_self_eq_true, ↓ite_true]
  wp_sym_steps 3
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
    (hQ := copy160_point4_post acc_bs ext' _ (2 ^ 52) hacc_len hext'_b hext'_v)
  intro acc' ⟨hacc'_b, hacc'_v⟩
  have hperm : ((s0.sp - 704#64) ↦ₛ acc' ∗ (s0.sp - 536#64) ↦ₛ ext' ∗ (s0.sp - 376#64) ↦ₛ comp' ∗
      memRegion (s0.sp - 1680#64) 912 ∗ (s0.sp - 216#64) ↦ₛ w ∗ table ↦ᵣ table_bs ∗ (s0.sp - 768#64) ↦ₛ digits ∗ F) =
      mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' w F := by unfold mulBaseLoopPre; sep_ac_rfl
  rw [hperm]
  refine hnext _ acc' ext' comp' w ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_copy⟩
    hacc'_b hacc'_v hext'_len hcomp'_len hniels_w_len
  · simp only [State.pc_setMem, State.pc_setPC, pc_even_end b hi]
  · simp only [arm64_norm, ofNat_2i1_add_1 hi]

attribute [local irreducible] edMulBaseStep

private theorem MulBaseLoopRegs.of_pc [DalekCliPlacement]
    {s0 s : State} {out table r22 r24 r26 pc1 pc2 x23 : BitVec 64}
    (h : MulBaseLoopRegs s0 s out table r22 r24 r26 pc1 x23) (hpc : pc1 = pc2) :
    MulBaseLoopRegs s0 s out table r22 r24 r26 pc2 x23 :=
  ⟨h.1.trans hpc, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16⟩

private theorem edMulBaseLoopWith_step {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) :
    edMulBaseLoopWith step i (rem + 1) acc = edMulBaseLoopWith step (i + 1) rem (step i acc) := rfl

private theorem edMulBaseLoop_step (table_bs digits : List (BitVec 8)) (parity i rem : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i (rem + 1) acc =
    edMulBaseLoop table_bs digits parity (i + 1) rem (edMulBaseStep table_bs i (digits.getD (2 * i + parity) 0#8) acc) :=
  edMulBaseLoopWith_step (edMulBaseStepAt table_bs digits parity) i rem acc

private theorem mul_base_odd_loop [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl26 b) (hbase : dalekCliPl26.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (rem i : Nat) (hrem : i + rem = 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseOddRegs s0 s out table (if rem == 0 then b + 316#64 else b + 152#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseOddRegs s0 sf' out table (b + 316#64) 64#64 → fe51Point4Bounded acc' (2 ^ 52) →
      edExtOfBytes acc' = edMulBaseLoop table_bs digits 1 i rem acc → ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  induction rem generalizing i s acc_bs ext_bs comp_bs niels_bs acc with
  | zero => cases loop_zero_eq hrem; exact hnext s acc_bs ext_bs comp_bs niels_bs hregs hacc_b hacc_v hext_len hcomp_len hniels_len
  | succ rem' ih =>
    have hi : i < 32 := loop_succ_lt hrem
    apply mul_base_odd_iter b hb hbase hSelect hAdd hMul i hi s0 s target_pc out table table_bs digits acc_bs ext_bs comp_bs niels_bs acc F post
      hsp0_align hregs htab_len htab_bnd hdigits_len hacc_b hacc_v hext_len hcomp_len hniels_len
    intro sf1 acc1 ext1 comp1 niels1 hregs1 hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    have hpc_eq : (if i == 31 then b + 316#64 else b + 152#64) = (if rem' == 0 then b + 316#64 else b + 152#64) := by rw [loop_succ_cond hrem]
    apply ih (i + 1) (loop_succ_add hrem) sf1 acc1 ext1 comp1 niels1 (edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
      (hregs1.of_pc hpc_eq) hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    intro sf' acc' ext' comp' niels' hr hbnd hv he hc hn
    exact hnext sf' acc' ext' comp' niels' hr hbnd (hv.trans (edMulBaseLoop_step table_bs digits 1 i rem' acc).symm) he hc hn

private theorem mul_base_even_loop [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl26 b) (hbase : dalekCliPl26.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (rem i : Nat) (hrem : i + rem = 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseEvenRegs s0 s out table (if rem == 0 then b + 580#64 else b + 416#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseEvenRegs s0 sf' out table (b + 580#64) 64#64 → fe51Point4Bounded acc' (2 ^ 52) →
      edExtOfBytes acc' = edMulBaseLoop table_bs digits 0 i rem acc → ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (dalekCliPC26.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  induction rem generalizing i s acc_bs ext_bs comp_bs niels_bs acc with
  | zero => cases loop_zero_eq hrem; exact hnext s acc_bs ext_bs comp_bs niels_bs hregs hacc_b hacc_v hext_len hcomp_len hniels_len
  | succ rem' ih =>
    have hi : i < 32 := loop_succ_lt hrem
    apply mul_base_even_iter b hb hbase hSelect hAdd hMul i hi s0 s target_pc out table table_bs digits acc_bs ext_bs comp_bs niels_bs acc F post
      hsp0_align hregs htab_len htab_bnd hdigits_len hacc_b hacc_v hext_len hcomp_len hniels_len
    intro sf1 acc1 ext1 comp1 niels1 hregs1 hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    have hpc_eq : (if i == 31 then b + 580#64 else b + 416#64) = (if rem' == 0 then b + 580#64 else b + 416#64) := by rw [loop_succ_cond hrem]
    apply ih (i + 1) (loop_succ_add hrem) sf1 acc1 ext1 comp1 niels1 (edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
      (hregs1.of_pc hpc_eq) hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    intro sf' acc' ext' comp' niels' hr hbnd hv he hc hn
    exact hnext sf' acc' ext' comp' niels' hr hbnd (hv.trans (edMulBaseLoop_step table_bs digits 0 i rem' acc).symm) he hc hn

/-! ## 3. Public Machine-Code Theorems (`B09`, `B26`, `B27`) -/

public section

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem lookup_table_affine_niels_select_ok : LookupTableAffineNielsSelectOk := by
  intro _
  apply dalekCaller_ok dalekCliPC09 dalekCliPl09
  intro b hb hbase
  wp_init
  have htab_b : fe51LookupTable8Bounded a_rest_1 (2 ^ 53) := by assumption
  have htab_u : a_rest_1.length = 960 ∧
      fe51AffineNielsBoundedAt a_rest_1 0 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 120 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 240 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 360 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 480 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 600 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 720 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 840 (2 ^ 53) := by
    unfold fe51LookupTable8Bounded at htab_b; exact htab_b
  have hout_len : a_3.length = 120 := by assumption
  have hx_reg : BitVec.zeroExtend 8 (s0.readReg64 (Reg.gpr 2#5)) = a_2 := by assumption
  have htab_len : a_rest_1.length = 960 := htab_u.1
  haveI : HasLenGe a_3 120 := ⟨by omega⟩; haveI : HasLenGe a_rest_1 960 := ⟨by omega⟩
  apply sepWP_split_stack_callee 16 176; open_cells (s0.sp - 176#64) 176 22
  wp_cut_codeLoaded
  wp_sym_steps 28; wp_conv_pre => rw [sbfx_getLsbD_7 _ _ hx_reg, sxtb_low8 _ _ hx_reg, sbfx_bit7 _ _ hx_reg]
  wp_steps; wp_dalek_call black_box_u8_ok; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 1#8 || a_2 == -1#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 2#8 || a_2 == -2#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 3#8 || a_2 == -3#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 4#8 || a_2 == -4#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_dalek_call black_box_u8_ok; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 5#8 || a_2 == -5#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  rcases hold_reg h_6 with ⟨d2_4, hd2_4, h_6⟩; rcases hold_reg h_7 with ⟨d1_4, hd1_4, h_7⟩; rcases hold_reg h_8 with ⟨yp0_4, hyp0_4, h_8⟩
  rcases hold_reg h_9 with ⟨ym1_4, hym1_4, h_9⟩; rcases hold_reg h_10 with ⟨ym0_4, hym0_4, h_10⟩; rcases hold_reg h_11 with ⟨d0_4, hd0_4, h_11⟩
  rcases hold_reg h_14 with ⟨d4_4, hd4_4, h_14⟩; rcases hold_reg h_15 with ⟨d3_4, hd3_4, h_15⟩
  apply hold_stack7; intro ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4 hym4_4 hym3_4 hyp3_4 hyp4_4 hym2_4 hyp1_4 hyp2_4
  exact lookup_table_affine_niels_select_tail b hb hbase R s0 _ a_1 a _ a_2 a_3 a_rest_1
    d2_4 d1_4 yp0_4 ym1_4 ym0_4 d0_4 d4_4 d3_4 ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4
    hsp_align hout_len htab_b (by assumption) (by assumption) (by assumption)
    h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_15 (by assumption) (by assumption) ‹_› hpost
    (fe51Bounds_hold_chain4 hyp0_4 hyp1_4 hyp2_4 hyp3_4 hyp4_4 htab_u.2.2.2.2.1.1 htab_u.2.2.2.1.1 htab_u.2.2.1.1 htab_u.2.1.1 (by decide))
    (fe51Bounds_hold_chain4 hym0_4 hym1_4 hym2_4 hym3_4 hym4_4 htab_u.2.2.2.2.1.2.1 htab_u.2.2.2.1.2.1 htab_u.2.2.1.2.1 htab_u.2.1.2.1 (by decide))
    (fe51Bounds_hold_chain4 hd0_4 hd1_4 hd2_4 hd3_4 hd4_4 htab_u.2.2.2.2.1.2.2 htab_u.2.2.2.1.2.2 htab_u.2.2.1.2.2 htab_u.2.1.2.2 (by decide))
    (by rw [fe51Val_hold_chain4 hyp0_4 hyp1_4 hyp2_4 hyp3_4 hyp4_4]; rfl)
    (by rw [fe51Val_hold_chain4 hym0_4 hym1_4 hym2_4 hym3_4 hym4_4]; rfl)
    (by rw [fe51Val_hold_chain4 hd0_4 hd1_4 hd2_4 hd3_4 hd4_4]; rfl)

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem edwards_basepoint_table_mul_base_ok_of
    (hMul : Fe51MulOk) (hMulPow2_4 : EdwardsPointMulByPow2_4Ok)
    (hAddAN : EdwardsPointAddAffineNielsOk) (hRadix16 : ScalarAsRadix16Ok) :
    EdwardsBasepointTableMulBaseOk := by
  have hSelect : LookupTableAffineNielsSelectOk := lookup_table_affine_niels_select_ok
  intro _
  apply dalekCaller_ok dalekCliPC26 dalekCliPl26
  intro b _hb hbase
  wp_init
  obtain ⟨htab_len, htab_bnd⟩ : fe51BasepointTable32Bounded a_4 (2 ^ 53) := by assumption
  have hout_len : a_3.length = 160 := by assumption
  have h1_len : fe51OneBytes.length = 40 := fe51OneBytes_length; haveI : HasLenGe fe51OneBytes 40 := ⟨by omega⟩
  apply sepWP_split_stack_callee 912 768
  apply sepWP_peel_stack_bytes s0.sp 768 64 704; intro sp_768 h_768
  apply sepWP_peel_stack_bytes s0.sp 704 160 544; intro sp_704 h_704
  apply sepWP_peel_stack_bytes s0.sp 544 8 536; intro sp_544 h_544
  apply sepWP_peel_stack_bytes s0.sp 536 160 376; intro sp_536 h_536
  apply sepWP_peel_stack_bytes s0.sp 376 160 216; intro sp_376 h_376
  apply sepWP_peel_stack_bytes s0.sp 216 120 96; intro sp_216 h_216
  open_cells (s0.sp - 96#64) 96 12
  wp_cut_codeLoaded; wp_steps; wp_dalek_call hRadix16
  have hdigits_len : (scalarRadix16Digits a_rest).length = 64 := scalarRadix16Digits_length a_rest
  wp_cut_codeLoaded
  wp_sym_steps 19
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_init
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero)
    (hQ := mul_base_init_post sp_704 h_704)
  intro acc0 ⟨hacc0_b, hacc0_v⟩; apply sepWP_fold_mulBaseLoopPre s0.sp a
  apply mul_base_odd_loop b _hb hbase hSelect hAddAN hMul 32 0 rfl s0 _ _ a_1 a a_4
    (scalarRadix16Digits a_rest) acc0 sp_536 sp_376 sp_216 edExtZero _ _ hsp_align
    ⟨by simp only [State.pc_setMem, State.pc_setPC]; rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_init⟩
    htab_len htab_bnd hdigits_len hacc0_b hacc0_v h_536 h_376 h_216
  intro sf_odd acc_odd ext_odd comp_odd niels_odd hregs_odd hacc_odd_b hacc_odd_v hext_odd_l hcomp_odd_l hniels_odd_l
  clear_dead_vars [sf]; try clear sf
  rcases hregs_odd with ⟨hpc_o, hrun_o, hsp_o, hx19_o, hx20_o, hx21_o, hx22_o, hx23_o, hx24_o, hx25_o, hx26_o, hx27_o, hx28_o, hx29_o, hvregs_o, hcl_o⟩
  unfold mulBaseLoopPre; obtain ⟨hacc_odd_l, hacc_o0, hacc_o40, hacc_o80, hacc_o120⟩ := hacc_odd_b
  replace hacc_o0 := fe51LimbsBoundedAt_mono hacc_o0 (b2 := 2 ^ 53); unpack_fe51_at hacc_o0
  replace hacc_o40 := fe51LimbsBoundedAt_mono hacc_o40 (b2 := 2 ^ 53); unpack_fe51_at hacc_o40
  replace hacc_o80 := fe51LimbsBoundedAt_mono hacc_o80 (b2 := 2 ^ 53); unpack_fe51_at hacc_o80
  replace hacc_o120 := fe51LimbsBoundedAt_mono hacc_o120 (b2 := 2 ^ 53); unpack_fe51_at hacc_o120
  wp_steps; wp_dalek_call hMulPow2_4; clean_prev_sf; clear_dead_vars [sf_odd]; try clear sf_odd; norm_sf 912
  obtain ⟨hw_b, hw_post⟩ : fe51Point4Bounded w (2 ^ 52) ∧ edExtOfBytes w = edDouble4 (edExtOfBytes acc_odd) :=
    ⟨by assumption, by assumption⟩
  have hw_len : w.length = 160 := hw_b.1; haveI : HasLenGe acc_odd 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 16
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_dbl
  have hw_v : edExtOfBytes w = edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero) := by
    rw [hw_post, hacc_odd_v]
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero))
    (hQ := copy160_point4_post acc_odd w _ (2 ^ 52) hacc_odd_l hw_b hw_v)
  intro acc_dbl ⟨hacc_dbl_b, hacc_dbl_v⟩; apply sepWP_fold_mulBaseLoopPre s0.sp a
  apply mul_base_even_loop b _hb hbase hSelect hAddAN hMul 32 0 rfl s0 _ _ a_1 a a_4
    (scalarRadix16Digits a_rest) acc_dbl ext_odd w niels_odd
    (edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero)) _ _ hsp_align
    ⟨by simp only [State.pc_setMem, State.pc_setPC]; rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_dbl⟩
    htab_len htab_bnd hdigits_len hacc_dbl_b hacc_dbl_v hext_odd_l hw_len hniels_odd_l
  intro sf_even acc_even ext_even comp_even niels_even hregs_even hacc_even_b hacc_even_v hext_even_l hcomp_even_l hniels_even_l
  rcases hregs_even with ⟨hpc_e, hrun_e, hsp_e, hx19_e, hx20_e, hx21_e, hx22_e, hx23_e, hx24_e, hx25_e, hx26_e, hx27_e, hx28_e, hx29_e, hvregs_e, hcl_e⟩
  unfold mulBaseLoopPre; have hacc_even_l : acc_even.length = 160 := hacc_even_b.1; haveI : HasLenGe a_3 160 := ⟨by omega⟩
  wp_sym_steps 18
  apply sepWP_abstract_bytes a_1
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBase a_4 a_rest)
    (hQ := copy160_point4_post a_3 acc_even _ (2 ^ 52) hout_len hacc_even_b hacc_even_v)
  intro res_bs ⟨hres_b, hres_v⟩; close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 216 120 96; apply sepWP_unpeel_stack_bytes s0.sp 376 160 216
  apply sepWP_unpeel_stack_bytes s0.sp 536 160 376; apply sepWP_unpeel_stack_bytes s0.sp 544 8 536
  apply sepWP_unpeel_stack_bytes s0.sp 704 160 544; apply sepWP_unpeel_stack_bytes s0.sp 768 64 704
  apply sepWP_merge_stack_callee 912 768
  obtain ⟨hres_l, hres0, hres40, hres80, hres120⟩ := hres_b
  unpack_fe51_at hres0; unpack_fe51_at hres40; unpack_fe51_at hres80; unpack_fe51_at hres120; wp_done

theorem scalar_mul_basepoint_table_ok_of (hMulBase : EdwardsBasepointTableMulBaseOk) :
    ScalarMulBasepointTableOk := by
  intro _
  apply dalekCaller_ok dalekCliPC27 dalekCliPl27
  intro b _hb hbase
  wp_init
  obtain ⟨htab_l, htab_b⟩ := fe51BasepointTable32Bounded_mono ed25519BasepointTableBytes_bounded (b2 := 2 ^ 53)
  wp_steps
  wp_dalek_tailcall hMulBase
  obtain ⟨hw_l, hw0, hw40, hw80, hw120⟩ : fe51Point4Bounded w (2 ^ 52) := by assumption
  unpack_fe51_at hw0; unpack_fe51_at hw40; unpack_fe51_at hw80; unpack_fe51_at hw120
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.BasepointTable
