/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar52
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `Scalar` Machine-Code Proofs

Machine-code proofs in `dalekCliMultiLib` for `curve25519_dalek::scalar::Scalar`:
1. `scalar_from_bytes_mod_order_ok : ScalarFromBytesModOrderOk` (`B01`, 3 insns)
2. `scalar_from_bytes_mod_order_wide_ok : ScalarFromBytesModOrderWideOk` (`B02`, 277 insns)
3. `scalar_mul_ref_ok : ScalarMulRefOk` (`B21`, 147 insns)
4. `scalar_mul_val_ok : ScalarMulValOk` (`B34`, 1 insn)
5. `scalar_add_ref_ok : ScalarAddRefOk` (`B23`, 197 insns)
6. `scalar_add_val_ok : ScalarAddValOk` (`B35`, 1 insn)
7. `scalar_as_radix_16_ok : ScalarAsRadix16Ok` (`B15`, 173 insns)
8. `scalar_as_radix_16_ro_ok : ScalarAsRadix16RoOk` (`B15`, 173 insns, RO input)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (edOrderL leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  sc52Val sc52ValOfBytes sc52_l sc52LBytes sc52_rr sc52RRBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  sc52LBytes_length sc52RRBytes_length sc52L_val sc52RR_val
  sc52L_readLE_0 sc52L_readLE_8 sc52L_readLE_16 sc52L_readLE_24 sc52L_readLE_32
  sc52RR_readLE_0 sc52RR_readLE_8 sc52RR_readLE_16 sc52RR_readLE_24 sc52RR_readLE_32)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  addWithCarry64_false_c stackFrame_eq_stackFrameAt stack_fold_step stack_fold_last
  stack_swap_slice pointsToBytes40_eq_cells)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  sc52LimbsBounded scalarRadix16Digits
  ScalarFromBytesModOrderOk ScalarFromBytesModOrderWideOk
  ScalarMulRefOk ScalarMulValOk ScalarAddRefOk ScalarAddValOk
  ScalarAsRadix16Ok ScalarAsRadix16RoOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (black_box_u8_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar52 (
  CheckpointEq sc52Pack5 sc52Pack5_length sc52ValOfBytes_sc52Pack5
  sc52LimbsBounded_sc52Pack5 sc52Pack5_cells_eq_rest stack_swap_slice_ro
  mask52_toNat sc52_cond_sub_l sc52_mul_bound_of_right_lt_l sc52_mul_bound_of_lt_256
  exists_bytes32 or_shiftLeft_toNat zext_toNat_eq pack32_toNat setWidth64_extr128_toNat
  sc52_unpack_bytes32 sc52BfiByte sc52PackBytes32 sc52PackBytes32_eq_natToLeBytes
  sc52_montgomery_mul_ro_right_ok sc52_mul_core_ok scalar_reduce_ok)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 01 dalekCliMultiLib DalekCliPlacement 3 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl01_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl01.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 02 dalekCliMultiLib DalekCliPlacement 277 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl02_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl02.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 15 dalekCliMultiLib DalekCliPlacement 173 rebase rho sub

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 21 dalekCliMultiLib DalekCliPlacement 147 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl21_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl21.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 23 dalekCliMultiLib DalekCliPlacement 197 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl23_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl23.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 34 dalekCliMultiLib DalekCliPlacement 1 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl34_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl34.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 35 dalekCliMultiLib DalekCliPlacement 1 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl35_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl35.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] Arm64.Program.fetch
attribute [local irreducible] MultiPlacedLib.CodeLoaded

private theorem sepWP_congr_state_pre {prog : Program} {target_pc : BitVec 64} {s1 s2 : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hs : s1 = s2) (hP : P1 = P2) (h : SepWP prog target_pc s1 P1 post oom) :
    SepWP prog target_pc s2 P2 post oom :=
  hs ▸ hP ▸ h

public section
theorem scalar_from_bytes_mod_order_ok : ScalarFromBytesModOrderOk := by
  intro _
  apply dalekCaller_ok dalekCliPC01 dalekCliPl01
  intro b hb hbase
  wp_init
  wp_steps
  wp_dalek_tailcall scalar_reduce_ok
  rw [show stackFrame sf 208 = stackFrame s0 208 by simp [stackFrame, hsp_sf]]
  wp_done
private theorem stackFrame_split_top (s : State) (n m k : Nat) (hmk : m + k = n := by rfl) (hn : n ≤ 2 ^ 64 := by decide) :
    stackFrame s n = memRegion (s.sp - BitVec.ofNat 64 n) m ∗ stackFrameAt s.sp k := by
  change memRegion (s.sp - BitVec.ofNat 64 n) n = _
  rw [memRegion_split_sub s.sp n m k hmk hn, ← stackFrameAt_eq_memRegion s.sp k (by omega)]
private theorem sc52Pack5_stack_rest (sp : BitVec 64) (n0 n1 n2 n3 n4 : Nat) (r0 r1 r2 r3 r4 : BitVec 64) (rest : SepProp)
    (h1 : sp - BitVec.ofNat 64 n0 + 8#64 = sp - BitVec.ofNat 64 n1 := by bv_omega)
    (h2 : sp - BitVec.ofNat 64 n0 + 16#64 = sp - BitVec.ofNat 64 n2 := by bv_omega)
    (h3 : sp - BitVec.ofNat 64 n0 + 24#64 = sp - BitVec.ofNat 64 n3 := by bv_omega)
    (h4 : sp - BitVec.ofNat 64 n0 + 32#64 = sp - BitVec.ofNat 64 n4 := by bv_omega) :
    ((sp - BitVec.ofNat 64 n0) ↦₆₄ r0 ∗ ((sp - BitVec.ofNat 64 n1) ↦₆₄ r1 ∗ ((sp - BitVec.ofNat 64 n2) ↦₆₄ r2 ∗
      ((sp - BitVec.ofNat 64 n3) ↦₆₄ r3 ∗ ((sp - BitVec.ofNat 64 n4) ↦₆₄ r4 ∗ rest))))) =
    ((sp - BitVec.ofNat 64 n0) ↦ₛ sc52Pack5 r0 r1 r2 r3 r4 ∗ rest) := by
  rw [← h1, ← h2, ← h3, ← h4, ← sc52Pack5_cells_eq_rest]
private def sc52Unpack32 (bs : List (BitVec 8)) : List (BitVec 8) :=
  sc52Pack5
    ((BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48) &&& 4503599627370495#64)
    (BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 12 0#8) <<< 32) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 7 0#8) <<< 56)) >>> 52))
    (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ++ (BitVec.zeroExtend 64 (bs.getD 13 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 14 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 15 0#8) <<< 56)) >>> 40) &&& 4503599627370495#64)
    (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack16 (bs.getD 24 0#8) (bs.getD 25 0#8)) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ||| BitVec.zeroExtend 64 (pack32 (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8)) <<< 32)) >>> 28))
    (BitVec.zeroExtend 64 (pack32 (bs.getD 26 0#8) (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 30 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 31 0#8) <<< 40)
private theorem sc52Unpack32_fold (bs : List (BitVec 8)) :
    sc52Pack5
      ((BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48) &&& 4503599627370495#64)
      (BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 12 0#8) <<< 32) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 7 0#8) <<< 56)) >>> 52))
      (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ++ (BitVec.zeroExtend 64 (bs.getD 13 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 14 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 15 0#8) <<< 56)) >>> 40) &&& 4503599627370495#64)
      (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack16 (bs.getD 24 0#8) (bs.getD 25 0#8)) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ||| BitVec.zeroExtend 64 (pack32 (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8)) <<< 32)) >>> 28))
      (BitVec.zeroExtend 64 (pack32 (bs.getD 26 0#8) (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 30 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 31 0#8) <<< 40) =
    sc52Unpack32 bs := rfl
private theorem sc52_unpack_bytes32_pack5 (bs : List (BitVec 8)) (h : bs.length = 32) :
    sc52LimbsBounded (sc52Unpack32 bs) (2 ^ 52) ∧ sc52ValOfBytes (sc52Unpack32 bs) = leBytesToNat bs ∧ leBytesToNat bs < 2 ^ 256 := by
  unfold sc52Unpack32; obtain ⟨h0, h1, h2, h3, h4, hval, hlt⟩ := sc52_unpack_bytes32 bs h _ _ _ _ _ rfl rfl rfl rfl rfl
  rw [sc52LimbsBounded_sc52Pack5, sc52ValOfBytes_sc52Pack5]; exact ⟨⟨h0, h1, h2, h3, h4⟩, hval, hlt⟩
private theorem and_mask52_of_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 52) : x &&& 4503599627370495#64 = x := by
  apply BitVec.eq_of_toNat_eq; rw [mask52_toNat, Nat.mod_eq_of_lt hx]
private theorem or_byte_mask52_eq_sc52BfiByte (x y : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 ((x &&& 4503599627370495#64) >>> 48) ||| BitVec.setWidth 32 y <<< 4) = sc52BfiByte x y := by
  unfold sc52BfiByte; ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  revert hi; generalize i = j; intro hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
private theorem write8_32_mul_order (bs : List (BitVec 8)) (h : bs.length = 32)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : BitVec 8) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 1 x1) 2 x2) 3 x3) 4 x4) 5 x5) 7 x7) 6 x6) 10 x10) 9 x9) 8 x8) 11 x11) 12 x12) 14 x14) 15 x15) 16 x16) 13 x13) 17 x17)
      18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25) 27 x27) 28 x28) 26 x26) 29 x29) 30 x30) 31 x31 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := exists_bytes32 h
  simp only [ByteSlice.write8, ByteSlice.write, List.take, List.drop, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
private theorem write8_32_mul (bs w : List (BitVec 8)) (h : bs.length = 32)
    (hw0 : (ByteSlice.readLE w 0 8).toNat < 2 ^ 52) (hw1 : (ByteSlice.readLE w 8 8).toNat < 2 ^ 52)
    (hw2 : (ByteSlice.readLE w 16 8).toNat < 2 ^ 52) (hw3 : (ByteSlice.readLE w 24 8).toNat < 2 ^ 52) (hw4 : (ByteSlice.readLE w 32 8).toNat < 2 ^ 52) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8))) 1 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8 >>> 8))) 2 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8 >>> 16))) 3 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8 >>> 24)))
      4 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8 >>> 32))) 5 (BitVec.zeroExtend 8 (ByteSlice.readLE w 0 8 >>> 40))) 7 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 4)))
      6 (BitVec.truncate 8 (BitVec.setWidth 32 (ByteSlice.readLE w 0 8 >>> 48) ||| BitVec.setWidth 32 (ByteSlice.readLE w 8 8) <<< 4)))
      10 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 28))) 9 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 20))) 8 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 12))) 11 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 36)))
      12 (BitVec.zeroExtend 8 (ByteSlice.readLE w 8 8 >>> 44))) 14 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8 >>> 8))) 15 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8 >>> 16))) 16 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8 >>> 24)))
      13 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8))) 17 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8 >>> 32))) 18 (BitVec.zeroExtend 8 (ByteSlice.readLE w 16 8 >>> 40)))
      19 (BitVec.truncate 8 (BitVec.setWidth 32 (ByteSlice.readLE w 16 8 >>> 48) ||| BitVec.setWidth 32 (ByteSlice.readLE w 24 8) <<< 4)))
      20 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 4))) 21 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 12))) 22 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 20))) 23 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 28)))
      24 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 36))) 25 (BitVec.zeroExtend 8 (ByteSlice.readLE w 24 8 >>> 44))) 27 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8 >>> 8))) 28 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8 >>> 16)))
      26 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8))) 29 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8 >>> 24))) 30 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8 >>> 32))) 31 (BitVec.zeroExtend 8 (ByteSlice.readLE w 32 8 >>> 40)) =
    natToLeBytes 32 (sc52ValOfBytes w) := by
  have hb6 : BitVec.truncate 8 (BitVec.setWidth 32 (ByteSlice.readLE w 0 8 >>> 48) ||| BitVec.setWidth 32 (ByteSlice.readLE w 8 8) <<< 4) = sc52BfiByte (ByteSlice.readLE w 0 8) (ByteSlice.readLE w 8 8) := by
    rw [← or_byte_mask52_eq_sc52BfiByte, and_mask52_of_lt hw0]
  have hb19 : BitVec.truncate 8 (BitVec.setWidth 32 (ByteSlice.readLE w 16 8 >>> 48) ||| BitVec.setWidth 32 (ByteSlice.readLE w 24 8) <<< 4) = sc52BfiByte (ByteSlice.readLE w 16 8) (ByteSlice.readLE w 24 8) := by
    rw [← or_byte_mask52_eq_sc52BfiByte, and_mask52_of_lt hw2]
  rw [hb6, hb19, write8_32_mul_order bs h]
  exact sc52PackBytes32_eq_natToLeBytes (ByteSlice.readLE w 0 8) (ByteSlice.readLE w 8 8) (ByteSlice.readLE w 16 8) (ByteSlice.readLE w 24 8) (ByteSlice.readLE w 32 8)
    (ByteSlice.readLE w 0 8) (ByteSlice.readLE w 8 8) (ByteSlice.readLE w 16 8) (ByteSlice.readLE w 24 8) (ByteSlice.readLE w 32 8)
    (and_mask52_of_lt hw0).symm (and_mask52_of_lt hw1).symm (and_mask52_of_lt hw2).symm (and_mask52_of_lt hw3).symm (and_mask52_of_lt hw4).symm
private theorem stackFrame448_mul_fold (s0 sf : State) (hsp : sf.sp = s0.sp - 160#64)
    (bs1 bs2 bs3 : List (BitVec 8)) (h1 : bs1.length = 40) (h2 : bs2.length = 40) (h3 : bs3.length = 40) (v0 v1 v2 v3 v4 : BitVec 64) :
    (stackFrame sf 288 ∗ ((s0.sp - 160#64) ↦₆₄ v0 ∗ ((s0.sp - 152#64) ↦ₛ bs1 ∗ ((s0.sp - 112#64) ↦ₛ bs2 ∗ ((s0.sp - 72#64) ↦ₛ bs3 ∗
      ((s0.sp - 32#64) ↦₆₄ v1 ∗ ((s0.sp - 24#64) ↦₆₄ v2 ∗ ((s0.sp - 16#64) ↦₆₄ v3 ∗ (s0.sp - 8#64) ↦₆₄ v4)))))))) ⊢ stackFrame s0 448 := by
  have hsf : stackFrame sf 288 = memRegion (s0.sp - 448#64) 288 := by
    change memRegion (sf.sp - 288#64) 288 = _; rw [hsp, show s0.sp - 160#64 - 288#64 = s0.sp - 448#64 by bv_omega]
  have hrhs : stackFrame s0 448 = memRegion (s0.sp - 448#64) 288 ∗ (memRegion (s0.sp - 160#64) 8 ∗ (memRegion (s0.sp - 152#64) 40 ∗
      (memRegion (s0.sp - 112#64) 40 ∗ (memRegion (s0.sp - 72#64) 40 ∗ (memRegion (s0.sp - 32#64) 8 ∗ (memRegion (s0.sp - 24#64) 8 ∗
      (memRegion (s0.sp - 16#64) 8 ∗ memRegion (s0.sp - 8#64) 8))))))) := by
    change memRegion (s0.sp - 448#64) 448 = _
    rw [memRegion_split_sub s0.sp 448 288 160, memRegion_split_sub s0.sp 160 8 152, memRegion_split_sub s0.sp 152 40 112,
        memRegion_split_sub s0.sp 112 40 72, memRegion_split_sub s0.sp 72 40 32, memRegion_split_sub s0.sp 32 8 24,
        memRegion_split_sub s0.sp 24 8 16, memRegion_split_sub s0.sp 16 8 8]
  rw [hsf, hrhs]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo64_entails_memRegion _ v0) ?_)
  refine sepConj_mono (h1 ▸ pointsToBytes_entails_memRegion _ bs1) (sepConj_mono (h2 ▸ pointsToBytes_entails_memRegion _ bs2) ?_)
  refine sepConj_mono (h3 ▸ pointsToBytes_entails_memRegion _ bs3) (sepConj_mono (pointsTo64_entails_memRegion _ v1) ?_)
  exact sepConj_mono (pointsTo64_entails_memRegion _ v2) (sepConj_mono (pointsTo64_entails_memRegion _ v3) (pointsTo64_entails_memRegion _ v4))
set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 512 in
attribute [local simp] sc52Pack5_length in
theorem scalar_mul_ref_ok : ScalarMulRefOk := by
  intro _
  apply dalekCaller_ok dalekCliPC21 dalekCliPl21
  intro b hb hbase
  wp_init
  wp_simp_pre only [stackFrame_split_top s0 448 288 160, reduceStackFrameAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_sym_steps
  wp_simp_pre only [sc52Pack5_stack_rest s0.sp 152 144 136 128 120, sc52Pack5_stack_rest s0.sp 112 104 96 88 80,
    sc52Pack5_stack_rest s0.sp 72 64 56 48 40, sc52Unpack32_fold a_4, sc52Unpack32_fold a_rest, show s0.sp - 448#64 = s0.sp - 160#64 - 288#64 by bv_omega]
  obtain ⟨⟨ha_len, _, _, _, _, _⟩, ha_val, ha_lt⟩ := sc52_unpack_bytes32_pack5 a_4 h_6
  obtain ⟨⟨hb_len, _, _, _, _, _⟩, hb_val, hb_lt⟩ := sc52_unpack_bytes32_pack5 a_rest h_1
  have hmul_bound : sc52ValOfBytes (sc52Unpack32 a_4) * sc52ValOfBytes (sc52Unpack32 a_rest) < 2 ^ 260 * edOrderL := by
    rw [ha_val, hb_val]; exact sc52_mul_bound_of_lt_256 ha_lt hb_lt
  have hmul_bound0 : leBytesToNat a_4 * leBytesToNat a_rest < 2 ^ 260 * edOrderL := sc52_mul_bound_of_lt_256 ha_lt hb_lt
  wp_steps 1; wp_dalek_call sc52_mul_core_ok; rcases (by assumption : sc52LimbsBounded w (2 ^ 52)) with ⟨hw_len, hw0, hw1, hw2, hw3, hw4⟩; wp_sym_steps 80
  have hval_eq : sc52ValOfBytes w = leBytesToNat a_4 * leBytesToNat a_rest % edOrderL := by rw [hpost, ha_val, hb_val]
  wp_simp_pre only [write8_32_mul a_3 w h_5 hw0 hw1 hw2 hw3 hw4, hval_eq]
  apply SepWP.weaken_pre
  · show _ ⊢ a ↦ₛ a_4 ∗ a_2 ↦ₛ a_rest ∗ stackFrame s0 448 ∗ a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_4 * leBytesToNat a_rest % edOrderL)
    rw [show ((s0.sp - 112#64) ↦ₛ sc52Unpack32 a_4 ∗ (s0.sp - 72#64) ↦ₛ sc52Unpack32 a_rest ∗ stackFrame sf 288 ∗ (s0.sp - 152#64) ↦ₛ w ∗
          a ↦ₛ a_4 ∗ a_2 ↦ₛ a_rest ∗ a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_4 * leBytesToNat a_rest % edOrderL) ∗ (s0.sp - 160#64) ↦₆₄ _ ∗
          (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗ (s0.sp - 8#64) ↦₆₄ _) =
        a ↦ₛ a_4 ∗ (a_2 ↦ₛ a_rest ∗ ((stackFrame sf 288 ∗ ((s0.sp - 160#64) ↦₆₄ _ ∗ ((s0.sp - 152#64) ↦ₛ w ∗
          ((s0.sp - 112#64) ↦ₛ sc52Unpack32 a_4 ∗ ((s0.sp - 72#64) ↦ₛ sc52Unpack32 a_rest ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗ (s0.sp - 8#64) ↦₆₄ _)))))))) ∗
          a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_4 * leBytesToNat a_rest % edOrderL))) by sep_ac_rfl]
    refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono ?_ (Entails.refl _)))
    exact stackFrame448_mul_fold s0 sf hsp_sf w (sc52Unpack32 a_4) (sc52Unpack32 a_rest) hw_len ha_len hb_len _ _ _ _ _
  wp_done
theorem scalar_mul_val_ok : ScalarMulValOk := by
  intro _
  apply dalekCaller_ok dalekCliPC34 dalekCliPl34
  intro b hb hbase
  wp_init
  wp_steps
  wp_dalek_tailcall scalar_mul_ref_ok
  rw [show stackFrame sf 448 = stackFrame s0 448 by simp [stackFrame, hsp_sf]]
  wp_done
private meta def isSimpleCheckpointVal (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
  let isBase (b : Lean.Expr) : Bool :=
    let b := b.consumeMData; b.isFVar || (b.isAppOfArity ``Arm64.State.sp 1 && (b.getArg! 0).consumeMData.isFVar)
  if isBase e || (ProofLib.evalBitVecLitPure? e).isSome || (e.isAppOfArity ``Obj.Placement.ρ 2 || e.isAppOfArity ``Obj.MultiPlacement.ρ 2 || e.isAppOfArity ``Obj.MultiPlacedLib.resolve 3 || e.isAppOfArity ``LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase.sc52_l 1 || e.isAppOfArity ``LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase.sc52_rr 1) then true
  else if e.isAppOfArity ``Arm64.State.readReg64 2 && (e.getArg! 0).consumeMData.isFVar then true
  else if (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6) &&
          isBase (e.getArg! 4) && (ProofLib.evalBitVecLitPure? (e.getArg! 5)).isSome then true
  else false
private meta structure CheckpointItem where (xName hName : Lean.Name) (ty val : Lean.Expr)
private meta partial def checkpointCollectState (recordVal : Lean.Expr → Lean.MetaM Unit) (st : Lean.Expr) : Lean.MetaM Unit := do
  let st := st.consumeMData
  if st.isAppOfArity ``Arm64.State.writeReg64 3 then checkpointCollectState recordVal (st.getArg! 0); recordVal (st.getArg! 2)
  else if st.isAppOfArity ``Arm64.State.setPState 2 then
    checkpointCollectState recordVal (st.getArg! 0); let p := (st.getArg! 1).consumeMData
    if p.isAppOfArity ``ProofLib.addsPState64 2 || p.isAppOfArity ``ProofLib.subsPState64 2 then recordVal (p.getArg! 0); recordVal (p.getArg! 1)
  else if st.isAppOfArity ``Arm64.State.setPC 2 || st.isAppOfArity ``Arm64.State.setMem 2 || st.isAppOfArity ``Arm64.State.writeVReg128 3 then
    checkpointCollectState recordVal (st.getArg! 0)
private meta partial def checkpointCollectPre (recordVal : Lean.Expr → Lean.MetaM Unit) (pr : Lean.Expr) : Lean.MetaM Unit := do
  let pr := pr.consumeMData
  if pr.isAppOfArity ``SepProp.sepConj 2 then checkpointCollectPre recordVal (pr.getArg! 0); checkpointCollectPre recordVal (pr.getArg! 1)
  else if pr.isAppOfArity ``Arm64.pointsTo64 2 then recordVal (pr.getArg! 1)
private meta partial def checkpointRebuildState (lookupVal : Lean.Expr → Lean.MetaM (Lean.Expr × Lean.Expr)) (st : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let st := st.consumeMData
  if st.isAppOfArity ``Arm64.State.writeReg64 3 then
    let s1 := st.getArg! 0; let r := st.getArg! 1; let v := st.getArg! 2
    let (s1', hs1) ← checkpointRebuildState lookupVal s1; let (v', hv) ← lookupVal v
    let st' := Lean.mkApp3 (Lean.mkConst ``Arm64.State.writeReg64) s1' r v'
    let c1 ← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.writeReg64) hs1
    let c2 ← Lean.Meta.mkCongr c1 (← Lean.Meta.mkEqRefl r); return (st', ← Lean.Meta.mkCongr c2 hv)
  else if st.isAppOfArity ``Arm64.State.setPState 2 then
    let s1 := st.getArg! 0; let p := (st.getArg! 1).consumeMData; let (s1', hs1) ← checkpointRebuildState lookupVal s1
    if p.isAppOfArity ``ProofLib.addsPState64 2 || p.isAppOfArity ``ProofLib.subsPState64 2 then
      let fn := p.getAppFn; let (a', ha) ← lookupVal (p.getArg! 0); let (b', hb) ← lookupVal (p.getArg! 1)
      let p' := Lean.mkApp2 fn a' b'; let hp ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg fn ha) hb
      return (Lean.mkApp2 (Lean.mkConst ``Arm64.State.setPState) s1' p', ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.setPState) hs1) hp)
    else
      return (Lean.mkApp2 (Lean.mkConst ``Arm64.State.setPState) s1' p, ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.setPState) hs1) (← Lean.Meta.mkEqRefl p))
  else if st.isAppOfArity ``Arm64.State.setPC 2 || st.isAppOfArity ``Arm64.State.setMem 2 then
    let fn := st.getAppFn; let s1 := st.getArg! 0; let a := st.getArg! 1; let (s1', hs1) ← checkpointRebuildState lookupVal s1
    return (Lean.mkApp2 fn s1' a, ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg fn hs1) (← Lean.Meta.mkEqRefl a))
  else if st.isAppOfArity ``Arm64.State.writeVReg128 3 then
    let fn := st.getAppFn; let s1 := st.getArg! 0; let r := st.getArg! 1; let v := st.getArg! 2; let (s1', hs1) ← checkpointRebuildState lookupVal s1
    return (Lean.mkApp3 fn s1' r v, ← Lean.Meta.mkCongr (← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg fn hs1) (← Lean.Meta.mkEqRefl r)) (← Lean.Meta.mkEqRefl v))
  else return (st, ← Lean.Meta.mkEqRefl st)
private meta partial def checkpointRebuildPre (lookupVal : Lean.Expr → Lean.MetaM (Lean.Expr × Lean.Expr)) (pr : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let pr := pr.consumeMData
  if pr.isAppOfArity ``SepProp.sepConj 2 then
    let (a', ha) ← checkpointRebuildPre lookupVal (pr.getArg! 0); let (b', hb) ← checkpointRebuildPre lookupVal (pr.getArg! 1)
    return (Lean.mkApp2 (Lean.mkConst ``SepProp.sepConj) a' b', ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg (Lean.mkConst ``SepProp.sepConj) ha) hb)
  else if pr.isAppOfArity ``Arm64.pointsTo64 2 then
    let addr := pr.getArg! 0; let (v', hv) ← lookupVal (pr.getArg! 1)
    return (Lean.mkApp2 (Lean.mkConst ``Arm64.pointsTo64) addr v', ← Lean.Meta.mkCongrArg (Lean.mkApp (Lean.mkConst ``Arm64.pointsTo64) addr) hv)
  else return (pr, ← Lean.Meta.mkEqRefl pr)
local elab "wp_checkpoint" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return
    let prog := ty.getArg! 0; let targetPc := ty.getArg! 1; let s := ty.getArg! 2
    let P := ty.getArg! 3; let post := ty.getArg! 4; let oom := ty.getArg! 5
    let lctx ← Lean.MonadLCtx.getLCtx; let mut baseIdx : Nat := 0
    for decl in lctx do if !decl.isImplementationDetail && decl.type.consumeMData.isAppOfArity ``CheckpointEq 3 then baseIdx := baseIdx + 1
    let itemsRef ← IO.mkRef (#[] : Array CheckpointItem); let mapRef ← IO.mkRef ({} : Std.HashMap Lean.Expr Nat)
    let recordVal (v : Lean.Expr) : Lean.MetaM Unit := do
      let v := v.consumeMData
      if isSimpleCheckpointVal v || (← mapRef.get).contains v then return
      let idx := (← itemsRef.get).size; let n := baseIdx + idx; let vTy ← Lean.Meta.inferType v
      itemsRef.modify (·.push { xName := Lean.Name.mkSimple s!"v_cp_{n}", hName := Lean.Name.mkSimple s!"hv_cp_{n}", ty := vTy, val := v })
      mapRef.modify (·.insert v idx)
    checkpointCollectState recordVal s; checkpointCollectPre recordVal P
    let items ← itemsRef.get; if items.isEmpty then return
    let idxMap ← mapRef.get
    let rec withItems (i : Nat) (xFVars hFVars : Array Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.MVarId) := do
      if h : i < items.size then
        let item := items[i]
        Lean.Meta.withLocalDeclD item.xName item.ty fun x => do
          let eqTy := Lean.mkApp3 (Lean.mkConst ``CheckpointEq) item.ty x item.val
          Lean.Meta.withLocalDeclD item.hName eqTy fun hx => do
            let hxEq := Lean.mkApp4 (Lean.mkConst ``CheckpointEq.to_eq) item.ty x item.val hx
            let (innerPrf, gNew) ← withItems (i + 1) (xFVars.push x) (hFVars.push hxEq)
            let cont ← Lean.Meta.mkLambdaFVars #[x, hx] innerPrf
            return (Lean.mkApp4 (Lean.mkConst ``CheckpointEq.elim) item.ty ty item.val cont, gNew)
      else
        let lookupVal (v : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
          let v := v.consumeMData; if let some idx := idxMap[v]? then return (xFVars[idx]!, hFVars[idx]!) else return (v, ← Lean.Meta.mkEqRefl v)
        let (s', hs) ← checkpointRebuildState lookupVal s; let (P', hP) ← checkpointRebuildPre lookupVal P
        let newGoalTy := Lean.mkApp6 (Lean.mkConst ``SepWP) prog targetPc s' P' post oom
        let gNew ← Lean.Meta.mkFreshExprMVar newGoalTy .syntheticOpaque (← g.getTag)
        return (Lean.mkAppN (Lean.mkConst ``sepWP_congr_state_pre) #[prog, targetPc, s', s, P', P, post, oom, hs, hP, gNew], gNew.mvarId!)
    let (prf, gNew) ← withItems 0 #[] #[]; g.assign prf; Lean.Elab.Tactic.replaceMainGoal [gNew]
private theorem sc52_add_step {s n : BitVec 64} {v : Nat} (hs : s.toNat = v) (hn : n = s &&& 4503599627370495#64) :
    ∃ c : Nat, n.toNat + 2 ^ 52 * c = v ∧ n.toNat < 2 ^ 52 ∧ (s >>> 52).toNat = c := by
  refine ⟨s.toNat / 2 ^ 52, ?_, ?_, ?_⟩
  · rw [hn, mask52_toNat, ← hs]; exact Nat.mod_add_div _ _
  · rw [hn, mask52_toNat]; exact Nat.mod_lt _ (by decide)
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

set_option exponentiation.threshold 512 in
private theorem sc52_add_limbs
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 sum0 sum1 sum2 sum3 n0 n1 n2 n3 n4 : BitVec 64)
    (ha0 : a0.toNat < 2 ^ 52) (ha1 : a1.toNat < 2 ^ 52) (ha2 : a2.toNat < 2 ^ 52) (ha3 : a3.toNat < 2 ^ 52)
    (hb0 : b0.toNat < 2 ^ 52) (hb1 : b1.toNat < 2 ^ 52) (hb2 : b2.toNat < 2 ^ 52) (hb3 : b3.toNat < 2 ^ 52)
    (ha_val : sc52Val a0 a1 a2 a3 a4 < edOrderL) (hb_val : sc52Val b0 b1 b2 b3 b4 < edOrderL)
    (hsum0 : sum0 = b0 + a0) (hn0 : n0 = sum0 &&& 4503599627370495#64)
    (hsum1 : sum1 = a1 + sum0 >>> 52 + b1) (hn1 : n1 = sum1 &&& 4503599627370495#64)
    (hsum2 : sum2 = a2 + sum1 >>> 52 + b2) (hn2 : n2 = sum2 &&& 4503599627370495#64)
    (hsum3 : sum3 = a3 + sum2 >>> 52 + b3) (hn3 : n3 = sum3 &&& 4503599627370495#64) (hn4 : n4 = a4 + b4 + sum3 >>> 52) :
    n0.toNat < 2 ^ 52 ∧ n1.toNat < 2 ^ 52 ∧ n2.toNat < 2 ^ 52 ∧ n3.toNat < 2 ^ 52 ∧
    sc52Val n0 n1 n2 n3 n4 = sc52Val a0 a1 a2 a3 a4 + sc52Val b0 b1 b2 b3 b4 ∧ sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL := by
  have hs0 : sum0.toNat = b0.toNat + a0.toNat := by rw [hsum0, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨c0, hd0, hlt0, hc0⟩ := sc52_add_step hs0 hn0; clear hsum0 hn0 hs0
  have hs1 : sum1.toNat = a1.toNat + c0 + b1.toNat := by
    rw [hsum1, BitVec.toNat_add, BitVec.toNat_add, hc0, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨c1, hd1, hlt1, hc1⟩ := sc52_add_step hs1 hn1; clear hsum1 hn1 hs1 hc0
  have hs2 : sum2.toNat = a2.toNat + c1 + b2.toNat := by
    rw [hsum2, BitVec.toNat_add, BitVec.toNat_add, hc1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨c2, hd2, hlt2, hc2⟩ := sc52_add_step hs2 hn2; clear hsum2 hn2 hs2 hc1
  have hs3 : sum3.toNat = a3.toNat + c2 + b3.toNat := by
    rw [hsum3, BitVec.toNat_add, BitVec.toNat_add, hc2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨c3, hd3, hlt3, hc3⟩ := sc52_add_step hs3 hn3; clear hsum3 hn3 hs3 hc2
  have ha4_lt : a4.toNat < 2 ^ 52 := by unfold sc52Val edOrderL at ha_val; omega
  have hb4_lt : b4.toNat < 2 ^ 52 := by unfold sc52Val edOrderL at hb_val; omega
  have hn4' : n4.toNat = a4.toNat + b4.toNat + c3 := by
    rw [hn4, BitVec.toNat_add, BitVec.toNat_add, hc3, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hval_eq : sc52Val n0 n1 n2 n3 n4 = sc52Val a0 a1 a2 a3 a4 + sc52Val b0 b1 b2 b3 b4 := by unfold sc52Val; grind
  exact ⟨hlt0, hlt1, hlt2, hlt3, hval_eq, by rw [hval_eq]; omega⟩
set_option exponentiation.threshold 512 in
private theorem sc52PackBytes32_cond_sub_l_add
    (n0 n1 n2 n3 n4 d0 s1 d1 s2 d2 s3 d3 s4 b4_bv : BitVec 64)
    (hn0 : n0.toNat < 2 ^ 52) (hn1 : n1.toNat < 2 ^ 52) (hn2 : n2.toNat < 2 ^ 52) (hn3 : n3.toNat < 2 ^ 52)
    (hn_val : sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL)
    (hd0 : d0 = (n0 + 18446072158876216339#64) &&& 4503599627370495#64)
    (hs1 : s1 = n1 + (n0 + 18446072158876216339#64).sshiftRight 63 + 18442827409384446591#64)
    (hd1 : d1 = s1 &&& 4503599627370495#64) (hs2 : s2 = n2 + s1.sshiftRight 63 - 1367801#64)
    (hd2 : d2 = s2 &&& 4503599627370495#64) (hs3 : s3 = n3 + s2.sshiftRight 63)
    (hd3 : d3 = s3 &&& 4503599627370495#64) (hs4 : s4 = n4 + s3.sshiftRight 63 + 18446726481523507200#64)
    (hb4 : b4_bv = s4 >>> 63) :
    let m := -BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv)
    let add0 := (m &&& 671914833335277#64) + d0; let add1 := (m &&& 3916664325105025#64) + d1 + add0 >>> 52
    let add2 := d2 + (m &&& 1367801#64) + add1 >>> 52; let add3 := d3 + add2 >>> 52
    let add4 := s4 + (m &&& 17592186044416#64) + add3 >>> 52
    sc52PackBytes32 add0 add1 add2 add3 add4 = natToLeBytes 32 (sc52Val n0 n1 n2 n3 n4 % edOrderL) := by
  intro m add0 add1 add2 add3 add4
  have hadd0 : add0 = d0 + (m &&& 671914833335277#64) := BitVec.add_comm _ _
  have hadd1 : add1 = (m &&& 3916664325105025#64) + (d0 + (m &&& 671914833335277#64)) >>> 52 + d1 := by
    change (m &&& 3916664325105025#64) + d1 + add0 >>> 52 = _; rw [hadd0, BitVec.add_assoc, BitVec.add_comm d1, ← BitVec.add_assoc]
  let r0 := add0 &&& 4503599627370495#64; let r1 := add1 &&& 4503599627370495#64; let r2 := add2 &&& 4503599627370495#64
  let r3 := add3 &&& 4503599627370495#64; let r4 := add4 &&& 4503599627370495#64
  have h_sub := sc52_cond_sub_l n0 n1 n2 n3 n4 d0 s1 d1 s2 d2 s3 d3 s4 b4_bv b4_bv r0 r1 r2 r3 r4
    hn0 hn1 hn2 hn3 hn_val hd0 hs1 hd1 hs2 hd2 hs3 hd3 hs4 hb4 rfl
    (by show add0 &&& _ = _; rw [hadd0]) (by show add1 &&& _ = _; rw [hadd1])
    (by show (d2 + (m &&& 1367801#64) + add1 >>> 52) &&& _ = _; rw [hadd1])
    (by show (d3 + (d2 + (m &&& 1367801#64) + add1 >>> 52) >>> 52) &&& _ = _; rw [hadd1])
    (by show (s4 + (m &&& 17592186044416#64) + (d3 + (d2 + (m &&& 1367801#64) + add1 >>> 52) >>> 52) >>> 52) &&& _ = _; rw [hadd1])
  rcases h_sub with ⟨_, _, _, _, _, hr_lt, q, _, hq_eq⟩
  have hmod : sc52Val r0 r1 r2 r3 r4 = sc52Val n0 n1 n2 n3 n4 % edOrderL := by rw [← hq_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr_lt]
  rw [sc52PackBytes32_eq_natToLeBytes add0 add1 add2 add3 add4 r0 r1 r2 r3 r4 rfl rfl rfl rfl rfl, hmod]
private theorem write8_32_add_order (bs : List (BitVec 8)) (h : bs.length = 32)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : BitVec 8) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 1 x1) 2 x2) 3 x3) 4 x4) 5 x5) 7 x7) 6 x6) 9 x9) 8 x8) 11 x11) 10 x10)
      12 x12) 14 x14) 15 x15) 13 x13) 16 x16) 18 x18) 17 x17) 21 x21) 20 x20) 24 x24)
      23 x23) 25 x25) 26 x26) 27 x27) 19 x19) 22 x22) 28 x28) 29 x29) 30 x30) 31 x31 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := exists_bytes32 h
  simp only [ByteSlice.write8, ByteSlice.write, List.take, List.drop, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
private theorem write8_32_add (bs : List (BitVec 8)) (h : bs.length = 32) (add0 add1 add2 add3 add4 : BitVec 64) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 (BitVec.zeroExtend 8 add0)) 1 (BitVec.zeroExtend 8 (add0 >>> 8)))
      2 (BitVec.zeroExtend 8 (add0 >>> 16))) 3 (BitVec.zeroExtend 8 (add0 >>> 24)))
      4 (BitVec.zeroExtend 8 (add0 >>> 32))) 5 (BitVec.zeroExtend 8 (add0 >>> 40)))
      7 (BitVec.zeroExtend 8 (add1 >>> 4)))
      6 (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (add0 >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 add1) &&& 268435455#64) <<< 4)))
      9 (BitVec.zeroExtend 8 (add1 >>> 20))) 8 (BitVec.zeroExtend 8 (add1 >>> 12)))
      11 (BitVec.zeroExtend 8 (add1 >>> 36))) 10 (BitVec.zeroExtend 8 (add1 >>> 28)))
      12 (BitVec.zeroExtend 8 (add1 >>> 44))) 14 (BitVec.zeroExtend 8 (add2 >>> 8)))
      15 (BitVec.zeroExtend 8 (add2 >>> 16))) 13 (BitVec.zeroExtend 8 add2))
      16 (BitVec.zeroExtend 8 (add2 >>> 24))) 18 (BitVec.zeroExtend 8 (add2 >>> 40)))
      17 (BitVec.zeroExtend 8 (add2 >>> 32))) 21 (BitVec.zeroExtend 8 (add3 >>> 12)))
      20 (BitVec.zeroExtend 8 (add3 >>> 4))) 24 (BitVec.zeroExtend 8 (add3 >>> 36)))
      23 (BitVec.zeroExtend 8 (add3 >>> 28))) 25 (BitVec.zeroExtend 8 (add3 >>> 44)))
      26 (BitVec.zeroExtend 8 add4)) 27 (BitVec.zeroExtend 8 (add4 >>> 8)))
      19 (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (add2 >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 add3) &&& 268435455#64) <<< 4)))
      22 (BitVec.zeroExtend 8 (add3 >>> 20))) 28 (BitVec.zeroExtend 8 (add4 >>> 16)))
      29 (BitVec.zeroExtend 8 (add4 >>> 24))) 30 (BitVec.zeroExtend 8 (add4 >>> 32)))
      31 (BitVec.zeroExtend 8 (add4 >>> 40)) =
    sc52PackBytes32 add0 add1 add2 add3 add4 := by
  exact write8_32_add_order bs h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
private theorem stackFrame80_add_fold (s0 sf : State) (hsp : sf.sp = s0.sp - 64#64) (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    (stackFrame sf 16 ∗ ((s0.sp - 64#64) ↦₆₄ v0 ∗ ((s0.sp - 56#64) ↦₆₄ v1 ∗ ((s0.sp - 48#64) ↦₆₄ v2 ∗
      ((s0.sp - 40#64) ↦₆₄ v3 ∗ ((s0.sp - 32#64) ↦₆₄ v4 ∗ ((s0.sp - 24#64) ↦₆₄ v5 ∗
        ((s0.sp - 16#64) ↦₆₄ v6 ∗ (s0.sp - 8#64) ↦₆₄ v7)))))))) ⊢ stackFrame s0 80 := by
  have hsf : stackFrame sf 16 = memRegion (s0.sp - 80#64) 16 := by
    change memRegion (sf.sp - 16#64) 16 = _; rw [hsp, show s0.sp - 64#64 - 16#64 = s0.sp - 80#64 by bv_omega]
  have hrhs : stackFrame s0 80 = memRegion (s0.sp - 80#64) 16 ∗ (memRegion (s0.sp - 64#64) 8 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ (memRegion (s0.sp - 48#64) 8 ∗ (memRegion (s0.sp - 40#64) 8 ∗
      (memRegion (s0.sp - 32#64) 8 ∗ (memRegion (s0.sp - 24#64) 8 ∗ (memRegion (s0.sp - 16#64) 8 ∗ memRegion (s0.sp - 8#64) 8))))))) := by
    change memRegion (s0.sp - 80#64) 80 = _
    rw [memRegion_split_sub s0.sp 80 16 64, memRegion_split_sub s0.sp 64 8 56, memRegion_split_sub s0.sp 56 8 48,
        memRegion_split_sub s0.sp 48 8 40, memRegion_split_sub s0.sp 40 8 32, memRegion_split_sub s0.sp 32 8 24,
        memRegion_split_sub s0.sp 24 8 16, memRegion_split_sub s0.sp 16 8 8]
  rw [hsf, hrhs]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo64_entails_memRegion _ v0) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ v1) (sepConj_mono (pointsTo64_entails_memRegion _ v2) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ v3) (sepConj_mono (pointsTo64_entails_memRegion _ v4) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ v5) (sepConj_mono (pointsTo64_entails_memRegion _ v6) (pointsTo64_entails_memRegion _ v7))
set_option maxHeartbeats 800000 in
theorem scalar_add_ref_ok : ScalarAddRefOk := by
  intro _
  apply dalekCaller_ok dalekCliPC23 dalekCliPl23
  intro b hb hbase
  wp_init
  wp_simp_pre only [stackFrame_split_top s0 80 16 64, reduceStackFrameAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_sym_steps 50; wp_checkpoint; wp_sym_steps 35; wp_checkpoint; wp_sym_steps 25; wp_checkpoint
  have h_res :
      let m := -BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_33)
      let add0 := (m &&& 671914833335277#64) + v_cp_24; let add1 := (m &&& 3916664325105025#64) + v_cp_26 + add0 >>> 52
      let add2 := v_cp_29 + (m &&& 1367801#64) + add1 >>> 52; let add3 := v_cp_31 + add2 >>> 52
      let add4 := v_cp_32 + (m &&& 17592186044416#64) + add3 >>> 52
      sc52PackBytes32 add0 add1 add2 add3 add4 = natToLeBytes 32 ((leBytesToNat a_4 + leBytesToNat a_rest) % edOrderL) := by
    obtain ⟨ha0, ha1, ha2, ha3, _, ha_val, _⟩ := sc52_unpack_bytes32 a_4 h_6 v_cp_6 v_cp_10 v_cp_11
      (BitVec.setWidth 64 ((v_cp_1 ++ v_cp_0) >>> 28)) (v_cp_3 ||| v_cp_2 <<< 40)
      hv_cp_6 hv_cp_10 hv_cp_11 (by rw [hv_cp_1, hv_cp_0]) (by rw [hv_cp_3, hv_cp_2])
    obtain ⟨hb0, hb1, hb2, hb3, _, hb_val, _⟩ := sc52_unpack_bytes32 a_rest h_7 (v_cp_7 &&& 4503599627370495#64)
      (BitVec.setWidth 64 ((v_cp_13 ++ v_cp_12) >>> 52))
      (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 (a_rest.getD 16 0#8) (a_rest.getD 17 0#8) (a_rest.getD 18 0#8) (a_rest.getD 19 0#8)) ++ (v_cp_8 ||| v_cp_9 <<< 48 ||| BitVec.zeroExtend 64 (a_rest.getD 15 0#8) <<< 56)) >>> 40) &&& 4503599627370495#64)
      v_cp_22 (v_cp_20 ||| v_cp_19 <<< 40) (by rw [hv_cp_7]) (by rw [hv_cp_13, hv_cp_12]) (by rw [hv_cp_8, hv_cp_9]) hv_cp_22 (by rw [hv_cp_20, hv_cp_19])
    obtain ⟨hn0, hn1, hn2, hn3, hn_val_eq, hn_lt⟩ := sc52_add_limbs v_cp_6 v_cp_10 v_cp_11
      (BitVec.setWidth 64 ((v_cp_1 ++ v_cp_0) >>> 28)) (v_cp_3 ||| v_cp_2 <<< 40)
      (v_cp_7 &&& 4503599627370495#64) (BitVec.setWidth 64 ((v_cp_13 ++ v_cp_12) >>> 52))
      (BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 (a_rest.getD 16 0#8) (a_rest.getD 17 0#8) (a_rest.getD 18 0#8) (a_rest.getD 19 0#8)) ++ (v_cp_8 ||| v_cp_9 <<< 48 ||| BitVec.zeroExtend 64 (a_rest.getD 15 0#8) <<< 56)) >>> 40) &&& 4503599627370495#64)
      v_cp_22 (v_cp_20 ||| v_cp_19 <<< 40) ((v_cp_7 &&& 4503599627370495#64) + v_cp_6)
      (v_cp_10 + ((v_cp_7 &&& 4503599627370495#64) + v_cp_6) >>> 52 + BitVec.setWidth 64 ((v_cp_13 ++ v_cp_12) >>> 52))
      v_cp_16 (v_cp_23 + v_cp_22) (((v_cp_7 &&& 4503599627370495#64) + v_cp_6) &&& 4503599627370495#64)
      ((v_cp_10 + ((v_cp_7 &&& 4503599627370495#64) + v_cp_6) >>> 52 + BitVec.setWidth 64 ((v_cp_13 ++ v_cp_12) >>> 52)) &&& 4503599627370495#64)
      v_cp_21 v_cp_25 ((v_cp_3 ||| v_cp_2 <<< 40) + (v_cp_20 ||| v_cp_19 <<< 40) + (v_cp_23 + v_cp_22) >>> 52)
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 (by rw [ha_val]; exact h_8) (by rw [hb_val]; exact h_1)
      rfl rfl rfl rfl hv_cp_16 (by rw [hv_cp_21, ← hv_cp_16]) (by rw [hv_cp_23, ← hv_cp_16]) hv_cp_25 rfl
    have h_pack := sc52PackBytes32_cond_sub_l_add
      (((v_cp_7 &&& 4503599627370495#64) + v_cp_6) &&& 4503599627370495#64)
      ((v_cp_10 + ((v_cp_7 &&& 4503599627370495#64) + v_cp_6) >>> 52 + BitVec.setWidth 64 ((v_cp_13 ++ v_cp_12) >>> 52)) &&& 4503599627370495#64)
      v_cp_21 v_cp_25 ((v_cp_3 ||| v_cp_2 <<< 40) + (v_cp_20 ||| v_cp_19 <<< 40) + (v_cp_23 + v_cp_22) >>> 52)
      v_cp_24 (v_cp_17 + 18442827409384446591#64) v_cp_26 v_cp_27 v_cp_29 v_cp_28 v_cp_31 v_cp_32 v_cp_33
      hn0 hn1 hn2 hn3 hn_lt (by rw [hv_cp_24, hv_cp_15]) (by rw [hv_cp_17]) hv_cp_26 hv_cp_27
      (by rw [hv_cp_29, ← hv_cp_27]) (by rw [hv_cp_28, ← hv_cp_25, ← hv_cp_27]) (by rw [hv_cp_31, ← hv_cp_28]) (by rw [hv_cp_32, ← hv_cp_28]) (by rw [hv_cp_33, ← hv_cp_32])
    dsimp only at h_pack ⊢; rw [h_pack, hn_val_eq, ha_val, hb_val]
  wp_simp_pre only [show s0.sp - 80#64 = s0.sp - 64#64 - 16#64 by bv_omega]; wp_steps 1; wp_dalek_call black_box_u8_ok; wp_sym_steps 100
  wp_simp_pre only [write8_32_add a_3 h_5, h_res]
  apply SepWP.weaken_pre
  · show _ ⊢ a ↦ₛ a_4 ∗ a_2 ↦ₛ a_rest ∗ stackFrame s0 80 ∗ a_1 ↦ₛ natToLeBytes 32 ((leBytesToNat a_4 + leBytesToNat a_rest) % edOrderL)
    rw [show (stackFrame sf 16 ∗ a ↦ₛ a_4 ∗ a_2 ↦ₛ a_rest ∗ a_1 ↦ₛ natToLeBytes 32 ((leBytesToNat a_4 + leBytesToNat a_rest) % edOrderL) ∗
          (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
          (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
          (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) =
        a ↦ₛ a_4 ∗ (a_2 ↦ₛ a_rest ∗ ((stackFrame sf 16 ∗ ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))) ∗
          a_1 ↦ₛ natToLeBytes 32 ((leBytesToNat a_4 + leBytesToNat a_rest) % edOrderL))) by sep_ac_rfl]
    refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono ?_ (Entails.refl _)))
    exact stackFrame80_add_fold s0 sf hsp_sf _ _ _ _ _ _ _ _
  wp_done
theorem scalar_add_val_ok : ScalarAddValOk := by
  intro _
  apply dalekCaller_ok dalekCliPC35 dalekCliPl35
  intro b hb hbase
  wp_init
  wp_steps
  wp_dalek_tailcall scalar_add_ref_ok
  rw [show stackFrame sf 80 = stackFrame s0 80 by simp [stackFrame, hsp_sf]]
  wp_done
private meta def matchStackCell? (e : Lean.Expr) : Option (Lean.Expr × Nat × Lean.Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.pointsTo64 2 then
    let addr := (e.getArg! 0).consumeMData; let v := e.getArg! 1
    if addr.isAppOfArity ``HSub.hSub 6 then match ProofLib.evalBitVecLitPure? (addr.getArg! 5) with | some (64, n) => some (addr.getArg! 4, n, v) | _ => none else none
  else none
private meta def matchStackRegion? (e : Lean.Expr) : Option (Lean.Expr × Nat) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.memRegion 2 then
    let addr := (e.getArg! 0).consumeMData; let kExpr := (e.getArg! 1).consumeMData
    if addr.isAppOfArity ``HSub.hSub 6 then
      match ProofLib.evalBitVecLitPure? (addr.getArg! 5), kExpr.nat? with | some (64, n), some k => if n == k then some (addr.getArg! 4, k) else none | _, _ => none
    else none
  else none
private meta partial def foldStackEntails (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let P := e.getArg! 0; let Q := e.getArg! 1; let (Q', hQ) ← foldStackEntails Q
    let step1 := Lean.mkApp4 (Lean.mkConst ``sepConj_mono_right) P Q Q' hQ
    let mid := Lean.mkApp2 (Lean.mkConst ``SepProp.sepConj) P Q'
    if let (some (sp1, n, v), some (sp2, k)) := (matchStackCell? P, matchStackRegion? Q') then
      if sp1 == sp2 && 8 + k == n && n ≤ 2 ^ 64 then
        let nExpr := Lean.mkNatLit n; let kExpr := Lean.mkNatLit k; let hmk ← Lean.Meta.mkEqRefl nExpr
        let hn ← Lean.Meta.mkDecideProof (← Lean.Meta.mkAppM ``LE.le #[nExpr, Lean.mkNatLit (2 ^ 64)])
        let step2 := Lean.mkApp6 (Lean.mkConst ``stack_fold_step) sp1 v nExpr kExpr hmk hn
        let subN ← Lean.Meta.mkAppM ``HSub.hSub #[sp1, Lean.ToExpr.toExpr (BitVec.ofNat 64 n)]
        let rhs := Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) subN nExpr
        return (rhs, Lean.mkApp5 (Lean.mkConst ``Entails.trans) e mid rhs step1 step2)
    return (mid, step1)
  else if let some (sp, 8, v) := matchStackCell? e then
    let sub8 ← Lean.Meta.mkAppM ``HSub.hSub #[sp, Lean.ToExpr.toExpr (8#64)]
    return (Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) sub8 (Lean.mkNatLit 8), Lean.mkApp2 (Lean.mkConst ``stack_fold_last) sp v)
  else return (e, Lean.mkApp (Lean.mkConst ``Entails.refl) e)
local elab "wp_fold_stack" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| wp_conv_pre => simp only [stack_swap_slice, stack_swap_slice_ro, sepConj_assoc]))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return
    let prog := ty.getArg! 0; let targetPc := ty.getArg! 1; let s := ty.getArg! 2
    let P := ty.getArg! 3; let post := ty.getArg! 4; let oom := ty.getArg! 5
    let (P', hent) ← foldStackEntails P
    let gNew ← Lean.Meta.mkFreshExprMVar (Lean.mkApp6 (Lean.mkConst ``SepWP) prog targetPc s P' post oom) .syntheticOpaque (← g.getTag)
    g.assign (Lean.mkAppN (Lean.mkConst ``SepWP.weaken_pre) #[prog, targetPc, s, P, P', post, oom, hent, gNew])
    Lean.Elab.Tactic.replaceMainGoal [gNew.mvarId!]
private theorem pointsToBytes40_cells_eq_rest (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40) (rest : SepProp) :
    ((a ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((a + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8 ∗
      ((a + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8 ∗ ((a + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8 ∗ ((a + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8 ∗ rest))))) =
    ((a ↦ₛ bs) ∗ rest) := by rw [pointsToBytes40_eq_cells a bs h]; sep_ac_rfl
private theorem sc52RRBytes_limbsBounded : sc52LimbsBounded sc52RRBytes (2 ^ 52) := by
  unfold sc52LimbsBounded
  rw [sc52RRBytes_length, sc52RR_readLE_0, sc52RR_readLE_8, sc52RR_readLE_16, sc52RR_readLE_24, sc52RR_readLE_32]
  decide
private theorem sc52LBytes_limbsBounded : sc52LimbsBounded sc52LBytes (2 ^ 52) := by
  unfold sc52LimbsBounded
  rw [sc52LBytes_length, sc52L_readLE_0, sc52L_readLE_8, sc52L_readLE_16, sc52L_readLE_24, sc52L_readLE_32]
  decide
private theorem edOrderL_pos : 0 < edOrderL := by unfold edOrderL; omega
set_option exponentiation.threshold 512 in
private theorem sc52RRBytes_val_lt : sc52ValOfBytes sc52RRBytes < edOrderL := by
  rw [sc52RR_val]; exact Nat.mod_lt _ edOrderL_pos
set_option exponentiation.threshold 512 in
private theorem sc52LBytes_val_lt : sc52ValOfBytes sc52LBytes < edOrderL := by
  rw [sc52L_val]; exact Nat.mod_lt _ edOrderL_pos
set_option exponentiation.threshold 512 in
private theorem cancel_mont_wide {w w1 lo hi total : Nat}
    (hw : w * 2 ^ 260 % edOrderL = lo * sc52ValOfBytes sc52RRBytes % edOrderL)
    (hw1 : w1 * 2 ^ 260 % edOrderL = hi * sc52ValOfBytes sc52LBytes % edOrderL) (htot : lo + hi * 2 ^ 260 = total) :
    (w + w1) % edOrderL = total % edOrderL := by
  let inv := 5706410653605570882457795059301885719620630590890452783038400561109479083972
  have hinv : (2 ^ 260 * inv) % edOrderL = 1 := by decide
  have h1 : (w + w1) * 2 ^ 260 % edOrderL = total * 2 ^ 260 % edOrderL := by
    rw [Nat.add_mul, Nat.add_mod, hw, hw1, sc52RR_val, sc52L_val, Nat.mul_mod_mod, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.add_mod, ← Nat.add_mul, htot]
  have h2 : ((w + w1) * (2 ^ 260 * inv)) % edOrderL = (total * (2 ^ 260 * inv)) % edOrderL := by
    rw [← Nat.mul_assoc, ← Nat.mod_mul_mod, h1, Nat.mod_mul_mod, Nat.mul_assoc]
  rwa [← Nat.mul_mod_mod, hinv, Nat.mul_one, ← Nat.mul_mod_mod, hinv, Nat.mul_one] at h2
set_option exponentiation.threshold 512 in
private theorem sc52_add_limbs_wide (w u : List (BitVec 8))
    (hw0 : (ByteSlice.readLE w 0 8).toNat < 2 ^ 52) (hw1 : (ByteSlice.readLE w 8 8).toNat < 2 ^ 52)
    (hw2 : (ByteSlice.readLE w 16 8).toNat < 2 ^ 52) (hw3 : (ByteSlice.readLE w 24 8).toNat < 2 ^ 52)
    (hu0 : (ByteSlice.readLE u 0 8).toNat < 2 ^ 52) (hu1 : (ByteSlice.readLE u 8 8).toNat < 2 ^ 52)
    (hu2 : (ByteSlice.readLE u 16 8).toNat < 2 ^ 52) (hu3 : (ByteSlice.readLE u 24 8).toNat < 2 ^ 52)
    (hw_val : sc52ValOfBytes w < edOrderL) (hu_val : sc52ValOfBytes u < edOrderL) :
    let w0 := ByteSlice.readLE w 0 8; let w1 := ByteSlice.readLE w 8 8; let w2 := ByteSlice.readLE w 16 8; let w3 := ByteSlice.readLE w 24 8; let w4 := ByteSlice.readLE w 32 8
    let u0 := ByteSlice.readLE u 0 8; let u1 := ByteSlice.readLE u 8 8; let u2 := ByteSlice.readLE u 16 8; let u3 := ByteSlice.readLE u 24 8; let u4 := ByteSlice.readLE u 32 8
    let s0 := w0 + u0; let n0 := s0 &&& 4503599627370495#64; let s1 := u1 + s0 >>> 52 + w1; let n1 := s1 &&& 4503599627370495#64
    let s2 := w2 + u2 + s1 >>> 52; let n2 := s2 &&& 4503599627370495#64; let s3 := w3 + u3 + s2 >>> 52; let n3 := s3 &&& 4503599627370495#64
    let n4 := (w4 + u4 + s3 >>> 52) &&& 4503599627370495#64
    n0.toNat < 2 ^ 52 ∧ n1.toNat < 2 ^ 52 ∧ n2.toNat < 2 ^ 52 ∧ n3.toNat < 2 ^ 52 ∧ sc52Val n0 n1 n2 n3 n4 = sc52ValOfBytes w + sc52ValOfBytes u ∧ sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL := by
  intro w0 w1 w2 w3 w4 u0 u1 u2 u3 u4 s0 n0 s1 n1 s2 n2 s3 n3 n4
  have hadd := sc52_add_limbs w0 w1 w2 w3 w4 u0 u1 u2 u3 u4 s0 s1 s2 s3 n0 n1 n2 n3 (w4 + u4 + s3 >>> 52) hw0 hw1 hw2 hw3 hu0 hu1 hu2 hu3 hw_val hu_val
    (BitVec.add_comm w0 u0) rfl (by change u1 + s0 >>> 52 + w1 = w1 + s0 >>> 52 + u1; bv_omega) rfl
    (by change w2 + u2 + s1 >>> 52 = w2 + s1 >>> 52 + u2; bv_omega) rfl (by change w3 + u3 + s2 >>> 52 = w3 + s2 >>> 52 + u3; bv_omega) rfl rfl
  have hn4_lt : (w4 + u4 + s3 >>> 52).toNat < 2 ^ 52 := by rcases hadd with ⟨_, _, _, _, _, hlt⟩; unfold sc52Val edOrderL at hlt; omega
  have hn4_eq : n4 = w4 + u4 + s3 >>> 52 := and_mask52_of_lt hn4_lt; rw [hn4_eq]; exact hadd
private theorem stackFrame448_wide_fold (s0 sf : State) (hsp : sf.sp = s0.sp - 192#64)
    (bs1 bs2 bs3 : List (BitVec 8)) (h1 : bs1.length = 40) (h2 : bs2.length = 40) (h3 : bs3.length = 40) (v0 : BitVec 64) :
    (memRegion (s0.sp - 448#64) 240 ∗ (stackFrame sf 16 ∗ ((s0.sp - 192#64) ↦ₛ bs1 ∗
      ((s0.sp - 152#64) ↦₆₄ v0 ∗ ((s0.sp - 144#64) ↦ₛ bs2 ∗ ((s0.sp - 104#64) ↦ₛ bs3 ∗ memRegion (s0.sp - 64#64) 64)))))) ⊢ stackFrame s0 448 := by
  have hsf : stackFrame sf 16 = memRegion (s0.sp - 208#64) 16 := by
    change memRegion (sf.sp - 16#64) 16 = _; rw [hsp, show s0.sp - 192#64 - 16#64 = s0.sp - 208#64 by bv_omega]
  have hrhs : stackFrame s0 448 = memRegion (s0.sp - 448#64) 240 ∗ (memRegion (s0.sp - 208#64) 16 ∗ (memRegion (s0.sp - 192#64) 40 ∗
      (memRegion (s0.sp - 152#64) 8 ∗ (memRegion (s0.sp - 144#64) 40 ∗ (memRegion (s0.sp - 104#64) 40 ∗ memRegion (s0.sp - 64#64) 64))))) := by
    change memRegion (s0.sp - 448#64) 448 = _
    rw [memRegion_split_sub s0.sp 448 240 208, memRegion_split_sub s0.sp 208 16 192, memRegion_split_sub s0.sp 192 40 152,
        memRegion_split_sub s0.sp 152 8 144, memRegion_split_sub s0.sp 144 40 104, memRegion_split_sub s0.sp 104 40 64]
  rw [hsf, hrhs]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (h1 ▸ pointsToBytes_entails_memRegion _ bs1) (sepConj_mono (pointsTo64_entails_memRegion _ v0) ?_)
  exact sepConj_mono (h2 ▸ pointsToBytes_entails_memRegion _ bs2) (sepConj_mono (h3 ▸ pointsToBytes_entails_memRegion _ bs3) (Entails.refl _))
private def unpack13Lo (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : BitVec 64 :=
  (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48) &&& 4503599627370495#64
private def unpack13Hi (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8) : BitVec 64 :=
  BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11) ||| BitVec.zeroExtend 64 b12 <<< 32) ++
    (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48 ||| BitVec.zeroExtend 64 b7 <<< 56)) >>> 52)
set_option exponentiation.threshold 512 in
private theorem unpack_pair13 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8)
    (a0 a1 : BitVec 64) (ha0 : a0 = unpack13Lo b0 b1 b2 b3 b4 b5 b6) (ha1 : a1 = unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12) :
    a0.toNat < 2 ^ 52 ∧ a1.toNat < 2 ^ 52 ∧ a0.toNat + a1.toNat * 2 ^ 52 =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 +
      b8.toNat * 2 ^ 64 + b9.toNat * 2 ^ 72 + b10.toNat * 2 ^ 80 + b11.toNat * 2 ^ 88 + b12.toNat * 2 ^ 96 := by
  have hp0 := zext_toNat_eq (pack32 b0 b1 b2 b3) (w := 64) (by decide); rw [pack32_toNat] at hp0
  have hp8 := zext_toNat_eq (pack32 b8 b9 b10 b11) (w := 64) (by decide); rw [pack32_toNat] at hp8
  have hb4 := zext_toNat_eq b4 (w := 64) (by decide); have hb5 := zext_toNat_eq b5 (w := 64) (by decide)
  have hb6 := zext_toNat_eq b6 (w := 64) (by decide); have hb7 := zext_toNat_eq b7 (w := 64) (by decide); have hb12 := zext_toNat_eq b12 (w := 64) (by decide)
  have s4 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 := by rw [or_shiftLeft_toNat (by omega) (by omega), hb4]
  have s5 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 := by rw [or_shiftLeft_toNat (by omega) (by omega), s4, hb5]
  have s6 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 := by rw [or_shiftLeft_toNat (by omega) (by omega), s5, hb6]
  have s7 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48 ||| BitVec.zeroExtend 64 b7 <<< 56).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 := by rw [or_shiftLeft_toNat (by omega) (by omega), s6, hb7]
  have s12 : (BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11) ||| BitVec.zeroExtend 64 b12 <<< 32).toNat = (BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11)).toNat + b12.toNat * 2 ^ 32 := by rw [or_shiftLeft_toNat (by omega) (by omega), hb12]
  have ha0' : a0.toNat = ((BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48) % 2 ^ 52 := by rw [ha0, unpack13Lo, mask52_toNat, s6]
  have ha1' : a1.toNat = (((BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11)).toNat + b12.toNat * 2 ^ 32) * 2 ^ 64 + ((BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56)) / 2 ^ 52 := by
    rw [ha1, unpack13Hi, setWidth64_extr128_toNat _ _ 52 (by omega), s12, s7]
  omega
private theorem leBytesToNat_take_succ (bs : List (BitVec 8)) :
    ∀ k, k < bs.length → leBytesToNat (bs.take (k + 1)) = leBytesToNat (bs.take k) + (bs.getD k 0#8).toNat * 256 ^ k
  | 0, hk => by cases bs <;> simp_all [leBytesToNat]
  | k + 1, hk => by
    rcases bs with _ | ⟨b, bs⟩; · simp at hk
    · have ih := leBytesToNat_take_succ bs k (by simpa using hk)
      simp only [List.take_succ_cons, leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
      rw [ih, Nat.pow_succ, ← Nat.mul_assoc]; omega
set_option exponentiation.threshold 512 in
private theorem leBytesToNat_take_add13 (bs : List (BitVec 8)) (k : Nat) (hk : k + 13 ≤ bs.length) (a0 a1 : BitVec 64)
    (ha0 : a0 = unpack13Lo (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8))
    (ha1 : a1 = unpack13Hi (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8)
      (bs.getD (k + 7) 0#8) (bs.getD (k + 8) 0#8) (bs.getD (k + 9) 0#8) (bs.getD (k + 10) 0#8) (bs.getD (k + 11) 0#8) (bs.getD (k + 12) 0#8)) :
    a0.toNat < 2 ^ 52 ∧ a1.toNat < 2 ^ 52 ∧ leBytesToNat (bs.take (k + 13)) = leBytesToNat (bs.take k) + (a0.toNat + a1.toNat * 2 ^ 52) * 256 ^ k := by
  have hp := unpack_pair13 (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8)
    (bs.getD (k + 7) 0#8) (bs.getD (k + 8) 0#8) (bs.getD (k + 9) 0#8) (bs.getD (k + 10) 0#8) (bs.getD (k + 11) 0#8) (bs.getD (k + 12) 0#8) a0 a1 ha0 ha1
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [show k + 13 = (k + 12) + 1 by rfl, leBytesToNat_take_succ bs (k + 12) (by omega), show k + 12 = (k + 11) + 1 by rfl, leBytesToNat_take_succ bs (k + 11) (by omega),
      show k + 11 = (k + 10) + 1 by rfl, leBytesToNat_take_succ bs (k + 10) (by omega), show k + 10 = (k + 9) + 1 by rfl, leBytesToNat_take_succ bs (k + 9) (by omega),
      show k + 9 = (k + 8) + 1 by rfl, leBytesToNat_take_succ bs (k + 8) (by omega), show k + 8 = (k + 7) + 1 by rfl, leBytesToNat_take_succ bs (k + 7) (by omega),
      show k + 7 = (k + 6) + 1 by rfl, leBytesToNat_take_succ bs (k + 6) (by omega), show k + 6 = (k + 5) + 1 by rfl, leBytesToNat_take_succ bs (k + 5) (by omega),
      show k + 5 = (k + 4) + 1 by rfl, leBytesToNat_take_succ bs (k + 4) (by omega), show k + 4 = (k + 3) + 1 by rfl, leBytesToNat_take_succ bs (k + 3) (by omega),
      show k + 3 = (k + 2) + 1 by rfl, leBytesToNat_take_succ bs (k + 2) (by omega), show k + 2 = (k + 1) + 1 by rfl, leBytesToNat_take_succ bs (k + 1) (by omega),
      leBytesToNat_take_succ bs k (by omega), hp.2.2]
  simp only [Nat.pow_add]; grind
set_option exponentiation.threshold 512 in
private theorem leBytesToNat_take_add12 (bs : List (BitVec 8)) (k : Nat) (hk : k + 12 ≤ bs.length) (a0 a1 : BitVec 64)
    (ha0 : a0 = unpack13Lo (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8))
    (ha1 : a1 = unpack13Hi (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8)
      (bs.getD (k + 7) 0#8) (bs.getD (k + 8) 0#8) (bs.getD (k + 9) 0#8) (bs.getD (k + 10) 0#8) (bs.getD (k + 11) 0#8) 0#8) :
    a0.toNat < 2 ^ 52 ∧ a1.toNat < 2 ^ 52 ∧ leBytesToNat (bs.take (k + 12)) = leBytesToNat (bs.take k) + (a0.toNat + a1.toNat * 2 ^ 52) * 256 ^ k := by
  have hp := unpack_pair13 (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8) (bs.getD (k + 3) 0#8) (bs.getD (k + 4) 0#8) (bs.getD (k + 5) 0#8) (bs.getD (k + 6) 0#8)
    (bs.getD (k + 7) 0#8) (bs.getD (k + 8) 0#8) (bs.getD (k + 9) 0#8) (bs.getD (k + 10) 0#8) (bs.getD (k + 11) 0#8) 0#8 a0 a1 ha0 ha1
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [show k + 12 = (k + 11) + 1 by rfl, leBytesToNat_take_succ bs (k + 11) (by omega), show k + 11 = (k + 10) + 1 by rfl, leBytesToNat_take_succ bs (k + 10) (by omega),
      show k + 10 = (k + 9) + 1 by rfl, leBytesToNat_take_succ bs (k + 9) (by omega), show k + 9 = (k + 8) + 1 by rfl, leBytesToNat_take_succ bs (k + 8) (by omega),
      show k + 8 = (k + 7) + 1 by rfl, leBytesToNat_take_succ bs (k + 7) (by omega), show k + 7 = (k + 6) + 1 by rfl, leBytesToNat_take_succ bs (k + 6) (by omega),
      show k + 6 = (k + 5) + 1 by rfl, leBytesToNat_take_succ bs (k + 5) (by omega), show k + 5 = (k + 4) + 1 by rfl, leBytesToNat_take_succ bs (k + 4) (by omega),
      show k + 4 = (k + 3) + 1 by rfl, leBytesToNat_take_succ bs (k + 3) (by omega), show k + 3 = (k + 2) + 1 by rfl, leBytesToNat_take_succ bs (k + 2) (by omega),
      show k + 2 = (k + 1) + 1 by rfl, leBytesToNat_take_succ bs (k + 1) (by omega), leBytesToNat_take_succ bs k (by omega), hp.2.2]
  simp only [Nat.pow_add, BitVec.toNat_ofNat]; grind
private theorem wide_limb1_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8) :
    BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11) ||| BitVec.zeroExtend 64 b12 <<< 32) ++
      (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48 ||| BitVec.zeroExtend 64 b7 <<< 56)) >>> 52) &&& 4503599627370495#64 =
    unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 := by unfold unpack13Hi pack32; bv_slice
private theorem wide_limb2_eq (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 b3 b4 b5 b6) ++ (BitVec.zeroExtend 64 b0 <<< 40 ||| BitVec.zeroExtend 64 b1 <<< 48 ||| BitVec.zeroExtend 64 b2 <<< 56)) >>> 40) &&& 4503599627370495#64 =
    unpack13Lo b0 b1 b2 b3 b4 b5 b6 := by unfold unpack13Lo pack32; bv_slice
private theorem wide_limb3_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8) :
    BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack16 b11 b12) ++ (BitVec.zeroExtend 64 b8 <<< 40 ||| BitVec.zeroExtend 64 b7 <<< 32 ||| BitVec.zeroExtend 64 b9 <<< 48 ||| BitVec.zeroExtend 64 b10 <<< 56 ||| BitVec.zeroExtend 64 (pack32 b3 b4 b5 b6))) >>> 28) =
    unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 := by unfold unpack13Hi pack32 pack16; bv_slice
private theorem wide_limb4_eq (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    BitVec.setWidth 64 ((BitVec.zeroExtend 64 b6 ++ (BitVec.zeroExtend 64 b0 <<< 16 ||| BitVec.zeroExtend 64 b1 <<< 24 ||| BitVec.zeroExtend 64 b2 <<< 32 ||| BitVec.zeroExtend 64 b3 <<< 40 ||| BitVec.zeroExtend 64 b4 <<< 48 ||| BitVec.zeroExtend 64 b5 <<< 56)) >>> 16) &&& 4503599627370495#64 =
    unpack13Lo b0 b1 b2 b3 b4 b5 b6 := by unfold unpack13Lo pack32; bv_slice
private theorem wide_limb5_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8) :
    (BitVec.zeroExtend 64 b12 <<< 48 ||| BitVec.zeroExtend 64 b11 <<< 40 ||| BitVec.zeroExtend 64 b6 ||| (BitVec.zeroExtend 64 b8 <<< 16 ||| BitVec.zeroExtend 64 b7 <<< 8 ||| BitVec.zeroExtend 64 b9 <<< 24 ||| BitVec.zeroExtend 64 b10 <<< 32)) >>> 4 =
    unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 := by unfold unpack13Hi pack32; bv_slice
private theorem wide_limb6_eq (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    BitVec.setWidth 64 ((((BitVec.zeroExtend 64 (pack32 b1 b2 b3 b4) ||| BitVec.zeroExtend 64 b5 <<< 32) &&& 18446463698244468735#64 ||| BitVec.zeroExtend 64 b6 <<< 40) ++ BitVec.zeroExtend 64 b0 <<< 56) >>> 56) &&& 4503599627370495#64 =
    unpack13Lo b0 b1 b2 b3 b4 b5 b6 := by unfold unpack13Lo pack32; bv_slice
private theorem wide_limb7_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8) :
    BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 b9 b10 b11 b12) ++ (BitVec.zeroExtend 64 b8 <<< 56 ||| BitVec.zeroExtend 64 b7 <<< 48 ||| BitVec.zeroExtend 64 b6 <<< 40)) >>> 44) =
    unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 := by unfold unpack13Hi pack32; bv_slice
private theorem wide_limb8_eq (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    BitVec.setWidth 64 ((BitVec.setWidth 64 (BitVec.zeroExtend 32 (pack16 b4 b5) ||| BitVec.setWidth 32 (BitVec.zeroExtend 64 b6 <<< 16)) ++
      (BitVec.zeroExtend 64 b0 <<< 32 ||| BitVec.zeroExtend 64 b1 <<< 40 ||| BitVec.zeroExtend 64 b2 <<< 48 ||| BitVec.zeroExtend 64 b3 <<< 56)) >>> 32) &&& 4503599627370495#64 =
    unpack13Lo b0 b1 b2 b3 b4 b5 b6 := by unfold unpack13Lo pack32 pack16; bv_slice
private theorem wide_limb9_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : BitVec 8) :
    ((BitVec.zeroExtend 64 b8 <<< 32 ||| BitVec.zeroExtend 64 b7 <<< 24 ||| BitVec.zeroExtend 64 b9 <<< 40 ||| BitVec.zeroExtend 64 b10 <<< 48 ||| BitVec.zeroExtend 64 b11 <<< 56) &&& 18446744073692839935#64 ||| (BitVec.zeroExtend 64 b6 &&& 255#64) <<< 16) >>> 20 =
    unpack13Hi b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 0#8 := by unfold unpack13Hi pack32; bv_slice
set_option maxHeartbeats 800000 in set_option exponentiation.threshold 512 in
attribute [local simp] sc52Pack5_length in
attribute [local wp_norm] State.sp_setMem State.sp_setPC State.sp_writeReg64_gpr State.sp_writeVReg128 in
theorem scalar_from_bytes_mod_order_wide_ok : ScalarFromBytesModOrderWideOk := by
  intro _
  apply dalekCaller_ok dalekCliPC02 dalekCliPl02
  intro b hb hbase
  wp_init
  wp_simp_pre only [stackFrame_split_top s0 448 256 192, reduceStackFrameAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_sym_steps; wp_checkpoint
  wp_simp_pre only [sc52Pack5_stack_rest s0.sp 192 184 176 168 160, sc52Pack5_stack_rest s0.sp 144 136 128 120 112,
    sc52Pack5_stack_rest s0.sp 104 96 88 80 72, show s0.sp - 448#64 = s0.sp - 192#64 - 256#64 by bv_omega]
  have h_unpack : sc52LimbsBounded (sc52Pack5 v_cp_19 v_cp_20 v_cp_21 v_cp_22 v_cp_23) (2 ^ 52) ∧
      sc52LimbsBounded (sc52Pack5 v_cp_24 v_cp_25 v_cp_16 v_cp_26 v_cp_18) (2 ^ 52) ∧
      sc52ValOfBytes (sc52Pack5 v_cp_19 v_cp_20 v_cp_21 v_cp_22 v_cp_23) < 2 ^ 260 ∧
      sc52ValOfBytes (sc52Pack5 v_cp_24 v_cp_25 v_cp_16 v_cp_26 v_cp_18) < 2 ^ 260 ∧
      sc52ValOfBytes (sc52Pack5 v_cp_19 v_cp_20 v_cp_21 v_cp_22 v_cp_23) + sc52ValOfBytes (sc52Pack5 v_cp_24 v_cp_25 v_cp_16 v_cp_26 v_cp_18) * 2 ^ 260 = leBytesToNat a_rest := by
    have hp0 := leBytesToNat_take_add13 a_rest 0 (by omega) v_cp_19 v_cp_20 (by rw [hv_cp_19]; rfl) (by rw [hv_cp_20, wide_limb1_eq])
    have hp1 := leBytesToNat_take_add13 a_rest 13 (by omega) v_cp_21 v_cp_22 (by rw [hv_cp_21, wide_limb2_eq]) (by rw [hv_cp_22, wide_limb3_eq])
    have hp2 := leBytesToNat_take_add13 a_rest 26 (by omega) v_cp_23 v_cp_24 (by rw [hv_cp_23, wide_limb4_eq]) (by rw [hv_cp_24, wide_limb5_eq])
    have hp3 := leBytesToNat_take_add13 a_rest 39 (by omega) v_cp_25 v_cp_16 (by rw [hv_cp_25, wide_limb6_eq]) (by rw [hv_cp_16, wide_limb7_eq])
    have hp4 := leBytesToNat_take_add12 a_rest 52 (by omega) v_cp_26 v_cp_18 (by rw [hv_cp_26, wide_limb8_eq]) (by rw [hv_cp_18, wide_limb9_eq])
    simp only [Nat.reduceAdd] at hp0 hp1 hp2 hp3 hp4
    have ht0 : leBytesToNat (a_rest.take 0) = 0 := rfl; have ht64 : a_rest.take 64 = a_rest := List.take_of_length_le (by omega)
    rw [ht0] at hp0; rw [ht64] at hp4
    rw [sc52LimbsBounded_sc52Pack5, sc52LimbsBounded_sc52Pack5, sc52ValOfBytes_sc52Pack5, sc52ValOfBytes_sc52Pack5]; unfold sc52Val
    exact ⟨⟨hp0.1, hp0.2.1, hp1.1, hp1.2.1, hp2.1⟩, ⟨hp2.2.1, hp3.1, hp3.2.1, hp4.1, hp4.2.1⟩, by omega, by omega, by omega⟩
  clear hv_cp_0 hv_cp_1 hv_cp_2 hv_cp_3 hv_cp_4 hv_cp_5 hv_cp_6 hv_cp_7 hv_cp_8 hv_cp_9 hv_cp_10 hv_cp_11 hv_cp_12 hv_cp_13 hv_cp_14 hv_cp_15 hv_cp_16 hv_cp_17 hv_cp_18 hv_cp_19 hv_cp_20 hv_cp_21 hv_cp_22 hv_cp_23 hv_cp_24 hv_cp_25 hv_cp_26
  rcases h_unpack with ⟨⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, hlo_lt, hhi_lt, h_wide_val⟩
  rcases sc52RRBytes_limbsBounded with ⟨_, _, _, _, _, _⟩; rcases sc52LBytes_limbsBounded with ⟨_, _, _, _, _, _⟩
  have hmul1_bound : sc52ValOfBytes (sc52Pack5 v_cp_19 v_cp_20 v_cp_21 v_cp_22 v_cp_23) * sc52ValOfBytes sc52RRBytes < 2 ^ 260 * edOrderL := sc52_mul_bound_of_right_lt_l hlo_lt sc52RRBytes_val_lt
  have hmul2_bound : sc52ValOfBytes (sc52Pack5 v_cp_24 v_cp_25 v_cp_16 v_cp_26 v_cp_18) * sc52ValOfBytes sc52LBytes < 2 ^ 260 * edOrderL := sc52_mul_bound_of_right_lt_l hhi_lt sc52LBytes_val_lt
  simp only [edOrderL, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul] at hmul1_bound hmul2_bound
  wp_steps 1; wp_dalek_call sc52_montgomery_mul_ro_right_ok; rcases (by assumption : sc52LimbsBounded w (2 ^ 52)) with ⟨hw_len, hw0, hw1, hw2, hw3, hw4⟩
  wp_conv_pre => rw [pointsToBytes40_eq_cells (s0.sp - 104#64) w hw_len, ← sc52Pack5_stack_rest s0.sp 192 184 176 168 160]; simp only [sepConj_assoc]
  wp_cut_codeLoaded; wp_sym_steps
  wp_simp_pre only [sepConj_assoc, pointsToBytes40_cells_eq_rest (s0.sp - 104#64) w hw_len,
    show stackFrame sf 256 = memRegion (s0.sp - 192#64 - 256#64) 256 by change memRegion (sf.sp - 256#64) 256 = _; rw [hsp_sf]]
  wp_steps 1; wp_dalek_call sc52_montgomery_mul_ro_right_ok; rcases (by assumption : sc52LimbsBounded w_1 (2 ^ 52)) with ⟨hw1_len, hw1_0, hw1_1, hw1_2, hw1_3, hw1_4⟩
  wp_conv_pre =>
    rw [pointsToBytes40_eq_cells (s0.sp - 104#64) w_1 hw1_len,
        ← sc52Pack5_stack_rest s0.sp 144 136 128 120 112]
    simp only [sepConj_assoc]
  wp_cut_codeLoaded; wp_sym_steps
  wp_simp_pre only [sepConj_assoc,
    sc52Pack5_stack_rest s0.sp 192 184 176 168 160,
    sc52Pack5_stack_rest s0.sp 144 136 128 120 112,
    pointsToBytes40_cells_eq_rest (s0.sp - 104#64) w_1 hw1_len]
  wp_checkpoint
  have h_res :
      let m := -BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_11)
      let add0 := (m &&& 671914833335277#64) + v_cp_2; let add1 := (m &&& 3916664325105025#64) + v_cp_4 + add0 >>> 52
      let add2 := (m &&& 1367801#64) + v_cp_7 + add1 >>> 52; let add3 := v_cp_9 + add2 >>> 52
      let add4 := v_cp_10 + (m &&& 17592186044416#64) + add3 >>> 52
      sc52PackBytes32 add0 add1 add2 add3 add4 = natToLeBytes 32 (leBytesToNat a_rest % edOrderL) := by
    obtain ⟨hn0, hn1, hn2, hn3, hn_val_eq, hn_lt⟩ := sc52_add_limbs_wide w w_1 hw0 hw1 hw2 hw3 hw1_0 hw1_1 hw1_2 hw1_3 (by assumption) (by assumption)
    have h_pack := sc52PackBytes32_cond_sub_l_add _ _ _ _ _ v_cp_2 _ v_cp_4 _ v_cp_7 _ v_cp_9 v_cp_10 v_cp_11
      hn0 hn1 hn2 hn3 hn_lt hv_cp_2 rfl hv_cp_4 rfl hv_cp_7 rfl hv_cp_9 hv_cp_10 (by rw [hv_cp_11, ← hv_cp_10])
    dsimp only at h_pack ⊢
    rw [BitVec.add_comm (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_11) &&& 1367801#64) v_cp_7, h_pack, hn_val_eq, cancel_mont_wide hpost hpost_1 h_wide_val]
  have hmr4 : stackFrame sf_1 256 = memRegion (s0.sp - 448#64) 240 ∗ memRegion (s0.sp - 192#64 - 16#64) 16 := by
    change memRegion (sf_1.sp - 256#64) 256 = _
    rw [hsp_sf_1, hsp_sf, show s0.sp - 192#64 - 256#64 = s0.sp - 448#64 by bv_omega, memRegion_split_le (s0.sp - 448#64) 240 256 (by decide) (by decide),
        show s0.sp - 448#64 + BitVec.ofNat 64 240 = s0.sp - 192#64 - 16#64 by bv_omega]
  wp_simp_pre only [hmr4, sepConj_assoc]; clear hmr4
  clear hv_cp_0 hv_cp_1 hv_cp_2 hv_cp_3 hv_cp_4 hv_cp_5 hv_cp_6 hv_cp_7 hv_cp_8 hv_cp_9 hv_cp_10 hv_cp_11
  wp_steps 1; wp_dalek_call black_box_u8_ok; have hsp2 : sf_2.sp = s0.sp - 192#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
  wp_sym_steps 100; wp_simp_pre only [write8_32_add a_2 h_4, h_res]; wp_fold_stack
  apply SepWP.weaken_pre
  · show _ ⊢ a ↦ₛ a_rest ∗ sc52_l dalekCliMpl ↦ᵣ sc52LBytes ∗ sc52_rr dalekCliMpl ↦ᵣ sc52RRBytes ∗ stackFrame s0 448 ∗ a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_rest % edOrderL)
    rw [show (stackFrame sf_2 16 ∗ (s0.sp - 144#64) ↦ₛ _ ∗ sc52_l dalekCliMpl ↦ᵣ sc52LBytes ∗ memRegion (s0.sp - 448#64) 240 ∗ (s0.sp - 104#64) ↦ₛ w_1 ∗ (s0.sp - 192#64) ↦ₛ _ ∗
          sc52_rr dalekCliMpl ↦ᵣ sc52RRBytes ∗ a ↦ₛ a_rest ∗ a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_rest % edOrderL) ∗ (s0.sp - 152#64) ↦₆₄ _ ∗ memRegion (s0.sp - 64#64) 64) =
        a ↦ₛ a_rest ∗ (sc52_l dalekCliMpl ↦ᵣ sc52LBytes ∗ (sc52_rr dalekCliMpl ↦ᵣ sc52RRBytes ∗
          ((memRegion (s0.sp - 448#64) 240 ∗ (stackFrame sf_2 16 ∗ ((s0.sp - 192#64) ↦ₛ _ ∗ ((s0.sp - 152#64) ↦₆₄ _ ∗ ((s0.sp - 144#64) ↦ₛ _ ∗ ((s0.sp - 104#64) ↦ₛ w_1 ∗ memRegion (s0.sp - 64#64) 64)))))) ∗
            a_1 ↦ₛ natToLeBytes 32 (leBytesToNat a_rest % edOrderL)))) by sep_ac_rfl]
    refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono ?_ (Entails.refl _))))
    exact stackFrame448_wide_fold s0 sf_2 hsp2 _ _ w_1 (by simp) (by simp) hw1_len _
  wp_done
private theorem pointsToBytes_sub1_cons2 (p : BitVec 64) (b0 b1 : BitVec 8) (bs : List (BitVec 8)) :
    ((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) = (((p - 1#64) ↦₈ b0) ∗ ((p ↦₈ b1) ∗ ((p + 1#64) ↦ₛ bs))) := by
  rw [pointsToBytes_cons, show p - 1#64 + 1#64 = p by bv_omega, pointsToBytes_cons]
private def radix16SxtbAsr4 (d : BitVec 64) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32) >>> 0 &&& 255#64 |||
    (if (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32)).getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64)).sshiftRight 4
private def radix16DigitHw (d : BitVec 64) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.setWidth 32 d - BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32) &&& 1030792151280#64))
private theorem radix16SxtbAsr4_eq : ∀ dNat ≤ 16, radix16SxtbAsr4 (BitVec.ofNat 64 dNat) = BitVec.ofNat 32 ((dNat + 8) / 16) := by decide
private theorem radix16DigitHw_eq : ∀ dNat ≤ 16, radix16DigitHw (BitVec.ofNat 64 dNat) = BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) := by decide
private theorem radix16NextReg_eq (b1 : BitVec 8) : ∀ c ≤ 1, b1.toNat < 16 → BitVec.setWidth 64 (BitVec.zeroExtend 32 b1 + BitVec.ofNat 32 c) = BitVec.ofNat 64 (b1.toNat + c) := by
  intro c hc hb1; apply BitVec.eq_of_toNat_eq; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp [BitVec.toNat_setWidth, BitVec.toNat_add] <;> omega
private theorem radix16NextByte_eq (b1 : BitVec 8) : ∀ c ≤ 1, b1.toNat < 16 → b1 + BitVec.truncate 8 (BitVec.ofNat 32 c) = BitVec.ofNat 8 (b1.toNat + c) := by
  intro c hc hb1; apply BitVec.eq_of_toNat_eq; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp [BitVec.toNat_add] <;> omega
private theorem radix16_iter [DalekCliPlacement] (b : BitVec 64) (_hb : DalekBase dalekCliPl15 b) (_hbase : dalekCliPl15.base = b) (target_pc : BitVec 64) (s : State) (R : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp) (p cnt : BitVec 64) (dNat : Nat) (b0 b1 : BitVec 8) (bs : List (BitVec 8))
    (hd : dNat ≤ 16) (hb1 : b1.toNat < 16) (hpc : s.pc = b + 648#64) (hrun : s.status = ExecStatus.Running)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = p) (hx8 : s.readReg64 (Reg.gpr 8#5) = cnt) (hx9 : s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 dNat)
    (hnext : ∀ s' : State, s'.pc = (if (cnt != 1#64) = true then b + 648#64 else b + 688#64) → s'.status = ExecStatus.Running →
      s'.sp = s.sp → s'.readReg64 Reg.lr = s.readReg64 Reg.lr → CalleeSavedPreserved s s' → s'.readReg64 (Reg.gpr 0#5) = p + 1#64 →
      s'.readReg64 (Reg.gpr 8#5) = cnt - 1#64 → s'.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (b1.toNat + (dNat + 8) / 16) →
      SepWP (dalekCliPC15.rebase b (fun _ => none)) target_pc s'
        ((((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ ((p ↦₈ BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16)) ∗ ((p + 1#64) ↦ₛ bs))) ∗ R) post oom) :
    SepWP (dalekCliPC15.rebase b (fun _ => none)) target_pc s (((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) ∗ R) post oom := by
  rw [pointsToBytes_sub1_cons2]; wp_sym_steps 10
  change SepWP (dalekCliPC15.rebase b (fun _ => none)) target_pc _
    ((((p - 1#64) ↦₈ radix16DigitHw (BitVec.ofNat 64 dNat)) ∗ ((p ↦₈ (b1 + BitVec.truncate 8 (radix16SxtbAsr4 (BitVec.ofNat 64 dNat)))) ∗ ((p + 1#64) ↦ₛ bs))) ∗ R) post oom
  have hc : (dNat + 8) / 16 ≤ 1 := by omega
  rw [radix16DigitHw_eq dNat hd, radix16SxtbAsr4_eq dNat hd, radix16NextByte_eq b1 _ hc hb1]
  refine hnext _ rfl hrun rfl rfl ⟨by simp, by simp⟩ rfl rfl ?_
  change BitVec.setWidth 64 (BitVec.zeroExtend 32 b1 + radix16SxtbAsr4 (BitVec.ofNat 64 dNat)) = _; rw [radix16SxtbAsr4_eq dNat hd, radix16NextReg_eq b1 _ hc hb1]
private def recenterNibbles (d : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => [BitVec.ofNat 8 d]
  | b :: bs => BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) :: recenterNibbles (b.toNat + (d + 8) / 16) bs
private def allNibbles : List (BitVec 8) → Prop | [] => True | x :: xs => x.toNat < 16 ∧ allNibbles xs
private theorem calleeSavedPreserved_trans {s1 s2 s3 : State} (h1 : CalleeSavedPreserved s1 s2) (h2 : CalleeSavedPreserved s2 s3) : CalleeSavedPreserved s1 s3 := by simp_all [CalleeSavedPreserved]
private theorem radix16_cnt_step : ∀ n < 63, (BitVec.ofNat 64 (n + 2) != 1#64) = true ∧ BitVec.ofNat 64 (n + 2) - 1#64 = BitVec.ofNat 64 (n + 1) := by decide
private theorem pointsToBytes_add1_sub1_cons (p : BitVec 64) (b0 : BitVec 8) (bs : List (BitVec 8)) :
    ((p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs)) = ((p + 1#64 - 1#64) ↦ₛ (b0 :: bs)) := by rw [show p + 1#64 - 1#64 = p by bv_omega, pointsToBytes_cons]
private theorem radix16_loop [DalekCliPlacement] (b : BitVec 64) (hb : DalekBase dalekCliPl15 b) (hbase : dalekCliPl15.base = b)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) (oom : State → SepProp) (bs : List (BitVec 8)) :
    ∀ (s : State) (R : SepProp) (p : BitVec 64) (dNat : Nat) (b0 b1 : BitVec 8),
      dNat ≤ 16 → b1.toNat < 16 → allNibbles bs → bs.length < 63 → s.pc = b + 648#64 → s.status = ExecStatus.Running →
      s.readReg64 (Reg.gpr 0#5) = p → s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (bs.length + 1) → s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 dNat →
      (∀ sf : State, sf.pc = b + 688#64 → sf.status = ExecStatus.Running → sf.sp = s.sp → sf.readReg64 Reg.lr = s.readReg64 Reg.lr →
        CalleeSavedPreserved s sf → SepWP (dalekCliPC15.rebase b (fun _ => none)) target_pc sf (((p - 1#64) ↦ₛ recenterNibbles dNat (b1 :: bs)) ∗ R) post oom) →
      SepWP (dalekCliPC15.rebase b (fun _ => none)) target_pc s (((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) ∗ R) post oom := by
  induction bs with
  | nil =>
    intro s R p dNat b0 b1 hd hb1 _ _ hpc hrun hx0 hx8 hx9 hnext
    refine radix16_iter b hb hbase target_pc s R post oom p 1#64 dNat b0 b1 [] hd hb1 hpc hrun hx0 hx8 hx9 ?_
    intro s' hpc' hrun' hsp' hlr' hcs' _ _ _; rw [← pointsToBytes_sub1_cons2]; exact hnext s' hpc' hrun' hsp' hlr' hcs'
  | cons b2 bs' ih =>
    intro s R p dNat b0 b1 hd hb1 hbs hlen hpc hrun hx0 hx8 hx9 hnext; rcases hbs with ⟨hb2, hbs'⟩
    have hlen' : bs'.length < 63 := by simp at hlen; omega
    have ⟨hcnt_ne, hcnt_sub⟩ := radix16_cnt_step bs'.length hlen'
    refine radix16_iter b hb hbase target_pc s R post oom p (BitVec.ofNat 64 (bs'.length + 2)) dNat b0 b1 (b2 :: bs') hd hb1 hpc hrun hx0 hx8 hx9 ?_
    intro s' hpc' hrun' hsp' hlr' hcs' hx0' hx8' hx9'; rw [hcnt_ne] at hpc'; rw [hcnt_sub] at hx8'
    rw [pointsToBytes_add1_sub1_cons, show (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗
          ((p + 1#64 - 1#64) ↦ₛ (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16) :: b2 :: bs'))) ∗ R =
        ((p + 1#64 - 1#64) ↦ₛ (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16) :: b2 :: bs')) ∗
          (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R) by sep_ac_rfl]
    refine ih s' (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R)
      (p + 1#64) (b1.toNat + (dNat + 8) / 16) (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16)) b2 (by omega) hb2 hbs' hlen' hpc' hrun' hx0' hx8' hx9' ?_
    intro sf hpcf hrunf hspf hlrf hcsf
    rw [show ((p + 1#64 - 1#64) ↦ₛ recenterNibbles (b1.toNat + (dNat + 8) / 16) (b2 :: bs')) ∗ (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R) =
        (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ ((p + 1#64 - 1#64) ↦ₛ recenterNibbles (b1.toNat + (dNat + 8) / 16) (b2 :: bs'))) ∗ R by sep_ac_rfl,
        show p + 1#64 - 1#64 = p - 1#64 + 1#64 by bv_omega, ← pointsToBytes_cons]
    exact hnext sf hpcf hrunf (hspf.trans hsp') (hlrf.trans hlr') (calleeSavedPreserved_trans hcs' hcsf)
private def nibbleAt (a_bs : List (BitVec 8)) (i : Nat) : BitVec 8 := if i % 2 == 0 then a_bs.getD (i / 2) 0#8 &&& 15#8 else a_bs.getD (i / 2) 0#8 >>> 4
private def nibblesFrom (a_bs : List (BitVec 8)) : Nat → List (BitVec 8) | 0 => [] | k + 1 => nibbleAt a_bs (63 - k) :: nibblesFrom a_bs k
private theorem nibbleAt_toNat_lt (a_bs : List (BitVec 8)) (i : Nat) : (nibbleAt a_bs i).toNat < 16 := by
  have h := (by decide : ∀ b : BitVec 8, (b &&& 15#8).toNat < 16 ∧ (b >>> 4).toNat < 16) (a_bs.getD (i / 2) 0#8); unfold nibbleAt; split <;> simp only [h.1, h.2]
private theorem nibblesFrom_allNibbles (a_bs : List (BitVec 8)) : ∀ k, allNibbles (nibblesFrom a_bs k)
  | 0 => trivial | k + 1 => ⟨nibbleAt_toNat_lt a_bs (63 - k), nibblesFrom_allNibbles a_bs k⟩
private theorem nibblesFrom_length (a_bs : List (BitVec 8)) : ∀ k, (nibblesFrom a_bs k).length = k
  | 0 => rfl | k + 1 => by simp [nibblesFrom, nibblesFrom_length a_bs k]
private theorem nibbleAt_toNat_int_eq (a_bs : List (BitVec 8)) (i : Nat) :
    (if i % 2 == 0 then Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat &&& 0x0f) else Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat >>> 4)) = Int.ofNat (nibbleAt a_bs i).toNat := by
  unfold nibbleAt; split <;> simp [BitVec.toNat_and, BitVec.toNat_ushiftRight]
private theorem scalarRadix16Digits_go_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    ∀ (k : Nat) (_hk : k ≤ 63) (carry : Nat) (acc : List (BitVec 8)),
      scalarRadix16Digits.go a_bs (k + 1) (Int.ofNat carry) acc = acc.reverse ++ recenterNibbles ((nibbleAt a_bs (63 - k)).toNat + carry) (nibblesFrom a_bs k) := by
  intro k; induction k with
  | zero =>
    intro _ carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    change scalarRadix16Digits.go a_bs 0 0 (BitVec.ofNat 8 ((nibbleAt a_bs 63).toNat + carry) :: acc) = _
    rw [scalarRadix16Digits.go]; simp [nibblesFrom, recenterNibbles]
  | succ m ih =>
    intro hk carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    have hm : 63 - (m + 1) < 63 := by omega
    let dNat := (nibbleAt a_bs (63 - (m + 1))).toNat + carry
    change (if 63 - (m + 1) < 63 then scalarRadix16Digits.go a_bs (m + 1) (Int.ofNat ((dNat + 8) / 16)) (BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) :: acc)
      else scalarRadix16Digits.go a_bs (m + 1) 0 (BitVec.ofInt 8 (Int.ofNat dNat) :: acc)) = _
    simp only [hm, ↓reduceIte]; rw [ih (by omega) ((dNat + 8) / 16)]; simp [nibblesFrom, recenterNibbles, dNat]
private theorem scalarRadix16Digits_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    scalarRadix16Digits a_bs = recenterNibbles (nibbleAt a_bs 0).toNat (nibblesFrom a_bs 63) := by
  unfold scalarRadix16Digits; simpa using scalarRadix16Digits_go_eq_recenterNibbles a_bs 63 (by omega) 0 []
private theorem loNibble_hw_eq : ∀ b : BitVec 8, BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 64424509455#64) = b &&& 15#8 := by decide
private theorem zeroExtend64_eq_ofNat_toNat : ∀ b : BitVec 8, BitVec.zeroExtend 64 b = BitVec.ofNat 64 b.toNat := by decide
private theorem write8_zero_eq_cons (bs : List (BitVec 8)) (v : BitVec 8) : ByteSlice.write8 bs 0 v = v :: bs.drop 1 := rfl
private theorem write8_cons_zero (x v : BitVec 8) (xs : List (BitVec 8)) : ByteSlice.write8 (x :: xs) 0 v = v :: xs := rfl
private theorem write8_cons_succ (x v : BitVec 8) (xs : List (BitVec 8)) (k : Nat) : ByteSlice.write8 (x :: xs) (k + 1) v = x :: ByteSlice.write8 xs k v := rfl
private theorem write8_61_radix16_getD0 (bs : List (BitVec 8))
    (x0 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
     x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 : BitVec 8) :
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 2 x2) 4 x4) 3 x3) 5 x5) 6 x6) 7 x7) 8 x8) 9 x9) 10 x10) 11 x11) 12 x12) 13 x13) 14 x14) 15 x15)
      16 x16) 17 x17) 18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25) 26 x26) 27 x27) 28 x28) 29 x29) 30 x30) 31 x31)
      32 x32) 33 x33) 34 x34) 35 x35) 36 x36) 37 x37) 38 x38) 39 x39) 40 x40) 41 x41) 42 x42) 43 x43) 44 x44) 45 x45) 46 x46) 47 x47)
      48 x48) 49 x49) 50 x50) 51 x51) 52 x52) 53 x53) 54 x54) 55 x55) 56 x56) 57 x57) 58 x58) 59 x59) 60 x60) 61 x61).getD 0 0#8 = x0 := by
  simp only [write8_zero_eq_cons, write8_cons_succ, List.getD_cons_zero]
set_option maxRecDepth 20000 in
private theorem write8_64_radix16_order (bs : List (BitVec 8)) (h : bs.length = 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
     x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : BitVec 8) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 2 x2) 4 x4) 3 x3) 5 x5) 6 x6) 7 x7) 8 x8) 9 x9) 10 x10) 11 x11) 12 x12) 13 x13) 14 x14) 15 x15)
      16 x16) 17 x17) 18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25) 26 x26) 27 x27) 28 x28) 29 x29) 30 x30) 31 x31)
      32 x32) 33 x33) 34 x34) 35 x35) 36 x36) 37 x37) 38 x38) 39 x39) 40 x40) 41 x41) 42 x42) 43 x43) 44 x44) 45 x45) 46 x46) 47 x47)
      48 x48) 49 x49) 50 x50) 51 x51) 52 x52) 53 x53) 54 x54) 55 x55) 56 x56) 57 x57) 58 x58) 59 x59) 60 x60) 61 x61) 62 x62) 63 x63) 1 x1 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31,
     x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63] := by
  have h1 : (bs.take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 32).length = 32 := by simp [h]
  rw [← List.take_append_drop 32 bs]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, htake⟩ := exists_bytes32 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, hdrop⟩ := exists_bytes32 h2
  rw [htake, hdrop]; simp only [List.cons_append, List.nil_append, write8_cons_zero, write8_cons_succ]
set_option maxHeartbeats 800000 in
theorem scalar_as_radix_16_ok : ScalarAsRadix16Ok := by
  intro _; apply dalekLeaf_ok dalekCliPC15 dalekCliPl15; intro b hb hbase; wp_init; wp_sym_steps 162
  rw [write8_61_radix16_getD0, write8_64_radix16_order a_2 h_3]; simp only [loNibble_hw_eq]
  change SepWP (dalekCliPC15.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) _ (a ↦ₛ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) _
  rw [show a ↦ₛ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62) =
      ((a_1 + 1#64 - 1#64) ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) ∗ (a ↦ₛ a_rest) by rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega]; sep_ac_rfl]
  refine radix16_loop b hb hbase (s0.readReg64 Reg.lr) _ _ (nibblesFrom a_rest 62) _ (a ↦ₛ a_rest) (a_1 + 1#64) (nibbleAt a_rest 0).toNat (nibbleAt a_rest 0) (nibbleAt a_rest 1)
    (Nat.le_of_lt (nibbleAt_toNat_lt a_rest 0)) (nibbleAt_toNat_lt a_rest 1) (nibblesFrom_allNibbles a_rest 62)
    (by rw [nibblesFrom_length]; omega) rfl hrun rfl (by rw [nibblesFrom_length]; rfl)
    (by change BitVec.zeroExtend 64 (nibbleAt a_rest 0) = _; exact zeroExtend64_eq_ofNat_toNat (nibbleAt a_rest 0)) ?_
  intro sf hpcf hrunf hspf hlrf hcsf
  have hcs0 : CalleeSavedPreserved s0 sf := calleeSavedPreserved_trans (by simp [CalleeSavedPreserved]) hcsf
  have _hlr0 : sf.readReg64 Reg.lr = s0.readReg64 Reg.lr := hlrf; have hsp0 : sf.sp = s0.sp := hspf
  change SepWP (dalekCliPC15.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf (((a_1 + 1#64 - 1#64) ↦ₛ recenterNibbles (nibbleAt a_rest 0).toNat (nibblesFrom a_rest 63)) ∗ (a ↦ₛ a_rest)) _
  rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega, ← scalarRadix16Digits_eq_recenterNibbles]
  wp_sym_steps 1; refine SepWP.done rfl hrunf ⟨fun hmem => ?_, hsp0, hcs0⟩
  rwa [show (a ↦ₛ a_rest ∗ a_1 ↦ₛ scalarRadix16Digits a_rest) ∗ R = (a_1 ↦ₛ scalarRadix16Digits a_rest ∗ a ↦ₛ a_rest) ∗ R by sep_ac_rfl]

set_option maxHeartbeats 800000 in
theorem scalar_as_radix_16_ro_ok : ScalarAsRadix16RoOk := by
  intro _; apply dalekLeaf_ok dalekCliPC15 dalekCliPl15; intro b hb hbase; wp_init; wp_sym_steps 162
  rw [write8_61_radix16_getD0, write8_64_radix16_order a_2 h_3]; simp only [loNibble_hw_eq]
  change SepWP (dalekCliPC15.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) _ (a ↦ᵣ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) _
  rw [show a ↦ᵣ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62) =
      ((a_1 + 1#64 - 1#64) ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) ∗ (a ↦ᵣ a_rest) by rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega]; sep_ac_rfl]
  refine radix16_loop b hb hbase (s0.readReg64 Reg.lr) _ _ (nibblesFrom a_rest 62) _ (a ↦ᵣ a_rest) (a_1 + 1#64) (nibbleAt a_rest 0).toNat (nibbleAt a_rest 0) (nibbleAt a_rest 1)
    (Nat.le_of_lt (nibbleAt_toNat_lt a_rest 0)) (nibbleAt_toNat_lt a_rest 1) (nibblesFrom_allNibbles a_rest 62)
    (by rw [nibblesFrom_length]; omega) rfl hrun rfl (by rw [nibblesFrom_length]; rfl)
    (by change BitVec.zeroExtend 64 (nibbleAt a_rest 0) = _; exact zeroExtend64_eq_ofNat_toNat (nibbleAt a_rest 0)) ?_
  intro sf hpcf hrunf hspf hlrf hcsf
  have hcs0 : CalleeSavedPreserved s0 sf := calleeSavedPreserved_trans (by simp [CalleeSavedPreserved]) hcsf
  have _hlr0 : sf.readReg64 Reg.lr = s0.readReg64 Reg.lr := hlrf; have hsp0 : sf.sp = s0.sp := hspf
  change SepWP (dalekCliPC15.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf (((a_1 + 1#64 - 1#64) ↦ₛ recenterNibbles (nibbleAt a_rest 0).toNat (nibblesFrom a_rest 63)) ∗ (a ↦ᵣ a_rest)) _
  rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega, ← scalarRadix16Digits_eq_recenterNibbles]
  wp_sym_steps 1; refine SepWP.done rfl hrunf ⟨fun hmem => ?_, hsp0, hcs0⟩
  rwa [show (a ↦ᵣ a_rest ∗ a_1 ↦ₛ scalarRadix16Digits a_rest) ∗ R = (a_1 ↦ₛ scalarRadix16Digits a_rest ∗ a ↦ᵣ a_rest) ∗ R by sep_ac_rfl]


end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar
