/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<MontgomeryPoint>::to_edwards` Machine-Code Proof

Machine-code proof in `dalekCliMultiLib` for `<MontgomeryPoint>::to_edwards` (`B08`),
together with read-only `MINUS_ONE` conversion lemmas and the bridge to `montToEdwards`.
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MontToEdwards

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpPow fpInv
  EdPoint edExtOfAffine leBytesToNat natToLeBytes recoverXEven decodeEdDalek)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51_minus_one fe51_edwards_d fe51_sqrt_m1
  fe51MinusOneBytes fe51EdwardsDBytes fe51SqrtM1Bytes
  fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51MulRoRightOk Fe51Pow2kOk
  Fe51ToBytesOk Fe51ToBytesRoOk Fe51Pow22501Ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards fe51Point4Bounded edExtOfBytes
  montgomeryPointToEdwardsSpec
  CompressedEdwardsYDecompressOk MontgomeryPointToEdwardsOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_natToLeBytes_of_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (
  slice32_ct_eq_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe write64_length_eq readLE_write64_self' readLE_write64_ne
  fe51Reduce_bounded fe51Reduce_val_mod fe51Sub_val_mod
  pointsToBytesRO40_eq_cells sepWP_norm_stackFrame
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_shrink sepWP_callee_grow sepWP_abstract_bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  packCanonical51Bytes pointsToBytes_packCanonical51Bytes
  pointsToBytes32_eq_cells8 bv64_and_mask51_toNat
  fe51_to_bytes_math fe51_to_bytes_of_bytes fe51LimbsBounded_of_52
  compress_recip_eq_fpInv setByte31Or
  pointsToBytes_setByte31Or_packCanonical51Bytes compress_byte31_eq
  write64_copy5_eq pointsToBytes40_sub_eq_cells
  sepWP_split_bytes_append pointsToBytes168_split)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 08 dalekCliMultiLib DalekCliPlacement 267 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl08_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl08.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 12 dalekCliMultiLib DalekCliPlacement 94 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl12_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl12.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

/-! ## 1. Read-Only `FieldElement51::to_bytes` & `MINUS_ONE` Facts -/

set_option maxHeartbeats 400000 in
private theorem fe51_to_bytes_ro_ok : Fe51ToBytesRoOk := by
  intro _
  apply dalekLeaf_ok dalekCliPC12 dalekCliPl12
  intro b hb hbase
  wp_init
  obtain ⟨h_len_a, hl0, hl1, hl2, hl3, hl4⟩ := ‹fe51LimbsBounded a_rest _›
  have hout32 : a_2.length = 32 := ‹_›
  wp_conv_pre =>
    rw [pointsToBytesRO40_eq_cells a a_rest h_len_a,
        pointsToBytes32_eq_cells8 a_1 a_2 hout32]
  generalize hl0_eq : ByteSlice.readLE a_rest 0 8 = l0 at *
  generalize hl1_eq : ByteSlice.readLE a_rest 8 8 = l1 at *
  generalize hl2_eq : ByteSlice.readLE a_rest 16 8 = l2 at *
  generalize hl3_eq : ByteSlice.readLE a_rest 24 8 = l3 at *
  generalize hl4_eq : ByteSlice.readLE a_rest 32 8 = l4 at *
  wp_sym_steps 22
  generalize hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0
  generalize hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1
  generalize hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2
  generalize hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3
  generalize hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4
  generalize hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
  generalize hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0
  wp_sym_steps 26
  generalize hu1 : h1 + u0 >>> 51 = u1; generalize hu2 : h2 + u1 >>> 51 = u2
  generalize hu3 : h3 + u2 >>> 51 = u3; generalize hu4 : h4 + u3 >>> 51 = u4
  wp_sym_steps
  have h_bytes : packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 (fe51ValOfBytes a_rest % p25519) := by
    rw [fe51ValOfBytes, hl0_eq, hl1_eq, hl2_eq, hl3_eq, hl4_eq]
    exact fe51_to_bytes_math l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4
      h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
      hh0.symm hh1.symm hh2.symm hh3.symm hh4.symm hq.symm
      hu0.symm hu1.symm hu2.symm hu3.symm hu4.symm
  wp_conv_pre =>
    rw [← hl0_eq, ← hl1_eq, ← hl2_eq, ← hl3_eq, ← hl4_eq,
        ← pointsToBytesRO40_eq_cells a a_rest h_len_a,
        pointsToBytes_packCanonical51Bytes a_1, h_bytes]
  wp_done

private theorem fe51MinusOneBytes_bounded54 : fe51LimbsBounded fe51MinusOneBytes (2 ^ 54) := by
  unfold fe51LimbsBounded
  decide +kernel

private theorem fe51MinusOneBytes_val : fe51ValOfBytes fe51MinusOneBytes % p25519 = p25519 - 1 := by
  decide +kernel

/-! ## 2. Math Bridge to `montToEdwards` -/

private theorem bv8_shl7_eq_mod2 (sign : BitVec 8) :
    sign <<< 7 = BitVec.ofNat 8 (sign.toNat % 2) <<< 7 := by
  bv_bits

private theorem setByte31Or_eq_mod2 (bs : List (BitVec 8)) (sign : BitVec 8) :
    setByte31Or bs sign = setByte31Or bs (BitVec.ofNat 8 (sign.toNat % 2)) := by
  unfold setByte31Or
  rw [bv8_shl7_eq_mod2]

private theorem setByte31Or_natToLeBytes_eq' (y s : Nat) (hy : y < p25519) (hs : s < 2) :
    setByte31Or (natToLeBytes 32 y) (BitVec.ofNat 8 s) =
      natToLeBytes 32 (y + s * 2 ^ 255) := by
  unfold setByte31Or
  apply List.ext_getElem
  · simp [natToLeBytes]
  · intro i hi1 hi2
    have hi : i < 32 := by simp [natToLeBytes] at hi1; exact hi1
    rw [List.getElem_set]
    by_cases h31 : 31 = i
    · subst h31
      have hget31 : (natToLeBytes 32 y).getD 31 0#8 = BitVec.ofNat 8 ((y / 256 ^ 31) % 256) := by
        simp [List.getD, natToLeBytes]
      have hget_i : ∀ n, (natToLeBytes 32 n)[31]'(by simp [natToLeBytes]) = BitVec.ofNat 8 ((n / 256 ^ 31) % 256) := by
        intro n; simp [natToLeBytes]
      rw [ite_eq_left rfl, hget31, hget_i]
      have hy_div : y / 256 ^ 31 < 128 := by
        have : p25519 < 128 * 256 ^ 31 := by decide +kernel
        omega
      have hy_mod : (y / 256 ^ 31) % 256 = y / 256 ^ 31 := Nat.mod_eq_of_lt (by omega)
      have h_add_div : (y + s * 2 ^ 255) / 256 ^ 31 = y / 256 ^ 31 + s * 128 := by
        have : s * 2 ^ 255 = (s * 128) * 256 ^ 31 := by
          rw [show (2 : Nat) ^ 255 = 128 * 256 ^ 31 by decide +kernel, Nat.mul_assoc]
        rw [this, Nat.add_mul_div_right _ _ (by decide +kernel)]
      have h_mod256 : (y / 256 ^ 31 + s * 128) % 256 = y / 256 ^ 31 + s * 128 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hy_mod, h_add_div, h_mod256]
      have hbv : ∀ (a b : BitVec 8), a.toNat < 128 → b.toNat < 2 →
          (a ||| (b <<< 7)) = BitVec.ofNat 8 (a.toNat + b.toNat * 128) := by
        intro a b ha hb; bv_bits
      have key := hbv (BitVec.ofNat 8 (y / 256 ^ 31)) (BitVec.ofNat 8 s)
        (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show y / 256 ^ 31 < 256 by omega),
        Nat.mod_eq_of_lt (show s < 256 by omega)] at key
      exact key
    · rw [ite_eq_right h31]
      have hget_i : ∀ n, (natToLeBytes 32 n)[i]'(by simp [natToLeBytes]; exact hi) =
          BitVec.ofNat 8 ((n / 256 ^ i) % 256) := by
        intro n; simp [natToLeBytes]
      rw [hget_i y, hget_i (y + s * 2 ^ 255)]
      have h_mod : ((y + s * 2 ^ 255) / 256 ^ i) % 256 = (y / 256 ^ i) % 256 := by
        have h_pow : 256 ^ i * (256 * 256 ^ (30 - i)) = 256 ^ 31 := by
          rw [← Nat.pow_succ', ← Nat.pow_add, show i + (30 - i + 1) = 31 by omega]
        have h_mul : s * 2 ^ 255 = (256 * (s * (128 * 256 ^ (30 - i)))) * 256 ^ i := by
          calc s * 2 ^ 255 = s * (128 * 256 ^ 31) := by
                rw [show (2 : Nat) ^ 255 = 128 * 256 ^ 31 by decide +kernel]
            _ = s * (128 * (256 ^ i * (256 * 256 ^ (30 - i)))) := by rw [← h_pow]
            _ = (256 * (s * (128 * 256 ^ (30 - i)))) * 256 ^ i := by
                simp only [Nat.mul_left_comm, Nat.mul_comm]
        have hpos : 0 < 256 ^ i := Nat.pow_pos (by decide)
        rw [h_mul, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_left]
      rw [h_mod]

private theorem montToEdwards_eq_none_of_u_eq_m1 (bs : List (BitVec 8)) (sign : Nat)
    (hu : decodeU255 bs % p25519 = p25519 - 1) :
    montToEdwards bs sign = none := by
  unfold montToEdwards
  simp [hu]

private theorem decodeEdDalek_eq_montToEdwards_of_ne_m1
    (bs : List (BitVec 8)) (sign : BitVec 8) (y : Nat)
    (hne : decodeU255 bs % p25519 ≠ p25519 - 1)
    (hy_lt : y < p25519)
    (hy_eq : y = fpMul (fpSub (decodeU255 bs % p25519) 1) (fpInv (fpAdd (decodeU255 bs % p25519) 1))) :
    decodeEdDalek (setByte31Or (natToLeBytes 32 y) sign) =
      montToEdwards bs (sign.toNat % 2) := by
  have hs_lt : sign.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [setByte31Or_eq_mod2, setByte31Or_natToLeBytes_eq' y (sign.toNat % 2) hy_lt hs_lt]
  have hy_lt255 : y < 2 ^ 255 := by
    have : p25519 < 2 ^ 255 := by decide +kernel
    omega
  have hsum_lt : y + (sign.toNat % 2) * 2 ^ 255 < 256 ^ 32 := by
    have : (2 : Nat) ^ 255 * 2 = 256 ^ 32 := by decide +kernel
    omega
  have hle := leBytesToNat_natToLeBytes_of_lt (len := 32) hsum_lt
  have hlen : (natToLeBytes 32 (y + (sign.toNat % 2) * 2 ^ 255)).length = 32 := by
    simp [natToLeBytes]
  have hmod255 : (y + (sign.toNat % 2) * 2 ^ 255) % 2 ^ 255 = y := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy_lt255]
  have hmodp : y % p25519 = y := Nat.mod_eq_of_lt hy_lt
  have hdiv255 : ((y + (sign.toNat % 2) * 2 ^ 255) / 2 ^ 255) % 2 = sign.toNat % 2 := by
    rw [Nat.add_mul_div_right _ _ (by decide +kernel), Nat.div_eq_of_lt hy_lt255,
        Nat.zero_add, Nat.mod_eq_of_lt hs_lt]
  have hbeq : (decodeU255 bs % p25519 == p25519 - 1) = false := beq_eq_false_iff_ne.mpr hne
  unfold decodeEdDalek montToEdwards
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hle, hmod255, hmodp, hdiv255, Nat.mod_mod, hbeq, ← hy_eq]
  cases recoverXEven y <;> simp

private theorem bv64_toNat_bytes (v : BitVec 64) :
    v.toNat = (v.extractLsb' 0 8).toNat + (v.extractLsb' 8 8).toNat * 256 +
      (v.extractLsb' 16 8).toNat * 65536 + (v.extractLsb' 24 8).toNat * 16777216 +
      (v.extractLsb' 32 8).toNat * 4294967296 + (v.extractLsb' 40 8).toNat * 1099511627776 +
      (v.extractLsb' 48 8).toNat * 281474976710656 + (v.extractLsb' 56 8).toNat * 72057594037927936 := by
  have h (k : Nat) : (v.extractLsb' k 8).toNat = (v.toNat / 2 ^ k) % 256 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [h 0, h 8, h 16, h 24, h 32, h 40, h 48, h 56]
  have := v.isLt; omega

private theorem pack64_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
      b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
      b6.toNat * 281474976710656 + b7.toNat * 72057594037927936 := by
  have h := unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  simp only [unpack64, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hv := bv64_toNat_bytes (pack64 b0 b1 b2 b3 b4 b5 b6 b7)
  unfold pack64 at hv; rw [h0, h1, h2, h3, h4, h5, h6, h7] at hv; exact hv

private theorem leBytesToNat_take_succ (bs : List (BitVec 8)) :
    ∀ k, k < bs.length →
      leBytesToNat (bs.take (k + 1)) = leBytesToNat (bs.take k) + (bs.getD k 0#8).toNat * 256 ^ k
  | 0, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · simp [leBytesToNat]
  | k + 1, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · have ih := leBytesToNat_take_succ bs k (by simpa using hk)
      simp only [List.take_succ_cons, leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
      rw [ih, Nat.pow_succ, ← Nat.mul_assoc]; omega

private theorem leBytesToNat_32 (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    leBytesToNat bs =
      (bs.getD 0 0#8).toNat + (bs.getD 1 0#8).toNat * 256 ^ 1 +
      (bs.getD 2 0#8).toNat * 256 ^ 2 + (bs.getD 3 0#8).toNat * 256 ^ 3 +
      (bs.getD 4 0#8).toNat * 256 ^ 4 + (bs.getD 5 0#8).toNat * 256 ^ 5 +
      (bs.getD 6 0#8).toNat * 256 ^ 6 + (bs.getD 7 0#8).toNat * 256 ^ 7 +
      (bs.getD 8 0#8).toNat * 256 ^ 8 + (bs.getD 9 0#8).toNat * 256 ^ 9 +
      (bs.getD 10 0#8).toNat * 256 ^ 10 + (bs.getD 11 0#8).toNat * 256 ^ 11 +
      (bs.getD 12 0#8).toNat * 256 ^ 12 + (bs.getD 13 0#8).toNat * 256 ^ 13 +
      (bs.getD 14 0#8).toNat * 256 ^ 14 + (bs.getD 15 0#8).toNat * 256 ^ 15 +
      (bs.getD 16 0#8).toNat * 256 ^ 16 + (bs.getD 17 0#8).toNat * 256 ^ 17 +
      (bs.getD 18 0#8).toNat * 256 ^ 18 + (bs.getD 19 0#8).toNat * 256 ^ 19 +
      (bs.getD 20 0#8).toNat * 256 ^ 20 + (bs.getD 21 0#8).toNat * 256 ^ 21 +
      (bs.getD 22 0#8).toNat * 256 ^ 22 + (bs.getD 23 0#8).toNat * 256 ^ 23 +
      (bs.getD 24 0#8).toNat * 256 ^ 24 + (bs.getD 25 0#8).toNat * 256 ^ 25 +
      (bs.getD 26 0#8).toNat * 256 ^ 26 + (bs.getD 27 0#8).toNat * 256 ^ 27 +
      (bs.getD 28 0#8).toNat * 256 ^ 28 + (bs.getD 29 0#8).toNat * 256 ^ 29 +
      (bs.getD 30 0#8).toNat * 256 ^ 30 + (bs.getD 31 0#8).toNat * 256 ^ 31 := by
  have htake : bs = bs.take 32 := (List.take_of_length_le (by omega)).symm
  conv => lhs; rw [htake]
  repeat rw [leBytesToNat_take_succ bs _ (by omega)]
  have h0 : leBytesToNat (bs.take 0) = 0 := rfl
  rw [h0]; omega

private theorem fe51_from_bytes_u255 (bs : List (BitVec 8)) (hbs : bs.length = 32)
    (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0_eq : ByteSlice.readLE bs 0 8 &&& 2251799813685247#64 = l0)
    (hl1_eq : (ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64 = l1)
    (hl2_eq : (ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64 = l2)
    (hl3_eq : (ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64 = l3)
    (hl4_eq : (ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64 = l4) :
    l0.toNat < 2 ^ 51 ∧ l1.toNat < 2 ^ 51 ∧ l2.toNat < 2 ^ 51 ∧ l3.toNat < 2 ^ 51 ∧ l4.toNat < 2 ^ 51 ∧
    fe51Val l0 l1 l2 l3 l4 = decodeU255 bs := by
  have hle32 := leBytesToNat_32 bs hbs
  have hl0 : l0.toNat =
      (pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
        (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)).toNat % 2 ^ 51 := by
    rw [← hl0_eq, bv64_and_mask51_toNat, ← ByteSlice.pack64_eq_readLE_8 bs 0]
  have hl1 : l1.toNat =
      ((pack64 (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8)
        (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8)).toNat / 8) % 2 ^ 51 := by
    rw [← hl1_eq, bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 6]
  have hl2 : l2.toNat =
      ((pack64 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8)
        (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)).toNat / 64) % 2 ^ 51 := by
    rw [← hl2_eq, bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 12]
  have hl3 : l3.toNat =
      ((pack64 (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8)
        (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)).toNat / 2) % 2 ^ 51 := by
    rw [← hl3_eq, bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 19]
  have hl4 : l4.toNat =
      ((pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
        (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8)).toNat / 4096) % 2 ^ 51 := by
    rw [← hl4_eq, bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 24]
  rw [pack64_toNat] at hl0 hl1 hl2 hl3 hl4
  have := (bs.getD 0 0#8).isLt; have := (bs.getD 1 0#8).isLt; have := (bs.getD 2 0#8).isLt; have := (bs.getD 3 0#8).isLt
  have := (bs.getD 4 0#8).isLt; have := (bs.getD 5 0#8).isLt; have := (bs.getD 6 0#8).isLt; have := (bs.getD 7 0#8).isLt
  have := (bs.getD 8 0#8).isLt; have := (bs.getD 9 0#8).isLt; have := (bs.getD 10 0#8).isLt; have := (bs.getD 11 0#8).isLt
  have := (bs.getD 12 0#8).isLt; have := (bs.getD 13 0#8).isLt; have := (bs.getD 14 0#8).isLt; have := (bs.getD 15 0#8).isLt
  have := (bs.getD 16 0#8).isLt; have := (bs.getD 17 0#8).isLt; have := (bs.getD 18 0#8).isLt; have := (bs.getD 19 0#8).isLt
  have := (bs.getD 20 0#8).isLt; have := (bs.getD 21 0#8).isLt; have := (bs.getD 22 0#8).isLt; have := (bs.getD 23 0#8).isLt
  have := (bs.getD 24 0#8).isLt; have := (bs.getD 25 0#8).isLt; have := (bs.getD 26 0#8).isLt; have := (bs.getD 27 0#8).isLt
  have := (bs.getD 28 0#8).isLt; have := (bs.getD 29 0#8).isLt; have := (bs.getD 30 0#8).isLt; have := (bs.getD 31 0#8).isLt
  unfold fe51Val decodeU255
  rw [List.take_of_length_le (by omega : bs.length ≤ 32)]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  omega

private theorem bfi_byte12_eq (u1 u2 : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u1 >>> 45)) &&& 18446744069414584383#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u2) &&& 67108863#64) <<< 6) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6) := by
  simp only [BitVec.zeroExtend, BitVec.truncate, BitVec.setWidth_or, BitVec.setWidth_and]
  bv_bits

private theorem bfi_byte19_eq (u2 u3 : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u2 >>> 50)) &&& 18446744069414584321#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u3) &&& 2147483647#64) <<< 1) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1) := by
  simp only [BitVec.zeroExtend, BitVec.truncate, BitVec.setWidth_or, BitVec.setWidth_and]
  bv_bits

private theorem bfi_byte25_eq (u3 u4 : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u3 >>> 47)) &&& 18446744069414584335#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u4) &&& 268435455#64) <<< 4) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4) := by
  simp only [BitVec.zeroExtend, BitVec.truncate, BitVec.setWidth_or, BitVec.setWidth_and]
  bv_bits

private theorem ubfx_byte31_eq (u4 : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u4 >>> 44)) &&& 127#64) =
    BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64) := by
  bv_bits

private theorem limb_lt51_h0_eq (l0 l4 : BitVec 64) (hl0 : l0.toNat < 2 ^ 51) (hl4 : l4.toNat < 2 ^ 51) :
    (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = l0 := by
  bv_bits

private theorem limb_lt51_hi_eq (li lprev : BitVec 64) (hli : li.toNat < 2 ^ 51) (hp : lprev.toNat < 2 ^ 51) :
    (li &&& 2251799813685247#64) + lprev >>> 51 = li := by
  bv_bits

private theorem fe51_inline_u_to_bytes (bs : List (BitVec 8))
    (l0 l1 l2 l3 l4 q : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 51) (hl1 : l1.toNat < 2 ^ 51) (hl2 : l2.toNat < 2 ^ 51)
    (hl3 : l3.toNat < 2 ^ 51) (hl4 : l4.toNat < 2 ^ 51)
    (hval : fe51Val l0 l1 l2 l3 l4 = decodeU255 bs)
    (hq : (l4 + (l3 + (l2 + (l1 + (l0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q) :
    let u0 := l0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64
    let u1 := l1 + u0 >>> 51
    let u2 := l2 + u1 >>> 51
    let u3 := l3 + u2 >>> 51
    let u4 := l4 + u3 >>> 51
    packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 (decodeU255 bs % p25519) := by
  intro u0 u1 u2 u3 u4
  let z40 := List.replicate 40 (0#8 : BitVec 8)
  haveI : HasLenGe z40 40 := ⟨by simp [z40]⟩
  let bs5 := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 z40 0 l0) 8 l1) 16 l2) 24 l3) 32 l4
  have hr0 : ByteSlice.readLE bs5 0 8 = l0 := by
    dsimp only [bs5]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
  have hr1 : ByteSlice.readLE bs5 8 8 = l1 := by
    dsimp only [bs5]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
  have hr2 : ByteSlice.readLE bs5 16 8 = l2 := by
    dsimp only [bs5]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
  have hr3 : ByteSlice.readLE bs5 24 8 = l3 := by
    dsimp only [bs5]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
  have hr4 : ByteSlice.readLE bs5 32 8 = l4 := by
    dsimp only [bs5]; simp (disch := decide) only [↓readLE_write64_self']
  have hv5 : fe51ValOfBytes bs5 = fe51Val l0 l1 l2 l3 l4 := by
    unfold fe51ValOfBytes; rw [hr0, hr1, hr2, hr3, hr4]
  have hb52 : 2 ^ 51 < 4503599627370496 := by decide
  have key := fe51_to_bytes_of_bytes bs5 l0 l1 l2 l3 l4 hr0 hr1 hr2 hr3 hr4
    (Nat.lt_trans hl0 hb52) (Nat.lt_trans hl1 hb52) (Nat.lt_trans hl2 hb52)
    (Nat.lt_trans hl3 hb52) (Nat.lt_trans hl4 hb52)
    l0 l1 l2 l3 l4 q u0 u1 u2 u3 u4
    (limb_lt51_h0_eq l0 l4 hl0 hl4)
    (limb_lt51_hi_eq l1 l0 hl1 hl0)
    (limb_lt51_hi_eq l2 l1 hl2 hl1)
    (limb_lt51_hi_eq l3 l2 hl3 hl2)
    (limb_lt51_hi_eq l4 l3 hl4 hl3)
    hq rfl rfl rfl rfl rfl
  rw [hv5, hval] at key
  exact key

private theorem natToLeBytes_32_eq_m1_iff (u : Nat) (hu : u < p25519) :
    (natToLeBytes 32 u == natToLeBytes 32 (p25519 - 1)) = decide (u = p25519 - 1) := by
  have hp256 : p25519 < 256 ^ 32 := by decide +kernel
  by_cases h : u = p25519 - 1
  · subst h; simp
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro heq
    have := congrArg leBytesToNat heq
    rw [leBytesToNat_natToLeBytes_of_lt (len := 32) (by omega),
        leBytesToNat_natToLeBytes_of_lt (len := 32) (by omega)] at this
    exact h this

private theorem tst_w0_ff_of_trunc8_1 (x0 : BitVec 64)
    (hw : BitVec.zeroExtend 8 x0 = 1#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 1095216660735#64) == 0#32) = false := by
  rw [beq_eq_false_iff_ne]
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.setWidth_and] at hw ⊢
  bv_bits

private theorem tst_w0_ff_of_trunc8_0 (x0 : BitVec 64)
    (hw : BitVec.zeroExtend 8 x0 = 0#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 1095216660735#64) == 0#32) = true := by
  rw [beq_iff_eq]
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.setWidth_and] at hw ⊢
  bv_bits

private theorem sepWP_merge_bytes_append (sp : BitVec 64) (off k rem : Nat)
    {bs1 bs2 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - BitVec.ofNat 64 off) ↦ₛ bs1) ∗
                  ((sp - BitVec.ofNat 64 rem) ↦ₛ bs2)) ∗ P := by sep_frame)
    (hbs1 : bs1.length = k)
    (hrem : off - k = rem := by decide)
    (_hle : k ≤ off := by decide)
    (_hbound : off < 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (((sp - BitVec.ofNat 64 off) ↦ₛ (bs1 ++ bs2)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hsub : (sp - BitVec.ofNat 64 off) + BitVec.ofNat 64 k = sp - BitVec.ofNat 64 rem := by
    subst hrem; bv_arith
  rw [hf, ← hsub, ← hbs1, ← pointsToBytes_append]
  exact hnext

private theorem sub1_bias0_eq (l : BitVec 64) :
    l + 36028797018963663#64 = (l - 1#64) + 36028797018963664#64 := by bv_bits

private theorem sub0_bias1_eq (l : BitVec 64) :
    l + 36028797018963952#64 = (l - 0#64) + 36028797018963952#64 := by bv_bits

private theorem to_edwards_y_of_muls
    (u : Nat) (um1_bs up1_bs t19_bs t3_bs t2_5_bs recip_bs y_bs : List (BitVec 8))
    (hum1 : fe51ValOfBytes um1_bs % p25519 = fpSub u 1)
    (hup1 : fe51ValOfBytes up1_bs % p25519 = fpAdd u 1)
    (ht19 : fe51ValOfBytes t19_bs % p25519 = fpPow (fe51ValOfBytes up1_bs % p25519) (2 ^ 250 - 1))
    (ht3 : fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes up1_bs % p25519) 11)
    (ht2_5 : fe51ValOfBytes t2_5_bs % p25519 = fpPow (fe51ValOfBytes t19_bs % p25519) (2 ^ (5#32 : BitVec 32).toNat))
    (hrecip : fe51ValOfBytes recip_bs % p25519 = (fe51ValOfBytes t2_5_bs * fe51ValOfBytes t3_bs) % p25519)
    (hy : fe51ValOfBytes y_bs % p25519 = (fe51ValOfBytes um1_bs * fe51ValOfBytes recip_bs) % p25519) :
    fe51ValOfBytes y_bs % p25519 = fpMul (fpSub u 1) (fpInv (fpAdd u 1)) := by
  have h5 : (5#32 : BitVec 32).toNat = 5 := rfl
  rw [h5] at ht2_5
  have hinv := compress_recip_eq_fpInv (fe51ValOfBytes up1_bs) (fe51ValOfBytes t19_bs)
    (fe51ValOfBytes t3_bs) (fe51ValOfBytes t2_5_bs) (fe51ValOfBytes recip_bs)
    ht19 ht3 ht2_5 hrecip
  rw [hup1] at hinv
  dsimp only [fpMul]
  rw [hy, Nat.mul_mod, hum1, hinv, ← Nat.mul_mod]

/-! ## 3. Segment Helpers for `<MontgomeryPoint>::to_edwards` (`B08`) -/

private def montToEdwardsIrred (bs : List (BitVec 8)) (sign : Nat) : Option EdPoint :=
  montToEdwards bs sign

attribute [local irreducible] montToEdwardsIrred

abbrev rust_spec montgomeryPointToEdwardsRawSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr) (sign : u8)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 168 ∧ self_bs.length = 32
  preserves     self ↦ₛ self_bs ∗
                (fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗
                (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
                (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes)
  requires      out ↦ₛ out_bs
  stack         2576
  ensures       match montToEdwardsIrred self_bs (sign.toNat % 2) with
                | none =>
                  ∃∗ pad_bs,
                    ⌜pad_bs.length = 160⌝ ∗
                    (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦ₛ pad_bs)
                | some P =>
                  ∃∗ pt_bs,
                    ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧
                     edExtOfBytes pt_bs = edExtOfAffine P⌝ ∗
                    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦ₛ pt_bs)

private theorem montgomeryPointToEdwardsSpec_eq (mpl : Obj.MultiPlacement) :
    montgomeryPointToEdwardsSpec mpl = montgomeryPointToEdwardsRawSpec mpl := by
  unfold montgomeryPointToEdwardsSpec montgomeryPointToEdwardsRawSpec montToEdwardsIrred
  rfl

private theorem sepWP_cases_opt {α : Type} (d : Option α)
    {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnone : d = none → SepWP prog target_pc s P post oom)
    (hsome : ∀ x, d = some x → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom := by
  cases hd : d with
  | none => exact hnone hd
  | some x => exact hsome x hd

private theorem mont_to_edwards_epilogue_step [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl08 b) (_hbase : dalekCliPl08.base = b)
    (s0 s : State)
    {c_pad : BitVec 64}
    {b400 b392 b352 b312 b272 b232 b224 b192 b184 b176 b136 : List (BitVec 8)}
    {Full Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      (memRegion (s0.sp - 2576#64) 2176 ∗
       ((s0.sp - 400#64) ↦ₛ b400) ∗
       ((s0.sp - 392#64) ↦ₛ b392) ∗
       ((s0.sp - 352#64) ↦ₛ b352) ∗
       ((s0.sp - 312#64) ↦ₛ b312) ∗
       ((s0.sp - 272#64) ↦ₛ b272) ∗
       ((s0.sp - 232#64) ↦ₛ b232) ∗
       ((s0.sp - 224#64) ↦ₛ b224) ∗
       ((s0.sp - 192#64) ↦ₛ b192) ∗
       ((s0.sp - 184#64) ↦ₛ b184) ∗
       ((s0.sp - 176#64) ↦ₛ b176) ∗
       ((s0.sp - 136#64) ↦ₛ b136) ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
       ((s0.sp - 72#64) ↦₆₄ c_pad) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
       ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
       ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗ Frame := by sep_frame)
    (hb400 : b400.length = 8) (hb392 : b392.length = 40) (hb352 : b352.length = 40)
    (hb312 : b312.length = 40) (hb272 : b272.length = 40) (hb232 : b232.length = 8)
    (hb224 : b224.length = 32) (hb192 : b192.length = 8) (hb184 : b184.length = 8)
    (hb176 : b176.length = 40) (hb136 : b136.length = 40)
    (hpc : s.pc = b + 1036#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 400#64) (h_sp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hdone : ∀ s_ret : State,
      s_ret.pc = s0.readReg64 (.gpr 30#5) →
      s_ret.status = .Running →
      s_ret.sp = s0.sp →
      CalleeSavedPreserved s0 s_ret →
      SepWP (dalekCliPC08.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s_ret
        (stackFrame s0 2576 ∗ Frame) post oom) :
    SepWP (dalekCliPC08.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s Full post oom := by
  rw [hf]
  wp_steps
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 136 40 96 (hbs := hb136)
  apply sepWP_unpeel_stack_bytes s0.sp 176 40 136 (hbs := hb176)
  apply sepWP_unpeel_stack_bytes s0.sp 184 8 176 (hbs := hb184)
  apply sepWP_unpeel_stack_bytes s0.sp 192 8 184 (hbs := hb192)
  apply sepWP_unpeel_stack_bytes s0.sp 224 32 192 (hbs := hb224)
  apply sepWP_unpeel_stack_bytes s0.sp 232 8 224 (hbs := hb232)
  apply sepWP_unpeel_stack_bytes s0.sp 272 40 232 (hbs := hb272)
  apply sepWP_unpeel_stack_bytes s0.sp 312 40 272 (hbs := hb312)
  apply sepWP_unpeel_stack_bytes s0.sp 352 40 312 (hbs := hb352)
  apply sepWP_unpeel_stack_bytes s0.sp 392 40 352 (hbs := hb392)
  apply sepWP_unpeel_stack_bytes s0.sp 400 8 392 (hbs := hb400)
  have hsp2576 : s0.sp - 2576#64 = s0.sp - 400#64 - 2176#64 := by bv_omega
  wp_conv_pre => rw [hsp2576]
  apply sepWP_merge_stack_callee 2176 400
  exact hdone _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm]) (by simp [CalleeSavedPreserved.iff_regs, arm64_norm, hx27, hvregs])

set_option maxHeartbeats 800000 in
set_option maxRecDepth 16384 in
private theorem mont_to_edwards_pack_y_step [DalekCliPlacement]
    (b sp out : BitVec 64) (_hb : DalekBase dalekCliPl08 b) (_hbase : dalekCliPl08.base = b)
    (sign : BitVec 8)
    (w_4 w_1 : List (BitVec 8))
    {r1 : BitVec 64} {s0 s : State} {target_pc : BitVec 64} {Full Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 176#64) ↦ₛ w_4) ∗ ((sp - 224#64) ↦ₛ w_1)) ∗ Frame := by sep_frame)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hw4_b : fe51LimbsBounded w_4 (2 ^ 52))
    (hw1_l : w_1.length = 40)
    (hpc : s.pc = b + 652#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 400#64)
    (hx19 : s.readReg64 (.gpr 19#5) = out)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.setWidth 64 (BitVec.setWidth 32 r1))
    (hr1 : BitVec.zeroExtend 8 r1 = sign)
    (hx26 : s.readReg64 (.gpr 26#5) = 19#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hx29 : s.readReg64 (.gpr 29#5) = sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf' : State,
      sf'.pc = b + 1032#64 →
      sf'.status = .Running →
      sf'.sp = sp - 400#64 →
      sf'.readReg64 (.gpr 8#5) = out →
      sf'.readReg64 (.gpr 0#5) = sp - 224#64 →
      sf'.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) →
      calleeSavedVRegs sf' = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl sf'.mem →
      SepWP (dalekCliPC08.rebase b (fun _ => none)) target_pc sf'
        ((((sp - 176#64) ↦ₛ w_4) ∗
          ((sp - 224#64) ↦ₛ setByte31Or (natToLeBytes 32 (fe51ValOfBytes w_4 % p25519)) sign) ∗
          ((sp - 192#64) ↦ₛ w_1.drop 32)) ∗ Frame) post oom) :
    SepWP (dalekCliPC08.rebase b (fun _ => none)) target_pc s Full post oom := by
  let _ := hx29
  rw [hf]
  obtain ⟨hw4_len, hyl0, hyl1, hyl2, hyl3, hyl4⟩ := hw4_b
  have h_w4 := pointsToBytes40_sub_eq_cells sp 176#64 168#64 160#64 152#64 144#64 w_4 hw4_len
  have hw1_split : ((sp - 224#64) ↦ₛ w_1) = ((sp - 224#64) ↦ₛ (w_1.take 32 ++ w_1.drop 32)) := by
    rw [List.take_append_drop]
  have hw1_take_l : (w_1.take 32).length = 32 := by simp [hw1_l]
  wp_conv_pre => rw [hw1_split]
  apply sepWP_split_bytes_append sp 224 32 192 (hbs1 := hw1_take_l)
  wp_conv_pre => rw [h_w4, pointsToBytes32_eq_cells8 (sp - 224#64) (w_1.take 32) hw1_take_l]
  generalize hyl0_eq : ByteSlice.readLE w_4 0 8 = ly0 at *
  generalize hyl1_eq : ByteSlice.readLE w_4 8 8 = ly1 at *
  generalize hyl2_eq : ByteSlice.readLE w_4 16 8 = ly2 at *
  generalize hyl3_eq : ByteSlice.readLE w_4 24 8 = ly3 at *
  generalize hyl4_eq : ByteSlice.readLE w_4 32 8 = ly4 at *
  wp_cut_codeLoaded
  wp_sym_steps 22
  apply SepWP.done
  · rfl
  · assumption
  intro hcl1
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl1
  clear hcl
  generalize hhy0 : (ly0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (ly4 >>> 51)) * 19#64 = hy0
  generalize hhy1 : (ly1 &&& 2251799813685247#64) + ly0 >>> 51 = hy1
  generalize hhy2 : (ly2 &&& 2251799813685247#64) + ly1 >>> 51 = hy2
  generalize hhy3 : (ly3 &&& 2251799813685247#64) + ly2 >>> 51 = hy3
  generalize hhy4 : (ly4 &&& 2251799813685247#64) + ly3 >>> 51 = hy4
  generalize hqy : (hy4 + (hy3 + (hy2 + (hy1 + (hy0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = qy
  generalize huy0 : hy0 + BitVec.setWidth 64 (BitVec.setWidth 32 qy) * 19#64 = uy0
  wp_conv_pre => rw [← h_w4]
  wp_cut_codeLoaded
  wp_sym_steps 3
  generalize huy1 : hy1 + uy0 >>> 51 = uy1
  wp_sym_steps 4
  generalize huy2 : hy2 + uy1 >>> 51 = uy2
  wp_sym_steps 8
  generalize huy3 : hy3 + uy2 >>> 51 = uy3
  wp_sym_steps 6
  generalize huy4 : hy4 + uy3 >>> 51 = uy4
  wp_sym_steps 52
  apply SepWP.done
  · rfl
  · assumption
  intro hcl2
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl2
  clear hcl1
  have h_bytes_y := fe51_to_bytes_of_bytes w_4 ly0 ly1 ly2 ly3 ly4 hyl0_eq hyl1_eq hyl2_eq hyl3_eq hyl4_eq
    hyl0 hyl1 hyl2 hyl3 hyl4 hy0 hy1 hy2 hy3 hy4 qy uy0 uy1 uy2 uy3 uy4
    hhy0 hhy1 hhy2 hhy3 hhy4 hqy huy0 huy1 huy2 huy3 huy4
  wp_conv_pre =>
    rw [compress_byte31_eq, hr1,
        pointsToBytes_setByte31Or_packCanonical51Bytes, h_bytes_y]
  have hpre_eq :
      ((((sp - 224#64) ↦ₛ setByte31Or (natToLeBytes 32 (fe51ValOfBytes w_4 % p25519)) sign) ∗
        ((sp - 192#64) ↦ₛ w_1.drop 32)) ∗ ((sp - 176#64) ↦ₛ w_4) ∗ Frame) =
      ((((sp - 176#64) ↦ₛ w_4) ∗
        ((sp - 224#64) ↦ₛ setByte31Or (natToLeBytes 32 (fe51ValOfBytes w_4 % p25519)) sign) ∗
        ((sp - 192#64) ↦ₛ w_1.drop 32)) ∗ Frame) := by sep_ac_rfl
  wp_conv_pre => rw [hpre_eq]
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx27]) (by simp [arm64_norm, hvregs]) hcl2

set_option maxHeartbeats 800000 in
private theorem mont_to_edwards_pack_u_step [DalekCliPlacement]
    (b sp : BitVec 64) (_hb : DalekBase dalekCliPl08 b) (_hbase : dalekCliPl08.base = b)
    (a_rest_1 ubytes_init : List (BitVec 8))
    (l0 l1 l2 l3 l4 q : BitVec 64)
    {s0 s : State} {target_pc : BitVec 64} {Full Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 224#64) ↦ₛ ubytes_init) ∗ Frame := by sep_frame)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hubytes_init : ubytes_init.length = 32)
    (hl0_b : l0.toNat < 2 ^ 51) (hl1_b : l1.toNat < 2 ^ 51) (hl2_b : l2.toNat < 2 ^ 51)
    (hl3_b : l3.toNat < 2 ^ 51) (hl4_b : l4.toNat < 2 ^ 51)
    (hl_val : fe51Val l0 l1 l2 l3 l4 = decodeU255 a_rest_1)
    (hq : (l4 + (l3 + (l2 + (l1 + (l0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q)
    (hpc : s.pc = b + 116#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 400#64)
    (hx8 : s.readReg64 (.gpr 8#5) = q)
    (hx9 : s.readReg64 (.gpr 9#5) = 19#64)
    (hx21 : s.readReg64 (.gpr 21#5) = l1)
    (hx22 : s.readReg64 (.gpr 22#5) = l0)
    (hx23 : s.readReg64 (.gpr 23#5) = l2)
    (hx24 : s.readReg64 (.gpr 24#5) = l3)
    (hx25 : s.readReg64 (.gpr 25#5) = l4)
    (hx29 : s.readReg64 (.gpr 29#5) = sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf' : State,
      sf'.pc = b + 408#64 →
      sf'.status = .Running →
      sf'.sp = sp - 400#64 →
      sf'.readReg64 (.gpr 8#5) = sp - 176#64 →
      sf'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      sf'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sf'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sf'.readReg64 (.gpr 21#5) = l1 →
      sf'.readReg64 (.gpr 22#5) = l0 →
      sf'.readReg64 (.gpr 23#5) = l2 →
      sf'.readReg64 (.gpr 24#5) = l3 →
      sf'.readReg64 (.gpr 25#5) = l4 →
      sf'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sf'.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      sf'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sf'.readReg64 (.gpr 29#5) = sp - 96#64 →
      calleeSavedVRegs sf' = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl sf'.mem →
      SepWP (dalekCliPC08.rebase b (fun _ => none)) target_pc sf'
        (((sp - 224#64) ↦ₛ natToLeBytes 32 (decodeU255 a_rest_1 % p25519)) ∗ Frame) post oom) :
    SepWP (dalekCliPC08.rebase b (fun _ => none)) target_pc s Full post oom := by
  rw [hf]
  wp_conv_pre =>
    rw [pointsToBytes32_eq_cells8 (sp - 224#64) ubytes_init hubytes_init]
  wp_cut_codeLoaded
  wp_sym_steps 73
  apply SepWP.done
  · rfl
  · assumption
  intro hcl'
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl'
  clear hcl
  let u0 := l0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64
  let u1 := l1 + u0 >>> 51
  let u2 := l2 + u1 >>> 51
  let u3 := l3 + u2 >>> 51
  let u4 := l4 + u3 >>> 51
  have h_ubytes : packCanonical51Bytes u0 u1 u2 u3 u4 =
      natToLeBytes 32 (decodeU255 a_rest_1 % p25519) :=
    fe51_inline_u_to_bytes a_rest_1 l0 l1 l2 l3 l4 q hl0_b hl1_b hl2_b hl3_b hl4_b hl_val hq
  wp_conv_pre =>
    try simp only [hx8, hx9, hx21, hx22, hx23, hx24, hx25]
    dsimp only []
    rw [bfi_byte12_eq u1 u2, bfi_byte19_eq u2 u3, bfi_byte25_eq u3 u4]
    try rw [ubfx_byte31_eq u4]
    rw [pointsToBytes_packCanonical51Bytes (sp - 224#64) u0 u1 u2 u3 u4, h_ubytes]
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) (by simp [arm64_norm]; try bv_omega)
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx21]) (by simp [arm64_norm, hx22])
    (by simp [arm64_norm, hx23]) (by simp [arm64_norm, hx24])
    (by simp [arm64_norm, hx25]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx29]) (by simp [arm64_norm, hvregs]) hcl'

private theorem setByte31Or_natToLeBytes32_len (n : Nat) (b : BitVec 8) :
    (setByte31Or (natToLeBytes 32 n) b).length = 32 := by
  unfold setByte31Or; simp [natToLeBytes]

attribute [local irreducible] decodeEdDalek edExtOfAffine in
private theorem mont_to_edwards_decompress_epilogue_step [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl08 b) (hbase : dalekCliPl08.base = b)
    (s0 sf_p : State)
    (hDecomp : CompressedEdwardsYDecompressOk)
    (hcl_p : dalekCliMultiLib.CodeLoaded dalekCliMpl sf_p.mem)
    (a_1 : BitVec 64) (a_3 y_enc w_4 : List (BitVec 8))
    {c_pad : BitVec 64} {b400 b392 b352 b312 b272 b232 b192 b184 b136 : List (BitVec 8)}
    {Full Frame : SepProp} {post : State → SepProp → Prop}
    (hf : Full =
      (memRegion (s0.sp - 2576#64) 2176 ∗ (a_1 ↦ₛ a_3) ∗
       ((s0.sp - 224#64) ↦ₛ y_enc) ∗
       (fe51_edwards_d dalekCliMpl ↦ᵣ fe51EdwardsDBytes) ∗
       (fe51_sqrt_m1 dalekCliMpl ↦ᵣ fe51SqrtM1Bytes) ∗
       ((s0.sp - 400#64) ↦ₛ b400) ∗ ((s0.sp - 392#64) ↦ₛ b392) ∗ ((s0.sp - 352#64) ↦ₛ b352) ∗
       ((s0.sp - 312#64) ↦ₛ b312) ∗ ((s0.sp - 272#64) ↦ₛ b272) ∗ ((s0.sp - 232#64) ↦ₛ b232) ∗
       ((s0.sp - 192#64) ↦ₛ b192) ∗ ((s0.sp - 184#64) ↦ₛ b184) ∗ ((s0.sp - 176#64) ↦ₛ w_4) ∗
       ((s0.sp - 136#64) ↦ₛ b136) ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ c_pad) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
      Frame := by sep_frame)
    (h_4 : a_3.length = 168) (hy_enc_len : y_enc.length = 32)
    (hb400 : b400.length = 8) (hb392 : b392.length = 40) (hb352 : b352.length = 40)
    (hb312 : b312.length = 40) (hb272 : b272.length = 40) (hb232 : b232.length = 8)
    (hb192 : b192.length = 8) (hb184 : b184.length = 8)
    (hw4_len : w_4.length = 40) (hb136 : b136.length = 40)
    (hpc_p : sf_p.pc = b + 1032#64) (hrun_p : sf_p.status = .Running)
    (hsp_p : sf_p.sp = s0.sp - 400#64) (h_sp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx8_p : sf_p.readReg64 (.gpr 8#5) = a_1) (hx0_p : sf_p.readReg64 (.gpr 0#5) = s0.sp - 224#64)
    (hx27_p : sf_p.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hvregs_p : calleeSavedVRegs sf_p = calleeSavedVRegs s0)
    (hnone : ∀ s_ret : State,
      s_ret.pc = s0.readReg64 (.gpr 30#5) → s_ret.status = .Running →
      s_ret.sp = s0.sp → CalleeSavedPreserved s0 s_ret →
      decodeEdDalek y_enc = none →
      SepWP (dalekCliPC08.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s_ret
        (stackFrame s0 2576 ∗ (fe51_edwards_d dalekCliMpl ↦ᵣ fe51EdwardsDBytes) ∗
         (fe51_sqrt_m1 dalekCliMpl ↦ᵣ fe51SqrtM1Bytes) ∗
         (∃∗ pad_bs, ⌜pad_bs.length = 160⌝ ∗ (a_1 ↦₆₄ 0#64) ∗ ((a_1 + 8#64) ↦ₛ pad_bs)) ∗
         Frame) post)
    (hsome : ∀ (s_ret : State) (P : EdPoint),
      s_ret.pc = s0.readReg64 (.gpr 30#5) → s_ret.status = .Running →
      s_ret.sp = s0.sp → CalleeSavedPreserved s0 s_ret →
      decodeEdDalek y_enc = some P →
      SepWP (dalekCliPC08.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s_ret
        (stackFrame s0 2576 ∗ (fe51_edwards_d dalekCliMpl ↦ᵣ fe51EdwardsDBytes) ∗
         (fe51_sqrt_m1 dalekCliMpl ↦ᵣ fe51SqrtM1Bytes) ∗
         (∃∗ pt_bs, ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧ edExtOfBytes pt_bs = edExtOfAffine P⌝ ∗
                    (a_1 ↦₆₄ 1#64) ∗ ((a_1 + 8#64) ↦ₛ pt_bs)) ∗
         Frame) post) :
    SepWP (dalekCliPC08.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) sf_p Full post := by
  let _ := hcl_p
  rw [hf]
  wp_steps
  wp_dalek_call hDecomp
  have hvregs_ep : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    first
    | exact ‹calleeSavedVRegs sf = calleeSavedVRegs sf_p›.trans hvregs_p
    | (have hcs_tmp : CalleeSavedPreserved _ sf := ‹_›
       have h1 := hcs_tmp.2.2.2.2.2.2.2.2.2.2.2
       simp only [arm64_norm] at h1
       exact h1.trans hvregs_p)
  rw [hsp_p, hx27_p] at *
  clear_dead_vars [sf_p]; try clear sf_p
  norm_sf 2176
  apply mont_to_edwards_epilogue_step b hb hbase s0 sf
    (hb400 := hb400) (hb392 := hb392) (hb352 := hb352)
    (hb312 := hb312) (hb272 := hb272) (hb232 := hb232)
    (hb224 := hy_enc_len) (hb192 := hb192) (hb184 := hb184)
    (hb176 := hw4_len) (hb136 := hb136)
    (hpc := hpc_sf) (hrun := hrun_sf) (hsp := hsp_sf) (h_sp_align := h_sp_align)
    (hx27 := ‹_›) (hvregs := hvregs_ep)
  intro s_ret hpc_r hrun_r hsp_r hcs_r
  clear_dead_vars [sf]; try clear sf
  apply sepWP_cases_opt (decodeEdDalek y_enc)
  · intro h_dec
    wp_conv_pre => rw [h_dec]; dsimp only
    have hgoal := hnone s_ret hpc_r hrun_r hsp_r hcs_r h_dec
    exact Eq.mp (congrFun (congrArg (fun P post => SepWP _ _ s_ret P post) (by sep_ac_rfl)) post) hgoal
  · intro P h_dec
    wp_conv_pre => rw [h_dec]; dsimp only
    have hgoal := hsome s_ret P hpc_r hrun_r hsp_r hcs_r h_dec
    exact Eq.mp (congrFun (congrArg (fun P post => SepWP _ _ s_ret P post) (by
      simp only [show (2 : Nat) ^ 52 = 4503599627370496 by decide]; try sep_ac_rfl)) post) hgoal

set_option maxHeartbeats 800000 in
private theorem montgomery_point_to_edwards_raw_ok_of
    (hPow22501 : Fe51Pow22501Ok) (hPow2k : Fe51Pow2kOk)
    (hMul : Fe51MulOk) (hDecomp : CompressedEdwardsYDecompressOk) :
    DalekBlockOk 8 montgomeryPointToEdwardsRawSpec := by
  intro _
  apply dalekCaller_ok dalekCliPC08 dalekCliPl08
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 168 := ‹_›
  have hself_len : a_rest_1.length = 32 := ‹_›
  have hr1_sign : BitVec.zeroExtend 8 (s0.readReg64 (.gpr 1#5)) = a_2 := ‹_›
  haveI hself_ge : HasLenGe a_rest_1 32 := ⟨by omega⟩
  apply sepWP_split_stack_callee 2176 400
  apply sepWP_peel_stack_bytes s0.sp 400 8 392; intro gap0_init hgap0_init
  apply sepWP_peel_stack_bytes s0.sp 392 40 352; intro um1_init hum1_init
  apply sepWP_peel_stack_bytes s0.sp 352 40 312; intro recip_init hrecip_init
  apply sepWP_peel_stack_bytes s0.sp 312 40 272; intro up1_init hup1_init
  apply sepWP_peel_stack_bytes s0.sp 272 40 232; intro c19_init hc19_init
  apply sepWP_peel_stack_bytes s0.sp 232 8 224; intro gap1_init hgap1_init
  apply sepWP_peel_stack_bytes s0.sp 224 32 192; intro ubytes_init hubytes_init
  apply sepWP_peel_stack_bytes s0.sp 192 8 184; intro ubytes_tail_init hubytes_tail_init
  apply sepWP_peel_stack_bytes s0.sp 184 8 176; intro gap2_init hgap2_init
  apply sepWP_peel_stack_bytes s0.sp 176 32 144; intro m1bytes_init hm1bytes_init
  apply sepWP_peel_stack_bytes s0.sp 144 48 96; intro m1tail_init hm1tail_init
  open_cells (s0.sp - 96#64) 96 12
  wp_cut_codeLoaded
  wp_sym_steps 21
  generalize hl0 : ByteSlice.readLE a_rest_1 0 8 &&& 2251799813685247#64 = l0 at *
  generalize hl1 : ByteSlice.readLE a_rest_1 6 8 >>> 3 &&& 2251799813685247#64 = l1 at *
  generalize hl2 : ByteSlice.readLE a_rest_1 12 8 >>> 6 &&& 2251799813685247#64 = l2 at *
  generalize hl3 : ByteSlice.readLE a_rest_1 19 8 >>> 1 &&& 2251799813685247#64 = l3 at *
  generalize hl4 : ByteSlice.readLE a_rest_1 24 8 >>> 12 &&& 2251799813685247#64 = l4 at *
  obtain ⟨hl0_b, hl1_b, hl2_b, hl3_b, hl4_b, hl_val⟩ :=
    fe51_from_bytes_u255 a_rest_1 hself_len l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4
  wp_sym_steps 8
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_pre_u
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl_pre_u
  generalize hq : (l4 + (l3 + (l2 + (l1 + (l0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
  apply mont_to_edwards_pack_u_step b s0.sp hb hbase a_rest_1 ubytes_init l0 l1 l2 l3 l4 q
    (s0 := s0) (hcl := hcl_pre_u) (hubytes_init := hubytes_init)
    (hl0_b := hl0_b) (hl1_b := hl1_b) (hl2_b := hl2_b) (hl3_b := hl3_b) (hl4_b := hl4_b)
    (hl_val := hl_val) (hq := hq)
    (hpc := by simp [arm64_norm]) (hrun := by simp [arm64_norm, ‹s0.status = .Running›])
    (hsp := by simp [arm64_norm])
    (hx8 := by simp [arm64_norm])
    (hx9 := by simp [arm64_norm])
    (hx21 := by simp [arm64_norm])
    (hx22 := by simp [arm64_norm])
    (hx23 := by simp [arm64_norm])
    (hx24 := by simp [arm64_norm])
    (hx25 := by simp [arm64_norm])
    (hx29 := by simp [arm64_norm]; try bv_omega)
    (hvregs := by simp [arm64_norm])
  intro sf_u hpc_u hrun_u hsp_u hx8_u hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u hx24_u hx25_u hx26_u hx27_u hx28_u hx29_u hvregs_u hcl_u
  clear hcl_pre_u
  simp only [arm64_norm] at hx0_u hx19_u hx20_u hx26_u hx27_u hx28_u
  -- Call 1: FieldElement51::to_bytes(&MINUS_ONE) at +0x198 (stack 0)
  obtain ⟨hm1_l, hm1_0, hm1_1, hm1_2, hm1_3, hm1_4⟩ := fe51MinusOneBytes_bounded54
  apply sepWP_callee_shrink (s0.sp - 400#64) 2176 0 2176
  wp_steps
  wp_dalek_call fe51_to_bytes_ro_ok
  rw [hsp_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u, hx24_u, hx25_u, hx26_u, hx27_u, hx28_u, hx29_u, hvregs_u] at *
  clear hm1_l hm1_0 hm1_1 hm1_2 hm1_3 hm1_4
    hpc_u hrun_u hsp_u hx8_u hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u hx24_u hx25_u hx26_u hx27_u hx28_u hx29_u hvregs_u sf_u
  norm_sf 0
  apply sepWP_callee_grow (s0.sp - 400#64) 2176 0 2176
  wp_conv_pre => rw [fe51MinusOneBytes_val]
  -- Step +0x19c .. +0x1a0 to bl ct_eq at +0x1a4 (stack 64)
  have hubytes_len : (natToLeBytes 32 (decodeU255 a_rest_1 % p25519)).length = 32 := by simp [natToLeBytes]
  have hm1bytes_len : (natToLeBytes 32 (p25519 - 1)).length = 32 := by simp [natToLeBytes]
  wp_steps
  apply sepWP_callee_shrink (s0.sp - 400#64) 2176 64 2112
  wp_dalek_call slice32_ct_eq_ok; clean_prev_sf; norm_sf 64
  apply sepWP_callee_grow (s0.sp - 400#64) 2176 64 2112
  have hp_pos : 0 < p25519 := by decide +kernel
  rw [natToLeBytes_32_eq_m1_iff _ (Nat.mod_lt _ hp_pos)] at *
  by_cases hu_m1 : decodeU255 a_rest_1 % p25519 = p25519 - 1
  · -- Branch 1: u == p25519 - 1 -> returns None
    simp only [decide_eq_true hu_m1, ↓reduceIte] at *
    have hbranch := tst_w0_ff_of_trunc8_1 _ ‹_›
    have hmte1 : montToEdwardsIrred a_rest_1 (a_2.toNat % 2) = none := by
      unfold montToEdwardsIrred
      exact montToEdwards_eq_none_of_u_eq_m1 a_rest_1 (a_2.toNat % 2) hu_m1
    rw [hmte1]
    simp only
    wp_conv_pre => rw [pointsToBytes168_split a_1 a_3 hout_len]
    have hdst_len : (a_3.drop 8).length = 160 := by simp [hout_len]
    wp_steps
    close_cells (s0.sp - 96#64) 96 12
    apply sepWP_unpeel_stack_bytes s0.sp 144 48 96 (hbs := hm1tail_init)
    apply sepWP_unpeel_stack_bytes s0.sp 176 32 144 (hbs := hm1bytes_len)
    apply sepWP_unpeel_stack_bytes s0.sp 184 8 176 (hbs := hgap2_init)
    apply sepWP_unpeel_stack_bytes s0.sp 192 8 184 (hbs := hubytes_tail_init)
    apply sepWP_unpeel_stack_bytes s0.sp 224 32 192 (hbs := hubytes_len)
    apply sepWP_unpeel_stack_bytes s0.sp 232 8 224 (hbs := hgap1_init)
    apply sepWP_unpeel_stack_bytes s0.sp 272 40 232 (hbs := hc19_init)
    apply sepWP_unpeel_stack_bytes s0.sp 312 40 272 (hbs := hup1_init)
    apply sepWP_unpeel_stack_bytes s0.sp 352 40 312 (hbs := hrecip_init)
    apply sepWP_unpeel_stack_bytes s0.sp 392 40 352 (hbs := hum1_init)
    apply sepWP_unpeel_stack_bytes s0.sp 400 8 392 (hbs := hgap0_init)
    apply sepWP_merge_stack_callee 2176 400
    wp_done
  · -- Branch 2: u != p25519 - 1 -> computes y = (u - 1) / (u + 1) and decompresses
    simp only [decide_eq_false hu_m1, Bool.false_eq_true, ↓reduceIte] at *
    have hbranch := tst_w0_ff_of_trunc8_0 _ ‹_›
    apply sepWP_merge_bytes_append s0.sp 224 32 192 (hbs1 := hubytes_len)
    apply sepWP_merge_bytes_append s0.sp 176 32 144 (hbs1 := hm1bytes_len)
    have hc3_old_len : (natToLeBytes 32 (decodeU255 a_rest_1 % p25519) ++ ubytes_tail_init).length = 40 := by
      rw [List.length_append, hubytes_len, hubytes_tail_init]
    have hpow_old_len : (natToLeBytes 32 (p25519 - 1) ++ m1tail_init).length = 80 := by
      rw [List.length_append, hm1bytes_len, hm1tail_init]
    generalize natToLeBytes 32 (decodeU255 a_rest_1 % p25519) ++ ubytes_tail_init = c3_old at hc3_old_len ⊢
    haveI hum1_ge : HasLenGe um1_init 40 := ⟨by omega⟩
    haveI hup1_ge : HasLenGe up1_init 40 := ⟨by omega⟩
    wp_cut_codeLoaded
    wp_steps
    apply SepWP.done
    · rfl
    · assumption
    intro hcl_b2
    try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl_b2
    have hl_b54 : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧ l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54 :=
      ⟨by omega, by omega, by omega, by omega, by omega⟩
    apply sepWP_abstract_bytes (s0.sp - 392#64)
      (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧
        fe51ValOfBytes buf % p25519 = fpSub (decodeU255 a_rest_1 % p25519) 1)
    · unfold fe51LimbsBounded fe51ValOfBytes
      simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hum1_init, Nat.min_eq_left]
      refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
      rw [fe51Reduce_val_mod]
      have hsub := fe51Sub_val_mod l0 l1 l2 l3 l4 1#64 0#64 0#64 0#64 0#64 hl_b54
        (B2 := 2 ^ 54) ⟨by decide, by decide, by decide, by decide, by decide⟩
      have hval1 : fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519 = 1 := by decide
      rw [sub1_bias0_eq l0, sub0_bias1_eq l1, sub0_bias1_eq l2, sub0_bias1_eq l3, sub0_bias1_eq l4,
          hsub, hl_val, hval1]
    intro um1_bs ⟨hum1_b, hum1_v⟩
    obtain ⟨hum1_l, hum1_0, hum1_1, hum1_2, hum1_3, hum1_4⟩ := fe51LimbsBounded_of_52 um1_bs hum1_b
    clear hum1_ge um1_init hum1_init
    apply sepWP_abstract_bytes (s0.sp - 312#64)
      (fun buf => buf.length = 40 ∧ fe51LimbsBounded buf (2 ^ 54) ∧
        fe51ValOfBytes buf % p25519 = fpAdd (decodeU255 a_rest_1 % p25519) 1)
    · have hl0_add : (l0 + 1#64).toNat = l0.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      unfold fe51LimbsBounded fe51ValOfBytes fpAdd
      simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hup1_init, Nat.min_eq_left]
      refine ⟨trivial, ⟨trivial, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
      unfold fe51Val at hl_val ⊢
      rw [hl0_add]
      have h_eq : l0.toNat + 1 + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204 =
          decodeU255 a_rest_1 + 1 := by omega
      rw [h_eq, ← Nat.mod_add_mod]
    intro up1_bs ⟨hup1_l, ⟨_, hup1_0, hup1_1, hup1_2, hup1_3, hup1_4⟩, hup1_v⟩
    clear hup1_ge up1_init hup1_init
    -- Call 3: pow22501 at +0x230 (stack 1040)
    apply sepWP_callee_shrink (s0.sp - 400#64) 2176 1040 1136
    wp_dalek_call hPow22501; clean_prev_sf; clear_dead_vars [sf_1]; try clear sf_1; norm_sf 1040
    apply sepWP_callee_grow (s0.sp - 400#64) 2176 1040 1136
    clear hup1_0 hup1_1 hup1_2 hup1_3 hup1_4
    have ht19_b : fe51LimbsBounded w (2 ^ 52) := ‹_›
    have ht3_b : fe51LimbsBounded w_1 (2 ^ 52) := ‹_›
    have ht19_v : fe51ValOfBytes w % p25519 = fpPow (fe51ValOfBytes up1_bs % p25519) (2 ^ 250 - 1) := ‹_›
    have ht3_v : fe51ValOfBytes w_1 % p25519 = fpPow (fe51ValOfBytes up1_bs % p25519) 11 := ‹_›
    apply sepWP_split_bytes_append s0.sp 176 40 136 (hbs1 := ht19_b.1)
    obtain ⟨ht19_l, ht19_0, ht19_1, ht19_2, ht19_3, ht19_4⟩ := fe51LimbsBounded_of_52 w ht19_b
    obtain ⟨ht3_l, ht3_0, ht3_1, ht3_2, ht3_3, ht3_4⟩ := fe51LimbsBounded_of_52 w_1 ht3_b
    haveI hc19_ge : HasLenGe c19_init 40 := ⟨by omega⟩
    haveI hc3_ge : HasLenGe c3_old 40 := ⟨by omega⟩
    wp_cut_codeLoaded
    wp_steps
    apply SepWP.done
    · rfl
    · assumption
    intro hcl_copy
    try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl_copy
    wp_conv_pre =>
      rw [write64_copy5_eq c19_init w hc19_init ht19_l,
          write64_copy5_eq c3_old w_1 hc3_old_len ht3_l]
    -- Call 4: pow2k at +0x268 (stack 96)
    apply sepWP_callee_shrink (s0.sp - 400#64) 2176 96 2080
    wp_dalek_call hPow2k; clean_prev_sf; norm_sf 96
    apply sepWP_callee_grow (s0.sp - 400#64) 2176 96 2080
    clear ht19_0 ht19_1 ht19_2 ht19_3 ht19_4 hc19_ge hc3_ge c19_init hc19_init
    have ht2_5_v : fe51ValOfBytes w_2 % p25519 = fpPow (fe51ValOfBytes w % p25519) (2 ^ (5#32 : BitVec 32).toNat) := ‹_›
    obtain ⟨ht2_5_l, ht2_5_0, ht2_5_1, ht2_5_2, ht2_5_3, ht2_5_4⟩ := fe51LimbsBounded_of_52 w_2 ‹fe51LimbsBounded w_2 _›
    -- Call 5 & 6: mul (recip, y) at +0x278, +0x288 (stack 224)
    apply sepWP_callee_shrink (s0.sp - 400#64) 2176 224 1952
    wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
    clear ht3_0 ht3_1 ht3_2 ht3_3 ht3_4 ht2_5_0 ht2_5_1 ht2_5_2 ht2_5_3 ht2_5_4 recip_init hrecip_init
    have hrec_v : fe51ValOfBytes w_3 % p25519 = (fe51ValOfBytes w_2 * fe51ValOfBytes w_1) % p25519 := ‹_›
    obtain ⟨hrec_l, hrec_0, hrec_1, hrec_2, hrec_3, hrec_4⟩ := fe51LimbsBounded_of_52 w_3 ‹fe51LimbsBounded w_3 _›
    wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
    apply sepWP_callee_grow (s0.sp - 400#64) 2176 224 1952
    clear hum1_0 hum1_1 hum1_2 hum1_3 hum1_4 hrec_0 hrec_1 hrec_2 hrec_3 hrec_4
    have hres_v : fe51ValOfBytes w_4 % p25519 = (fe51ValOfBytes um1_bs * fe51ValOfBytes w_3) % p25519 := ‹_›
    have hw4_b : fe51LimbsBounded w_4 (2 ^ 52) := ‹_›
    have hw4_len : w_4.length = 40 := hw4_b.1
    have hw1_drop_l : (w_1.drop 32).length = 8 := by simp [ht3_l]
    have hy_val := to_edwards_y_of_muls (decodeU255 a_rest_1 % p25519)
      um1_bs up1_bs w w_1 w_2 w_3 w_4 hum1_v hup1_v ht19_v ht3_v ht2_5_v hrec_v hres_v
    apply mont_to_edwards_pack_y_step b s0.sp a_1 hb hbase a_2 w_4 w_1
      (s0 := s0) (hcl := ‹_›) (hw4_b := hw4_b) (hw1_l := ht3_l)
      (hpc := ‹_›) (hrun := ‹_›) (hsp := ‹_›)
      (hx19 := ‹_›) (hx20 := ‹_›) (hr1 := hr1_sign)
      (hx26 := ‹_›) (hx27 := ‹_›) (hx29 := ‹_›) (hvregs := ‹_›)
    intro sf_p hpc_p hrun_p hsp_p hx8_p hx0_p hx27_p hvregs_p hcl_p
    clear_dead_vars [sf, sf_1]; try clear sf; try clear sf_1
    apply sepWP_abstract_bytes (s0.sp - 224#64)
      (fun y_enc => y_enc.length = 32 ∧
        decodeEdDalek y_enc = montToEdwardsIrred a_rest_1 (a_2.toNat % 2))
    · refine ⟨setByte31Or_natToLeBytes32_len _ a_2, ?_⟩
      unfold montToEdwardsIrred
      exact decodeEdDalek_eq_montToEdwards_of_ne_m1 a_rest_1 a_2 (fe51ValOfBytes w_4 % p25519)
        hu_m1 (Nat.mod_lt _ (by decide +kernel)) hy_val
    intro y_enc ⟨hy_enc_len, hdec_irred⟩
    clear hy_val
    apply mont_to_edwards_decompress_epilogue_step b hb hbase s0 sf_p hDecomp hcl_p a_1 a_3 y_enc w_4
      (h_4 := hout_len) (hy_enc_len := hy_enc_len) (hb400 := hgap0_init) (hb392 := hum1_l) (hb352 := hrec_l)
      (hb312 := hup1_l) (hb272 := ht19_l) (hb232 := hgap1_init)
      (hb192 := hw1_drop_l) (hb184 := hgap2_init) (hw4_len := hw4_len) (hb136 := ht3_l)
      (hpc_p := hpc_p) (hrun_p := hrun_p) (hsp_p := hsp_p) (h_sp_align := hsp_align)
      (hx8_p := hx8_p) (hx0_p := hx0_p) (hx27_p := hx27_p) (hvregs_p := hvregs_p)
    · intro s_ret hpc_r hrun_r hsp_r hcs_r h_dec
      clear_dead_vars [sf_p]; try clear sf_p
      have h_mte : montToEdwardsIrred a_rest_1 (a_2.toNat % 2) = none :=
        hdec_irred.symm.trans h_dec
      rw [h_mte]; dsimp only; wp_pull_exists; wp_done
    · intro s_ret P hpc_r hrun_r hsp_r hcs_r h_dec
      clear_dead_vars [sf_p]; try clear sf_p
      have h_mte : montToEdwardsIrred a_rest_1 (a_2.toNat % 2) = some P :=
        hdec_irred.symm.trans h_dec
      rw [h_mte]; dsimp only; wp_pull_exists; wp_focus_pure
      rintro ⟨⟨hpt_l, ⟨hpt0_0, hpt0_1, hpt0_2, hpt0_3, hpt0_4⟩,
        ⟨hpt1_0, hpt1_1, hpt1_2, hpt1_3, hpt1_4⟩, ⟨hpt2_0, hpt2_1, hpt2_2, hpt2_3, hpt2_4⟩,
        ⟨hpt3_0, hpt3_1, hpt3_2, hpt3_3, hpt3_4⟩⟩, hpt_eq⟩
      wp_done

public section

theorem montgomery_point_to_edwards_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk) (hPow2k : Fe51Pow2kOk)
    (hToBytes : Fe51ToBytesOk) (hPow22501 : Fe51Pow22501Ok)
    (hDecomp : CompressedEdwardsYDecompressOk) :
    MontgomeryPointToEdwardsOk := by
  have _ : Fe51MulRoRightOk := hMulRo
  have _ : Fe51ToBytesOk := hToBytes
  intro inst
  letI := inst
  rw [montgomeryPointToEdwardsSpec_eq]
  exact montgomery_point_to_edwards_raw_ok_of hPow22501 hPow2k hMul hDecomp

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MontToEdwards
