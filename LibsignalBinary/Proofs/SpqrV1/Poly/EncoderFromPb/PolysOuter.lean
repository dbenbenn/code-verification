/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: `.polys` Outer Loop

**Checked by Lean.**

Proves empty / odd-length error branches (`+1204 → +1496`), even-slice buffer allocation and `GF16`
deserialization (`+1204..+1356`), old-buffer deallocation + unaligned header store
(`+1356 → +1204 / +1548`), and 16-slot outer-loop induction (`polys_outer_loop`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  ofNat_succ_sub_one ofNat_succ_add_neg_one zeroExtend_setWidth32_setWidth8
  add_neg_64_eq_sub_64 add_neg_48_eq_sub_48 add_neg_32_eq_sub_32
  add_neg_24_eq_sub_24 add_neg_16_eq_sub_16
  fsp_928_sub_64 fsp_928_sub_48 fsp_928_sub_32 fsp_928_sub_24 fsp_928_sub_16

@[local arm64_norm, local wp_norm]
theorem fsp_896_add_9 (fsp : BitVec 64) :
    fsp + 896#64 + 9#64 = fsp + 905#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_896_add_16 (fsp : BitVec 64) :
    fsp + 896#64 + 16#64 = fsp + 912#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_864_add_7 (fsp : BitVec 64) :
    fsp + 864#64 + 7#64 = fsp + 871#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_864_add_23 (fsp : BitVec 64) :
    fsp + 864#64 + 23#64 = fsp + 887#64 := by bv_omega

theorem cmn_one_ne_zero {m : Nat} (hm : m + 1 < 2 ^ 63) :
    (BitVec.ofNat 64 (m + 1) + 1#64 == 0#64) = false := by
  rw [← BitVec.ofNat_add]
  exact ofNat_beq_zero_false_of_pos (by omega) (by omega)

theorem cmn_one_bne_zero {m : Nat} (hm : m + 1 < 2 ^ 63) :
    (BitVec.ofNat 64 (m + 1) + 1#64 != 0#64) = true := by
  rw [bne_iff_ne, ← BitVec.ofNat_add]
  exact ofNat_ne_zero_of_pos (by omega) (by omega)

theorem neg_one_beq_false {m : Nat} (hm : m + 1 < 2 ^ 63) :
    (BitVec.ofNat 64 (m + 1) == 18446744073709551615#64) = false := by
  apply beq_false_of_ne
  intro heq
  have ht := congrArg BitVec.toNat heq
  have hm64 : m + 1 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at ht
  omega

theorem neg_one_beq_false' {m : Nat} (hm : m + 1 < 2 ^ 63) :
    (18446744073709551615#64 == BitVec.ofNat 64 (m + 1)) = false := by
  rw [ Bool.beq_comm ]
  exact neg_one_beq_false hm

theorem bit0_and_32_eq_zero_of_even_63 {n : Nat} (heven : n % 2 = 0) (hn : n < 2 ^ 63) :
    (((BitVec.ofNat 64 n).setWidth 32).zeroExtend 64 &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hmod64 : n % 2 ^ 32 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hmod64]
  change (n % 2 ^ 32) &&& (2 ^ 1 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_32_eq_one_of_odd_63 {n : Nat} (hodd : n % 2 ≠ 0) (hn : n < 2 ^ 63) :
    (((BitVec.ofNat 64 n).setWidth 32).zeroExtend 64 &&& 1#64) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hmod64 : n % 2 ^ 32 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hmod64]
  change (n % 2 ^ 32) &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_64_eq_zero_of_even_63 {n : Nat} (heven : n % 2 = 0) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  change n &&& (2 ^ 1 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_64_eq_one_of_odd_63 {n : Nat} (hodd : n % 2 ≠ 0) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n &&& 1#64) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  change n &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shiftRight_1_nat_eq_div_2_63 {n : Nat} (hn : n < 2 ^ 63) :
    BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hdiv64 : n / 2 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64,
    Nat.mod_eq_of_lt hdiv64, Nat.shiftRight_eq_div_pow]

theorem shiftRight_1_eq_div_2_63 {n : Nat} (hn : n < 2 ^ 63) :
    BitVec.ofNat 64 n >>> 1#64 = BitVec.ofNat 64 (n / 2) :=
  shiftRight_1_nat_eq_div_2_63 hn

theorem vecU8Rest_entails_len_lt (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Rest A a cap ptr bs ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ vecU8Rest A a cap ptr bs := by
  unfold vecU8Rest
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.refl _))

/-! ## Error Steps (`+1204 -> +1496`, `0x4b4 -> 0x5d8`) -/

attribute [local arm64_norm, local wp_norm] madd_24_eq mul_24_eq

theorem fsp_904_split_at_1_rest (fsp v0 v1 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ v0) ∗ ((fsp + 912#64) ↦₆₄ v1) ∗ Rest =
      ((fsp + 904#64) ↦₈ v0.extractLsb' 0 8) ∗
      ((fsp + 905#64) ↦₆₄ midWord1 v0 v1) ∗
      ((fsp + 913#64) ↦ₛ tailBytes7 v1) ∗ Rest := by
  rw [← sepConj_assoc, fsp_904_split_at_1 fsp v0 v1, sepConj_assoc, sepConj_assoc]

theorem fsp_864_split_at_7_rest (fsp u0 u1 : BitVec 64) (Rest : SepProp) :
    ((fsp + 864#64) ↦₆₄ u0) ∗ ((fsp + 872#64) ↦₆₄ u1) ∗ Rest =
      ((fsp + 864#64) ↦ₛ headBytes7 u0) ∗
      ((fsp + 871#64) ↦₆₄ midWord7 u0 u1) ∗
      ((fsp + 879#64) ↦₈ u1.extractLsb' 56 8) ∗ Rest := by
  rw [← sepConj_assoc, fsp_864_split_at_7 fsp u0 u1, sepConj_assoc, sepConj_assoc]

theorem fsp_864_after_write_rest (fsp outPtr len : BitVec 64) (b15 : BitVec 8) (Rest : SepProp) :
    ((fsp + 864#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
    ((fsp + 871#64) ↦₆₄ len) ∗
    ((fsp + 879#64) ↦₈ b15) ∗ Rest =
      ((fsp + 864#64) ↦₆₄ midWord1 outPtr len) ∗
      ((fsp + 872#64) ↦₆₄ shiftedWord7 len b15) ∗ Rest := by
  rw [show ((fsp + 864#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
      ((fsp + 871#64) ↦₆₄ len) ∗ ((fsp + 879#64) ↦₈ b15) ∗ Rest =
    (((fsp + 864#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
      ((fsp + 871#64) ↦₆₄ len) ∗ ((fsp + 879#64) ↦₈ b15)) ∗ Rest by ac_rfl,
    fsp_864_after_write fsp outPtr len b15, sepConj_assoc]

theorem fsp_880_split_at_7_rest (fsp u0 u1 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ u0) ∗ ((fsp + 888#64) ↦₆₄ u1) ∗ Rest =
      ((fsp + 880#64) ↦ₛ headBytes7 u0) ∗
      ((fsp + 887#64) ↦₆₄ midWord7 u0 u1) ∗
      ((fsp + 895#64) ↦₈ u1.extractLsb' 56 8) ∗ Rest := by
  rw [← sepConj_assoc, fsp_880_split_at_7 fsp u0 u1, sepConj_assoc, sepConj_assoc]

theorem fsp_880_after_write_rest (fsp outPtr len : BitVec 64) (b15 : BitVec 8) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
    ((fsp + 887#64) ↦₆₄ len) ∗
    ((fsp + 895#64) ↦₈ b15) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ midWord1 outPtr len) ∗
      ((fsp + 888#64) ↦₆₄ shiftedWord7 len b15) ∗ Rest := by
  rw [show ((fsp + 880#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
      ((fsp + 887#64) ↦₆₄ len) ∗ ((fsp + 895#64) ↦₈ b15) ∗ Rest =
    (((fsp + 880#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
      ((fsp + 887#64) ↦₆₄ len) ∗ ((fsp + 895#64) ↦₈ b15)) ∗ Rest by ac_rfl,
    fsp_880_after_write fsp outPtr len b15, sepConj_assoc]

theorem slot_split_at_1_rest (slotAddr v0 v1 : BitVec 64) (Rest : SepProp) :
    ((slotAddr + 8#64) ↦₆₄ v0) ∗ ((slotAddr + 16#64) ↦₆₄ v1) ∗ Rest =
      ((slotAddr + 8#64) ↦₈ v0.extractLsb' 0 8) ∗
      ((slotAddr + 9#64) ↦₆₄ midWord1 v0 v1) ∗
      ((slotAddr + 17#64) ↦ₛ tailBytes7 v1) ∗ Rest := by
  rw [← sepConj_assoc, slot_split_at_1 slotAddr v0 v1, sepConj_assoc, sepConj_assoc]

theorem slot_after_write_rest (slotAddr outPtr len old1 : BitVec 64) (Rest : SepProp) :
    ((slotAddr + 8#64) ↦₈ outPtr.extractLsb' 0 8) ∗
    ((slotAddr + 9#64) ↦₆₄ midWord1 outPtr len) ∗
    ((slotAddr + 17#64) ↦ₛ tailBytes7 old1) ∗ Rest =
      ((slotAddr + 8#64) ↦₆₄ outPtr) ∗
      ((slotAddr + 16#64) ↦₆₄ replaceLowByte64 (len.extractLsb' 0 8) old1) ∗ Rest := by
  rw [show ((slotAddr + 8#64) ↦₈ outPtr.extractLsb' 0 8) ∗
      ((slotAddr + 9#64) ↦₆₄ midWord1 outPtr len) ∗ ((slotAddr + 17#64) ↦ₛ tailBytes7 old1) ∗ Rest =
    (((slotAddr + 8#64) ↦₈ outPtr.extractLsb' 0 8) ∗
      ((slotAddr + 9#64) ↦₆₄ midWord1 outPtr len) ∗ ((slotAddr + 17#64) ↦ₛ tailBytes7 old1)) ∗ Rest by ac_rfl,
    slot_after_write slotAddr outPtr len old1, sepConj_assoc]

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
