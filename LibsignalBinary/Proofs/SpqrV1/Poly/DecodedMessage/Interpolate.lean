/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Inlined `lagrange_interpolate` Loops and Cleanup

Proves the inner accumulation loop (`0x6bf64..0x6bf8c`), outer interpolation loop
(`0x6bf2c..0x6bff0`), temporary-buffer cleanup, cache-slot store (`0x6bff0..0x6c084`), and cache-hit
path of the inlined `Poly::lagrange_interpolate` block in `decoded_message`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName LagrangePrepareArgs lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.ComputeAt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.sp_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg64_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg32_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg_setMem_setPC_pre

theorem gf16SliceAt_to_memRegion (ptr : BitVec 64) (cs : List GF16) :
    gf16SliceAt ptr cs ⊢ memRegion ptr (2 * cs.length) := by
  rw [gf16SliceAt_eq_pointsToBytes cs ptr, ← gf16ListBytes_length cs]
  exact pointsToBytes_entails_memRegion ptr (gf16ListBytes cs)

theorem bv64_eq_succ_false (k j : Nat) (hjk : j < k) (hk : k ≤ 65536) :
    (BitVec.ofNat 64 (k + 1) == BitVec.ofNat 64 (j + 1)) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  omega

@[local wp_norm, local arm64_norm]
theorem bv64_lsl1_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  change (n % 18446744073709551616 * 2) % 18446744073709551616 = (2 * n) % 18446744073709551616
  rw [Nat.mod_mul_mod, Nat.mul_comm]

@[local wp_norm, local arm64_norm]
theorem bv64_add1_norm (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

theorem bv64_neg_add_succ_bne_one (k j : Nat) (hjk : j < k) (hk : k ≤ 65536) :
    (-BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1 + 1) != 1#64) = decide (j + 1 ≠ k) := by
  have h0 : -BitVec.ofNat 64 k = 0#64 - BitVec.ofNat 64 k := (BitVec.zero_sub _).symm
  have h1 : -BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1 + 1) =
      BitVec.ofNat 64 ((2 ^ 64 - k) + (j + 2)) := by
    rw [h0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  by_cases hjeq : j + 1 = k
  · have heq : -BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1 + 1) = 1#64 := by
      rw [h1]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [bne_eq_false_iff_eq.mpr heq, eq_comm, decide_eq_false_iff_not, not_not]
    exact hjeq
  · have hne : -BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1 + 1) ≠ 1#64 := by
      rw [h1]
      intro heq
      have h2 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
      omega
    rw [bne_iff_ne.mpr hne, eq_comm, decide_eq_true_eq]
    exact hjeq

theorem gf16_add_comm (a b : GF16) : a.add b = b.add a := by
  cases a with | mk va =>
  cases b with | mk vb =>
  unfold GF16.add
  congr 1
  exact BitVec.xor_comm va vb

@[local wp_norm, local arm64_norm]
theorem bv32_xor_gf16 (a b : GF16) :
    BitVec.truncate 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 a.value ^^^ BitVec.zeroExtend 64 b.value)) =
      (GF16.add b a).value := by
  unfold GF16.add
  ext idx hidx
  simp [hidx, Bool.xor_comm]

/-! ## Inner Accumulation Loop (`0x6bf64..0x6bf8c`, `+996..+1036`) -/

theorem memcpy_gf16Slice_pre (ptr_l ptr_b : BitVec 64) (w b_cs : List GF16)
    (hlen : w.length = b_cs.length) (Rest : SepProp) :
    gf16SliceAt ptr_l w ∗ gf16SliceAt ptr_b b_cs ∗ Rest ⊢
      memRegion ptr_l (gf16ListBytes b_cs).length ∗
        (ptr_b ↦ₛ gf16ListBytes b_cs) ∗ Rest := by
  rw [gf16ListBytes_length, ← hlen, ← gf16SliceAt_eq_pointsToBytes b_cs ptr_b]
  exact sepConj_mono_left (gf16SliceAt_to_memRegion ptr_l w)

theorem toNat_two_mul_succ_eq_gf16ListBytes (k : Nat) (b_cs : List GF16)
    (hk : k ≤ 65536) (hb_len : b_cs.length = k + 1) :
    (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_cs).length := by
  rw [gf16ListBytes_length, hb_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv64_succ_bne_of_le (i k : Nat) (hi : i < k) (hk : k ≤ 65536) :
    (BitVec.ofNat 64 (i + 1) != BitVec.ofNat 64 k) = decide (i + 1 ≠ k) := by
  by_cases heq : i + 1 = k
  · simp [heq]
  · have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 k := by
      intro h
      have h1 := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      omega
    rw [bne_iff_ne.mpr hne, decide_eq_true heq]

theorem gf16Slice_spare_to_memRegion (ptr : BitVec 64) (cs : List GF16) (cap : Nat)
    (hle : cs.length ≤ cap) (hcap : cap * 2 < 2 ^ 63) (Rest : SepProp) :
    gf16SliceAt ptr cs ∗
      memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap - cs.length) * 2) ∗ Rest ⊢
      memRegion ptr (cap * 2) ∗ Rest := by
  have h1 : gf16SliceAt ptr cs ⊢ memRegion ptr (cs.length * 2) := by
    rw [Nat.mul_comm]
    exact gf16SliceAt_to_memRegion ptr cs
  have h2 : memRegion ptr (cs.length * 2) ∗
      memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap - cs.length) * 2) =
      memRegion ptr (cap * 2) := by
    rw [← memRegion_split ptr (cs.length * 2) ((cap - cs.length) * 2) (by omega),
      show cs.length * 2 + (cap - cs.length) * 2 = cap * 2 by omega]
  rw [← sepConj_assoc, ← h2]
  exact sepConj_mono_left (sepConj_mono_left h1)

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_120 (sp0 : BitVec 64) : sp0 - 96#64 - 120#64 = sp0 - 216#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_96 (sp0 : BitVec 64) : sp0 - 96#64 - 96#64 = sp0 - 192#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_80 (sp0 : BitVec 64) : sp0 - 96#64 - 80#64 = sp0 - 176#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_72 (sp0 : BitVec 64) : sp0 - 96#64 - 72#64 = sp0 - 168#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_64 (sp0 : BitVec 64) : sp0 - 96#64 - 64#64 = sp0 - 160#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_56 (sp0 : BitVec 64) : sp0 - 96#64 - 56#64 = sp0 - 152#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_48 (sp0 : BitVec 64) : sp0 - 96#64 - 48#64 = sp0 - 144#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_40 (sp0 : BitVec 64) : sp0 - 96#64 - 40#64 = sp0 - 136#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub_32 (sp0 : BitVec 64) : sp0 - 96#64 - 32#64 = sp0 - 128#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp216_add_48 (sp0 : BitVec 64) : sp0 - 216#64 + 48#64 = sp0 - 168#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp192_add_8 (sp0 : BitVec 64) : sp0 - 192#64 + 8#64 = sp0 - 184#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp168_add_8 (sp0 : BitVec 64) : sp0 - 168#64 + 8#64 = sp0 - 160#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp144_add_8 (sp0 : BitVec 64) : sp0 - 144#64 + 8#64 = sp0 - 136#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp144_add_16 (sp0 : BitVec 64) : sp0 - 144#64 + 16#64 = sp0 - 128#64 := by bv_omega

theorem bv64_add_one_beq_zero_false {k : Nat} (hk : k ≤ 65536) :
    (BitVec.ofNat 64 k + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h1
  change k + 1 = 0 at h1
  omega

theorem fold_optPolyCacheSlotAt_some (A : RustAlloc) (v acc_ptr : BitVec 64)
    (outCoeffs : List GF16) (k : Nat)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536) (hlen : outCoeffs.length = k)
    (hptr : acc_ptr ≠ 0#64) (Rest : SepProp) :
    (v ↦₆₄ BitVec.ofNat 64 k) ∗
      ((v + 8#64) ↦₆₄ acc_ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 k) ∗
      A.live acc_ptr (2 * k) 2 ∗
      gf16SliceAt acc_ptr outCoeffs ∗ Rest ⊢
      optPolyCacheSlotAt A v (some ⟨outCoeffs⟩) ∗ Rest := by
  rw [show (v ↦₆₄ BitVec.ofNat 64 k) ∗ ((v + 8#64) ↦₆₄ acc_ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 k) ∗ A.live acc_ptr (2 * k) 2 ∗
        gf16SliceAt acc_ptr outCoeffs ∗ Rest =
      ((v ↦₆₄ BitVec.ofNat 64 k) ∗ ((v + 8#64) ↦₆₄ acc_ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 k) ∗ A.live acc_ptr (2 * k) 2 ∗
        gf16SliceAt acc_ptr outCoeffs) ∗ Rest by ac_rfl]
  apply sepConj_mono_left
  unfold optPolyCacheSlotAt
  apply Entails.sepExists_right acc_ptr
  simp only [hlen]
  exact Entails.pure_right ⟨hk_pos, hk_le, hptr⟩ (Entails.of_eq (by ac_rfl))

@[local arm64_norm, local wp_norm]
theorem umaddl_24_ofNat (base : BitVec 64) (i : Nat) :
    base + ((BitVec.ofNat 64 i).setWidth 32).zeroExtend 64 * 24#64 =
      base + BitVec.ofNat 64 (24 * (i % 4294967296)) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h1 : (((BitVec.ofNat 64 i).setWidth 32).zeroExtend 64).toNat = i % 4294967296 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have h2 : (24#64 : BitVec 64).toNat = 24 := rfl
  rw [BitVec.toNat_mul, h1, h2, BitVec.toNat_ofNat]
  omega

theorem memcpy_memRegion_gf16Slice_pre (dst src : BitVec 64) (b_cs : List GF16)
    (n : Nat) (hn : n = 2 * b_cs.length) (Rest : SepProp) :
    memRegion dst n ∗ gf16SliceAt src b_cs ∗ Rest =
      memRegion dst (gf16ListBytes b_cs).length ∗
        (src ↦ₛ gf16ListBytes b_cs) ∗ Rest := by
  rw [gf16ListBytes_length, hn, gf16SliceAt_eq_pointsToBytes]

theorem toNat_two_mul_eq_gf16ListBytes (k : Nat) (cs : List GF16)
    (hk : k ≤ 65536) (hlen : cs.length = k) :
    (BitVec.ofNat 64 (2 * k)).toNat = (gf16ListBytes cs).length := by
  rw [gf16ListBytes_length, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end CryptoVerification.SpqrV1.Poly.DecodedMessage

