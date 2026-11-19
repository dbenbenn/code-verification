/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: `.polys` Initialization and Inner Loop

**Checked by Lean.**

Proves unaligned 15-byte header-copy bridges, 16-slot `Poly::zero()` initialization (`+556..+1204`),
and the inner `GF16` big-endian deserialization loop (`+1308..+1356`) of `<PolyEncoder>::from_pb`.
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
  ofNat_succ_sub_one ofNat_succ_add_neg_one

@[local arm64_norm, local wp_norm]
theorem zeroExtend_setWidth32_setWidth8 (b0 : BitVec 8) :
    (((b0.zeroExtend 64).setWidth 32).setWidth 8) = b0 := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem add_neg_64_eq_sub_64 (x : BitVec 64) :
    x + 18446744073709551552#64 = x - 64#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_48_eq_sub_48 (x : BitVec 64) :
    x + 18446744073709551568#64 = x - 48#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_32_eq_sub_32 (x : BitVec 64) :
    x + 18446744073709551584#64 = x - 32#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_24_eq_sub_24 (x : BitVec 64) :
    x + 18446744073709551592#64 = x - 24#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_16_eq_sub_16 (x : BitVec 64) :
    x + 18446744073709551600#64 = x - 16#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_64 (fsp : BitVec 64) :
    fsp + 928#64 - 64#64 = fsp + 864#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_48 (fsp : BitVec 64) :
    fsp + 928#64 - 48#64 = fsp + 880#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_32 (fsp : BitVec 64) :
    fsp + 928#64 - 32#64 = fsp + 896#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_24 (fsp : BitVec 64) :
    fsp + 928#64 - 24#64 = fsp + 904#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_16 (fsp : BitVec 64) :
    fsp + 928#64 - 16#64 = fsp + 912#64 := by bv_omega

/-! ## `zeroPolySlotAt` and `zeroPolySlotsAt` (`Poly::zero()` Slots) -/

/-- One initialized `Poly::zero()` slot (`cap = 1, ptr = p, len = 0`, with a live 2-byte allocation). -/
@[expose] def zeroPolySlotAt (A : RustAlloc) (addr : BitVec 64) : SepProp :=
  ∃∗ ptr,
    ⌜ptr ≠ 0#64⌝ ∗
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
    A.live ptr 2 2 ∗ memRegion ptr 2

/-- `n` contiguous `zeroPolySlotAt` headers starting at `base` with stride 24. -/
@[expose] def zeroPolySlotsAt (A : RustAlloc) (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => zeroPolySlotAt A base ∗ zeroPolySlotsAt A (base + 24#64) n

theorem zeroPolySlotAt_intro (A : RustAlloc) (addr ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr 2 2 ∗ memRegion ptr 2 ⊢
      zeroPolySlotAt A addr := by
  unfold zeroPolySlotAt
  refine Entails.sepExists_right ptr ?_
  exact Entails.pure_right hptr (Entails.of_eq (by ac_rfl))

theorem zeroPolySlotAt_entails_vecGF16Of (A : RustAlloc) (addr : BitVec 64) :
    zeroPolySlotAt A addr ⊢ vecGF16Of A addr [] := by
  unfold zeroPolySlotAt vecGF16Of vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro hptr
  refine Entails.sepExists_right 1#64 (Entails.sepExists_right ptr ?_)
  have h1_ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hp : ([] : List GF16).length ≤ (1#64 : BitVec 64).toNat ∧
      (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0 := ⟨by decide, by decide, hptr⟩
  simp only [BitVec.ofNat_eq_ofNat, h1_ne, ↓reduceIte, h1_toNat, List.length_nil, Nat.zero_mul,
    Nat.sub_zero, Nat.one_mul, BitVec.add_zero, arrayAt, emp_sepConj]
  simp only [sepConj_pure_left_comm]
  refine Entails.pure_right hp ?_
  exact Entails.of_eq (by ac_rfl)

theorem zeroPolySlotsAt_entails_vecGF16ListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      zeroPolySlotsAt A base n ⊢ vecGF16ListOf A base (List.replicate n [])
  | 0, base => by
    simp [zeroPolySlotsAt, vecGF16ListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    simp only [zeroPolySlotsAt, List.replicate_succ, vecGF16ListOf, arrayAt, vecHeaderBytes,
      BitVec.ofNat_eq_ofNat]
    exact sepConj_mono (zeroPolySlotAt_entails_vecGF16Of A base)
      (zeroPolySlotsAt_entails_vecGF16ListOf A n (base + 24#64))

/-! ## Unaligned 15-Byte Header Copy Bridges (`pair64_split_at_1`, `pair64_split_at_7`) -/

/-- 64-bit word formed by bytes `1..7` of `v0` followed by byte `0` of `v1`. -/
@[expose] def midWord1 (v0 v1 : BitVec 64) : BitVec 64 :=
  pack64 (v0.extractLsb' 8 8) (v0.extractLsb' 16 8) (v0.extractLsb' 24 8)
    (v0.extractLsb' 32 8) (v0.extractLsb' 40 8) (v0.extractLsb' 48 8)
    (v0.extractLsb' 56 8) (v1.extractLsb' 0 8)

/-- Trailing 7 bytes (`1..7`) of `v1`. -/
@[expose] def tailBytes7 (v1 : BitVec 64) : List (BitVec 8) :=
  [v1.extractLsb' 8 8, v1.extractLsb' 16 8, v1.extractLsb' 24 8,
   v1.extractLsb' 32 8, v1.extractLsb' 40 8, v1.extractLsb' 48 8,
   v1.extractLsb' 56 8]

/-- Replace byte `0` of `v1` with `b0`. -/
@[expose] def replaceLowByte64 (b0 : BitVec 8) (v1 : BitVec 64) : BitVec 64 :=
  pack64 b0 (v1.extractLsb' 8 8) (v1.extractLsb' 16 8) (v1.extractLsb' 24 8)
    (v1.extractLsb' 32 8) (v1.extractLsb' 40 8) (v1.extractLsb' 48 8)
    (v1.extractLsb' 56 8)

/-- Leading 7 bytes (`0..6`) of `u0`. -/
@[expose] def headBytes7 (u0 : BitVec 64) : List (BitVec 8) :=
  [u0.extractLsb' 0 8, u0.extractLsb' 8 8, u0.extractLsb' 16 8,
   u0.extractLsb' 24 8, u0.extractLsb' 32 8, u0.extractLsb' 40 8,
   u0.extractLsb' 48 8]

/-- 64-bit word at offset `+7` spanning byte `7` of `u0` and bytes `0..6` of `u1`. -/
@[expose] def midWord7 (u0 u1 : BitVec 64) : BitVec 64 :=
  pack64 (u0.extractLsb' 56 8)
    (u1.extractLsb' 0 8) (u1.extractLsb' 8 8) (u1.extractLsb' 16 8)
    (u1.extractLsb' 24 8) (u1.extractLsb' 32 8) (u1.extractLsb' 40 8)
    (u1.extractLsb' 48 8)

/-- Second 64-bit word formed after writing `len` at offset `+7` with trailing byte `b15`. -/
@[expose] def shiftedWord7 (len : BitVec 64) (b15 : BitVec 8) : BitVec 64 :=
  pack64 (len.extractLsb' 8 8) (len.extractLsb' 16 8) (len.extractLsb' 24 8)
    (len.extractLsb' 32 8) (len.extractLsb' 40 8) (len.extractLsb' 48 8)
    (len.extractLsb' 56 8) b15

theorem extractLsb_0_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 = b0 := by unfold pack64; bv_bits
theorem extractLsb_8_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 = b1 := by unfold pack64; bv_bits
theorem extractLsb_16_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 = b2 := by unfold pack64; bv_bits
theorem extractLsb_24_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 = b3 := by unfold pack64; bv_bits
theorem extractLsb_32_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 = b4 := by unfold pack64; bv_bits
theorem extractLsb_40_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 = b5 := by unfold pack64; bv_bits
theorem extractLsb_48_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 = b6 := by unfold pack64; bv_bits
theorem extractLsb_56_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 = b7 := by unfold pack64; bv_bits

theorem pack64_extractLsb' (v : BitVec 64) :
    pack64 (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8)
      (v.extractLsb' 24 8) (v.extractLsb' 32 8) (v.extractLsb' 40 8)
      (v.extractLsb' 48 8) (v.extractLsb' 56 8) = v := by
  unfold pack64; bv_bits

theorem pair64_split_at_1 (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) =
      ((a ↦₈ v0.extractLsb' 0 8) ∗
       ((a + 1#64) ↦₆₄ midWord1 v0 v1) ∗
       ((a + 9#64) ↦ₛ tailBytes7 v1)) := by
  have hu0 : a + BitVec.ofNat 64 (unpack64 v0).length = a + 8#64 := rfl
  rw [pointsTo64_eq_pointsToBytes a v0, pointsTo64_eq_pointsToBytes (a + 8#64) v1,
      ← hu0, ← pointsToBytes_append a (unpack64 v0) (unpack64 v1),
      ← pointsToBytes_singleton a (v0.extractLsb' 0 8),
      pointsTo64_eq_pointsToBytes (a + 1#64) (midWord1 v0 v1),
      midWord1, pack64, unpack64_pack64]
  have h9 : a + 1#64 + BitVec.ofNat 64 ([v0.extractLsb' 8 8, v0.extractLsb' 16 8, v0.extractLsb' 24 8,
    v0.extractLsb' 32 8, v0.extractLsb' 40 8, v0.extractLsb' 48 8,
    v0.extractLsb' 56 8, v1.extractLsb' 0 8] : List (BitVec 8)).length = a + 9#64 := by
    change a + 1#64 + 8#64 = a + 9#64
    bv_omega
  rw [← h9, ← pointsToBytes_append (a + 1#64)]
  have ha1 : a + BitVec.ofNat 64 ([v0.extractLsb' 0 8] : List (BitVec 8)).length = a + 1#64 := rfl
  rw [← ha1, ← pointsToBytes_append a]
  rfl

theorem midWord1_replaceLowByte64 (outPtr len old1 : BitVec 64) :
    midWord1 outPtr (replaceLowByte64 (len.extractLsb' 0 8) old1) = midWord1 outPtr len := by
  simp only [midWord1, replaceLowByte64, extractLsb_0_pack64]

theorem tailBytes7_replaceLowByte64 (b0 : BitVec 8) (old1 : BitVec 64) :
    tailBytes7 (replaceLowByte64 b0 old1) = tailBytes7 old1 := by
  simp only [tailBytes7, replaceLowByte64, extractLsb_8_pack64, extractLsb_16_pack64,
    extractLsb_24_pack64, extractLsb_32_pack64, extractLsb_40_pack64,
    extractLsb_48_pack64, extractLsb_56_pack64]

theorem split_at_1_after_write (a outPtr len old1 : BitVec 64) :
    ((a ↦₈ outPtr.extractLsb' 0 8) ∗
     ((a + 1#64) ↦₆₄ midWord1 outPtr len) ∗
     ((a + 9#64) ↦ₛ tailBytes7 old1)) =
      ((a ↦₆₄ outPtr) ∗
       ((a + 8#64) ↦₆₄ replaceLowByte64 (len.extractLsb' 0 8) old1)) := by
  rw [pair64_split_at_1 a outPtr (replaceLowByte64 (len.extractLsb' 0 8) old1),
      midWord1_replaceLowByte64, tailBytes7_replaceLowByte64]

theorem pair64_split_at_7 (b u0 u1 : BitVec 64) :
    ((b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u1)) =
      ((b ↦ₛ headBytes7 u0) ∗
       ((b + 7#64) ↦₆₄ midWord7 u0 u1) ∗
       ((b + 15#64) ↦₈ u1.extractLsb' 56 8)) := by
  have hu0 : b + BitVec.ofNat 64 (unpack64 u0).length = b + 8#64 := rfl
  rw [pointsTo64_eq_pointsToBytes b u0, pointsTo64_eq_pointsToBytes (b + 8#64) u1,
      ← hu0, ← pointsToBytes_append b (unpack64 u0) (unpack64 u1),
      ← pointsToBytes_singleton (b + 15#64) (u1.extractLsb' 56 8),
      pointsTo64_eq_pointsToBytes (b + 7#64) (midWord7 u0 u1),
      midWord7, pack64, unpack64_pack64]
  have h15 : b + 7#64 + BitVec.ofNat 64 ([u0.extractLsb' 56 8, u1.extractLsb' 0 8, u1.extractLsb' 8 8,
    u1.extractLsb' 16 8, u1.extractLsb' 24 8, u1.extractLsb' 32 8,
    u1.extractLsb' 40 8, u1.extractLsb' 48 8] : List (BitVec 8)).length = b + 15#64 := by
    change b + 7#64 + 8#64 = b + 15#64
    bv_omega
  rw [← h15, ← pointsToBytes_append (b + 7#64)]
  have hb7 : b + BitVec.ofNat 64 (headBytes7 u0).length = b + 7#64 := rfl
  rw [← hb7, ← pointsToBytes_append b]
  rfl

theorem midWord7_midWord1_shiftedWord7 (outPtr len : BitVec 64) (b15 : BitVec 8) :
    midWord7 (midWord1 outPtr len) (shiftedWord7 len b15) = len := by
  simp only [midWord7, midWord1, shiftedWord7, extractLsb_56_pack64,
    extractLsb_0_pack64, extractLsb_8_pack64, extractLsb_16_pack64,
    extractLsb_24_pack64, extractLsb_32_pack64, extractLsb_40_pack64,
    extractLsb_48_pack64, pack64_extractLsb']

theorem extractLsb56_shiftedWord7 (len : BitVec 64) (b15 : BitVec 8) :
    (shiftedWord7 len b15).extractLsb' 56 8 = b15 := by
  simp only [shiftedWord7, extractLsb_56_pack64]

theorem split_at_7_after_write (b outPtr len : BitVec 64) (b15 : BitVec 8) :
    ((b ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((b + 7#64) ↦₆₄ len) ∗
     ((b + 15#64) ↦₈ b15)) =
      ((b ↦₆₄ midWord1 outPtr len) ∗
       ((b + 8#64) ↦₆₄ shiftedWord7 len b15)) := by
  rw [pair64_split_at_7 b (midWord1 outPtr len) (shiftedWord7 len b15),
      midWord7_midWord1_shiftedWord7, extractLsb56_shiftedWord7]

theorem fsp_904_split_at_1 (fsp v0 v1 : BitVec 64) :
    (((fsp + 904#64) ↦₆₄ v0) ∗ ((fsp + 912#64) ↦₆₄ v1)) =
      (((fsp + 904#64) ↦₈ v0.extractLsb' 0 8) ∗
       ((fsp + 905#64) ↦₆₄ midWord1 v0 v1) ∗
       ((fsp + 913#64) ↦ₛ tailBytes7 v1)) := by
  have h1 : fsp + 904#64 + 8#64 = fsp + 912#64 := by bv_omega
  have h2 : fsp + 904#64 + 1#64 = fsp + 905#64 := by bv_omega
  have h3 : fsp + 904#64 + 9#64 = fsp + 913#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_1 (fsp + 904#64) v0 v1

theorem fsp_864_split_at_7 (fsp u0 u1 : BitVec 64) :
    (((fsp + 864#64) ↦₆₄ u0) ∗ ((fsp + 872#64) ↦₆₄ u1)) =
      (((fsp + 864#64) ↦ₛ headBytes7 u0) ∗
       ((fsp + 871#64) ↦₆₄ midWord7 u0 u1) ∗
       ((fsp + 879#64) ↦₈ u1.extractLsb' 56 8)) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 864#64 + 7#64 = fsp + 871#64 := by bv_omega
  have h3 : fsp + 864#64 + 15#64 = fsp + 879#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_7 (fsp + 864#64) u0 u1

theorem fsp_864_after_write (fsp outPtr len : BitVec 64) (b15 : BitVec 8) :
    (((fsp + 864#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((fsp + 871#64) ↦₆₄ len) ∗
     ((fsp + 879#64) ↦₈ b15)) =
      (((fsp + 864#64) ↦₆₄ midWord1 outPtr len) ∗
       ((fsp + 872#64) ↦₆₄ shiftedWord7 len b15)) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 864#64 + 7#64 = fsp + 871#64 := by bv_omega
  have h3 : fsp + 864#64 + 15#64 = fsp + 879#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_7_after_write (fsp + 864#64) outPtr len b15

theorem fsp_880_split_at_7 (fsp u0 u1 : BitVec 64) :
    (((fsp + 880#64) ↦₆₄ u0) ∗ ((fsp + 888#64) ↦₆₄ u1)) =
      (((fsp + 880#64) ↦ₛ headBytes7 u0) ∗
       ((fsp + 887#64) ↦₆₄ midWord7 u0 u1) ∗
       ((fsp + 895#64) ↦₈ u1.extractLsb' 56 8)) := by
  have h1 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  have h2 : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
  have h3 : fsp + 880#64 + 15#64 = fsp + 895#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_7 (fsp + 880#64) u0 u1

theorem fsp_880_after_write (fsp outPtr len : BitVec 64) (b15 : BitVec 8) :
    (((fsp + 880#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((fsp + 887#64) ↦₆₄ len) ∗
     ((fsp + 895#64) ↦₈ b15)) =
      (((fsp + 880#64) ↦₆₄ midWord1 outPtr len) ∗
       ((fsp + 888#64) ↦₆₄ shiftedWord7 len b15)) := by
  have h1 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  have h2 : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
  have h3 : fsp + 880#64 + 15#64 = fsp + 895#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_7_after_write (fsp + 880#64) outPtr len b15

theorem slot_split_at_1 (slotAddr v0 v1 : BitVec 64) :
    (((slotAddr + 8#64) ↦₆₄ v0) ∗ ((slotAddr + 16#64) ↦₆₄ v1)) =
      (((slotAddr + 8#64) ↦₈ v0.extractLsb' 0 8) ∗
       ((slotAddr + 9#64) ↦₆₄ midWord1 v0 v1) ∗
       ((slotAddr + 17#64) ↦ₛ tailBytes7 v1)) := by
  have h1 : slotAddr + 8#64 + 8#64 = slotAddr + 16#64 := by bv_omega
  have h2 : slotAddr + 8#64 + 1#64 = slotAddr + 9#64 := by bv_omega
  have h3 : slotAddr + 8#64 + 9#64 = slotAddr + 17#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_1 (slotAddr + 8#64) v0 v1

theorem slot_after_write (slotAddr outPtr len old1 : BitVec 64) :
    (((slotAddr + 8#64) ↦₈ outPtr.extractLsb' 0 8) ∗
     ((slotAddr + 9#64) ↦₆₄ midWord1 outPtr len) ∗
     ((slotAddr + 17#64) ↦ₛ tailBytes7 old1)) =
      (((slotAddr + 8#64) ↦₆₄ outPtr) ∗
       ((slotAddr + 16#64) ↦₆₄ replaceLowByte64 (len.extractLsb' 0 8) old1)) := by
  have h1 : slotAddr + 8#64 + 8#64 = slotAddr + 16#64 := by bv_omega
  have h2 : slotAddr + 8#64 + 1#64 = slotAddr + 9#64 := by bv_omega
  have h3 : slotAddr + 8#64 + 9#64 = slotAddr + 17#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_1_after_write (slotAddr + 8#64) outPtr len old1

theorem cells_864_eq (fsp : BitVec 64) :
    cells (fsp + 864#64) 4 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ((fsp + 864#64) ↦₆₄ v0) ∗ ((fsp + 872#64) ↦₆₄ v1) ∗
        ((fsp + 880#64) ↦₆₄ v2) ∗ ((fsp + 888#64) ↦₆₄ v3) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 872#64 + 8#64 = fsp + 880#64 := by bv_omega
  have h3 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, h3,
      ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

theorem cells_896_eq (fsp : BitVec 64) :
    cells (fsp + 896#64) 3 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2,
        ((fsp + 896#64) ↦₆₄ v0) ∗ ((fsp + 904#64) ↦₆₄ v1) ∗ ((fsp + 912#64) ↦₆₄ v2) := by
  have h1 : fsp + 896#64 + 8#64 = fsp + 904#64 := by bv_omega
  have h2 : fsp + 904#64 + 8#64 = fsp + 912#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

/-! ## `.polys` 16-Slot `Poly::zero()` Initialization (`+556 -> +1204`, `0x22c -> 0x4b4`) -/

local macro "polys_alloc_call" mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

local macro "polys_oom_exit" hoom:ident hpanic:ident : tactic => `(tactic| (
  conv => arg 4; simp only [$hoom:ident, ↓reduceIte, sepConj_assoc]
  apply sepWPp_pure_mid; intro _
  refine $hpanic:ident _ _ ?_
  wp_steps
  exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, *])
))

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
