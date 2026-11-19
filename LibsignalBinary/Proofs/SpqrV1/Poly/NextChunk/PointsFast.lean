/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `EncoderState::Points` Fast Path

Verifies the `EncoderState::Points` fast path (`0x6a3e0..0x6a534`) when
`(x.enc.idx.setWidth 16).toNat < pts[i].value.length` for all `i < 16`, composing the setup block,
16-iteration point-indexing loop, prologue, and epilogue.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Local Frame Split for `[fsp + 48]`, `[fsp + 88]`, `[fsp + 104]` -/

@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_48 (sp : BitVec 64) :
    (sp - 1200#64) + 48#64 = sp - 1152#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_48' (sp : BitVec 64) :
    48#64 + (sp - 1200#64) = sp - 1152#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_88 (sp : BitVec 64) :
    (sp - 1200#64) + 88#64 = sp - 1112#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_88' (sp : BitVec 64) :
    88#64 + (sp - 1200#64) = sp - 1112#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_104 (sp : BitVec 64) :
    (sp - 1200#64) + 104#64 = sp - 1096#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_104' (sp : BitVec 64) :
    104#64 + (sp - 1200#64) = sp - 1096#64 := by bv_omega

/-- Rest of the local stack frame during the `0x6a460..0x6a534` loop, after splitting out
    `[fsp + 48]` (`#0x30`), `[fsp + 88]` (`#0x58`), and `[fsp + 104]` (`#0x68`). -/
@[expose] def localFramePointsRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 48 ∗
  memRegion (fsp + 64#64) 24 ∗
  memRegion (fsp + 96#64) 8 ∗
  memRegion (fsp + 112#64) 120 ∗
  memRegion (fsp + 256#64) 848

theorem localFrameRest_unfold_points (fsp : BitVec 64) :
    localFrameRest fsp ⊢
      ∃∗ u48 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u104 : BitVec 64,
        ((fsp + 48#64) ↦₆₄ u48) ∗
        ((fsp + 88#64) ↦₆₄ u88) ∗
        ((fsp + 104#64) ↦₆₄ u104) ∗
        localFramePointsRest fsp := by
  unfold localFrameRest localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 48) (k := 8) (b' := fsp + 48#64)
        rfl rfl (by decide),
      ProofLib.memRegion_eight (fsp + 48#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 24) (k := 144) (b' := fsp + 88#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 88#64) (n := 8) (k := 136) (b' := fsp + 96#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 88#64),
      ProofLib.memRegion_split' (b := fsp + 96#64) (n := 8) (k := 128) (b' := fsp + 104#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 104#64) (n := 8) (k := 120) (b' := fsp + 112#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 104#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u104
  apply Entails.sepExists_elim; intro u88
  apply Entails.sepExists_elim; intro u48
  exact Entails.sepExists_right u48
    (Entails.sepExists_right u88
      (Entails.sepExists_right u104 (Entails.of_eq (by ac_rfl))))

theorem localFrameRest_fold_points (fsp u48 u88 u104 : BitVec 64) :
    ((fsp + 48#64) ↦₆₄ u48) ∗
      ((fsp + 88#64) ↦₆₄ u88) ∗
      ((fsp + 104#64) ↦₆₄ u104) ∗
      localFramePointsRest fsp ⊢
      localFrameRest fsp := by
  unfold localFrameRest localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 48) (k := 8) (b' := fsp + 48#64)
        rfl rfl (by decide),
      ProofLib.memRegion_eight (fsp + 48#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 24) (k := 144) (b' := fsp + 88#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 88#64) (n := 8) (k := 136) (b' := fsp + 96#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 88#64),
      ProofLib.memRegion_split' (b := fsp + 96#64) (n := 8) (k := 128) (b' := fsp + 104#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 104#64) (n := 8) (k := 120) (b' := fsp + 112#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 104#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u104
  apply Entails.sepExists_right u88
  apply Entails.sepExists_right u48
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. `pointOf`, `pointListOf`, and `gf16SliceAt` Splitting Helpers -/

theorem pointListOf_split_idx (A : RustAlloc) (base : BitVec 64)
    (pts : List Point) (i : Nat) (hi : i < pts.length) :
    pointListOf A base pts =
      (pointListOf A base (pts.take i) ∗
        pointOf A (base + BitVec.ofNat 64 (24 * i)) (pts[i]'hi) ∗
        pointListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1))) := by
  unfold pointListOf
  conv => lhs; rw [← List.take_append_drop i pts]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hi]
  simp only [arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 24 =
      base + BitVec.ofNat 64 (24 * (i + 1)) := by
    have hm : 24 * i + 24 = 24 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

theorem gf16SliceAt_split_idx (ptr : BitVec 64) (xs : List GF16)
    (j : Nat) (hj : j < xs.length) :
    gf16SliceAt ptr xs =
      (gf16SliceAt ptr (xs.take j) ∗
        ((ptr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (xs[j]'hj).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * (j + 1))) (xs.drop (j + 1))) := by
  unfold gf16SliceAt
  conv => lhs; rw [← List.take_append_drop j xs]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hj]
  simp only [arrayAt, gf16Stride, gf16At]
  have haddr : (ptr + BitVec.ofNat 64 (2 * j)) + BitVec.ofNat 64 2 =
      ptr + BitVec.ofNat 64 (2 * (j + 1)) := by
    have hm : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

/-- Spare-capacity and allocator-liveness portion of `pointOf`'s buffer. -/
@[expose] def pointBufRest (A : RustAlloc) (cap ptr : BitVec 64) (pt : Point) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
    memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
      ((cap.toNat - pt.value.length) * gf16Stride)

theorem pointBufBody_eq_slice_rest (A : RustAlloc) (cap ptr : BitVec 64)
    (pt : Point) (hlen : pt.value.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
       arrayAt gf16At gf16Stride ptr pt.value ∗
       memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
         ((cap.toNat - pt.value.length) * gf16Stride)) =
      (gf16SliceAt ptr pt.value ∗ pointBufRest A cap ptr pt) := by
  unfold pointBufRest gf16SliceAt
  by_cases h0 : cap = 0
  · have hcap0 : cap.toNat = 0 := by subst h0; rfl
    have hlen0 : pt.value.length = 0 := by omega
    have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hlen0
    simp [h0, hnil, arrayAt]
  · simp only [h0, ↓reduceIte]
    ac_rfl

theorem pointOf_unfold (A : RustAlloc) (v : BitVec 64) (pt : Point) :
    pointOf A v pt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ⌜pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
           arrayAt gf16At gf16Stride ptr pt.value ∗
           memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
             ((cap.toNat - pt.value.length) * gf16Stride)) := by
  unfold pointOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem pointOf_fold (A : RustAlloc) (v cap ptr : BitVec 64) (pt : Point)
    (hbounds : pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
      gf16SliceAt ptr pt.value ∗
      pointBufRest A cap ptr pt ⊢
      pointOf A v pt := by
  have htrue : (pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => hbounds⟩
  unfold pointOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  rw [htrue, pure_true, emp_sepConj, pointBufBody_eq_slice_rest A cap ptr pt hbounds.1]
  exact Entails.of_eq (by ac_rfl)

theorem pointValue_len_lt_two_pow_63 {len cap : Nat}
    (hlen : len ≤ cap) (hcap : cap * gf16Stride < 2 ^ 63) :
    len < 2 ^ 63 := by
  dsimp [gf16Stride] at hcap
  omega

/-! ## 3. Arithmetic and Bitvector Normalization for the `Points` Fast Path -/

@[local simp, local arm64_norm, local wp_norm]
theorem madd_24_eq (base : BitVec 64) (i : Nat) :
    base + BitVec.ofNat 64 i * 24#64 = base + BitVec.ofNat 64 (24 * i) := by
  have hm : BitVec.ofNat 64 i * 24#64 = BitVec.ofNat 64 (24 * i) := by
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  rw [hm]

@[local simp, local arm64_norm, local wp_norm]
theorem madd_24_eq' (base : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 i * 24#64 + base = base + BitVec.ofNat 64 (24 * i) := by
  rw [BitVec.add_comm, madd_24_eq]

@[local simp, local arm64_norm, local wp_norm]
theorem zext16_shl1_bv_eq (idx16 : BitVec 16) :
    (idx16.setWidth 64) <<< 1#64 = BitVec.ofNat 64 (2 * idx16.toNat) := by
  have h1 : (idx16.setWidth 64) <<< 1#64 = 2#64 * (idx16.setWidth 64) := by
    bv_slice
  have h2 : (idx16.setWidth 64) = BitVec.ofNat 64 idx16.toNat := by
    apply BitVec.eq_of_toNat_eq
    have hlt : idx16.toNat < 2 ^ 64 := Nat.lt_trans idx16.isLt (by decide : 2 ^ 16 < 2 ^ 64)
    simp [Nat.mod_eq_of_lt hlt]
  rw [h1, h2, ← BitVec.ofNat_mul]

@[local simp, local arm64_norm, local wp_norm]
theorem zext16_shl1_nat_eq (idx16 : BitVec 16) :
    (idx16.setWidth 64) <<< 1 = BitVec.ofNat 64 (2 * idx16.toNat) :=
  zext16_shl1_bv_eq idx16

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_two_mul_add_one ofNat_two_mul_add_two

theorem cmp_len_idx_gt {len : Nat} {idx16 : BitVec 16}
    (hlt : idx16.toNat < len) (hlen : len < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) = false ∧
    BitVec.ule (BitVec.ofNat 64 len) (idx16.setWidth 64) = false ∧
    (BitVec.ofNat 64 len == idx16.setWidth 64) = false ∧
    (BitVec.ofNat 64 len - idx16.setWidth 64 == 0#64) = false := by
  have hlen64 : len < 2 ^ 64 := Nat.lt_trans hlen (by decide : 2 ^ 63 < 2 ^ 64)
  have hidx64 : idx16.toNat < 2 ^ 64 := Nat.lt_trans idx16.isLt (by decide : 2 ^ 16 < 2 ^ 64)
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlen64
  have hidx_mod : (idx16.setWidth 64).toNat = idx16.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt hidx64
  have hne : BitVec.ofNat 64 len ≠ idx16.setWidth 64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    omega
  have hsub : BitVec.ofNat 64 len - idx16.setWidth 64 ≠ 0#64 := by
    intro h
    exact hne (by revert h; bv_omega)
  refine ⟨?_, ?_, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hsub⟩
  · simp [BitVec.ult, hlen_mod, hidx_mod]; omega
  · simp [BitVec.ule, hlen_mod, hidx_mod]; omega

theorem ofNat_add_one_beq_16 {i : Nat} (hi : i < 16) :
    (BitVec.ofNat 64 (i + 1) == 16#64) = (i == 15) ∧
    (BitVec.ofNat 64 (i + 1) - 16#64 == 0#64) = (i == 15) := by
  by_cases h15 : i = 15
  · subst h15; decide
  · have hlt : i + 1 < 16 := by omega
    have h16 : (16#64 : BitVec 64) = BitVec.ofNat 64 16 := rfl
    rw [h16]
    rcases ofNat_beq_false_of_lt (a := i + 1) (b := 16) hlt (by omega) with ⟨h1, h2, _, _⟩
    have hi15 : (i == 15) = false := beq_eq_false_iff_ne.mpr h15
    rw [h1, h2, hi15]
    exact ⟨rfl, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem lsr8_zext16_eq (v : BitVec 16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v >>> 8) =
      BitVec.setWidth 8 (v >>> 8) := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem trunc8_zext16_eq (v : BitVec 16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v) = BitVec.setWidth 8 v := by
  bv_slice

theorem chunkPointsBytes_add (idx : BitVec 16) (pts : List Point) :
    ∀ (m k n : Nat),
      chunkPointsBytes idx pts k (m + n) =
        chunkPointsBytes idx pts k m ++ chunkPointsBytes idx pts (k + m) n
  | 0, k, n => by simp [chunkPointsBytes]
  | m + 1, k, n => by
    have hadd : m + 1 + n = (m + n) + 1 := by omega
    have hk : k + (m + 1) = (k + 1) + m := by omega
    rw [hadd]
    conv => lhs; unfold chunkPointsBytes
    conv => rhs; arg 1; unfold chunkPointsBytes
    rw [chunkPointsBytes_add idx pts m (k + 1) n, hk]
    simp only [List.cons_append]

theorem chunkPointsBytes_zero_succ (idx : BitVec 16) (pts : List Point)
    (i : Nat) (hi : i < pts.length) (hidx : idx.toNat < (pts[i]'hi).value.length) :
    chunkPointsBytes idx pts 0 (i + 1) =
      chunkPointsBytes idx pts 0 i ++
        [BitVec.setWidth 8 (((pts[i]'hi).value[idx.toNat]'hidx).value >>> 8),
         BitVec.setWidth 8 ((pts[i]'hi).value[idx.toNat]'hidx).value] := by
  rw [chunkPointsBytes_add idx pts i 0 1, Nat.zero_add]
  have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hg : (pts[i]'hi).value[idx.toNat]? = some ((pts[i]'hi).value[idx.toNat]'hidx) :=
    List.getElem?_eq_getElem hidx
  simp [chunkPointsBytes, hpt, hg]

/-! ## 4. Single Iteration of the `Points` Fast-Path Loop (`0x6a4a4..0x6a534 -> 0x6a4e0..0x6a4f8 -> 0x6a480..0x6a4a0`) -/

end CryptoVerification.SpqrV1.Poly.NextChunk
