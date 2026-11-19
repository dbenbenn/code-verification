/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import

/-!
# NEON `compress_{1, 4, 5, 10, 11}` and `decompress_{1, 4, 5, 10, 11}` soundness

1. NEON `compress_1` (`cmlt #0 & 0xf2ff`, `sub`, `+ 1664`, `cmlt #0 ^ ·`, `+ (-832)`, MSB `>>> 15`,
   matching `B04 +0x3990..+0x39c8`) proved equal to `Spec.compressCoeff 1` on `[-3329, 3328]`.
2. NEON `compress_{4, 5, 10, 11}` (`toUnsignedRep16`, even/odd `4s` shift-and-mask split,
   `+ 1664` / `||| 1664`, `sqdmulh32 · 10321340#32`, `>>> 4`, `trn1.8h`, `& (2^d - 1)`, matching
   `B20`, `B03`, `B06`) proved equal to `Spec.compressCoeff d` on `[-3329, 3328]`, plus
   `Spec.neonCompressSerialize4 = Spec.compressAndEncode 4` on `[-3329, 3328]`.
3. NEON `decompress_{1, 4, 5, 10, 11}` (`cmeq #0` + `bic 1665` for `d = 1`; `umlal · 3329` onto
   `2^(d-1)` + `ushr #d` + `trn1.8h` for `d ∈ {4, 5, 10, 11}`) proved equal to `Spec.decompressCoeff d`
   with canonical range `[0, 3328]`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ sqdmulh32 compressCoeff decompressCoeff
  byteEncode byteDecodeRaw compressAndEncode decodeAndDecompress neonCompressSerialize4
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane32 pack4x32 dup8x16
  lane32_pack4x32 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdSub8h simdCmltZero8h simdCmeqZero8h simdSqdmulh4s simdTrn1_8h
  lane16_and lane16_eor lane16_not lane16_simdAdd8h lane16_simdSub8h
  lane16_simdCmeqZero8h lane32_simdSqdmulh4s lane16_simdTrn1_8h
  lane16_simdCmltZero8h_eq_sshiftRight15
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  toUnsignedRep16 toUnsignedRep16_spec lane16_toUnsignedRep_cmlt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents
)

private theorem compressCoeff_mod (d x : Nat) :
    compressCoeff d (x % mlkemQ) = compressCoeff d x := by
  unfold compressCoeff
  rw [Nat.mod_mod]

private theorem mod3329_eq_of_int_mod {x : BitVec 16} {c : Nat}
    (h : x.toInt % 3329 = (c : Int) % 3329) :
    (x.toInt % 3329).toNat = c % mlkemQ := by
  have hlo : 0 ≤ x.toInt % 3329 := Int.emod_nonneg _ (by omega)
  dsimp [mlkemQ]
  omega

/-! ## 1. NEON `compress_1` (`B04 +0x3990..+0x39c8`) -/

/-- Exact 1-lane pre-shift result of NEON `compress_1` (`B04 +0x3990..+0x39c4`):
    bit 15 (`>>> 15`) holds the compressed bit `compressCoeff 1 x`. -/
@[expose] def neonCompress1PreShift16 (x : BitVec 16) : BitVec 16 :=
  let m1 := (x.sshiftRight 15) &&& 0xf2ff#16
  let t1 := (m1 - x) + 1664#16
  let m2 := t1.sshiftRight 15
  (m2 ^^^ t1) + 0xfcc0#16

/-- Extracted 1-bit (`0#16` or `1#16`) output of `neonCompress1PreShift16`. -/
@[expose] def neonCompress1Lane16 (x : BitVec 16) : BitVec 16 :=
  neonCompress1PreShift16 x >>> 15

/-- 8-lane NEON vector `compress_1` pre-shift step matching `B04 +0x3990..+0x39c4`. -/
@[expose] def neonCompress1PreShift8h (vn : BitVec 128) : BitVec 128 :=
  let m1 := simdCmltZero8h vn &&& dup8x16 0xf2ff#16
  let t1 := simdAdd8h (simdSub8h m1 vn) (dup8x16 1664#16)
  let m2 := simdCmltZero8h t1
  simdAdd8h (m2 ^^^ t1) (dup8x16 0xfcc0#16)

@[simp] theorem lane16_neonCompress1PreShift8h (vn : BitVec 128) (i : Fin 8) :
    lane16 (neonCompress1PreShift8h vn) i = neonCompress1PreShift16 (lane16 vn i) := by
  unfold neonCompress1PreShift8h neonCompress1PreShift16
  simp only [lane16_simdAdd8h, lane16_eor, lane16_simdSub8h, lane16_and, lane16_dup8x16,
    lane16_simdCmltZero8h_eq_sshiftRight15]

@[expose] def checkCompress1At (k : Nat) : Bool :=
  let z : Int := (k : Int) - 3329
  let x : BitVec 16 := BitVec.ofInt 16 z
  let u : Nat := (z % 3329).toNat
  decide ((neonCompress1Lane16 x).toNat = compressCoeff 1 u)

private theorem checkCompress1_blocks :
    ∀ hi : Fin 27, ∀ lo : Fin 256,
      256 * hi.val + lo.val < 6658 → checkCompress1At (256 * hi.val + lo.val) = true := by
  decide +kernel

/-- Exact soundness of NEON `compress_1` for all signed `x ∈ [-3329, 3328]`. -/
theorem neonCompress1Lane16_spec {x : BitVec 16} (hlo : -3329 ≤ x.toInt) (hhi : x.toInt < 3329) :
    (neonCompress1Lane16 x).toNat = compressCoeff 1 (x.toInt % 3329).toNat ∧
    (neonCompress1Lane16 x).toNat < 2 := by
  let k := (x.toInt + 3329).toNat
  have hk : k < 6658 := by omega
  have hdiv : 256 * (k / 256) + k % 256 = k := Nat.div_add_mod k 256
  have h := checkCompress1_blocks ⟨k / 256, by omega⟩ ⟨k % 256, by omega⟩ (by dsimp only; omega)
  dsimp only at h
  rw [hdiv] at h
  unfold checkCompress1At at h
  simp only [decide_eq_true_eq] at h
  have hz : ((k : Int) - 3329) = x.toInt := by omega
  have hx : BitVec.ofInt 16 ((k : Int) - 3329) = x := by
    rw [hz, BitVec.ofInt_toInt]
  rw [hx, hz] at h
  refine ⟨h, ?_⟩
  rw [h]; unfold compressCoeff
  exact Nat.mod_lt _ (by decide)

theorem neonCompress1Lane16_of_mod {x : BitVec 16} {c : Nat}
    (hlo : -3329 ≤ x.toInt) (hhi : x.toInt < 3329)
    (hmod : x.toInt % 3329 = (c : Int) % 3329) :
    (neonCompress1Lane16 x).toNat = compressCoeff 1 c := by
  rw [(neonCompress1Lane16_spec hlo hhi).1, mod3329_eq_of_int_mod hmod, compressCoeff_mod]

/-! ## 2. NEON `compress_{4, 5, 10, 11}` (`B20`, `B03`, `B06`) -/

/-- NEON 1-lane unsigned compression via `sqdmulh32 ((u32 <<< d) + 1664) 10321340`. -/
@[expose] def neonCompressUnsigned16 (d : Nat) (u : BitVec 16) : BitVec 16 :=
  let comp : BitVec 32 := (u.zeroExtend 32 <<< d) + 1664#32
  let qd := sqdmulh32 comp 10321340#32
  ((qd >>> 4).truncate 16) &&& BitVec.ofNat 16 ((1 <<< d) - 1)

/-- NEON 1-lane signed compression (`toUnsignedRep16` followed by `neonCompressUnsigned16`). -/
@[expose] def neonCompressLane16 (d : Nat) (x : BitVec 16) : BitVec 16 :=
  neonCompressUnsigned16 d (toUnsignedRep16 x)

private theorem getLsbD_1664_ge11 :
    ∀ i : Fin 32, ¬ (i.val < 11) → (1664#32).getLsbD i.val = false := by
  decide +kernel

private theorem getLsbD_0xffff32 :
    ∀ j : Fin 32, (0x0000ffff#32).getLsbD j.val = decide (j.val < 16) := by
  decide +kernel

/-- In `compress_11` (`B06 +0xb158`), LLVM lowers `+ 1664#32` (`0x680`) to `||| 1664#32` because
    `(u.zeroExtend 32 <<< 11)` has low 11 bits zero (`1664 < 2048 = 2^11`). -/
theorem neonCompress11_orr_eq_add (u : BitVec 16) :
    ((u.zeroExtend 32 <<< 11) ||| 1664#32) = (u.zeroExtend 32 <<< 11) + 1664#32 := by
  have hdisj : ((u.zeroExtend 32 <<< 11) &&& 1664#32) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, hi, decide_true,
      Bool.true_and]
    by_cases h11 : i < 11
    · simp [h11]
    · rw [getLsbD_1664_ge11 ⟨i, hi⟩ h11]; simp
  exact (BitVec.add_eq_or_of_and_eq_zero (u.zeroExtend 32 <<< 11) 1664#32 hdisj).symm

/-- Even/odd 32-bit lane shift-and-mask extraction used in compiled NEON `compress_{4, 5, 10, 11}`. -/
theorem even_shl_extract32 (w : BitVec 32) (d : Nat) (hd : d ≤ 16) :
    ((w <<< d) &&& (0x0000ffff#32 <<< d)) = ((w.truncate 16).zeroExtend 32 <<< d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.zeroExtend, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hd_lt : i < d
  · simp [hd_lt]
  · have hlt32 : i - d < 32 := by omega
    have hm := getLsbD_0xffff32 ⟨i - d, hlt32⟩
    dsimp only at hm
    simp only [hd_lt, hlt32, hm, decide_false, Bool.not_false, Bool.true_and, decide_true]
    by_cases h16 : i - d < 16 <;> simp [h16]

theorem odd_ushr_extract32 (w : BitVec 32) (d : Nat) (hd1 : 1 ≤ d) (hd2 : d ≤ 16) :
    ((w >>> (16 - d)) &&& (0x0000ffff#32 <<< d)) = (((w >>> 16).truncate 16).zeroExtend 32 <<< d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  by_cases hd_lt : i < d
  · simp [hd_lt]
  · have hlt32 : i - d < 32 := by omega
    have hm := getLsbD_0xffff32 ⟨i - d, hlt32⟩
    dsimp only at hm
    simp only [hd_lt, hlt32, hm, decide_false, Bool.not_false, Bool.true_and, decide_true]
    by_cases h16 : i - d < 16
    · have hidx : 16 - d + i = 16 + (i - d) := by omega
      simp [h16, hidx]
    · simp [h16]

/-- Full 8-lane NEON vector `compress_d` matching `B20`, `B03`, and `B06`:
    `toUnsignedRep` → split even/odd to `4s` → `+ 1664` → `sqdmulh.4s` → `ushr #4` → `trn1.8h` → `& mask`. -/
@[expose] def neonCompress8h (d : Nat) (vn : BitVec 128) : BitVec 128 :=
  let u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  let cMul := pack4x32 fun _ => 10321340#32
  let evenIn := pack4x32 fun k => ((lane32 u k <<< d) &&& (0x0000ffff#32 <<< d)) + 1664#32
  let oddIn := pack4x32 fun k => ((lane32 u k >>> (16 - d)) &&& (0x0000ffff#32 <<< d)) + 1664#32
  let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
  let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
  simdTrn1_8h evenOut oddOut &&& dup8x16 (BitVec.ofNat 16 ((1 <<< d) - 1))

private theorem lane32_lo16_eq_lane16_even (v : BitVec 128) (k : Fin 4) :
    (lane32 v k).truncate 16 = lane16 v ⟨2 * k.val, by omega⟩ := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [lane32, lane16, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hb, show b < 32 by omega, decide_true, Bool.true_and]
  congr 1; omega

private theorem lane32_hi16_eq_lane16_odd (v : BitVec 128) (k : Fin 4) :
    ((lane32 v k) >>> 16).truncate 16 = lane16 v ⟨2 * k.val + 1, by omega⟩ := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [lane32, lane16, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hb, show 16 + b < 32 by omega,
    decide_true, Bool.true_and]
  congr 1; omega

private theorem lane16_trn1_idx_eq_lane32_lo16 (v : BitVec 128) (i : Fin 8) :
    lane16 v ⟨(i.val / 2) * 2, by omega⟩ = (lane32 v ⟨i.val / 2, by omega⟩).truncate 16 := by
  rw [lane32_lo16_eq_lane16_even v ⟨i.val / 2, by omega⟩]
  congr 1; ext; dsimp only; omega

theorem lane16_neonCompress8h {d : Nat} (hd1 : 1 ≤ d) (hd2 : d ≤ 16)
    (vn : BitVec 128) (i : Fin 8) :
    lane16 (neonCompress8h d vn) i = neonCompressLane16 d (lane16 vn i) := by
  unfold neonCompress8h neonCompressLane16 neonCompressUnsigned16
  let u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have hu_lane : ∀ j : Fin 8, lane16 u j = toUnsignedRep16 (lane16 vn j) := by
    intro j; simp only [u, lane16_simdAdd8h, lane16_and, lane16_dup8x16, lane16_toUnsignedRep_cmlt]
  rw [lane16_and, lane16_dup8x16, lane16_simdTrn1_8h]
  dsimp only
  by_cases he : i.val % 2 = 0
  · have hbeq : (i.val % 2 == 0) = true := beq_iff_eq.mpr he
    have hidx : (⟨2 * (i.val / 2), by omega⟩ : Fin 8) = i := by ext; dsimp only; omega
    simp only [hbeq, ↓reduceIte, lane16_trn1_idx_eq_lane32_lo16, lane32_pack4x32,
      lane32_simdSqdmulh4s, even_shl_extract32 _ d hd2, lane32_lo16_eq_lane16_even]
    rw [hidx, hu_lane i]
  · have hbeq : (i.val % 2 == 0) = false := beq_false_of_ne he
    have hidx : (⟨2 * (i.val / 2) + 1, by omega⟩ : Fin 8) = i := by ext; dsimp only; omega
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, lane16_trn1_idx_eq_lane32_lo16,
      lane32_pack4x32, lane32_simdSqdmulh4s, odd_ushr_extract32 _ d hd1 hd2,
      lane32_hi16_eq_lane16_odd]
    rw [hidx, hu_lane i]

@[expose] def checkCompressUnsignedAt (d u : Nat) : Bool :=
  decide ((neonCompressUnsigned16 d (BitVec.ofNat 16 u)).toNat = compressCoeff d u)

private theorem checkCompress4_blocks :
    ∀ hi : Fin 14, ∀ lo : Fin 256,
      256 * hi.val + lo.val < 3329 → checkCompressUnsignedAt 4 (256 * hi.val + lo.val) = true := by
  decide +kernel

private theorem checkCompress5_blocks :
    ∀ hi : Fin 14, ∀ lo : Fin 256,
      256 * hi.val + lo.val < 3329 → checkCompressUnsignedAt 5 (256 * hi.val + lo.val) = true := by
  decide +kernel

private theorem checkCompress10_blocks :
    ∀ hi : Fin 14, ∀ lo : Fin 256,
      256 * hi.val + lo.val < 3329 → checkCompressUnsignedAt 10 (256 * hi.val + lo.val) = true := by
  decide +kernel

private theorem checkCompress11_blocks :
    ∀ hi : Fin 14, ∀ lo : Fin 256,
      256 * hi.val + lo.val < 3329 → checkCompressUnsignedAt 11 (256 * hi.val + lo.val) = true := by
  decide +kernel

theorem neonCompressUnsigned16_spec {d u : Nat}
    (hd : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11) (hu : u < 3329) :
    (neonCompressUnsigned16 d (BitVec.ofNat 16 u)).toNat = compressCoeff d u ∧
    (neonCompressUnsigned16 d (BitVec.ofNat 16 u)).toNat < 2 ^ d := by
  have hdiv : 256 * (u / 256) + u % 256 = u := Nat.div_add_mod u 256
  have hchk : checkCompressUnsignedAt d u = true := by
    rw [← hdiv]
    rcases hd with rfl | rfl | rfl | rfl
    · exact checkCompress4_blocks ⟨u / 256, by omega⟩ ⟨u % 256, by omega⟩ (by dsimp only; omega)
    · exact checkCompress5_blocks ⟨u / 256, by omega⟩ ⟨u % 256, by omega⟩ (by dsimp only; omega)
    · exact checkCompress10_blocks ⟨u / 256, by omega⟩ ⟨u % 256, by omega⟩ (by dsimp only; omega)
    · exact checkCompress11_blocks ⟨u / 256, by omega⟩ ⟨u % 256, by omega⟩ (by dsimp only; omega)
  unfold checkCompressUnsignedAt at hchk
  simp only [decide_eq_true_eq] at hchk
  refine ⟨hchk, ?_⟩
  rw [hchk]; unfold compressCoeff
  have hpow : 1 <<< d = 2 ^ d := by rcases hd with rfl | rfl | rfl | rfl <;> rfl
  rw [hpow]
  exact Nat.mod_lt _ (by rcases hd with rfl | rfl | rfl | rfl <;> decide)

/-- Exact soundness of NEON `compress_{4, 5, 10, 11}` for all signed `x ∈ [-3329, 3328]`. -/
theorem neonCompressLane16_spec {d : Nat} {x : BitVec 16}
    (hd : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11)
    (hlo : -3329 ≤ x.toInt) (hhi : x.toInt < 3329) :
    (neonCompressLane16 d x).toNat = compressCoeff d (x.toInt % 3329).toNat ∧
    (neonCompressLane16 d x).toNat < 2 ^ d := by
  unfold neonCompressLane16
  obtain ⟨hu_eq, hu_lt, _⟩ := toUnsignedRep16_spec hlo hhi
  rw [hu_eq] at hu_lt
  have hbw : toUnsignedRep16 x = BitVec.ofNat 16 (x.toInt % 3329).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [hu_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hbw]
  exact neonCompressUnsigned16_spec hd hu_lt

theorem neonCompressLane16_of_mod {d : Nat} {x : BitVec 16} {c : Nat}
    (hd : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11)
    (hlo : -3329 ≤ x.toInt) (hhi : x.toInt < 3329)
    (hmod : x.toInt % 3329 = (c : Int) % 3329) :
    (neonCompressLane16 d x).toNat = compressCoeff d c := by
  rw [(neonCompressLane16_spec hd hlo hhi).1, mod3329_eq_of_int_mod hmod, compressCoeff_mod]

private theorem array_getElem_eq_getD_nat (a : Array Nat) (i : Nat) (h : i < a.size) :
    a[i]'h = a.getD i 0 := by
  simp only [Array.getD, h, ↓reduceDIte]; rfl

set_option maxRecDepth 4096 in
/-- Bridge from `Spec.neonCompressSerialize4` to `Spec.compressAndEncode 4` for any `Poly16`
    with lanes in `[-3329, 3328]` representing `f : Poly`. -/
theorem neonCompressSerialize4_eq_compressAndEncode {re : Poly16} {f : Poly}
    (hb : ∀ i < 256, -3329 ≤ (re.getD i 0#16).toInt ∧ (re.getD i 0#16).toInt < 3329)
    (hr : PolyRepresents re f) (hf_size : f.size = 256) :
    neonCompressSerialize4 re = compressAndEncode 4 f := by
  unfold neonCompressSerialize4 compressAndEncode
  dsimp only
  apply congrArg (byteEncode 4)
  apply Array.ext
  · simp [hf_size]
  · intro i hi1 hi2
    have hi : i < 256 := by simp at hi1; exact hi1
    simp only [Array.getElem_ofFn, Array.getElem_map]
    have hdef : (let x := re.getD i 0#16
        let u16 := x + ((x.sshiftRight 15) &&& 3329#16)
        let u32 : BitVec 32 := u16.zeroExtend 32
        let comp := (u32 <<< 4) + 1664#32
        let qd := sqdmulh32 comp 10321340#32
        (((qd >>> 4).truncate 16) &&& 0x000f#16).toNat) =
        (neonCompressLane16 4 (re.getD i 0#16)).toNat := rfl
    rw [hdef, array_getElem_eq_getD_nat f i (by omega)]
    exact neonCompressLane16_of_mod (Or.inl rfl) (hb i hi).1 (hb i hi).2 (hr.2 i hi)

/-! ## 3. NEON `decompress_{1, 4, 5, 10, 11}` (`B20`, `B04`, `B06`) -/

/-- Exact 1-lane NEON `decompress_1` (`cmeq #0` + `bic 1665#16, mask`, matching `B20 +0x076c..+0x0778`). -/
@[expose] def neonDecompress1Lane16 (raw : BitVec 16) : BitVec 16 :=
  let bit := raw &&& 1#16
  let mask := if bit == 0#16 then 0xffff#16 else 0#16
  1665#16 &&& ~~~mask

/-- 8-lane NEON vector `decompress_1` matching `B20 +0x076c..+0x0778`. -/
@[expose] def neonDecompress1_8h (vn : BitVec 128) : BitVec 128 :=
  let bitVec := vn &&& dup8x16 1#16
  let mask := simdCmeqZero8h bitVec
  dup8x16 1665#16 &&& ~~~mask

@[simp] theorem lane16_neonDecompress1_8h (vn : BitVec 128) (i : Fin 8) :
    lane16 (neonDecompress1_8h vn) i = neonDecompress1Lane16 (lane16 vn i) := by
  unfold neonDecompress1_8h neonDecompress1Lane16
  simp only [lane16_and, lane16_not, lane16_simdCmeqZero8h, lane16_dup8x16]

theorem neonDecompress1Lane16_spec (raw : BitVec 16) :
    let b := (raw &&& 1#16).toNat
    neonDecompress1Lane16 raw = BitVec.ofNat 16 (decompressCoeff 1 b) ∧
    0 ≤ (neonDecompress1Lane16 raw).toInt ∧ (neonDecompress1Lane16 raw).toInt ≤ 1665 := by
  dsimp only
  have hcases : (raw &&& 1#16) = 0#16 ∨ (raw &&& 1#16) = 1#16 := by
    have hlt : (raw &&& 1#16).toNat < 2 := by
      rw [BitVec.toNat_and]; change raw.toNat &&& 1 < 2
      rw [Nat.and_one_is_mod]; omega
    rcases n_eq : (raw &&& 1#16).toNat with _ | _ | n <;> try omega
    · left; apply BitVec.eq_of_toNat_eq; exact n_eq
    · right; apply BitVec.eq_of_toNat_eq; exact n_eq
  rcases hcases with h | h <;> unfold neonDecompress1Lane16 <;> rw [h] <;> decide

/-- Exact 1-lane NEON `decompress_d` (`umlal · 3329` onto `2^(d-1)` + `ushr #d`, `B04`/`B06`). -/
@[expose] def neonDecompressLane16 (d : Nat) (y : BitVec 16) : BitVec 16 :=
  (((y.zeroExtend 32 * 3329#32) + BitVec.ofNat 32 (1 <<< (d - 1))) >>> d).truncate 16

@[expose] def checkDecompressAt (d : Nat) (y : Fin (2 ^ d)) : Bool :=
  let out := neonDecompressLane16 d (BitVec.ofNat 16 y.val)
  decide (out = BitVec.ofNat 16 (decompressCoeff d y.val)) &&
  decide (0 ≤ out.toInt ∧ out.toInt ≤ 3328) &&
  decide (decompressCoeff d y.val < mlkemQ)

private theorem checkDecompress4_all : ∀ y : Fin (2 ^ 4), checkDecompressAt 4 y = true := by decide +kernel
private theorem checkDecompress5_all : ∀ y : Fin (2 ^ 5), checkDecompressAt 5 y = true := by decide +kernel
private theorem checkDecompress10_all : ∀ y : Fin (2 ^ 10), checkDecompressAt 10 y = true := by decide +kernel
private theorem checkDecompress11_all : ∀ y : Fin (2 ^ 11), checkDecompressAt 11 y = true := by decide +kernel

/-- Exact soundness & canonical range `[0, 3328]` of NEON `decompress_{4, 5, 10, 11}`. -/
theorem neonDecompressLane16_spec {d : Nat} {y : BitVec 16}
    (hd : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11) (hy : y.toNat < 2 ^ d) :
    neonDecompressLane16 d y = BitVec.ofNat 16 (decompressCoeff d y.toNat) ∧
    (0 ≤ (neonDecompressLane16 d y).toInt ∧ (neonDecompressLane16 d y).toInt ≤ 3328) ∧
    decompressCoeff d y.toNat < mlkemQ := by
  have hchk : checkDecompressAt d ⟨y.toNat, hy⟩ = true := by
    rcases hd with rfl | rfl | rfl | rfl
    · exact checkDecompress4_all ⟨y.toNat, hy⟩
    · exact checkDecompress5_all ⟨y.toNat, hy⟩
    · exact checkDecompress10_all ⟨y.toNat, hy⟩
    · exact checkDecompress11_all ⟨y.toNat, hy⟩
  unfold checkDecompressAt at hchk
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, decide_eq_true_eq] at hchk
  exact ⟨hchk.1.1, hchk.1.2, hchk.2⟩

/-- Lifting `decompressCoeff d` (`d ∈ {1, 4, 5, 10, 11}`) over `byteDecodeRaw d bs` produces a
    `PolyBounded16 3328` `Poly16` representing `Spec.decodeAndDecompress d bs`. -/
theorem decodeAndDecompress_poly16_spec {d : Nat} (bs : List (BitVec 8))
    (hd : d = 1 ∨ d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11)
    (hraw_lt : ∀ i < 256, (byteDecodeRaw d bs).getD i 0 < 2 ^ d) :
    let out : Poly16 := (decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c
    PolyBounded16 3328 out ∧ PolyRepresents out (decodeAndDecompress d bs) := by
  dsimp only
  have hsize_dec : (decodeAndDecompress d bs).size = 256 := by
    simp [decodeAndDecompress, byteDecodeRaw]
  have hsize : ((decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c).size = 256 := by
    simp [hsize_dec]
  have hcoeff_lt : ∀ i < 256, (decodeAndDecompress d bs).getD i 0 < 3329 := by
    intro i hi
    have hy := hraw_lt i hi
    have hget : (decodeAndDecompress d bs).getD i 0 =
        decompressCoeff d ((byteDecodeRaw d bs).getD i 0) := by
      simp [decodeAndDecompress, byteDecodeRaw, Array.getD, hi]
    rw [hget]
    rcases hd with rfl | hd4
    · have hy2 : (byteDecodeRaw 1 bs).getD i 0 = 0 ∨ (byteDecodeRaw 1 bs).getD i 0 = 1 := by omega
      rcases hy2 with h | h <;> rw [h] <;> decide
    · have hbw : (BitVec.ofNat 16 ((byteDecodeRaw d bs).getD i 0)).toNat =
          (byteDecodeRaw d bs).getD i 0 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        rcases hd4 with rfl | rfl | rfl | rfl <;> omega
      have hs := (neonDecompressLane16_spec hd4 (y := BitVec.ofNat 16 ((byteDecodeRaw d bs).getD i 0))
        (by rw [hbw]; exact hy)).2.2
      rw [hbw] at hs; exact hs
  refine ⟨⟨hsize, ?_⟩, ⟨hsize, ?_⟩⟩
  · intro i hi
    have hc := hcoeff_lt i hi
    have hmap : ((decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((decodeAndDecompress d bs).getD i 0) := by
      simp [Array.getD, hsize_dec, hi]
    rw [hmap, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro i hi
    have hc := hcoeff_lt i hi
    have hmap : ((decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((decodeAndDecompress d bs).getD i 0) := by
      simp [Array.getD, hsize_dec, hi]
    rw [hmap, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt64 : 2 * ((decodeAndDecompress d bs).getD i 0) < 65536 := by omega
    omega

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
