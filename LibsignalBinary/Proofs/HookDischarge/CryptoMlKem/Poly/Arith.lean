/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import

/-!
# NEON 16-bit modular arithmetic soundness and range bounds

1. `RoTables.zetaTableAt` (`k < 128`) ↔ `Spec.zetasTimesMontgomeryR` and `Spec.fipsZetas`,
   with `|(zetaTableAt k).toInt| ≤ 1664` and `zetaTableAt k ≠ 0x8000#16`.
2. Integer semantics of `sqdmulh16` and `neonBarrettReduce16`: for every `v : BitVec 16`,
   `|(neonBarrettReduce16 v).toInt| ≤ 1664`, `(neonBarrettReduce16 v).toInt % 3329 = v.toInt % 3329`,
   and `neonBarrettReduce16 v` equals the unique centered representative in `[-1664, 1664]`.
3. Integer semantics of `neonMontgomeryReduce16` (32-bit `(low, high)` decomposition) and
   `neonMontgomeryMul16` (including LLVM's `c * 62209#16` constant-folding identity, `c = 1353#16`,
   and `c = 1441#16`).
4. `condSubtract3329` and `toUnsignedRep16` canonical `[0, 3329)` representative lemmas.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData00Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (readLE_cons2 zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkemQ bitRev7 fipsZetas zetasTimesMontgomeryR
  sqdmulh16 neonBarrettReduce16 neonMontgomeryReduce16 neonMontgomeryMul16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdCmltZero8h lane16_simdCmltZero8h_eq_sshiftRight15
)

/-! ## 1. `RoTables.zetaTableAt` ↔ `Spec.zetasTimesMontgomeryR` & `Spec.fipsZetas` -/

@[expose] def fipsZetaAt (k : Nat) : Nat :=
  (17 ^ bitRev7 k) % mlkemQ

@[expose] def montZetaAt (k : Nat) : BitVec 16 :=
  let u := (fipsZetaAt k * 65536) % mlkemQ
  let s : Int := if u ≤ 1664 then (u : Int) else (u : Int) - 3329
  BitVec.ofInt 16 s

private theorem getD_ofFn_128 {α : Type} (g : Fin 128 → α) (k : Nat) (d : α) (hk : k < 128) :
    (Array.ofFn g).getD k d = g ⟨k, hk⟩ := by
  simp [Array.getD, hk]

theorem fipsZetas_getD {k : Nat} (hk : k < 128) :
    fipsZetas.getD k 0 = fipsZetaAt k :=
  getD_ofFn_128 _ _ _ hk

theorem zetasTimesMontgomeryR_getD {k : Nat} (hk : k < 128) :
    zetasTimesMontgomeryR.getD k 0#16 = montZetaAt k := by
  unfold zetasTimesMontgomeryR montZetaAt
  rw [getD_ofFn_128 _ _ _ hk]
  dsimp only
  rw [fipsZetas_getD hk]

@[expose] def checkZetaBytes (bs : List (BitVec 8)) (idx rem : Nat) : Bool :=
  match rem, bs with
  | 0, _ => true
  | rem + 1, b0 :: b1 :: rest =>
    ((b1 ++ b0) == montZetaAt idx) && checkZetaBytes rest (idx + 1) rem
  | _ + 1, _ => false

theorem of_checkZetaBytes {bs : List (BitVec 8)} {idx rem k : Nat}
    (h : checkZetaBytes bs idx rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (2 * k) 2).setWidth 16 = montZetaAt (idx + k) := by
  induction rem generalizing bs idx k with
  | zero => omega
  | succ rem ih =>
    unfold checkZetaBytes at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    all_goals try contradiction
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.add_zero, ← h.1]
      simp only [ByteSlice.readLE_succ, ByteSlice.readLE_zero, Nat.add_zero,
        List.getD_cons_zero, List.getD_cons_succ]
      bv_bits
    · have hrec := @ih rest (idx + 1) k h.2 (by omega)
      rw [show idx + 1 + k = idx + (k + 1) by omega] at hrec
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, readLE_cons2]
      exact hrec

theorem checkWords16_zeta : checkZetaBytes mlkemData00Bytes 0 128 = true := by
  decide +kernel

theorem zetaTableAt_eq_zetasTimesMontgomeryR {k : Nat} (hk : k < 128) :
    zetaTableAt k = zetasTimesMontgomeryR.getD k 0#16 := by
  rw [zetasTimesMontgomeryR_getD hk]
  simpa [zetaTableAt] using of_checkZetaBytes checkWords16_zeta hk

@[expose] def zetaPropsAt (k : Nat) : Bool :=
  let z := montZetaAt k
  let fz : Int := fipsZetaAt k
  let ng : Int := ((mlkemQ - fipsZetaAt k) % mlkemQ : Nat)
  decide (-1664 ≤ z.toInt) &&
  decide (z.toInt ≤ 1664) &&
  (z != 0x8000#16) &&
  decide ((-z).toInt = -z.toInt) &&
  decide (z.toInt % 3329 = (fz * 65536) % 3329) &&
  decide ((-z).toInt % 3329 = (ng * 65536) % 3329)

theorem zetaProps_all : (List.range 128).all zetaPropsAt = true := by
  decide +kernel

private theorem zetaPropsAt_of_lt {k : Nat} (hk : k < 128) : zetaPropsAt k = true :=
  (List.all_eq_true.mp zetaProps_all) k (List.mem_range.mpr hk)

theorem zetasTimesMontgomeryR_bounds {k : Nat} (hk : k < 128) :
    -1664 ≤ (zetasTimesMontgomeryR.getD k 0#16).toInt ∧
    (zetasTimesMontgomeryR.getD k 0#16).toInt ≤ 1664 := by
  rw [zetasTimesMontgomeryR_getD hk]
  have h := zetaPropsAt_of_lt hk; unfold zetaPropsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

theorem zetaTableAt_bounds {k : Nat} (hk : k < 128) :
    -1664 ≤ (zetaTableAt k).toInt ∧ (zetaTableAt k).toInt ≤ 1664 := by
  rw [zetaTableAt_eq_zetasTimesMontgomeryR hk]; exact zetasTimesMontgomeryR_bounds hk

theorem zetasTimesMontgomeryR_ne_0x8000 {k : Nat} (hk : k < 128) :
    zetasTimesMontgomeryR.getD k 0#16 ≠ 0x8000#16 := by
  rw [zetasTimesMontgomeryR_getD hk]
  have h := zetaPropsAt_of_lt hk; unfold zetaPropsAt at h
  simp only [Bool.and_eq_true, bne_iff_ne] at h; exact h.1.1.1.2

theorem zetaTableAt_ne_0x8000 {k : Nat} (hk : k < 128) : zetaTableAt k ≠ 0x8000#16 := by
  rw [zetaTableAt_eq_zetasTimesMontgomeryR hk]; exact zetasTimesMontgomeryR_ne_0x8000 hk

theorem zetasTimesMontgomeryR_neg_toInt {k : Nat} (hk : k < 128) :
    (-(zetasTimesMontgomeryR.getD k 0#16)).toInt = -(zetasTimesMontgomeryR.getD k 0#16).toInt := by
  rw [zetasTimesMontgomeryR_getD hk]
  have h := zetaPropsAt_of_lt hk; unfold zetaPropsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.2

theorem zetasTimesMontgomeryR_mod_3329 {k : Nat} (hk : k < 128) :
    (zetasTimesMontgomeryR.getD k 0#16).toInt % 3329 =
      ((fipsZetas.getD k 0 : Int) * 65536) % 3329 := by
  rw [zetasTimesMontgomeryR_getD hk, fipsZetas_getD hk]
  have h := zetaPropsAt_of_lt hk; unfold zetaPropsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2

theorem zetaTableAt_mod_3329 {k : Nat} (hk : k < 128) :
    (zetaTableAt k).toInt % 3329 = ((fipsZetas.getD k 0 : Int) * 65536) % 3329 := by
  rw [zetaTableAt_eq_zetasTimesMontgomeryR hk]; exact zetasTimesMontgomeryR_mod_3329 hk

theorem zetasTimesMontgomeryR_neg_mod_3329 {k : Nat} (hk : k < 128) :
    (-(zetasTimesMontgomeryR.getD k 0#16)).toInt % 3329 =
      ((((mlkemQ - fipsZetas.getD k 0) % mlkemQ : Nat) : Int) * 65536) % 3329 := by
  rw [zetasTimesMontgomeryR_getD hk, fipsZetas_getD hk]
  have h := zetaPropsAt_of_lt hk; unfold zetaPropsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-! ## 2. `BitVec 16` Signed Modular Helpers, `sqdmulh16`, and `neonBarrettReduce16` -/

theorem toInt_emod_65536 (x : BitVec 16) : x.toInt % 65536 = (x.toNat : Int) := by
  have hx := x.isLt; rw [BitVec.toInt_eq_msb_cond]; cases x.msb <;> simp <;> omega

theorem toInt_eq_of_emod_65536 {x : BitVec 16} {z : Int}
    (hlo : -32768 ≤ z) (hhi : z < 32768) (hmod : x.toInt % 65536 = z % 65536) :
    x.toInt = z := by
  have h1 : -32768 ≤ x.toInt := BitVec.le_toInt x
  have h2 : x.toInt < 32768 := @BitVec.toInt_lt 16 x
  omega

theorem toInt_add_emod_65536 (a b : BitVec 16) :
    (a + b).toInt % 65536 = (a.toInt + b.toInt) % 65536 := by
  have := toInt_emod_65536 a; have := toInt_emod_65536 b
  rw [toInt_emod_65536, BitVec.toNat_add]; simp only [Nat.reducePow]; omega

theorem toInt_sub_emod_65536 (a b : BitVec 16) :
    (a - b).toInt % 65536 = (a.toInt - b.toInt) % 65536 := by
  have := toInt_emod_65536 a; have := toInt_emod_65536 b; have hb_lt := b.isLt
  rw [toInt_emod_65536, BitVec.toNat_sub]; simp only [Nat.reducePow] at hb_lt ⊢; omega

theorem toInt_mul_emod_65536 (a b : BitVec 16) :
    (a * b).toInt % 65536 = (a.toInt * b.toInt) % 65536 := by
  rw [Int.mul_emod, toInt_emod_65536 a, toInt_emod_65536 b, toInt_emod_65536 (a * b),
    BitVec.toNat_mul]
  simp only [Nat.reducePow, Int.natCast_emod, Int.natCast_mul]
  omega

theorem toInt_add_of_bounds {a b : BitVec 16}
    (hlo : -32768 ≤ a.toInt + b.toInt) (hhi : a.toInt + b.toInt < 32768) :
    (a + b).toInt = a.toInt + b.toInt :=
  toInt_eq_of_emod_65536 hlo hhi (toInt_add_emod_65536 a b)

theorem toInt_sub_of_bounds {a b : BitVec 16}
    (hlo : -32768 ≤ a.toInt - b.toInt) (hhi : a.toInt - b.toInt < 32768) :
    (a - b).toInt = a.toInt - b.toInt :=
  toInt_eq_of_emod_65536 hlo hhi (toInt_sub_emod_65536 a b)

private theorem toInt_not_16 (x : BitVec 16) : (~~~x).toInt = -1 - x.toInt := by
  have := x.isLt; rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, BitVec.msb_not,
    BitVec.toNat_not]; cases x.msb <;> simp <;> omega

private theorem toInt_not_32 (x : BitVec 32) : (~~~x).toInt = -1 - x.toInt := by
  have := x.isLt; rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, BitVec.msb_not,
    BitVec.toNat_not]; cases x.msb <;> simp <;> omega

private theorem not_sshiftRight {w : Nat} (x : BitVec w) (s : Nat) (hm : x.msb = true) :
    ~~~(x.sshiftRight s) = (~~~x) >>> s := by
  ext b hb; simp only [BitVec.getElem_not, BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight]
  by_cases hsb : s + b < w <;> simp [hsb, hm]

theorem toInt_sshiftRight_16 (x : BitVec 16) (s : Nat) (hs : s < 16) :
    (x.sshiftRight s).toInt = x.toInt / (2 ^ s : Int) := by
  cases hm : x.msb
  · have hnat : x.toInt = (x.toNat : Int) := by rw [BitVec.toInt_eq_msb_cond, hm]; simp
    have hsr : x.sshiftRight s = x >>> s := by
      ext b hb
      by_cases hsb : s + b < 16
      · simp [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hsb]
      · simp [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hm, hsb,
          BitVec.getLsbD_of_ge x (s + b) (by omega)]
    have hmsb2 : (x >>> s).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight]
      by_cases h0 : s = 0
      · subst h0; rwa [Nat.zero_add, ← BitVec.msb_eq_getLsbD_last]
      · exact BitVec.getLsbD_of_ge x (s + (16 - 1)) (by omega)
    rw [hsr, BitVec.toInt_eq_msb_cond, hmsb2]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, hnat]
    have hdiv := Int.natCast_ediv x.toNat (2 ^ s)
    simp only [Int.natCast_pow] at hdiv
    exact hdiv.symm
  · have hnx := toInt_not_16 x; have hnsr := toInt_not_16 (x.sshiftRight s)
    rw [not_sshiftRight x s hm] at hnsr
    have hmsb_nx : (~~~x).msb = false := by simp [hm]
    have hmsb2 : ((~~~x) >>> s).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight]
      by_cases h0 : s = 0
      · subst h0; rwa [Nat.zero_add, ← BitVec.msb_eq_getLsbD_last]
      · exact BitVec.getLsbD_of_ge (~~~x) (s + (16 - 1)) (by omega)
    have hnx_nat : (~~~x).toInt = ((~~~x).toNat : Int) := by
      rw [BitVec.toInt_eq_msb_cond, hmsb_nx]; simp
    have hsr_int : ((~~~x) >>> s).toInt = (~~~x).toInt / (2 ^ s : Int) := by
      rw [BitVec.toInt_eq_msb_cond, hmsb2]
      simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, hnx_nat]
      have hdiv := Int.natCast_ediv (~~~x).toNat (2 ^ s)
      simp only [Int.natCast_pow] at hdiv
      exact hdiv.symm
    rcases s with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | s <;>
      first | (simp at hsr_int ⊢; omega) | omega

private theorem toInt_sshiftRight_32_16 (x : BitVec 32) :
    (x.sshiftRight 16).toInt = x.toInt / 65536 := by
  cases hm : x.msb
  · have hnat : x.toInt = (x.toNat : Int) := by rw [BitVec.toInt_eq_msb_cond, hm]; simp
    have hsr : x.sshiftRight 16 = x >>> 16 := by
      ext b hb
      by_cases hsb : 16 + b < 32
      · simp [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hsb]
      · simp [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hm, hsb,
          BitVec.getLsbD_of_ge x (16 + b) (by omega)]
    have hmsb2 : (x >>> 16).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight]
      exact BitVec.getLsbD_of_ge x (16 + (32 - 1)) (by omega)
    rw [hsr, BitVec.toInt_eq_msb_cond, hmsb2]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, hnat]
    omega
  · have hnx := toInt_not_32 x; have hnsr := toInt_not_32 (x.sshiftRight 16)
    rw [not_sshiftRight x 16 hm] at hnsr
    have hmsb_nx : (~~~x).msb = false := by simp [hm]
    have hmsb2 : ((~~~x) >>> 16).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight]
      exact BitVec.getLsbD_of_ge (~~~x) (16 + (32 - 1)) (by omega)
    have hnx_nat : (~~~x).toInt = ((~~~x).toNat : Int) := by
      rw [BitVec.toInt_eq_msb_cond, hmsb_nx]; simp
    have hsr_int : ((~~~x) >>> 16).toInt = (~~~x).toInt / 65536 := by
      rw [BitVec.toInt_eq_msb_cond, hmsb2]
      simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.reducePow, hnx_nat]
      omega
    omega

/-- Exact signed value of `sqdmulh16 a b` whenever `(a, b) ≠ (-32768, -32768)`. -/
theorem sqdmulh16_toInt {a b : BitVec 16} (hne : ¬ (a = 0x8000#16 ∧ b = 0x8000#16)) :
    (sqdmulh16 a b).toInt = (a.toInt * b.toInt) / 32768 := by
  have ha_lo : -32768 ≤ a.toInt := BitVec.le_toInt a
  have ha_hi : a.toInt < 32768 := @BitVec.toInt_lt 16 a
  have hb_lo : -32768 ≤ b.toInt := BitVec.le_toInt b
  have hb_hi : b.toInt < 32768 := @BitVec.toInt_lt 16 b
  have hcond : (a == 0x8000#16 && b == 0x8000#16) = false := by
    cases ha8 : (a == 0x8000#16) <;> cases hb8 : (b == 0x8000#16) <;> simp_all
  have h8000 : (0x8000#16 : BitVec 16).toInt = -32768 := rfl
  have hnot_both : ¬ (a.toInt = -32768 ∧ b.toInt = -32768) := fun ⟨ha, hb⟩ =>
    hne ⟨BitVec.eq_of_toInt_eq (ha.trans h8000.symm), BitVec.eq_of_toInt_eq (hb.trans h8000.symm)⟩
  have hprod_bound : -1073709056 ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 1073709056 := by
    by_cases ha_min : a.toInt = -32768
    · rw [ha_min]; constructor <;> omega
    · have ha_gt : -32767 ≤ a.toInt := by omega
      constructor <;> by_cases hb0 : 0 ≤ b.toInt
      · have := Int.mul_le_mul_of_nonneg_right ha_gt hb0; omega
      · have := Int.mul_le_mul_of_nonpos_right (by omega : a.toInt ≤ 32767) (by omega : b.toInt ≤ 0); omega
      · have := Int.mul_le_mul_of_nonneg_right (by omega : a.toInt ≤ 32767) hb0; omega
      · have := Int.mul_le_mul_of_nonpos_right ha_gt (by omega : b.toInt ≤ 0); omega
  unfold sqdmulh16; rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hmul32 : (a.signExtend 32 * b.signExtend 32).toInt = a.toInt * b.toInt := by
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
  have hshl1 : ((a.signExtend 32 * b.signExtend 32) <<< 1).toInt = 2 * (a.toInt * b.toInt) := by
    have : ((a.signExtend 32 * b.signExtend 32) <<< 1) =
        (a.signExtend 32 * b.signExtend 32) * 2#32 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]
    rw [this, BitVec.toInt_mul, hmul32]
    change ((a.toInt * b.toInt) * 2).bmod 4294967296 = 2 * (a.toInt * b.toInt)
    rw [Int.bmod_eq_of_le] <;> omega
  have hsr_val := toInt_sshiftRight_32_16 ((a.signExtend 32 * b.signExtend 32) <<< 1)
  rw [hshl1] at hsr_val
  have htrunc : ∀ y : BitVec 32, -32768 ≤ y.toInt → y.toInt < 32768 →
      (y.truncate 16).toInt = y.toInt := by
    intro y hlo hhi; apply toInt_eq_of_emod_65536 hlo hhi
    rw [toInt_emod_65536, BitVec.toNat_setWidth, BitVec.toInt_eq_msb_cond]
    have := y.isLt
    cases y.msb <;> simp only [Nat.reducePow, ↓reduceIte, Bool.false_eq_true] at hlo hhi ⊢ <;> omega
  rw [htrunc _ (by omega) (by omega), hsr_val]; omega

/-- NEON `MLA Vd.8H, quot.8H, 0xf2ff#16` matches `v - quot * 3329#16`. -/
theorem barrett_mla_0xf2ff (v quot : BitVec 16) :
    v + quot * 0xf2ff#16 = v - quot * 3329#16 := by
  have h : (0xf2ff#16 : BitVec 16) = -3329#16 := by decide
  rw [h, BitVec.mul_neg, BitVec.sub_eq_add_neg]

/-- Universal Barrett reduction soundness for all `v : BitVec 16`:
    `|(neonBarrettReduce16 v).toInt| ≤ 1664` and `(neonBarrettReduce16 v).toInt % 3329 = v.toInt % 3329`. -/
theorem neonBarrettReduce16_spec (v : BitVec 16) :
    -1664 ≤ (neonBarrettReduce16 v).toInt ∧
    (neonBarrettReduce16 v).toInt ≤ 1664 ∧
    (neonBarrettReduce16 v).toInt % 3329 = v.toInt % 3329 := by
  have hv_lo : -32768 ≤ v.toInt := BitVec.le_toInt v
  have hv_hi : v.toInt < 32768 := @BitVec.toInt_lt 16 v
  unfold neonBarrettReduce16
  change -1664 ≤ (v - ((sqdmulh16 v 20159#16 + 1024#16).sshiftRight 11) * 3329#16).toInt ∧
    (v - ((sqdmulh16 v 20159#16 + 1024#16).sshiftRight 11) * 3329#16).toInt ≤ 1664 ∧
    (v - ((sqdmulh16 v 20159#16 + 1024#16).sshiftRight 11) * 3329#16).toInt % 3329 = v.toInt % 3329
  have hne : ¬ (v = 0x8000#16 ∧ (20159#16 : BitVec 16) = 0x8000#16) := by
    rintro ⟨_, h⟩; revert h; decide
  have hsq : (sqdmulh16 v 20159#16).toInt = (v.toInt * 20159) / 32768 := by
    have h20159 : (20159#16 : BitVec 16).toInt = 20159 := rfl
    rw [sqdmulh16_toInt hne, h20159]
  have h1024 : (1024#16 : BitVec 16).toInt = 1024 := rfl
  have hvec : (sqdmulh16 v 20159#16 + 1024#16).toInt =
      (v.toInt * 20159) / 32768 + 1024 := by
    rw [toInt_add_of_bounds (by omega) (by omega), hsq, h1024]
  let quot := (sqdmulh16 v 20159#16 + 1024#16).sshiftRight 11
  have hquot : quot.toInt = (v.toInt * 20159 + 33554432) / 67108864 := by
    change ((sqdmulh16 v 20159#16 + 1024#16).sshiftRight 11).toInt = _
    rw [toInt_sshiftRight_16 _ 11 (by omega), hvec]
    change ((v.toInt * 20159) / 32768 + 1024) / 2048 = (v.toInt * 20159 + 33554432) / 67108864
    omega
  have hbounds : -1664 ≤ v.toInt - quot.toInt * 3329 ∧ v.toInt - quot.toInt * 3329 ≤ 1664 := by
    rw [hquot]; omega
  have h3329 : (3329#16 : BitVec 16).toInt = 3329 := rfl
  have hres : (v - quot * 3329#16).toInt = v.toInt - quot.toInt * 3329 := by
    apply toInt_eq_of_emod_65536 (by omega) (by omega)
    rw [toInt_sub_emod_65536, Int.sub_emod, toInt_mul_emod_65536, h3329, ← Int.sub_emod]
  change -1664 ≤ (v - quot * 3329#16).toInt ∧ (v - quot * 3329#16).toInt ≤ 1664 ∧
    (v - quot * 3329#16).toInt % 3329 = v.toInt % 3329
  rw [hres]
  exact ⟨hbounds.1, hbounds.2, by omega⟩

/-- `neonBarrettReduce16 v` produces the unique centered representative in `[-1664, 1664]`. -/
theorem neonBarrettReduce16_eq_centered (v : BitVec 16) :
    (neonBarrettReduce16 v).toInt =
      if v.toInt % 3329 ≤ 1664 then v.toInt % 3329 else v.toInt % 3329 - 3329 := by
  obtain ⟨hlo, hhi, hmod⟩ := neonBarrettReduce16_spec v
  omega

/-! ## 3. `neonMontgomeryReduce16` and `neonMontgomeryMul16` -/

/-- Exact signed decomposition of a 32-bit word into its signed high 16 bits and unsigned low 16 bits. -/
theorem prod32_low_high_toInt (prod32 : BitVec 32) :
    prod32.toInt =
      65536 * ((prod32 >>> 16).truncate 16).toInt + ((prod32.truncate 16).toNat : Int) := by
  have hp := prod32.isLt
  have hlo : (prod32.truncate 16).toNat = prod32.toNat % 65536 := by
    simp [BitVec.toNat_setWidth]
  have hhi_nat : ((prod32 >>> 16).truncate 16).toNat = prod32.toNat / 65536 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.reducePow]
    omega
  have hmsb : ((prod32 >>> 16).truncate 16).msb = prod32.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
    simp
  rw [BitVec.toInt_eq_msb_cond prod32, BitVec.toInt_eq_msb_cond ((prod32 >>> 16).truncate 16),
    hmsb, hhi_nat, hlo]
  cases prod32.msb <;> simp only [Nat.reducePow, ↓reduceIte, Bool.false_eq_true] <;> omega

/-- Exact Montgomery reduction law for a 32-bit signed product `prod32` (`|prod32.toInt| ≤ 2000000000`). -/
theorem neonMontgomeryReduce16_prod32 (prod32 : BitVec 32) {B : Int}
    (hB_lo : -B ≤ prod32.toInt) (hB_hi : prod32.toInt ≤ B) (hB_max : B ≤ 2000000000) :
    let r := neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)
    (r.toInt * 65536) % 3329 = prod32.toInt % 3329 ∧
    -((B + 109084672) / 65536) ≤ r.toInt ∧
    r.toInt ≤ (B + 109084672) / 65536 := by
  dsimp only
  let low := prod32.truncate 16
  let high := (prod32 >>> 16).truncate 16
  let k := low * 62209#16
  let c := (sqdmulh16 k 3329#16).sshiftRight 1
  have hdecomp : prod32.toInt = 65536 * high.toInt + (low.toNat : Int) :=
    prod32_low_high_toInt prod32
  have hlow_lt : low.toNat < 65536 := low.isLt
  have hk_lo : -32768 ≤ k.toInt := BitVec.le_toInt k
  have hk_hi : k.toInt < 32768 := @BitVec.toInt_lt 16 k
  have hne : ¬ (k = 0x8000#16 ∧ 3329#16 = 0x8000#16) := by rintro ⟨_, h⟩; revert h; decide
  have hc_int : c.toInt = (k.toInt * 3329) / 65536 := by
    dsimp [c]
    rw [toInt_sshiftRight_16 _ 1 (by omega), sqdmulh16_toInt hne]
    have h3329 : (3329#16 : BitVec 16).toInt = 3329 := rfl
    rw [h3329]; omega
  have hk_mod : (k.toInt * 3329) % 65536 = (low.toNat : Int) := by
    have hm : k.toInt % 65536 = (low.toInt * (-3327)) % 65536 := by
      dsimp [k]; rw [toInt_mul_emod_65536]; rfl
    have hlow_mod := toInt_emod_65536 low
    rw [Int.mul_emod, hm, ← Int.mul_emod, Int.mul_assoc]
    change (low.toInt * (-11075583)) % 65536 = (low.toNat : Int)
    have hid : (low.toInt * (-11075583)) % 65536 = low.toInt % 65536 := by
      rw [Int.mul_emod]
      have : (-11075583 : Int) % 65536 = 1 := by decide
      rw [this, Int.mul_one, Int.emod_emod]
    rw [hid, hlow_mod]
  have hk_eq : k.toInt * 3329 = 65536 * c.toInt + (low.toNat : Int) := by omega
  have hexact : prod32.toInt - k.toInt * 3329 = 65536 * (high.toInt - c.toInt) := by omega
  have hr_int : (neonMontgomeryReduce16 low high).toInt = high.toInt - c.toInt := by
    change (high - c).toInt = high.toInt - c.toInt
    exact toInt_sub_of_bounds (by omega) (by omega)
  rw [hr_int]
  refine ⟨?_, by omega, by omega⟩
  have hmul : (high.toInt - c.toInt) * 65536 = prod32.toInt - k.toInt * 3329 := by omega
  rw [hmul]; omega

/-- Constant-folded `montgomery_multiply_by_constant` low-half identity: `(v * c) * 62209 = v * (c * 62209)`. -/
theorem montgomery_precomp_mul (v c : BitVec 16) :
    (v * c) * 62209#16 = v * (c * 62209#16) :=
  BitVec.mul_assoc v c 62209#16

/-- Exact `neonMontgomeryMul16 v c` soundness for any `c ≠ 0x8000#16`:
    reduces `v * c * 2^{-16} mod 3329`, and when `|c.toInt| ≤ 1664`, output is in `[-2496, 2496]`. -/
theorem neonMontgomeryMul16_spec (v c : BitVec 16) (hc : c ≠ 0x8000#16) :
    ((neonMontgomeryMul16 v c).toInt * 65536) % 3329 = (v.toInt * c.toInt) % 3329 ∧
    (-1664 ≤ c.toInt ∧ c.toInt ≤ 1664 →
      -2496 ≤ (neonMontgomeryMul16 v c).toInt ∧ (neonMontgomeryMul16 v c).toInt ≤ 2496) := by
  let prod32 : BitVec 32 := v.signExtend 32 * c.signExtend 32
  have hv_lo : -32768 ≤ v.toInt := BitVec.le_toInt v
  have hv_hi : v.toInt < 32768 := @BitVec.toInt_lt 16 v
  have hc_lo : -32768 ≤ c.toInt := BitVec.le_toInt c
  have hc_hi : c.toInt < 32768 := @BitVec.toInt_lt 16 c
  have hc_gt : -32767 ≤ c.toInt := by
    by_contra h
    have h8000 : (0x8000#16 : BitVec 16).toInt = -32768 := rfl
    exact hc (BitVec.eq_of_toInt_eq (by omega))
  have hcomm : v.toInt * c.toInt = c.toInt * v.toInt := Int.mul_comm _ _
  have hprod_bound : -1073709056 ≤ v.toInt * c.toInt ∧ v.toInt * c.toInt ≤ 1073709056 := by
    rw [hcomm]
    constructor
    · by_cases hv0 : 0 ≤ v.toInt
      · have := Int.mul_le_mul_of_nonneg_right hc_gt hv0; omega
      · have := Int.mul_le_mul_of_nonpos_right (by omega : c.toInt ≤ 32767) (by omega : v.toInt ≤ 0)
        omega
    · by_cases hv0 : 0 ≤ v.toInt
      · have := Int.mul_le_mul_of_nonneg_right (by omega : c.toInt ≤ 32767) hv0; omega
      · have := Int.mul_le_mul_of_nonpos_right hc_gt (by omega : v.toInt ≤ 0); omega
  have hprod32_int : prod32.toInt = v.toInt * c.toInt := by
    dsimp [prod32]
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
  have hlow_eq : v * c = prod32.truncate 16 := by
    apply BitVec.eq_of_toNat_eq
    have h1 := toInt_emod_65536 (v * c)
    have h2 := toInt_mul_emod_65536 v c
    have hdec := prod32_low_high_toInt prod32
    have hlo_lt := (prod32.truncate 16).isLt
    rw [hprod32_int] at hdec
    omega
  have hhigh_eq : (sqdmulh16 v c).sshiftRight 1 = (prod32 >>> 16).truncate 16 := by
    apply BitVec.eq_of_toInt_eq
    rw [toInt_sshiftRight_16 _ 1 (by omega), sqdmulh16_toInt (fun h => hc h.2)]
    have hdec := prod32_low_high_toInt prod32
    have hlo_lt := (prod32.truncate 16).isLt
    rw [hprod32_int] at hdec
    omega
  have heq_red : neonMontgomeryMul16 v c =
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16) := by
    unfold neonMontgomeryMul16; rw [hlow_eq, hhigh_eq]
  rw [heq_red]
  constructor
  · have h1 := (neonMontgomeryReduce16_prod32 prod32 (B := 1073709056)
      (by omega) (by omega) (by omega)).1
    rwa [hprod32_int] at h1
  · rintro ⟨hclo, hchi⟩
    have hb54 : -54525952 ≤ prod32.toInt ∧ prod32.toInt ≤ 54525952 := by
      rw [hprod32_int, hcomm]
      constructor
      · by_cases hv0 : 0 ≤ v.toInt
        · have := Int.mul_le_mul_of_nonneg_right hclo hv0; omega
        · have := Int.mul_le_mul_of_nonpos_right hchi (by omega : v.toInt ≤ 0); omega
      · by_cases hv0 : 0 ≤ v.toInt
        · have := Int.mul_le_mul_of_nonneg_right hchi hv0; omega
        · have := Int.mul_le_mul_of_nonpos_right hclo (by omega : v.toInt ≤ 0); omega
    have h2 := neonMontgomeryReduce16_prod32 prod32 (B := 54525952) hb54.1 hb54.2 (by omega)
    exact ⟨by have := h2.2.1; omega, by have := h2.2.2; omega⟩

/-- `to_standard_domain`: `neonMontgomeryMul16 v 1353#16` multiplies by `65536 mod 3329` with bound `2496`. -/
theorem neonMontgomeryMul16_1353 (v : BitVec 16) :
    (neonMontgomeryMul16 v 1353#16).toInt % 3329 = (v.toInt * 65536) % 3329 ∧
    -2496 ≤ (neonMontgomeryMul16 v 1353#16).toInt ∧
    (neonMontgomeryMul16 v 1353#16).toInt ≤ 2496 := by
  have ⟨hm, hb⟩ := neonMontgomeryMul16_spec v 1353#16 (by decide)
  have h1353 : (1353#16 : BitVec 16).toInt = 1353 := rfl
  rw [h1353] at hm hb
  obtain ⟨hlo, hhi⟩ := hb ⟨by omega, by omega⟩
  refine ⟨?_, hlo, hhi⟩
  have hdiff : ((neonMontgomeryMul16 v 1353#16).toInt * 65536 - v.toInt * 65536 * 65536) % 3329 = 0 := by
    have : (v.toInt * 65536 * 65536) % 3329 = (v.toInt * 1353) % 3329 := by omega
    omega
  let d := (neonMontgomeryMul16 v 1353#16).toInt - v.toInt * 65536
  have hd64 : (d * 65536) % 3329 = 0 := by dsimp [d]; omega
  have hd1 : d % 3329 = 0 := by
    have : ((d * 65536) * 169) % 3329 = 0 := by rw [Int.mul_emod, hd64]; simp
    have h169 : (d * 65536) * 169 = d + d * 3327 * 3329 := by omega
    rw [h169] at this; omega
  dsimp [d] at hd1; omega

/-- Final INTT normalization `neonMontgomeryMul16 v 1441#16`:
    `1441 = 3303 * 2^{32} mod 3329 = 128^{-1} * 2^{32} mod 3329`, so `128 * out ≡ v * 65536 (mod 3329)`. -/
theorem neonMontgomeryMul16_1441 (v : BitVec 16) :
    (128 * (neonMontgomeryMul16 v 1441#16).toInt) % 3329 = (v.toInt * 65536) % 3329 ∧
    -2496 ≤ (neonMontgomeryMul16 v 1441#16).toInt ∧
    (neonMontgomeryMul16 v 1441#16).toInt ≤ 2496 := by
  have ⟨hm, hb⟩ := neonMontgomeryMul16_spec v 1441#16 (by decide)
  have h1441 : (1441#16 : BitVec 16).toInt = 1441 := rfl
  rw [h1441] at hm hb
  obtain ⟨hlo, hhi⟩ := hb ⟨by omega, by omega⟩
  refine ⟨?_, hlo, hhi⟩
  let d := 128 * (neonMontgomeryMul16 v 1441#16).toInt - v.toInt * 65536
  have hd64 : (d * 65536) % 3329 = 0 := by
    have hr128 : ((128 * (neonMontgomeryMul16 v 1441#16).toInt) * 65536) % 3329 =
        (v.toInt * (128 * 1441)) % 3329 := by
      have : (128 * (neonMontgomeryMul16 v 1441#16).toInt) * 65536 =
          128 * ((neonMontgomeryMul16 v 1441#16).toInt * 65536) := by omega
      rw [this, Int.mul_emod, hm, ← Int.mul_emod]; congr 1; omega
    have hv128 : (v.toInt * 65536 * 65536) % 3329 = (v.toInt * (128 * 1441)) % 3329 := by omega
    dsimp [d]; omega
  have hd1 : d % 3329 = 0 := by
    have : ((d * 65536) * 169) % 3329 = 0 := by rw [Int.mul_emod, hd64]; simp
    have h169 : (d * 65536) * 169 = d + d * 3327 * 3329 := by omega
    rw [h169] at this; omega
  dsimp [d] at hd1; omega

/-! ## 4. `toUnsignedRep16` and `condSubtract3329` Canonical `[0, 3329)` Representatives -/

/-- `to_unsigned_representative`: `x + ((x >>s 15) & 3329)`. -/
@[expose] def toUnsignedRep16 (x : BitVec 16) : BitVec 16 :=
  x + ((x.sshiftRight 15) &&& 3329#16)

/-- `cond_subtract_3329`: `x - ((if 3329 ≤ x.toInt then 0xffff else 0) & 3329)`. -/
@[expose] def condSubtract3329 (x : BitVec 16) : BitVec 16 :=
  x - ((if 3329 ≤ x.toInt then 0xffff#16 else 0#16) &&& 3329#16)

theorem sshiftRight15_and_3329 (x : BitVec 16) :
    (x.sshiftRight 15) &&& 3329#16 = if x.toInt < 0 then 3329#16 else 0#16 := by
  have hx := toInt_sshiftRight_16 x 15 (by omega)
  change (x.sshiftRight 15).toInt = x.toInt / 32768 at hx
  have hlo : -32768 ≤ x.toInt := BitVec.le_toInt x
  have hhi : x.toInt < 32768 := @BitVec.toInt_lt 16 x
  by_cases hneg : x.toInt < 0
  · have hm1 : (0xffff#16 : BitVec 16).toInt = -1 := rfl
    have heq : x.sshiftRight 15 = 0xffff#16 := BitVec.eq_of_toInt_eq (by omega)
    simp [hneg, heq]
  · have h0 : (0#16 : BitVec 16).toInt = 0 := rfl
    have heq : x.sshiftRight 15 = 0#16 := BitVec.eq_of_toInt_eq (by omega)
    simp [hneg, heq]

/-- For any `x` with `-3329 ≤ x.toInt < 3329`, `toUnsignedRep16 x` is the exact canonical
    unsigned representative `(x.toInt % 3329).toNat ∈ [0, 3329)`. -/
theorem toUnsignedRep16_spec {x : BitVec 16} (hlo : -3329 ≤ x.toInt) (hhi : x.toInt < 3329) :
    (toUnsignedRep16 x).toNat = (x.toInt % 3329).toNat ∧
    (toUnsignedRep16 x).toNat < 3329 ∧
    (toUnsignedRep16 x).toInt = x.toInt % 3329 := by
  unfold toUnsignedRep16; rw [sshiftRight15_and_3329]
  have h3329 : (3329#16 : BitVec 16).toInt = 3329 := rfl
  by_cases hneg : x.toInt < 0
  · simp only [hneg, ↓reduceIte]
    have hsum : (x + 3329#16).toInt = x.toInt + 3329 := by
      rw [toInt_add_of_bounds (by omega) (by omega)]; omega
    have := toInt_emod_65536 (x + 3329#16); exact ⟨by omega, by omega, by omega⟩
  · simp only [hneg, ↓reduceIte, BitVec.add_zero]
    have := toInt_emod_65536 x; exact ⟨by omega, by omega, by omega⟩

/-- `CMLT #0` vector form of `to_unsigned_representative` matches `toUnsignedRep16` lane-by-lane. -/
theorem lane16_toUnsignedRep_cmlt (vn : BitVec 128) (i : Fin 8) :
    lane16 vn i + (lane16 (simdCmltZero8h vn) i &&& 3329#16) = toUnsignedRep16 (lane16 vn i) := by
  rw [lane16_simdCmltZero8h_eq_sshiftRight15]; rfl

/-- For any `x` with `0 ≤ x.toInt < 6658`, `condSubtract3329 x` produces `x.toNat % 3329 < 3329`. -/
theorem condSubtract3329_spec {x : BitVec 16} (hlo : 0 ≤ x.toInt) (hhi : x.toInt < 6658) :
    (condSubtract3329 x).toNat = x.toNat % 3329 ∧
    (condSubtract3329 x).toNat < 3329 ∧
    (condSubtract3329 x).toInt = x.toInt % 3329 := by
  unfold condSubtract3329
  have := toInt_emod_65536 x
  have h3329 : (3329#16 : BitVec 16).toInt = 3329 := rfl
  by_cases hge : 3329 ≤ x.toInt
  · simp only [hge, ↓reduceIte, show (0xffff#16 &&& 3329#16 : BitVec 16) = 3329#16 by decide]
    have hsub : (x - 3329#16).toInt = x.toInt - 3329 := by
      rw [toInt_sub_of_bounds (by omega) (by omega)]; omega
    have := toInt_emod_65536 (x - 3329#16); exact ⟨by omega, by omega, by omega⟩
  · simp only [hge, ↓reduceIte, BitVec.zero_and, BitVec.sub_zero]
    exact ⟨by omega, by omega, by omega⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
