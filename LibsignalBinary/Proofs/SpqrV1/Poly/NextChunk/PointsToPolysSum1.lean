/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `Poly::add_assign` and `lagrange_sum` Iteration Helpers

**Checked by Lean.**

Pure fold characterizations of `Poly.lagrangeSum` and `Poly.addAssignCoeffs`, together with
verification of the `Poly::add_assign` push/XOR loops and per-iteration `Poly::clone` / deallocation
blocks for `Poly::lagrange_sum`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm exists_pow_two_eq_eight_sm
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

/-! ## 1. Pure Lemmas for `Poly.addAssignCoeffs` and `Poly.lagrangeSum` -/

@[simp]
theorem addAssignCoeffs_nil_left (cs : List GF16) :
    Poly.addAssignCoeffs [] cs = cs := by
  cases cs <;> rfl

@[simp]
theorem addAssignCoeffs_nil_right (cs : List GF16) :
    Poly.addAssignCoeffs cs [] = cs := by
  cases cs <;> rfl

@[simp]
theorem addAssignCoeffs_cons (a : GF16) (as_ : List GF16) (b : GF16) (bs : List GF16) :
    Poly.addAssignCoeffs (a :: as_) (b :: bs) = GF16.add a b :: Poly.addAssignCoeffs as_ bs := rfl

theorem addAssignCoeffs_length_eq :
    ∀ {as_ bs : List GF16}, as_.length = bs.length →
      (Poly.addAssignCoeffs as_ bs).length = as_.length
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: as_, _ :: bs, h => by
    have h' : as_.length = bs.length := by simp at h; omega
    simp [addAssignCoeffs_cons, addAssignCoeffs_length_eq h']

@[simp]
theorem multAssign_length (p : Poly) (c : GF16) :
    (p.multAssign c).coefficients.length = p.coefficients.length := by
  unfold Poly.multAssign
  exact parallelMult_length c p.coefficients

/-- Recursive fold for `Poly::lagrange_sum` over `pts` and `polys`. -/
@[expose] def lagrangeSumFoldPoly (acc : Poly) : List Pt → List Poly → Poly
  | pt :: ptsRest, poly :: polysRest =>
    lagrangeSumFoldPoly (acc.addAssign (poly.multAssign pt.y)) ptsRest polysRest
  | _, _ => acc

@[simp]
theorem lagrangeSumFoldPoly_nil_left (acc : Poly) (polys : List Poly) :
    lagrangeSumFoldPoly acc [] polys = acc := rfl

@[simp]
theorem lagrangeSumFoldPoly_cons (acc : Poly) (pt : Pt) (ptsRest : List Pt)
    (poly : Poly) (polysRest : List Poly) :
    lagrangeSumFoldPoly acc (pt :: ptsRest) (poly :: polysRest) =
      lagrangeSumFoldPoly (acc.addAssign (poly.multAssign pt.y)) ptsRest polysRest := rfl

theorem lagrangeSum_eq_foldPoly (pts : List Pt) (polys : List Poly) :
    Poly.lagrangeSum pts polys = lagrangeSumFoldPoly Poly.zero pts polys := by
  unfold Poly.lagrangeSum
  have h : ∀ (pts : List Pt) (polys : List Poly) (acc : Poly),
      (pts.zip polys).foldl (fun (out : Poly) (pair : Pt × Poly) =>
        let p := pair.2.multAssign pair.1.y
        out.addAssign p) acc =
      lagrangeSumFoldPoly acc pts polys := by
    intro pts
    induction pts with
    | nil => intro polys acc; rfl
    | cons pt ptsRest ih =>
      intro polys acc
      cases polys with
      | nil => rfl
      | cons poly polysRest =>
        simp only [List.zip_cons_cons, List.foldl_cons, lagrangeSumFoldPoly_cons]
        exact ih polysRest _
  exact h pts polys Poly.zero

theorem gf16SliceAt_cons (ptr : BitVec 64) (c : GF16) (cs : List GF16) :
    gf16SliceAt ptr (c :: cs) = (gf16At c ptr ∗ gf16SliceAt (ptr + 2#64) cs) := rfl

/-! ## 2. `Poly::add_assign` Loops (`0x6b24c..0x6b2b4`, `+3784 -> +2640`) -/

@[local arm64_norm, local wp_norm]
theorem shl1_ofNat_sum (j : Nat) :
    BitVec.ofNat 64 j <<< 1 = BitVec.ofNat 64 (2 * j) :=
  shl_one_ofNat_eq_nat j

@[local arm64_norm, local wp_norm]
theorem add1_ofNat_sum (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_sum (m : Nat) :
    BitVec.ofNat 64 (2 * (m + 1)) - 2#64 = BitVec.ofNat 64 (2 * m) := by
  have h2 : BitVec.ofNat 64 (2 * (m + 1)) = BitVec.ofNat 64 (2 * m) + 2#64 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, BitVec.ofNat_add]
  rw [h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_sum_add (m : Nat) :
    BitVec.ofNat 64 (2 * (m + 1)) + 18446744073709551614#64 = BitVec.ofNat 64 (2 * m) := by
  have h1 : (18446744073709551614#64 : BitVec 64) = -2#64 := rfl
  have h2 : BitVec.ofNat 64 (2 * (m + 1)) = BitVec.ofNat 64 (2 * m) + 2#64 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem xor_zext64_gf16_sum (a b : GF16) :
    BitVec.truncate 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 a.value ^^^ BitVec.zeroExtend 64 b.value)) =
      (GF16.add a b).value := by
  cases a; cases b; unfold GF16.add; dsimp only; bv_bits

@[local arm64_norm, local wp_norm]
theorem zext16_trunc32_xor_zext64_gf16_sum (a b : GF16) :
    BitVec.zeroExtend 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 a.value ^^^ BitVec.zeroExtend 64 b.value)) =
      (GF16.add a b).value := by
  cases a; cases b; unfold GF16.add; dsimp only; bv_bits

theorem ult_self_false_sum (j : Nat) :
    (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 j) = false := by
  simp [BitVec.ult]

theorem beq_lt_false_sum {j n : Nat} (hj : j < n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 j == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hto
  omega

theorem bne_2m1_two_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (2 * (m + 1)) != 2#64) = decide (m ≠ 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_true_eq.mpr h, bne_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change 2 * (m + 1) = 2 at hto; omega

theorem beq_2m1_two_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (2 * (m + 1)) == 2#64) = decide (m = 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_false_iff_not.mpr h, beq_eq_false_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change 2 * (m + 1) = 2 at hto; omega

theorem polyOf_expose_sum (A : RustAlloc) (addr : BitVec 64) (p : Poly) (n : Nat)
    (hn_pos : 0 < n) (hlen : p.coefficients.length = n) :
    polyOf A addr p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜n ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr (cap.toNat * 2) 2 ∗
        (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
        memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_eq : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0_eq, ↓reduceIte, sepConj_pure_left_comm]
    apply Entails.pure_left; intro ⟨h0, _⟩
    have h0_nat : (0 : BitVec 64).toNat = 0 := rfl
    omega
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, hcap0', ↓reduceIte, hlen, sepConj_pure_left_comm]
    apply Entails.pure_left; intro ⟨hle, hcap_lt, hptr⟩
    have hbytes : arrayAt gf16At 2 ptr p.coefficients = (ptr ↦ₛ gf16SliceBytes p.coefficients) :=
      gf16SliceAt_eq_pointsToBytes ptr p.coefficients
    rw [hbytes]
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    exact Entails.pure_right ⟨hle, hcap_lt, hptr, hcap0⟩ (Entails.of_eq (by ac_rfl))

theorem polyOf_fold_sum (A : RustAlloc) (addr cap ptr : BitVec 64) (p : Poly) (n : Nat)
    (hlen : p.coefficients.length = n)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 2 < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
    ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
    A.live ptr (cap.toNat * 2) 2 ∗
    (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
    memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ⊢
    polyOf A addr p := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hbytes : arrayAt gf16At 2 ptr p.coefficients = (ptr ↦ₛ gf16SliceBytes p.coefficients) :=
    gf16SliceAt_eq_pointsToBytes ptr p.coefficients
  have hcap' : cap ≠ 0 := hcap
  simp only [hcap, hcap', ↓reduceIte, hlen, hbytes, sepConj_pure_left_comm]
  exact Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem polyOf_entails_dealloc_sum (A : RustAlloc) (addr : BitVec 64) (p : Poly) (n : Nat)
    (hn_pos : 0 < n) (hlen : p.coefficients.length = n) :
    polyOf A addr p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr (cap.toNat * 2) 2 ∗
        memRegion ptr (cap.toNat * 2) := by
  refine Entails.trans (polyOf_expose_sum A addr p n hn_pos hlen) ?_
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro ⟨hle, hcap_lt, hptr, hcap⟩
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.pure_right ⟨hcap_lt, hptr, hcap⟩ ?_
  have hlen_bs : (gf16SliceBytes p.coefficients).length = n * 2 := by
    rw [gf16SliceBytes_length, hlen, Nat.mul_comm]
  have hm := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat * 2)
    (n := n * 2) (k := (cap.toNat - n) * 2) (b' := ptr + BitVec.ofNat 64 (n * 2))
    (by omega) rfl (by omega)
  have h1 : (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ⊢
      memRegion ptr (cap.toNat * 2) := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr _)) ?_
    rw [hlen_bs, ← hm]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show
    ((addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
     A.live ptr (cap.toNat * 2) 2 ∗ (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
     memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2)) =
    ((addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
     A.live ptr (cap.toNat * 2) 2 ∗
     ((ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2))) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h1)))

@[local arm64_norm, local wp_norm]
theorem madd_basis_addr_sum (basisPtr : BitVec 64) (i : Nat) :
    basisPtr + BitVec.ofNat 64 i * 24#64 = basisPtr + BitVec.ofNat 64 (24 * i) := by
  have h : BitVec.ofNat 64 i * 24#64 = BitVec.ofNat 64 (24 * i) := by
    rw [Nat.mul_comm 24 i, BitVec.ofNat_mul]
  rw [h]

@[local arm64_norm, local wp_norm]
theorem shl2_ofNat_sum (i : Nat) :
    BitVec.ofNat 64 i <<< 2#64 = BitVec.ofNat 64 (4 * i) := by
  have h1 : BitVec.ofNat 64 i <<< 2#64 = 4#64 * BitVec.ofNat 64 i := by bv_bits
  have h2 : BitVec.ofNat 64 (4 * i) = 4#64 * BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_mul]
  rw [h1, h2]

@[local arm64_norm, local wp_norm]
theorem shl2_ofNat_sum_nat (i : Nat) :
    BitVec.ofNat 64 i <<< 2 = BitVec.ofNat 64 (4 * i) :=
  shl2_ofNat_sum i

@[local arm64_norm, local wp_norm]
theorem extractLsb_lo_concat_sum (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[local arm64_norm, local wp_norm]
theorem extractLsb_hi_concat_sum (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

theorem beq_i1_n_sum {i m n : Nat} (him : (i + 1) + m = n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 n) = decide (m = 0) := by
  by_cases hm : m = 0
  · subst hm
    have hi : i + 1 = n := by omega
    rw [hi, beq_self_eq_true]; rfl
  · rw [decide_eq_false hm, beq_eq_false_iff_ne]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hto
    omega

end CryptoVerification.SpqrV1.Poly.NextChunk
