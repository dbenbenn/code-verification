/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Fallback Setup

**Checked by Lean.**

Verifies OOM panic blocks, `fillXsLoop` (`[(x_i, 1)]`), and `allocXsAndBasis` (`0x6aa90..0x6ab1c`,
`+1804 -> +4116`) for the dynamic Lagrange fallback path (`n ∉ {0, 1, 3, 5, 30, 34, 36}`).
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fb :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fb :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one_fb (i : Nat) :
    BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

private theorem add_neg_one_eq_sub_one (x : BitVec 64) :
    x + 18446744073709551615#64 = x - 1#64 := by bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one_fb (i : Nat) :
    BitVec.ofNat 64 (i + 1) + 18446744073709551615#64 = BitVec.ofNat 64 i := by
  rw [add_neg_one_eq_sub_one, ofNat_succ_sub_one_fb]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq_succ_fb (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [← BitVec.ofNat_add]

/-! ## 1. OOM Panic Blocks (`+4588`, `+4592`, `+4820`) & Bitvector Helpers -/

theorem sle_four_of_le {n : Nat} (hle : n ≤ 4) :
    (BitVec.ofNat 64 n).sle 4#64 = true := by
  have h : (BitVec.ofNat 64 n : BitVec 64) ≤ 4#64 := by bv_omega
  revert h; bv_bits

theorem sle_four_of_gt {n : Nat} (hgt : 4 < n) (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).sle 4#64 = false := by
  have h1 : (4#64 : BitVec 64) < BitVec.ofNat 64 n := by bv_omega
  have h2 : BitVec.ofNat 64 n ≤ (0x0555555555555555#64 : BitVec 64) := by bv_omega
  revert h1 h2; bv_bits

theorem slt_33_of_le {n : Nat} (hle : n ≤ 33) :
    (33#64 : BitVec 64).slt (BitVec.ofNat 64 n) = false := by
  have h : (BitVec.ofNat 64 n : BitVec 64) ≤ 33#64 := by bv_omega
  revert h; bv_bits

theorem slt_33_of_gt {n : Nat} (hgt : 33 < n) (hb : n ≤ 0x0555555555555555) :
    (33#64 : BitVec 64).slt (BitVec.ofNat 64 n) = true := by
  have h1 : (33#64 : BitVec 64) < BitVec.ofNat 64 n := by bv_omega
  have h2 : BitVec.ofNat 64 n ≤ (0x0555555555555555#64 : BitVec 64) := by bv_omega
  revert h1 h2; bv_bits

theorem ofNat_ne_ofNat_false {a b : Nat} (hne : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false ∧
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0#64) = false := by
  have h1 : (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
    apply Bool.eq_false_iff.mpr; intro h
    have heq := beq_iff_eq.mp h
    bv_omega
  refine ⟨h1, by simp [bne, h1], ?_⟩
  apply Bool.eq_false_iff.mpr; intro h
  have heq := beq_iff_eq.mp h
  bv_omega

/-- Map a list of points to `[(pt.x, GF16.ONE)]` for Lagrange basis computation. -/
@[expose] def toOnePts (pts : List Pt) : List Pt :=
  pts.map (fun pt => { x := pt.x, y := GF16.ONE })

@[simp] theorem toOnePts_nil : toOnePts [] = [] := rfl
@[simp] theorem toOnePts_cons (pt : Pt) (pts : List Pt) :
    toOnePts (pt :: pts) = { x := pt.x, y := GF16.ONE } :: toOnePts pts := rfl
@[simp] theorem toOnePts_length (pts : List Pt) :
    (toOnePts pts).length = pts.length := List.length_map _

theorem mul24_shl_eq (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (24 * n) := by
  have h1 : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n * 2#64 := by bv_bits
  have h2 : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 3#64 =
      (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) * 8#64 := by bv_bits
  rw [h1, h2]
  bv_omega

theorem mul24_shl_eq_nat (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 = BitVec.ofNat 64 (24 * n) :=
  mul24_shl_eq n

theorem ult_max_pts_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (0x0555555555555555#64).ult (BitVec.ofNat 64 n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have hlt := BitVec.ult_iff_lt.mp h
  bv_omega

end CryptoVerification.SpqrV1.Poly.NextChunk
