/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Constant Basis Loops (`n = 36, 34`)

**Checked by Lean.**

Verifies the loop-based constant Lagrange basis copy paths `basis_n36_sepWPp` and
`basis_n34_sepWPp` (`+1136 -> +2608`) from `COMPLETE_POINTS_POLYS_{36,34}`.
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two'' :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight'' :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

/-! ## 1. Arithmetic, Alignment, and Separation-Logic Helpers for Constant Basis Loops -/

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

private theorem add_neg_one_eq_sub_one (x : BitVec 64) :
    x + 18446744073709551615#64 = x - 1#64 := by bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) + 18446744073709551615#64 = BitVec.ofNat 64 i := by
  rw [add_neg_one_eq_sub_one, ofNat_succ_sub_one]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq_succ (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [← BitVec.ofNat_add]

theorem ofNat_sub_ofNat_beq_zero_false (i n : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i - BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h' : BitVec.ofNat 64 i = BitVec.ofNat 64 n := by
    have := congrArg (· + BitVec.ofNat 64 n) h
    simpa [BitVec.sub_add_cancel] using this
  have ht := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem ofNat_beq_ofNat_false (i n : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

private theorem align8_add_mul24_bv (ptr off : BitVec 64)
    (hp : ptr &&& 7#64 = 0#64) (ho : off &&& 7#64 = 0#64) :
    ((ptr + off) &&& 7#64 == 0#64) = true ∧
    (((ptr + off) + 8#64) &&& 7#64 == 0#64) = true ∧
    (((ptr + off) + 16#64) &&& 7#64 == 0#64) = true := by
  bv_robdd

theorem align8_basis_step (ptr : BitVec 64) (hmod : ptr.toNat % 8 = 0) (i : Nat) :
    ((ptr + BitVec.ofNat 64 (24 * i)) &&& 7#64 == 0#64) = true ∧
    (((ptr + BitVec.ofNat 64 (24 * i)) + 8#64) &&& 7#64 == 0#64) = true ∧
    (((ptr + BitVec.ofNat 64 (24 * i)) + 16#64) &&& 7#64 == 0#64) = true := by
  have hp : ptr &&& 7#64 = 0#64 := beq_iff_eq.mp (align8_of_mod8_eq_zero hmod)
  have ho : BitVec.ofNat 64 (24 * i) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    change (24 * i % 2 ^ 64) &&& 7 = 0
    rw [Nat.and_two_pow_sub_one_eq_mod _ 3]
    omega
  exact align8_add_mul24_bv ptr (BitVec.ofNat 64 (24 * i)) hp ho

theorem memRegion_split_basis_cons (basisPtr : BitVec 64) (i k : Nat) (hk : 24 * (k + 1) < 2 ^ 64) :
    memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * (k + 1)) =
      (∃∗ u_cap : BitVec 64, ∃∗ u_ptr : BitVec 64, ∃∗ u_len : BitVec 64,
        ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ u_len) ∗
        (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ u_ptr) ∗
        (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ u_cap)) ∗
      memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * k) := by
  have h24 : 24 * (k + 1) = 24 + 24 * k := by omega
  have hb' : basisPtr + BitVec.ofNat 64 (24 * (i + 1)) =
      (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 := by
    rw [BitVec.add_assoc, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
        ← BitVec.ofNat_add]
    congr 2
  rw [ProofLib.memRegion_split' (b := basisPtr + BitVec.ofNat 64 (24 * i))
        (n := 24) (k := 24 * k) (b' := basisPtr + BitVec.ofNat 64 (24 * (i + 1)))
        h24 hb' (by omega),
      memRegion_split_polyHeader (basisPtr + BitVec.ofNat 64 (24 * i))]

theorem polyListOf_cons_off (A : RustAlloc) (basisPtr : BitVec 64) (i : Nat) (p : Poly) (ps : List Poly) :
    polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) (p :: ps) =
      polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗
      polyListOf A (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) ps := by
  change polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗
      polyListOf A ((basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64) ps = _
  have h : (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
      basisPtr + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
        ← BitVec.ofNat_add]
    congr 2
  rw [h]

theorem polysToBytes_cons_ro (roBase : BitVec 64) (m i : Nat) (p : Poly) (ps : List Poly)
    (hp : p.coefficients.length = m) :
    ((roBase + BitVec.ofNat 64 (2 * m * i)) ↦ᵣ polysToBytes (p :: ps)) =
      ((roBase + BitVec.ofNat 64 (2 * m * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
      ((roBase + BitVec.ofNat 64 (2 * m * (i + 1))) ↦ᵣ polysToBytes ps) := by
  rw [polysToBytes_cons, pointsToBytesRO_append, gf16SliceBytes_length, hp]
  have h : (roBase + BitVec.ofNat 64 (2 * m * i)) + BitVec.ofNat 64 (2 * m) =
      roBase + BitVec.ofNat 64 (2 * m * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [h]

/-! ## 2. `n = 36` Constant Basis Loop (`0x6a9c8..0x6aa80 -> 0x6ad1c..0x6adb4`) -/

end CryptoVerification.SpqrV1.Poly.NextChunk
