/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `Poly::lagrange_sum` Loop and Basis Deallocation

**Checked by Lean.**

Verifies the `Poly::lagrange_sum` accumulation loop (`0x6adb4..0x6b2c8`, `+2608 -> +3908`),
`Vec<Poly>` basis deallocation (`+3908 -> +4004`), and combined `lagrangeSumAndFree_sepWPp`.
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

/-! ## 1. `Poly::lagrange_sum` Loop (`0x6adb4..0x6b2c8`, `+2608 -> +3908`) -/

@[local arm64_norm, local wp_norm]
theorem sub1_ofNat_sum (m : Nat) :
    BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  have h : BitVec.ofNat 64 (m + 1) = BitVec.ofNat 64 m + 1#64 := by
    rw [BitVec.ofNat_add]
  rw [h]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub1_ofNat_sum_add (m : Nat) :
    BitVec.ofNat 64 (m + 1) + 18446744073709551615#64 = BitVec.ofNat 64 m := by
  have h1 : (18446744073709551615#64 : BitVec 64) = -1#64 := rfl
  have h2 : BitVec.ofNat 64 (m + 1) = BitVec.ofNat 64 m + 1#64 := by
    rw [BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

theorem beq_m1_one_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (m + 1) == 1#64) = decide (m = 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_false_iff_not.mpr h, beq_eq_false_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change m + 1 = 1 at hto; omega

@[local arm64_norm, local wp_norm]
theorem mul24_ofNat_sum (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (24 * n) := by
  have h1 : (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 =
      24#64 * BitVec.ofNat 64 n := by bv_bits
  have h2 : BitVec.ofNat 64 (24 * n) = 24#64 * BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_mul]
  rw [h1, h2]

@[local arm64_norm, local wp_norm]
theorem mul24_ofNat_sum_nat (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 = BitVec.ofNat 64 (24 * n) :=
  mul24_ofNat_sum n

end CryptoVerification.SpqrV1.Poly.NextChunk
