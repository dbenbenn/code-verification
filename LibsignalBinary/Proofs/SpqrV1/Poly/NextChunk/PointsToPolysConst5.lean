/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Constant Basis `n = 5` and Shared Loop Exit

**Checked by Lean.**

Verifies `basis_n5_sepWPp` (`+1136 -> +2608`) from `COMPLETE_POINTS_POLYS_5` and the shared
`accPtr` allocation exit block `basis_loop_exit_sepWPp` (`+2456 -> +2608`) for `n ∈ {30, 34, 36}`.
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two' :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight' :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

private theorem add_page_mask_6a000 (b off : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hoff : (0x64f8c#64 + off) &&& 0xfff#64 = (0x64f8c#64 + off) - 0x65000#64) :
    ((b + 0x64f8c#64) + off) &&& 0xfffffffffffff000#64 = b + 0x65000#64 := by
  bv_robdd

private theorem shl_one_eq_two_mul (x : BitVec 64) : x <<< (1 : Nat) = 2#64 * x := by bv_robdd
private theorem shl_one_bv_eq_two_mul (x : BitVec 64) : x <<< 1#64 = 2#64 * x := by bv_robdd

end CryptoVerification.SpqrV1.Poly.NextChunk
