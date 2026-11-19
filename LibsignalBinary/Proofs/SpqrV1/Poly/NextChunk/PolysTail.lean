/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFast -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Polynomial Evaluation Tail Loop

Verifies the polynomial evaluation tail loop (`+296 -> +4484`) executed on indices `i0..15` after
`points_to_polys` transitions the encoder from `EncoderState::Points` to `EncoderState::Polys`.
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
  madd_24_eq madd_24_eq' ofNat_add_one_eq
  ofNat_two_mul_add_one ofNat_two_mul_add_two

/-! ## 1. Arithmetic & List Helpers for the Tail Loop -/

theorem trunc8_zext64_trunc32_of_trunc16 {w0 : BitVec 64} {v : BitVec 16}
    (h : w0.truncate 16 = v) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w0)) =
      BitVec.setWidth 8 v := by
  revert h; bv_slice

theorem ubfx8_trunc8_of_trunc16 {w0 : BitVec 64} {v : BitVec 16}
    (h : w0.truncate 16 = v) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w0) >>> 8 &&& 255#64) =
      BitVec.setWidth 8 (v >>> 8) := by
  revert h; bv_slice

end CryptoVerification.SpqrV1.Poly.NextChunk
