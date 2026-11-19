/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Top-Level Proof

**Checked by Lean.**

Composes prologue allocation, `collectPointsVecs` loops, `Option<Poly>` cache initialization, the
main evaluation/interpolation loop, and cache/epilogue drop glue to prove
`polyDecoderDecodedMessage_ok` (`0x6bb80..0x6c390`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName LagrangePrepareArgs lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompleteName LagrangeCompleteArgs lagrangeCompletePure lagrangeCompletePure_length lagrangeCompleteStack)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local wp_norm ↓, local arm64_norm ↓] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.sp_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg64_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg32_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg_setPC_pre
  CryptoVerification.SpqrV1.GF.UnacceleratedMul.readReg_setMem_setPC_pre

/-! ## Initialization of `polys: [Option<Poly>; 16]` (`0x6bce0..0x6bd28`, `+352..+424`) -/

attribute [local wp_norm, local arm64_norm] bv64_lsl1_norm_proof

end CryptoVerification.SpqrV1.Poly.DecodedMessage
