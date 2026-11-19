/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1Chunk
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyDecoder as Decoder>::decoded_message` Bridge & `<HeaderSent>::recv_ct1_chunk`

**Checked by Lean.**

Bridges `Poly.DecodedMessage.polyDecoderDecodedMessage_ok` (`decodedMessageSpec A b`) to
`Leaves.polyDecoderDecodedMessageSpec A b`, and discharges `add_chunk_ok_ext`,
`polyDecoderDecodedMessage_ok_ext`, and `hA.dealloc` in `<HeaderSent>::recv_ct1_chunk` (`0x5d8fc`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

theorem optVecU8Of_eq_optVecU8At (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optVecU8At A a opt := by
  cases opt <;> rfl

end CryptoVerification.SpqrV1.States.Leaves
