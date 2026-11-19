/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Proof
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1c
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2b
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2c
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3c
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Top-Level Verification

**Checked by Lean.** Composes all segments (`Part1`..`Part3c`) of `<EkSentCt1Received>::recv_ct2_chunk`
(`0x5ec2c .. 0x5f434`, `514` instructions) to prove `recv_ct2_chunk_ok_x` and `recv_ct2_chunk_ok_ext`.
-/

public section

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk

/-! ## Bridging `DecodedMessageOkExt` to `PolyDecodedMessageOkX` -/

theorem optVecU8Of_eq_optKeyBytesAt (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

theorem lt_128_of_compare_prefix_drop_bne {ct2Full tag : List (BitVec 8)}
    (hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    128 < ct2Full.length := by
  by_contra hle
  have hdrop : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, compare_prefix] at hcmp
  change (isNonZero 0#8 != 0#8) = true at hcmp
  revert hcmp; decide

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
