/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Contract-Backed Stack & Callee Bridges

Postcondition `recvCt2ChunkPostQExt` (`20,272`-byte stack), bottom `720`-byte stack framing,
and `.inImage img` bridges for `hkdf_to_slice` and `Authenticator::update`.
-/

public section

set_option autoImplicit false

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
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem stackAt_extHook_eq_authUpdateExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 720 ∗
      (memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack) =
      stackAt (sp - 2496#64) authUpdateStackExt := by
  have h1 := stackAt_polyDecodedMessage_eq_extHook (sp - 2496#64)
  have h2 := stackAt_authUpdateExt_eq_poly (sp - 2496#64)
  have hsub1 : (sp - 2496#64) - 17056#64 = sp - 19552#64 := by bv_kernel
  have hsub2 : (sp - 2496#64) - 17776#64 = sp - 20272#64 := by bv_kernel
  rw [hsub1] at h1
  rw [hsub2] at h2
  rw [← h1, ← h2]

theorem stackAt_hkdfToSliceExt_eq_authUpdateExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 160 ∗ stackAt (sp - 2496#64) hkdfToSliceStackExt =
      stackAt (sp - 2496#64) authUpdateStackExt := by
  have h := stackAt_authUpdateExt_eq_hkdfExt (sp - 2496#64)
  have hsub : (sp - 2496#64) - 17776#64 = sp - 20272#64 := by bv_kernel
  rw [hsub] at h
  exact h.symm

theorem stackAt_extHook_eq_hkdfToSliceExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 720 ∗
      (memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack) =
      memRegion (sp - 20272#64) 160 ∗ stackAt (sp - 2496#64) hkdfToSliceStackExt := by
  rw [stackAt_extHook_eq_authUpdateExt sp, stackAt_hkdfToSliceExt_eq_authUpdateExt sp]

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
