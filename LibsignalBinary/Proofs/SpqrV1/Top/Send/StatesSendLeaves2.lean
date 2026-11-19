/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` Leaf-Call Arms

**Checked by Lean.**

Verifies the six leaf-call arms of `<States>::send` inlined in `spqr::send` (`0x3085c`):
`.headerSent`, `.ct1Received`, `.keysSampled`, `.ct1Sampled`, `.ct2Sampled`, and
`.ekReceivedCt1Sampled`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



theorem keysSampled_send_hdr_chunk_to_ct1Received {F : ShaCompress}
    {st outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_hdr_chunk = .ok (outSt, chunk)) :
    (chunkedKeysSampledToCt1Received st).send_ek_chunk =
      .ok (chunkedKeysSampledToCt1Received outSt, chunk) := by
  unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at h
  unfold Chunked.SendEk.Ct1Received.send_ek_chunk chunkedKeysSampledToCt1Received
  dsimp only [Bind.bind, Except.bind] at h ⊢
  cases hnc : spqrPolyApi.next_chunk st.sending_hdr with
  | error e => rw [hnc] at h; contradiction
  | ok p => rw [hnc] at h; rcases p with ⟨enc', ch⟩; cases h; rfl

end CryptoVerification.SpqrV1.Top.Send
