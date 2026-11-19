/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractDefsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Segments

Proves the prologue, initial `new_from_slice` call, and `ikm` absorption (`0x63284 → 0x633cc`)
under `HkdfStubsExt` and `HPreExt`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64
  read8_write64_264_271

section ExtractSegments

private theorem s2Frame_disj_208_hi {s₀ : State} {n : ℕ} {off : BitVec 64} {sz : ℕ}
    (hn : n < 64) (hoff : decide (272 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 688) = true) :
    ∀ r ∈ [(hsp s₀ + 208#64, n), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff; intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

end ExtractSegments

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof
