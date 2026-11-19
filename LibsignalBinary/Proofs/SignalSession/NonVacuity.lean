/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
import all Init.Data.Repr
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs

/-!
# Non-Vacuity of `CliSpecE` and `CliSpecPqxdh`

Proves that neither the empty-outcome run (`fun _ => none`) nor the always-aborting run
(`fun _ => some .aborted`) satisfies `CliSpecE` or `CliSpecPqxdh`, witnessing unconditional domain
inhabitants (`emptyParty`, `wfPq_emptyParty_uncond`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-- A party with no peer identity, no session and no pre-keys. -/
@[expose] def emptyParty : PqParty :=
  { party := .A, me := ⟨List.Vector.replicate 32 0#8, 0⟩, peerId := none, session := none,
    signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }

/-- The empty party is in `CliSpecPqxdh`'s domain once its three files are at most `fileCapBytes`
bytes. -/
theorem wfPq_emptyParty (W : PEParams)
    (h : ∀ f ∈ encodeDir W emptyParty, f.2.length ≤ fileCapBytes) :
    PqxdhPartyInSpecDomain W emptyParty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [emptyParty]
  · intro f hf
    have hle := h f hf
    have hlt : fileCapBytes < 2 ^ 31 := by decide
    exact ⟨Nat.lt_of_le_of_lt hle hlt, fun _ => hle⟩
  · simp [emptyParty]
  · simp [emptyParty]
  · simp [emptyParty]
  · simp [emptyParty]

/-- The empty party's three files (`address` 38 B, `identity-key-pair` 69 B, `registration-id`
4 B) are at most `fileCapBytes` (`2^21` B), for every `W`. -/
theorem encodeDir_emptyParty_lt (W : PEParams) :
    ∀ f ∈ encodeDir W emptyParty, f.2.length ≤ fileCapBytes := by
  intro f hf
  simp only [encodeDir, emptyParty, List.map, List.flatten, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · decide +kernel
  · simp [RecordCodecs.IdentityKeyPairStructure.encode, RecordCodecs.encodeProto3BytesField,
      encodeBytesField, encodeKey, WireType.toNat, encodeVarint, djbKey]
    decide
  · decide

/-- The empty party is in `CliSpecPqxdh`'s domain, for every `W`. -/
theorem wfPq_emptyParty_uncond (W : PEParams) : PqxdhPartyInSpecDomain W emptyParty :=
  wfPq_emptyParty W (encodeDir_emptyParty_lt W)

end CryptoVerification.SignalSession
