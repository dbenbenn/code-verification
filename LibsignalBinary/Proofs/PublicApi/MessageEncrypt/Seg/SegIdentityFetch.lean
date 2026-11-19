/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalPublicApi
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Instruction Decode and Stepping Lemmas for `segIdentity_ok`

Decode and basic-block stepping lemmas for `+0x2c8..+0x344` (`Otr → Key`) of
`session_message_encrypt_with_stores` (`0x3caf4`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi

@[expose] def ikChunks6 (o : BitVec 64) (c0 : BitVec 32) (c4 : BitVec 16)
    (c6 c14 c22 : BitVec 64) (c30 : BitVec 16) : SepProp :=
  (o ↦₃₂ c0) ∗ ((o + 0x04#64) ↦₁₆ c4) ∗ ((o + 0x06#64) ↦₆₄ c6) ∗
  ((o + 0x0e#64) ↦₆₄ c14) ∗ ((o + 0x16#64) ↦₆₄ c22) ∗ ((o + 0x1e#64) ↦₁₆ c30)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
