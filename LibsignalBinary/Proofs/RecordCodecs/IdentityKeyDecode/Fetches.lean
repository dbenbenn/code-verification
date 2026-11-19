/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsBinary -- proof-setup: allow-public-import

/-!
# `IdentityKey::decode` Instruction Fetches and Call Transfer

Instruction-fetch lemmas and `[LibsignalPlacement]` cross-block call transfer for
`IdentityKey::decode` (Block `18`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers

open Arm64 ProofLib CryptoVerification.LibsignalTripleRatchet
open CryptoVerification CryptoVerification.RecordCodecs.Placed

theorem ikDec_pkTryFrom_placed_call_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpk : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedSpec) :
    subroutine_ok (lsProg_18 H) (lsmpl.base 211)
      (withLsCl lsmpl pkTryFromPlacedSpec) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_18 H) hpk

end CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers
