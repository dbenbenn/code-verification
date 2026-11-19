/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Top-Level `try_decrypt_with_state` Assembly for the CLI Image

Assembles `DecryptCallees` and the front/back decrypt segment proofs into `TryDecryptRunStmt`,
`TryDecryptEmptyRunStmt`, and `TryDecryptV1RunStmt` for the CLI image.
-/

public section

open Arm64 CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

local instance instHkdfHooks_decryptAssembly_trap (C : Crypto) (abs : String → Option (State → State)) :
    HkdfHooks C.F (trTrapExterns C abs) where
  memset := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memset (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  memcpy := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memcpy (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  compress256 := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.compress256 (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)

end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

/-! ## Top-Level `try_decrypt_with_state` Run Theorems -/

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly
