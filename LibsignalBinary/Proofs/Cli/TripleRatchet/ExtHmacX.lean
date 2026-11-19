/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsB
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# `crypto::hmac_sha256` Verification under `HkdfContractsExt`

Composes `seg0a` through `seg4b` with `nfs32_runsTo_ext_x` to prove `hmac_sha256_ok_of_hkdfContracts`
on `tripleRatchetProgAtExt img.base ext` at stack budget `2048 + extHookStack = 18432` bytes.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding RW length_hmacWith
open CryptoVerification.SignalSession
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (session2MemsetExternSpec compress256ExternShaSpec)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
