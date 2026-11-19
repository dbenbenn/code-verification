/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# Constant-Time Equality and `sha2::compress256` Hook Bridges

Derives `subtle::black_box::<u8>` and `sha2::sha256::compress256` hook agreement from
`CliExternsOk` and `AgreeOnCliHooks`.
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

theorem hookSat_blackBox32_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' "subtle::black_box::<u8>" CliExt.blackBoxSpec :=
  hAg.hookSat (by decide) hOk.blackBox

theorem hookSat_compress256_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' "sha2::sha256::compress256" (CliExt.compress256Spec P.C) :=
  hAg.hookSat (by decide) hOk.compress256

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq
