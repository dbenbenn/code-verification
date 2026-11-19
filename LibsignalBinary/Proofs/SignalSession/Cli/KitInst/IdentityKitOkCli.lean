/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Instantiation of `IdentityStoreKitOkIE`

Specializes `IdKit.cliIdKitOkIE` to `cliExterns W` using the CLI
`read_file` and `subtle::black_box::<u8>` hook contracts.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

open ProofLib.ProgramReflection in
theorem cliExterns_blackBox (W : CliHooks) :
    Rust.withPanics (cliExterns W) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  Slots.cliExterns_sessionExterns_le W _ _ (by rfl_kernel)

end CryptoVerification.SignalSession.Cli.KitInst.IdKit

namespace CryptoVerification.SignalSession.Cli.KitInst

end CryptoVerification.SignalSession.Cli.KitInst
