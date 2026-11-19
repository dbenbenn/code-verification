/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
public import ProofLib.FsTrace
public import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.Placed.GenLsBlockFast

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Relocatable `strlen` and `from_utf8` Callee Contracts for `main`

Relocatable (`[LibsignalPlacement]`) subroutine contracts for `strlen` and
`core::str::converts::from_utf8` (ASCII) on Block `617`, discharging the corresponding fields of
`MainCalleesPlaced`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.SignalSession.Cli.MainHops
