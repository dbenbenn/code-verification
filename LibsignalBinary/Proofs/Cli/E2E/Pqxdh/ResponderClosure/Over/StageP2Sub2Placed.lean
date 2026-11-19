/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym

/-!
# Placed Stage P2 Over-Path Scratch-Region Split Helper

Lifts the 88-byte `sp + 0x3e0` scratch-region split (`16 + 72` bytes) under `[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
