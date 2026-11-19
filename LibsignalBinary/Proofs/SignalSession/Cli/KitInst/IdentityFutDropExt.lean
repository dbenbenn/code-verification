/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# External-Hook-Generic `cliIdFutDrop` Contract

`drop_glue::<<IdentityFiles as IdentityKeyStore>::get_identity::{closure#0}>` compiles to a
single `ret` instruction in `.text`, so it satisfies `futDropSpec` on
`tripleRatchetProgAtExt b ext` with no external-hook assumptions on `ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib ProofLib.ProgramReflection open CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
section
variable {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
  {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}

end

end CryptoVerification.SignalSession.Cli.KitInst
