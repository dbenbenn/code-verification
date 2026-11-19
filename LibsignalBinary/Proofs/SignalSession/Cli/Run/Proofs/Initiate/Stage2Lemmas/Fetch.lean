/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option maxRecDepth 200000

section Decodes

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

end Decodes

abbrev staticSecretDropName : String :=
  "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"

abbrev handleErrorName : String :=
  "alloc::raw_vec::handle_error"

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
