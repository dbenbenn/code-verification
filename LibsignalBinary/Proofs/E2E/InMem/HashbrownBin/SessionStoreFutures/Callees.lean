/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.ReserveRehash
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Callee Names and Offset Guards for `InMemSessionStore` Future Closures
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

abbrev stringCloneName : String :=
  "<alloc::string::String as core::clone::Clone>::clone"

abbrev sessionCloneName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"

abbrev vecVecCloneName : String :=
  "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
