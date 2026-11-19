/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs -- shake: keep
public section

set_option autoImplicit false

/-!
# Kernel Instruction Decode Lemmas for `Chain::clone [local#1]`
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells

abbrev chainCloneLocal1Name : String :=
  "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
