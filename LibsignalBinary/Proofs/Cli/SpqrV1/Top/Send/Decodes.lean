/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
import ProofLib.Lemmas
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Decode Lemmas & `.rodata` Jump Tables for `spqr::send::<signal_session_ratchet::Coins>`

Generates instruction-decode lemmas and unpacks the `.rodata` jump tables (`0x9d4f0`,
`0x9d506`, `0x9d51c`) for `spqr::send::<signal_session_ratchet::Coins>` in the CLI image.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification

open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

/-- Symbol name of `spqr::send::<signal_session_ratchet::Coins>` (3,436 instructions). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName : String :=
  "spqr::send::<libsignal_cli_ratchet::Coins>"

end CryptoVerification.SpqrV1.Top.Send
