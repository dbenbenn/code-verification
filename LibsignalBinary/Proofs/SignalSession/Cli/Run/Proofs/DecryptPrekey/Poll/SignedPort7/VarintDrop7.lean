/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import ProofLib.GenDecodes
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.VarintSlow

/-!
# X-Form Crate-10 `decode_varint [local#6]` and `drop_glue<DecodeError> [local#3]`

Proves `decodeVarint6_ok_of_alloc_x` and `dropDecodeError3_ok_of_alloc_x` on
`tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
