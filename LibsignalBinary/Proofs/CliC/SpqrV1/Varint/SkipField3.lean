/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas

/-!
# `prost::encoding::skip_field` Proof for `CliC`

Proves `skipField3Spec` for `CliC` `prost::encoding::skip_field::<&mut &[u8]>` across all seven
wire-type/depth cases by induction on recursion depth.
-/

public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev _root_.CryptoVerification.CliC.SpqrV1.Varint.skipField3Name : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#6]"

end CryptoVerification.SpqrV1.Varint
