/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import ProofLib.SepLogic.WPp

/-!
# CLI Unchunked `EkSentCt1Received` and `Ct1Sent` Encoder Definitions

Generates instruction decode lemmas and defines symbol names, `fnOff` lemmas, and `subroutine_ok`
predicates for `EkSentCt1Received` and `Ct1Sent` message encoders (`[local#3]`) on the CLI image.
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalTripleRatchet.Prost

open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Varint

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- CLI symbol name for `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>> [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]"

/-- CLI symbol name for `prost::encoding::message::encode::<Ct1Sent, Vec<u8>> [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]"

end CryptoVerification.SpqrV1.Prost.MessageEncode
