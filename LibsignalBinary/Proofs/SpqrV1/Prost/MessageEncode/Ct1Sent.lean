/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent1
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93

/-!
# `prost::encoding::message::encode::<unchunked::Ct1Sent, Vec<u8>> [local#2]`

Verification of the second monomorphization
`prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]`
at `0x52d34` (`219` instructions, calling `Ct1Sent::encoded_len [local#2]`,
`encode_varint [local#1]`, `encode<Authenticator> [local#2]`,
`do_reserve_and_handle [local#7]`, and `memcpy`), plus unpinned bridges
for both `[local#1]` and `[local#2]`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

end CryptoVerification.SpqrV1.Prost.MessageEncode
