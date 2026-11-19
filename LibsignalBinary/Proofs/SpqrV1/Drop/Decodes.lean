/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.RustHeap.Alloc
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep -- proof-setup: allow-public-import
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# Instruction Decode Trees and Layout Offsets for SPQR V1 Drop Glue

Isolates `gen_decodes`, `ls_off%`, and `ls_stub%` invocations for SPQR V1 drop-glue functions so
that downstream symbolic execution files do not unpickle `libsignalSessionCode_tree`.
-/

public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.CodeLayout

abbrev deallocName : String := "__rustc::__rust_dealloc"

abbrev dropChainEpochSliceLocal1Name : String :=
  "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]"

abbrev dropChainEpochSliceLocal2Name : String :=
  "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]"

abbrev dropSpqrChainName : String :=
  "core::ptr::drop_glue::<spqr::chain::Chain>"

abbrev dropProtoEpochSliceName : String :=
  "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"

abbrev dropProtoSpqrChainName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]"

abbrev dropOptProtoSpqrChainName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"

abbrev dropPoly16Name : String :=
  "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

abbrev dropSortedSetPt16Name : String :=
  "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"

abbrev dropPolyEncoderLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]"

abbrev dropPolyDecoderName : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]"

abbrev dropPolyEncoderLocal2Name : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]"

abbrev dropProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"

abbrev dropOptProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"

abbrev dropUnchunkedCt1SentLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"

abbrev dropUnchunkedCt1SentLocal2Name : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"

abbrev dropUnchunkedEkSentName : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>"

abbrev dropOptProtoUnchunkedCt1SentName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]"

abbrev dropProtoUnchunkedCt1SentEkReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"

abbrev dropChunkedHeaderSentName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"

abbrev dropChunkedCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"

abbrev dropChunkedEkSentCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"

abbrev dropChunkedEkReceivedCt1SampledName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"

abbrev dropChunkedCt2SampledName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>"

abbrev dropProtoChunkedHeaderSentName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"

abbrev dropProtoChunkedEkSentCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"

abbrev dropProtoChunkedHeaderReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"

abbrev dropProtoChunkedNoHeaderReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"

abbrev dropProtoChunkedCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"

end CryptoVerification.SpqrV1.Drop

namespace CryptoVerification.SpqrV1.Layout.L1

open Lean Meta Elab Command Arm64 CryptoVerification.CodeLayout

syntax (name := genFnDecodesStx)
  "gen_fn_decodes " ident ident " [" str,* "]" : command

end CryptoVerification.SpqrV1.Layout.L1

namespace CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Layout.L1

end CryptoVerification.SpqrV1.Drop
