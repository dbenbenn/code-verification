/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

/-!
# X-Form Crate-10 `bytes::merge [local#7]` Verification

Proves error epilogues (`+0x074`, `+0x07c`), Phase 1 (`+0x000..+0x074`), and top-level X-form
contracts `bytesMerge7_ok_of_alloc_x` (`bytesMerge3Spec A img`) and
`bytesMerge7_proto_ok_of_alloc_x` (`bytesMerge3ProtoSpec A img`) on
`tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc vecU8At allocFailedIn)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk bytesMergeRawSpecX MergePostX MergePanicX
   savedRegsStack bm_HighCalleeSaved spAligned_sub_224
   decodeVarintSliceStackX decodeErrorHookStackX
   sliceCursorAt sliceCursorAfter
   DecodeVarintSlowGhost
   fold_stackAt_bytesMergeX stackAt_sliceX_to_decodeErrorX
   session2ShimSpecBMX session2MemcpySpecBMX
   bm_decodeVarint_suffix mergeBytes_of_decodeVarint_none
   mergeBytes_lengthDelimited_underflow mergeBytes_ne_lengthDelimited
   sliceCursorAfter_to_err fold_memRegion_40_bytes fold_slot_16
   mask_ff_32_of_setWidth8)
open CryptoVerification.SpqrV1.Varint (decodeVarint2StackX decodeVarint2SpecX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (bytesMerge3RawSpec bytesMerge3ProtoRawSpec BytesMergeProtoGhost protoWireTypeToCodec_toNat proto_mergeBytes_toOption stackAt_bytesMerge3_entry stackAt_varint2_to_slice)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.DoReserve11 (doReserve11Name)

open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23 (bytesMerge7Name decodeVarint6Name bm7Off050 bm7Off074 bm7Off07c bm7Off094)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7
