/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

/-!
# X-Form Crate-10 `skip_field::<&mut &[u8]> [local#7]` Non-Group Cases

Proves the `depth = 0`, `.endGroup`, `.sixtyFourBit`, `.thirtyTwoBit`, `.varint`, and
`.lengthDelimited` arms of crate-10 `prost::encoding::skip_field::<&mut &[u8]> [local#7]` against
`(PrevDec.skipField3SpecAt A depth P).inImage img`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7A

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec
  (WireType skipBytes decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorFromSpecWithStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (decodeErrorHookStackX pointsTo64_pair_entails_memRegion16 sliceCursorAt sliceCursorAfter
   memRegion_48_split allocFailedIn_trans allowPanic_frame'
   cbz_depth_zero cbz_depth_succ w0_and_255_eq skipField_depth_zero skipField_succ_endGroup
   skipField_succ_sixtyFourBit skipField_succ_thirtyTwoBit skipField_succ_varint
   skipField_succ_lengthDelimited ule_len_of_lt ule_len_of_ge bv_len_sub_skip bv_ptr_add_skip
   bv_ptr_add_skip_top)
open CryptoVerification.SpqrV1.Varint (decodeVarint2SpecX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
  (skipField3SpecAt stackAt_skipField3 skipBelow3_leaf skipBelow3_leaf_entails
   skipBelow3_err skipBelow3_err_entails)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

abbrev skipField7Name : String :=
  CryptoVerification.CliC.SpqrV1.Varint.skipField3Name

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7A
