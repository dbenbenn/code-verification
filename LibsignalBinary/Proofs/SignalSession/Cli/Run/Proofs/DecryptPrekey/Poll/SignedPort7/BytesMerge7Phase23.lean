/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.DoReserve11 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXPhase2
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# X-Form Crate-10 `bytes::merge [local#6]` Phases 2 and 3

Proves the vtable-drop epilogue (`+0x254`), Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2c8`:
`Vec::clear`, `Vec::reserve`, `memcpy`, `vtable.drop`), and Phase 2 (`+0x094..+0x20c`:
`BytesMut::with_capacity`, `memcpy`, `bytes::from_vec`) for crate-10 `bytes::merge`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc vecU8At vecHeader allocFailedIn allocFailedEvent)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (extHookStack rustAllocSpecWithStack allocFailedIn_of_eq doReserveStackX doReserveSpecX reserveCap bytesFromVecName bytesFromVecStack bytesPtr bytesData bytesBoxU8Buf bytesVtableDropStackX bytesVtableDropSpecX decodeErrorFromSpecWithStack KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (mergeBytes_length_sumX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk bytesMergeCapOk_mono bytesMergeCapOk_reserveCap_bound
   bytesMergeCapOk_after_reserve bytesMergeRawSpecX MergePostX MergePanicX
   savedRegsStack bm_HighCalleeSaved spAligned_sub_224
   decodeVarintSliceStackX decodeErrorHookStackX
   sliceCursorAfter
   fold_stackAt_bytesMergeX stackAt_sliceX_to_decodeErrorX stackAt_sliceX_to_allocX
   stackAt_sliceX_to_bytesFromVecX stackAt_sliceX_to_doReserveX stackAt_sliceX_to_vtableDropX
   session2ShimSpecBMX session2MemcpySpecBMX
   bm_vecU8Buf bm_vecU8At_eq_header_sep_buf fold_vecU8At_clear
   vecU8At_nil_eq fold_vecU8At_copied bytesBoxU8Buf_nonempty fold_bytesBoxU8Buf_nonempty
   vecU8At_entails_exists
   fold_vecU8At_sp136 unfold_vecHeader_sp136 memRegion_104_fold
   bm_decodeVarint_suffix mergeBytes_lengthDelimited_ok vecU8Buf_nil_one
   sliceCursorAfter_split_copy sliceCursorAfter_advance_fold fold_vecU8Buf_nonempty
   bytesMutDataWord bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
   bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
   bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
   bitvec_sub_self_64 bitvec_if_zero_ult_self)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.DoReserve11
  (doReserve11Name)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Layout-Independent Symbol & Offset Constants for `bytes::merge [local#6]` -/

abbrev bytesMerge7Name : String :=
  CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.bytesMerge3Name

abbrev decodeVarint6Name : String :=
  CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name

abbrev bm7Off050 : BitVec 64 := 80#64
abbrev bm7Off074 : BitVec 64 := 116#64
abbrev bm7Off07c : BitVec 64 := 124#64
abbrev bm7Off094 : BitVec 64 := 148#64
abbrev bm7Off0e4 : BitVec 64 := 228#64
abbrev bm7Off1b8 : BitVec 64 := 440#64
abbrev bm7Off210 : BitVec 64 := 528#64
abbrev bm7Off220 : BitVec 64 := 544#64
abbrev bm7Off230 : BitVec 64 := 560#64
abbrev bm7Off254 : BitVec 64 := 596#64
abbrev bm7Off29c : BitVec 64 := 668#64
abbrev bm7Off2c8 : BitVec 64 := 712#64

attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  CryptoVerification.LibsignalTripleRatchet.Prost.bitvec_ult_self
  bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## 2. Drop Epilogue (`+0x254`) & Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2c8`) -/

private theorem mergePanicX_of_allocFailed {A : RustAlloc} {x : BytesMergeGhost}
    {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpecX A).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpecX, allocFailedIn] at hm ⊢; rw [htr] at hm; exact allowPanic_frame id hm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23
