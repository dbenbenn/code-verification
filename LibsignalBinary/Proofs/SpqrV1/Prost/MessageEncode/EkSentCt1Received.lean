/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<unchunked::EkSentCt1Received, Vec<u8>> [local#2]`

Verification of the second monomorphization
`prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#2]`
at `0x52a9c` (`166` instructions, calling `EkSentCt1Received::encoded_len [local#2]`,
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

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSaved.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

theorem ekSentCt1ReceivedEncode_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EkSentCt1ReceivedEncodeGhost} {g : Unchunked4PBGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOf resStack A).post
      ⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (ekSentCt1ReceivedEncodeSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf] at hq
  dsimp only [ekSentCt1ReceivedEncodeSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
    A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ ekSentCt1ReceivedPBPinnedAt A g x.msgA x.m ∗ Rest := by convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ ekSentCt1ReceivedPBAt A x.msgA x.m ∗ Rest := by
    rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]; exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem ekSentCt1ReceivedEncode_unpinned_of_pinned {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (ekSentCt1ReceivedEncodePinnedSpecOf resStack A)) :
    subroutine_ok prog entry (ekSentCt1ReceivedEncodeSpecOf resStack A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [ekSentCt1ReceivedEncodeSpecOf] at hpre
  rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre hsp).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, ekSentCt1ReceivedEncode_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

end CryptoVerification.SpqrV1.Prost.MessageEncode
