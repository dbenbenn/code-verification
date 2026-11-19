/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Shared Base for `prost::encoding::message::encode` on `unchunked::EkSentCt1Received` and `unchunked::Ct1Sent`

Shared instruction decode lemmas (`0x37a10..0x37f7c` and `0x52a9c..0x530a0`), symbol names,
pure encoding model bridge lemmas, and specifications for:
1. `prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#1, #2]`
   (`0x37a10`, 150 insns; `0x52a9c`, 166 insns)
2. `prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#1, #2]`
   (`0x37c68`, 197 insns; `0x52d34`, 219 insns)
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

abbrev ekSentCt1ReceivedEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#1]"

abbrev ekSentCt1ReceivedEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#2]"

abbrev ct1SentEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#1]"

abbrev ct1SentEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]"

/-- Stack budget for `encode<EkSentCt1Received>` and `encode<Ct1Sent>` parameterized by `resStack`:
`64 + authEncodeStackOf resStack = 128 + (0x30 + resStack)` bytes
(`0x40 = 64` B own frame + `authEncodeStackOf resStack` for `encode<Authenticator>`). -/
abbrev unchunkedMsgEncodeStackOf (resStack : Nat) : Nat := 64 + authEncodeStackOf resStack

/-- Stack budget at `doReserveStack` (`4384` B). -/
abbrev unchunkedMsgEncodeStack : Nat := unchunkedMsgEncodeStackOf doReserveStack

/-- Stack budget at `doReserveStackX` (`16624` B). -/
abbrev unchunkedMsgEncodeStackX : Nat := unchunkedMsgEncodeStackOf doReserveStackX

/-! ## 2. Pure Model Equivalence & Decomposition Lemmas -/

theorem protoEncodeKey_1_varint :
    Proto.encodeKey 1#32 .varint = [0x08#8] := rfl

theorem protoEncodeKey_3_lengthDelimited :
    Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := rfl

theorem protoEncodeKey_4_lengthDelimited :
    Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := rfl

theorem protoEncodeKey_5_lengthDelimited :
    Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] := rfl

theorem protoEncodeKey_6_lengthDelimited :
    Proto.encodeKey 6#32 .lengthDelimited = [0x32#8] := rfl

theorem protoEncodeKey_7_lengthDelimited :
    Proto.encodeKey 7#32 .lengthDelimited = [0x3a#8] := rfl

theorem protoEncodeU64Field_zero (tag : BitVec 32) :
    Proto.encodeUint64Field tag 0#64 = [] := rfl

theorem protoEncodeU64Field_1_of_ne_zero {v : BitVec 64} (hne : v ≠ 0#64) :
    Proto.encodeUint64Field 1#32 v =
      [0x08#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint v := by
  have hbeq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [Proto.encodeUint64Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_1_varint, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_3_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 3#32 bs =
      [0x1a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_3_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_4_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 4#32 bs =
      [0x22#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_4_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_5_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 5#32 bs =
      [0x2a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_5_lengthDelimited, protoEncodeVarint_eq_codec]

/-- Pure bytes appended by `encode<EkSentCt1Received>` (`tag = 1`, length-delimited):
`Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m`
(definitionally equal to `Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 (some m)`). -/
abbrev encodeEkSentCt1ReceivedMsg (m : V1State.Unchunked.EkSentCt1Received) : List (BitVec 8) :=
  Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m

/-- Pure bytes appended by `encode<Ct1Sent>` (`tag = 1`, length-delimited):
`Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m`
(definitionally equal to `Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 (some m)`). -/
abbrev encodeCt1SentMsg (m : V1State.Unchunked.Ct1Sent) : List (BitVec 8) :=
  Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m

/-- Outer message header bytes (`tag = 1`, length-delimited: `0x0a#8` + `encodeVarint innerLen`). -/
@[expose] def msgHeaderBytes (innerLen : Nat) : List (BitVec 8) :=
  [0x0a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 innerLen)

/-- Encoded `epoch: u64` field (`tag = 1`, varint). -/
@[expose] def u64Field1Bytes (epoch : BitVec 64) : List (BitVec 8) :=
  Proto.encodeUint64Field 1#32 epoch

/-- Encoded `auth: Option<Authenticator>` field (`tag = 2`, length-delimited). -/
@[expose] def optAuthField2Bytes (auth : Option AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth

/-- Encoded `Vec<u8>` field with tag `tag` (length-delimited). -/
@[expose] def bytesFieldTagged (tag : BitVec 32) (bs : List (BitVec 8)) : List (BitVec 8) :=
  Proto.encodeBytesField tag bs

theorem bs_append_msgHeaderBytes (bs : List (BitVec 8)) (innerLen : Nat) :
    (bs ++ [0x0a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 innerLen) =
      bs ++ msgHeaderBytes innerLen := by
  simp only [msgHeaderBytes, List.append_assoc]

theorem msgHeaderBytes_len_bounds (innerLen : Nat) :
    2 ≤ (msgHeaderBytes innerLen).length ∧ (msgHeaderBytes innerLen).length ≤ 11 := by
  have hb := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 innerLen)
  simp only [msgHeaderBytes, List.length_append, List.length_singleton]
  omega

theorem bs_append_u64Field1Bytes_of_ne_zero {epoch : BitVec 64} (hne : epoch ≠ 0#64)
    (bs : List (BitVec 8)) :
    (bs ++ [0x08#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint epoch =
      bs ++ u64Field1Bytes epoch := by
  rw [u64Field1Bytes, protoEncodeU64Field_1_of_ne_zero hne]
  simp only [List.append_assoc]

theorem bs_append_u64Field1Bytes_of_zero {epoch : BitVec 64} (hz : epoch = 0#64)
    (bs : List (BitVec 8)) :
    bs = bs ++ u64Field1Bytes epoch := by
  subst hz
  simp only [u64Field1Bytes, protoEncodeU64Field_zero, List.append_nil]

theorem u64Field1Bytes_len_of_ne_zero {epoch : BitVec 64} (hne : epoch ≠ 0#64) :
    (u64Field1Bytes epoch).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length := by
  rw [u64Field1Bytes, protoEncodeU64Field_1_of_ne_zero hne]
  simp only [List.length_append, List.length_singleton]

theorem bs_append_optAuthField2Bytes_some (bs : List (BitVec 8)) (au : AuthenticatorPB) :
    bs ++ encodeAuthMsg au = bs ++ optAuthField2Bytes (some au) := rfl

theorem bs_append_optAuthField2Bytes_none (bs : List (BitVec 8)) :
    bs = bs ++ optAuthField2Bytes none := by
  simp only [optAuthField2Bytes, Proto.encodeOptMessage, List.append_nil]

theorem bs_append_bytesField3_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 3#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_3_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesField4_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x22#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 4#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_4_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesField5_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x2a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 5#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_5_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesFieldTagged_of_empty (tag : BitVec 32) {f : List (BitVec 8)}
    (hemp : f.isEmpty = true) (bs : List (BitVec 8)) :
    bs = bs ++ bytesFieldTagged tag f := by
  have hnil : f = [] := List.isEmpty_iff.mp hemp
  subst hnil
  simp only [bytesFieldTagged, protoEncodeBytesField_nil, List.append_nil]

theorem bytesField3_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 3#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_3_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem bytesField4_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 4#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_4_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem bytesField5_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 5#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_5_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem encodeEkSentCt1ReceivedMsg_eq_parts (m : V1State.Unchunked.EkSentCt1Received) :
    encodeEkSentCt1ReceivedMsg m =
      msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m) ++
        u64Field1Bytes m.epoch ++
        optAuthField2Bytes m.auth ++
        bytesFieldTagged 3#32 m.dk ++
        bytesFieldTagged 4#32 m.ct1 := by
  have hlen : (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length = ekSentCt1ReceivedPBEncodedLen m :=
    ekSentCt1ReceivedPBEncodedLen_eq_proto m
  dsimp only [encodeEkSentCt1ReceivedMsg, Proto.encodeMessage, msgHeaderBytes, u64Field1Bytes,
    optAuthField2Bytes, bytesFieldTagged]
  rw [hlen, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [V1State.Unchunked.EkSentCt1Received.encodeRaw, Proto.encodeUint64Field, List.append_assoc]

theorem bs0_append_encodeEkSentCt1ReceivedMsg (bs0 : List (BitVec 8))
    (m : V1State.Unchunked.EkSentCt1Received) :
    ((((bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ++ u64Field1Bytes m.epoch) ++
      optAuthField2Bytes m.auth) ++ bytesFieldTagged 3#32 m.dk) ++ bytesFieldTagged 4#32 m.ct1 =
      bs0 ++ encodeEkSentCt1ReceivedMsg m := by
  rw [encodeEkSentCt1ReceivedMsg_eq_parts]
  simp only [List.append_assoc]

theorem encodeEkSentCt1ReceivedMsg_len_split (m : V1State.Unchunked.EkSentCt1Received) :
    (encodeEkSentCt1ReceivedMsg m).length =
      (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length +
        (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.dk).length +
        (bytesFieldTagged 4#32 m.ct1).length := by
  rw [encodeEkSentCt1ReceivedMsg_eq_parts]
  simp only [List.length_append, Nat.add_assoc]

theorem ekSentCt1ReceivedPBEncodedLen_eq_fields_len (m : V1State.Unchunked.EkSentCt1Received) :
    ekSentCt1ReceivedPBEncodedLen m =
      (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.dk).length +
        (bytesFieldTagged 4#32 m.ct1).length := by
  have h := ekSentCt1ReceivedPBEncodedLen_eq_proto m
  rw [← h]
  simp only [V1State.Unchunked.EkSentCt1Received.encodedLen,
    V1State.Unchunked.EkSentCt1Received.encodeRaw, Proto.encodeUint64Field,
    u64Field1Bytes, optAuthField2Bytes, bytesFieldTagged, List.length_append, Nat.add_assoc]

theorem encodeCt1SentMsg_eq_parts (m : V1State.Unchunked.Ct1Sent) :
    encodeCt1SentMsg m =
      msgHeaderBytes (ct1SentPBEncodedLen m) ++
        u64Field1Bytes m.epoch ++
        optAuthField2Bytes m.auth ++
        bytesFieldTagged 3#32 m.hdr ++
        bytesFieldTagged 4#32 m.es ++
        bytesFieldTagged 5#32 m.ct1 := by
  have hlen : (V1State.Unchunked.Ct1Sent.encodeRaw m).length = ct1SentPBEncodedLen m :=
    ct1SentPBEncodedLen_eq_proto m
  dsimp only [encodeCt1SentMsg, Proto.encodeMessage, msgHeaderBytes, u64Field1Bytes,
    optAuthField2Bytes, bytesFieldTagged]
  rw [hlen, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [V1State.Unchunked.Ct1Sent.encodeRaw, Proto.encodeUint64Field, List.append_assoc]

theorem bs0_append_encodeCt1SentMsg (bs0 : List (BitVec 8))
    (m : V1State.Unchunked.Ct1Sent) :
    (((((bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ++ u64Field1Bytes m.epoch) ++
      optAuthField2Bytes m.auth) ++ bytesFieldTagged 3#32 m.hdr) ++ bytesFieldTagged 4#32 m.es) ++
      bytesFieldTagged 5#32 m.ct1 =
      bs0 ++ encodeCt1SentMsg m := by
  rw [encodeCt1SentMsg_eq_parts]
  simp only [List.append_assoc]

theorem encodeCt1SentMsg_len_split (m : V1State.Unchunked.Ct1Sent) :
    (encodeCt1SentMsg m).length =
      (msgHeaderBytes (ct1SentPBEncodedLen m)).length +
        (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.hdr).length +
        (bytesFieldTagged 4#32 m.es).length +
        (bytesFieldTagged 5#32 m.ct1).length := by
  rw [encodeCt1SentMsg_eq_parts]
  simp only [List.length_append, Nat.add_assoc]

theorem ct1SentPBEncodedLen_eq_fields_len (m : V1State.Unchunked.Ct1Sent) :
    ct1SentPBEncodedLen m =
      (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.hdr).length +
        (bytesFieldTagged 4#32 m.es).length +
        (bytesFieldTagged 5#32 m.ct1).length := by
  have h := ct1SentPBEncodedLen_eq_proto m
  rw [← h]
  simp only [V1State.Unchunked.Ct1Sent.encodedLen,
    V1State.Unchunked.Ct1Sent.encodeRaw, Proto.encodeUint64Field,
    u64Field1Bytes, optAuthField2Bytes, bytesFieldTagged, List.length_append, Nat.add_assoc]

/-! ## 3. Specifications of `encode<EkSentCt1Received>` & `encode<Ct1Sent>` (`[local#1, 2]`) -/

/-- Shared panic postcondition for `prost::encoding::message::encode` subroutines. -/
@[expose] def msgEncodeOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Pinned ghost arguments of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>`:
- `msgA`: pointer to `&spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received` (`x0`, 104 bytes),
- `g`: `(cap, ptr)` pins for `dk`, `ct1`, and `auth`,
- `m`: pure `V1State.Unchunked.EkSentCt1Received` value,
- `v`: pointer to `buf: &mut Vec<u8>` (`x1`, 24 bytes),
- `cap`, `ptr`, `bs`: initial capacity, buffer pointer, and contents of `buf`. -/
structure EkSentCt1ReceivedEncodePinnedGhost where
  msgA : BitVec 64
  g : Unchunked4PBGhost
  m : V1State.Unchunked.EkSentCt1Received
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>`. -/
structure EkSentCt1ReceivedEncodeGhost where
  msgA : BitVec 64
  m : V1State.Unchunked.EkSentCt1Received
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`.
Note on the capacity/length bound: top-level `Message::encode` pre-allocates `cap = encoded_len`,
discharging the left disjunct `x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat`;
growing callers discharge the right disjunct `< 2 ^ 62` from protocol message size bounds. -/
@[expose] def ekSentCt1ReceivedEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EkSentCt1ReceivedEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`. -/
@[expose] def ekSentCt1ReceivedEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EkSentCt1ReceivedEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBAt A x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBAt A x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

abbrev ekSentCt1ReceivedEncodePinnedSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodePinnedGhost :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStack A

abbrev ekSentCt1ReceivedEncodePinnedSpecX (A : RustAlloc) : Spec EkSentCt1ReceivedEncodePinnedGhost :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A

abbrev ekSentCt1ReceivedEncodeSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodeGhost :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStack A

abbrev ekSentCt1ReceivedEncodeSpecX (A : RustAlloc) : Spec EkSentCt1ReceivedEncodeGhost :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStackX A

/-- Pinned ghost arguments of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>`:
- `msgA`: pointer to `&spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent` (`x0`, 128 bytes),
- `g`: `(cap, ptr)` pins for `hdr`, `es`, `ct1`, and `auth`,
- `m`: pure `V1State.Unchunked.Ct1Sent` value,
- `v`: pointer to `buf: &mut Vec<u8>` (`x1`, 24 bytes),
- `cap`, `ptr`, `bs`: initial capacity, buffer pointer, and contents of `buf`. -/
structure Ct1SentEncodePinnedGhost where
  msgA : BitVec 64
  g : Unchunked5PBGhost
  m : V1State.Unchunked.Ct1Sent
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>`. -/
structure Ct1SentEncodeGhost where
  msgA : BitVec 64
  m : V1State.Unchunked.Ct1Sent
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`.
Note on the capacity/length bound: top-level `Message::encode` pre-allocates `cap = encoded_len`,
discharging the left disjunct `x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat`;
growing callers discharge the right disjunct `< 2 ^ 62` from protocol message size bounds. -/
@[expose] def ct1SentEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec Ct1SentEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`. -/
@[expose] def ct1SentEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec Ct1SentEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBAt A x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBAt A x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

abbrev ct1SentEncodePinnedSpec (A : RustAlloc) : Spec Ct1SentEncodePinnedGhost :=
  ct1SentEncodePinnedSpecOf doReserveStack A

abbrev ct1SentEncodePinnedSpecX (A : RustAlloc) : Spec Ct1SentEncodePinnedGhost :=
  ct1SentEncodePinnedSpecOf doReserveStackX A

abbrev ct1SentEncodeSpec (A : RustAlloc) : Spec Ct1SentEncodeGhost :=
  ct1SentEncodeSpecOf doReserveStack A

abbrev ct1SentEncodeSpecX (A : RustAlloc) : Spec Ct1SentEncodeGhost :=
  ct1SentEncodeSpecOf doReserveStackX A

/-! ## 4. Stack, Memory, and Callee Helpers -/

theorem stackAt_unchunkedMsgEncode {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (unchunkedMsgEncodeStackOf resStack) =
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (authEncodeStackOf resStack) 8
    (by dsimp [authEncodeStackOf]; omega)
  have heq : authEncodeStackOf resStack + 8 * 8 = unchunkedMsgEncodeStackOf resStack := by
    dsimp [unchunkedMsgEncodeStackOf, authEncodeStackOf]; omega
  rw [heq] at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_authEncode_eq_encodeVarint64 {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (authEncodeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
        stackAt sp1 (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp1 (0x30 + resStack) 64 (by omega)
  have heq : 0x30 + resStack + 64 = authEncodeStackOf resStack := by
    dsimp [authEncodeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_authEncode_eq_encodedLen {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (authEncodeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (authEncodeStackOf resStack)) (authEncodeStackOf resStack - 16) ∗
        stackAt sp1 unchunkedEncodedLenStack := by
  have h := ProofLib.stackAt_split_bottom sp1 unchunkedEncodedLenStack
    (authEncodeStackOf resStack - 16) (by dsimp [unchunkedEncodedLenStack, authEncodeStackOf]; omega)
  have heq : unchunkedEncodedLenStack + (authEncodeStackOf resStack - 16) =
      authEncodeStackOf resStack := by
    dsimp [unchunkedEncodedLenStack, authEncodeStackOf]; omega
  simpa only [heq] using h

end CryptoVerification.SpqrV1.Prost.MessageEncode
