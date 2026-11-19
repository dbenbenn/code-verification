/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Base for `prost::encoding::message::encode::<ChainParams, Vec<u8>>` (`[local#1, 2]`)

Shared pure model lemmas, specifications, fetch macros, and basic-block stepping lemmas for
`prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>>`
(`[local#1]` at `0x37194` and `[local#2]` at `0x52170`).
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local arm64_norm] private theorem zext64_trunc32_orr_1 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 1#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_trunc32_orr_100000001 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 0x100000001#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_orr_1_32 (w : BitVec 32) :
    BitVec.zeroExtend 64 (w ||| 1#32) = BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

/-! ## 1. Pure Model & Specification -/

/-- Pure bytes appended by `encode<ChainParams>` with field `tag` (length-delimited):
`Proto.encodeMessage ChainParamsPB.encodeRaw tag p`. -/
abbrev encodeChainParamsMsg (tag : BitVec 32) (p : ChainParamsPB) : List (BitVec 8) :=
  Proto.encodeMessage ChainParamsPB.encodeRaw tag p

/-- Header bytes (key + length varint) of `encodeChainParamsMsg tag p`. -/
abbrev chainParamsHeaderBytes (tag : BitVec 32) (p : ChainParamsPB) : List (BitVec 8) :=
  Proto.encodeKey tag .lengthDelimited ++
    Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length)

theorem encodeChainParamsMsg_eq (tag : BitVec 32) (p : ChainParamsPB) :
    encodeChainParamsMsg tag p =
      chainParamsHeaderBytes tag p ++
        Proto.encodeUint32Field 1#32 p.maxJump ++
        Proto.encodeUint32Field 2#32 p.maxOooKeys := by
  simp only [encodeChainParamsMsg, chainParamsHeaderBytes, Proto.encodeMessage,
    ChainParamsPB.encodeRaw, List.append_assoc]

theorem bs0_append_encodeChainParamsMsg (bs0 : List (BitVec 8)) (tag : BitVec 32) (p : ChainParamsPB) :
    bs0 ++ encodeChainParamsMsg tag p =
      ((bs0 ++ chainParamsHeaderBytes tag p) ++ Proto.encodeUint32Field 1#32 p.maxJump) ++
        Proto.encodeUint32Field 2#32 p.maxOooKeys := by
  rw [encodeChainParamsMsg_eq]; simp only [List.append_assoc]

theorem chainParams_encodeRaw_length (p : ChainParamsPB) :
    (ChainParamsPB.encodeRaw p).length =
      u32VarintFieldEncodedLen p.maxJump + u32VarintFieldEncodedLen p.maxOooKeys := by
  simp only [ChainParamsPB.encodeRaw, List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 p.maxJump ⟨by decide, by decide⟩,
    u32VarintFieldEncodedLen_eq_proto 2#32 p.maxOooKeys ⟨by decide, by decide⟩]

theorem chainParams_encodeRaw_length_le_12 (p : ChainParamsPB) :
    (ChainParamsPB.encodeRaw p).length ≤ 12 := by
  rw [chainParams_encodeRaw_length]
  have h1 := u32VarintFieldEncodedLen_le_six p.maxJump
  have h2 := u32VarintFieldEncodedLen_le_six p.maxOooKeys
  omega

theorem chainParamsHeaderBytes_eq (tag : BitVec 32) (p : ChainParamsPB) :
    chainParamsHeaderBytes tag p =
      LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64) ++
        LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) := by
  simp only [chainParamsHeaderBytes, orr_lsl3_two_eq_encodeKey_lengthDelimited,
    protoEncodeVarint_eq_codec]

theorem bs0_append_chainParamsHeaderBytes (bs0 : List (BitVec 8)) (tag : BitVec 32) (p : ChainParamsPB) :
    (bs0 ++ LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)) ++
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) =
    bs0 ++ chainParamsHeaderBytes tag p := by
  rw [chainParamsHeaderBytes_eq, List.append_assoc]

theorem u32VarintFieldEncodedLen_of_beq_true {w : BitVec 32} (hw : (w == 0#32) = true) :
    u32VarintFieldEncodedLen w = 0 := by
  have heq : w = 0#32 := eq_of_beq hw
  subst heq
  rfl

theorem chainParamsHeaderBytes_len_eq (tag : BitVec 32) (p : ChainParamsPB) :
    (chainParamsHeaderBytes tag p).length =
      (LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)).length +
        (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length)).length := by
  rw [chainParamsHeaderBytes_eq, List.length_append]

theorem chainParamsHeaderBytes_len_bounds (tag : BitVec 32) (p : ChainParamsPB) :
    1 ≤ (LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)).length ∧
    1 ≤ (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length)).length ∧
    2 ≤ (chainParamsHeaderBytes tag p).length := by
  have h1 := Varint.encodeVarint_length_bounds ((2#32 ||| (tag <<< 3)).zeroExtend 64)
  have h2 := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length)
  rw [chainParamsHeaderBytes_len_eq]
  omega

theorem bs_append_maxJump_of_ne_zero (bs : List (BitVec 8)) (p : ChainParamsPB)
    (hmj : (p.maxJump == 0#32) = false) :
    (bs ++ [0x08#8]) ++ LibsignalProtoCodec.encodeVarint (p.maxJump.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 1#32 p.maxJump := by
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hmj), List.append_assoc]

theorem bs_append_maxJump_of_zero (bs : List (BitVec 8)) (p : ChainParamsPB)
    (hmj : (p.maxJump == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 1#32 p.maxJump = bs := by
  rw [eq_of_beq hmj, protoEncodeUint32Field_zero, List.append_nil]

theorem maxJump_field_len_of_ne_zero (p : ChainParamsPB) (hmj : (p.maxJump == 0#32) = false) :
    (Proto.encodeUint32Field 1#32 p.maxJump).length =
      1 + (LibsignalProtoCodec.encodeVarint (p.maxJump.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 1#32 p.maxJump).length := by
  have hb := Varint.encodeVarint_length_bounds (p.maxJump.zeroExtend 64)
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hmj),
    List.length_append, List.length_singleton]
  omega

theorem bs_append_maxOooKeys_of_ne_zero (bs : List (BitVec 8)) (p : ChainParamsPB)
    (hmo : (p.maxOooKeys == 0#32) = false) :
    (bs ++ [0x10#8]) ++ LibsignalProtoCodec.encodeVarint (p.maxOooKeys.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 2#32 p.maxOooKeys := by
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hmo), List.append_assoc]

theorem bs_append_maxOooKeys_of_zero (bs : List (BitVec 8)) (p : ChainParamsPB)
    (hmo : (p.maxOooKeys == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 2#32 p.maxOooKeys = bs := by
  rw [eq_of_beq hmo, protoEncodeUint32Field_zero, List.append_nil]

theorem maxOooKeys_field_len_of_ne_zero (p : ChainParamsPB) (hmo : (p.maxOooKeys == 0#32) = false) :
    (Proto.encodeUint32Field 2#32 p.maxOooKeys).length =
      1 + (LibsignalProtoCodec.encodeVarint (p.maxOooKeys.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 2#32 p.maxOooKeys).length := by
  have hb := Varint.encodeVarint_length_bounds (p.maxOooKeys.zeroExtend 64)
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hmo),
    List.length_append, List.length_singleton]
  omega

theorem encodeChainParamsMsg_len_split (tag : BitVec 32) (p : ChainParamsPB) :
    (encodeChainParamsMsg tag p).length =
      (chainParamsHeaderBytes tag p).length +
        (Proto.encodeUint32Field 1#32 p.maxJump).length +
        (Proto.encodeUint32Field 2#32 p.maxOooKeys).length := by
  rw [encodeChainParamsMsg_eq, List.length_append, List.length_append]

/-- Ghost inputs for `prost::encoding::message::encode::<ChainParams, Vec<u8>>`. -/
structure EncodeChainParamsGhost where
  tag : BitVec 32
  p   : ChainParamsPB
  v   : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs  : List (BitVec 8)

/-- Specification of `prost::encoding::message::encode::<ChainParams, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`. Callers establish `1 ≤ x.tag.toNat < 2 ^ 29` (tags `4` and `6`) and
either pre-allocate exact capacity (`x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat`)
or bound the serialized size below `2 ^ 62 - 10`. -/
@[expose] def encodeChainParamsSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeChainParamsGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48VarintStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48VarintStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

abbrev encodeChainParamsSpec (A : RustAlloc) : Spec EncodeChainParamsGhost :=
  encodeChainParamsSpecOf doReserveStack A

abbrev encodeChainParamsSpecX (A : RustAlloc) : Spec EncodeChainParamsGhost :=
  encodeChainParamsSpecOf doReserveStackX A

end CryptoVerification.SpqrV1.Prost.MessageEncode
