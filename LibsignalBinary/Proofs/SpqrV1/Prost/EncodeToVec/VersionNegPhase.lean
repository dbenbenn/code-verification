/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2b (`0x6d254 .. 0x6d4cc`): `Option<VersionNegotiation>` Encoding

Proves symbolic execution of the inline `Option<VersionNegotiation>` encoding phase
(`+580 .. +1212`, `0x6d254 .. 0x6d4cc`) in
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`,
producing `vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
  (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation)` at
`entry + 1212#64` (`0x6d4cc`).
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Protobuf Encoding Bridge Lemmas for `VersionNegotiationPB` -/

theorem encodeKey_1_lengthDelimited :
    Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := by decide

theorem encodeKey_2_varint :
    Proto.encodeKey 2#32 .varint = [0x10#8] := by decide

theorem encodeKey_3_varint :
    Proto.encodeKey 3#32 .varint = [0x18#8] := by decide

theorem encodeBytesField_1_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 1#32 bs =
      if bs.isEmpty then []
      else [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  rw [encodeKey_1_lengthDelimited]

theorem encodeInt32Field_2_eq (v : BitVec 32) :
    Proto.encodeInt32Field 2#32 v =
      if v == 0#32 then []
      else [0x10#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_2_varint]

theorem encodeInt32Field_3_eq (v : BitVec 32) :
    Proto.encodeInt32Field 3#32 v =
      if v == 0#32 then []
      else [0x18#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_3_varint]

theorem encodeOptMessage_versionNeg_some (vn : VersionNegotiationPB) :
    Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn) =
      [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) ++
        Proto.encodeBytesField 1#32 vn.authKey ++
        Proto.encodeInt32Field 2#32 vn.direction ++
        Proto.encodeInt32Field 3#32 vn.minVersion ++
        Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams := by
  have hlen : (VersionNegotiationPB.encodeRaw vn).length = versionNegotiationPBEncodedLen vn :=
    versionNegotiationPBEncodedLen_eq_proto vn
  dsimp only [Proto.encodeOptMessage, Proto.encodeMessage]
  rw [encodeKey_1_lengthDelimited, hlen]
  dsimp only [VersionNegotiationPB.encodeRaw, Proto.encodeOptMessage, Proto.encodeMessage]
  simp only [List.append_assoc]

theorem optVersionNegotiationPB_encode_len_le (st : PqRatchetState) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation).length ≤
      pqRatchetStatePBEncodedLen st := by
  rw [optVersionNegotiationPBFieldEncodedLen_eq_proto 1#32 st.versionNegotiation ⟨by decide, by decide⟩]
  unfold pqRatchetStatePBEncodedLen
  omega

/-- Discriminant tag (`0#32` or `1#32`) of `Option<ChainParamsPB>`. -/
@[expose] def optChainParamsTag : Option ChainParamsPB → BitVec 32
  | none => 0#32
  | some _ => 1#32

@[simp, arm64_norm] theorem optChainParamsTag_zext_trunc (opt : Option ChainParamsPB) :
    ((optChainParamsTag opt).zeroExtend 64).truncate 32 = optChainParamsTag opt := by
  cases opt <;> rfl

@[simp, arm64_norm] theorem optChainParamsTag_zext_zext (opt : Option ChainParamsPB) :
    (((optChainParamsTag opt).zeroExtend 64).truncate 32).zeroExtend 64 =
      (optChainParamsTag opt).zeroExtend 64 := by
  cases opt <;> rfl

/-! ## 2. Sub-Step Lemmas for `VersionNegotiationPB` Encoding (`0x6d254 .. 0x6d4cc`) -/

/-- Step `+580 .. +604` (`0x6d254 .. 0x6d268`): writes the outer `VersionNegotiation` tag `0x0a#8`
into `vecU8At A (sp - 120#64) cap ptr []` and loads `x25 = BitVec.ofNat 64 vn.authKey.length`. -/

theorem bv_versionNegLen_none_combine (vn : VersionNegotiationPB) (hcp : vn.chainParams = none) :
    (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) +
      BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)) +
      (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) + 0#64) =
      BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) := by
  unfold versionNegotiationPBEncodedLen; rw [hcp]; dsimp only [optChainParamsPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add, BitVec.add_zero]; congr 1; omega

theorem bv_versionNegLen_some_combine (vn : VersionNegotiationPB) :
    (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) +
      BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)) +
      (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) +
        BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) =
      BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) := by
  unfold versionNegotiationPBEncodedLen; simp only [← BitVec.ofNat_add]; congr 1; omega



end CryptoVerification.SpqrV1.Prost.EncodeToVec
