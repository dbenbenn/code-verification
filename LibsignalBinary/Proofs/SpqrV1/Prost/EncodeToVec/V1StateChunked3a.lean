/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2c (Part 3a): `V1State::encode_raw` Variants `idx = 10, 6` in `PqRatchetState::encode_to_vec`

Proves shared pure unfolding/bytes-field helpers and symbolic execution of the `V1State.InnerState`
branches `idx = 10` (`.ct2Sampled`, `+3008 .. +5712`) and `idx = 6` (`.headerReceived`, `+2908 .. +5208`)
in `PqRatchetState::encode_to_vec` (`0x6d010`).
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

local macro "etv_cs" mid:term : tactic =>
  `(tactic| (apply SepWPp.of_sepWP_cs (mid := $mid); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])))
local macro "s_an" : term => `(by simp only [arm64_norm, *])
local macro "s_an0" : term => `(by simp only [arm64_norm])

/-! ## 1. Pure Encoding Unfolding & Shared Stepping Helpers -/

theorem etv3_encodeBytesField_5_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 5#32 bs = if bs.isEmpty then [] else [0x2a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond; rw [show Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] from rfl]

theorem etv3_bv_optCt2Sent_some_eq (u : V1State.Unchunked.Ct2Sent) :
    BitVec.ofNat 64 (ct2SentPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen (some u)) := by
  dsimp only [optCt2SentPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptCt2Sent_some_eq (u : V1State.Unchunked.Ct2Sent) :
    Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 (some u) =
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]; rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.Ct2Sent.encodedLen, ct2SentPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.Ct2Sent.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_ct2Sampled_eq (v : V1State.Chunked.Ct2Sampled) :
    V1State.InnerState.encode (.ct2Sampled v) =
      (([0x5a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt2 := by
  have hlen : (V1State.Chunked.Ct2Sampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.ct2Sampled v) := by
    dsimp only [V1State.Chunked.Ct2Sampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optCt2SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt2 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 11#32 .lengthDelimited = [0x5a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.Ct2Sampled.encodeRaw]; simp only [List.append_assoc]

theorem etv3_bv_optHeaderReceived_some_eq (u : V1State.Unchunked.HeaderReceived) :
    BitVec.ofNat 64 (headerReceivedPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optHeaderReceivedPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptHeaderReceived_some_eq (u : V1State.Unchunked.HeaderReceived) :
    Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) =
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++ Proto.encodeBytesField 3#32 u.hdr := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.HeaderReceived.encodedLen, headerReceivedPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.HeaderReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_headerReceived_eq (v : V1State.Chunked.HeaderReceived) :
    V1State.InnerState.encode (.headerReceived v) =
      (([0x3a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialDecoder.encodeRaw 2#32 v.receivingEk := by
  have hlen : (V1State.Chunked.HeaderReceived.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.headerReceived v) := by
    dsimp only [V1State.Chunked.HeaderReceived.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optHeaderReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 7#32 .lengthDelimited = [0x3a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.HeaderReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_bv_optHeaderSent_some_eq (u : V1State.Unchunked.HeaderSent) :
    BitVec.ofNat 64 (headerSentPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen (some u)) := by
  dsimp only [optHeaderSentPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_bv_optCt1SentEkReceived_some_eq (u : V1State.Unchunked.Ct1SentEkReceived) :
    BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optCt1SentEkReceivedPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptCt1SentEkReceived_some_eq (u : V1State.Unchunked.Ct1SentEkReceived) :
    Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) =
      ((((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++
        Proto.encodeBytesField 3#32 u.es) ++ Proto.encodeBytesField 4#32 u.ek) ++ Proto.encodeBytesField 5#32 u.ct1 := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.Ct1SentEkReceived.encodedLen, ct1SentEkReceivedPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.Ct1SentEkReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_ekReceivedCt1Sampled_eq (v : V1State.Chunked.EkReceivedCt1Sampled) :
    V1State.InnerState.encode (.ekReceivedCt1Sampled v) =
      (([0x4a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt1 := by
  have hlen : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v) := by
    dsimp only [V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optCt1SentEkReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt1 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 9#32 .lengthDelimited = [0x4a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.EkReceivedCt1Sampled.encodeRaw]; simp only [List.append_assoc]



end CryptoVerification.SpqrV1.Prost.EncodeToVec
