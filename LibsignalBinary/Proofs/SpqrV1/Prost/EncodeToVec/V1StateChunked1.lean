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
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2c (Part 1): `V1State::encode_raw` Delegating Variants in `PqRatchetState::encode_to_vec`

Proves symbolic execution of the shared `PolynomialEncoder` / `PolynomialDecoder` tails and the
4 delegating `V1State.InnerState` branches in `PqRatchetState::encode_to_vec` (`0x6d010`):
- `idx = 7`: `.ct1Sampled` (`+2620 .. +2748`, `0x6da4c .. 0x6dacc`)
- `idx = 4`: `.ekSentCt1Received` (`+1976 .. +2072`, `+3576 .. +3644`, `+4344 .. +4400`, `+5196 .. +5204`)
- `idx = 9`: `.ct1Acknowledged` (`+2076 .. +2172`, `+3648 .. +3712`, `+4404 .. +4468`)
- `idx = 3`: `.ct1Received` (`+2520 .. +2616`, `+3716 .. +3784`, `+4472 .. +4520`, `+4904 .. +4912`, `+5704 .. +5708`)
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
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Encoding Unfolding & Arithmetic Lemmas -/

theorem ult_of_lt_of_fit {vlen tot : Nat} (hlt : vlen < tot) (htot : tot < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]
  omega

theorem bv_optEkSentCt1Received_some_eq (u : V1State.Unchunked.EkSentCt1Received) :
    BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optCt1Sent_some_eq (u : V1State.Unchunked.Ct1Sent) :
    BitVec.ofNat 64 (ct1SentPBEncodedLen u) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen (some u)) := by
  dsimp only [optCt1SentPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optPolyDec_some_eq (dec : PolynomialDecoder) :
    BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec))) + 1#64 =
      BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen (some dec)) := by
  dsimp only [optPolynomialDecoderPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optPolyEnc_some_eq (enc : PolynomialEncoder) :
    BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc))) + 1#64 =
      BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen (some enc)) := by
  dsimp only [optPolynomialEncoderPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem encodeInnerState_ct1Sampled_eq (v : V1State.Chunked.Ct1Sampled) :
    V1State.InnerState.encode (.ct1Sampled v) =
      ((([0x42#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen v))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt1) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 v.receivingEk := by
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 8#32 .lengthDelimited = [0x42#8] from rfl,
    ← V1State.Chunked.Ct1Sampled.encodedLen, chunkedCt1SampledPBEncodedLen_eq_proto]
  dsimp only [V1State.Chunked.Ct1Sampled.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ekSentCt1Received_eq (v : V1State.Chunked.EkSentCt1Received) :
    V1State.InnerState.encode (.ekSentCt1Received v) =
      (([0x2a#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 v.receivingCt2 := by
  have hlen : (V1State.Chunked.EkSentCt1Received.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ekSentCt1Received v) := by
    dsimp only [V1State.Chunked.EkSentCt1Received.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialDecoderPBFieldEncodedLen_eq_proto 3#32 v.receivingCt2 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] from rfl, hlen]; dsimp only [V1State.Chunked.EkSentCt1Received.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ct1Acknowledged_eq (v : V1State.Chunked.Ct1Acknowledged) :
    V1State.InnerState.encode (.ct1Acknowledged v) =
      (([0x52#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 2#32 v.receivingEk := by
  have hlen : (V1State.Chunked.Ct1Acknowledged.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ct1Acknowledged v) := by
    dsimp only [V1State.Chunked.Ct1Acknowledged.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optCt1SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 10#32 .lengthDelimited = [0x52#8] from rfl, hlen]; dsimp only [V1State.Chunked.Ct1Acknowledged.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ct1Received_eq (v : V1State.Chunked.Ct1Received) :
    V1State.InnerState.encode (.ct1Received v) =
      (([0x22#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk := by
  have hlen : (V1State.Chunked.Ct1Received.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ct1Received v) := by
    dsimp only [V1State.Chunked.Ct1Received.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] from rfl, hlen]; dsimp only [V1State.Chunked.Ct1Received.encodeRaw]
  simp only [List.append_assoc]

/-! ## 2. Shared `PolynomialDecoder` / `PolynomialEncoder` Tail Blocks -/



end CryptoVerification.SpqrV1.Prost.EncodeToVec
