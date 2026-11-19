/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2c (Part 2): `V1State::encode_raw` Variants `idx = 0, 2, 5` in `PqRatchetState::encode_to_vec`

Proves symbolic execution of `V1State.InnerState` branches in `PqRatchetState::encode_to_vec` (`0x6d010`):
- `idx = 0`: `.keysUnsampled` (`+1896`, `0x6d778`)
- `idx = 2`: `.headerSent` (`+2176`, `0x6d890`)
- `idx = 5`: `.noHeaderReceived` (`+2848`, `0x6db30`)
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

/-! ## 1. Pure Encoding Unfolding Lemmas -/

theorem etv2_encodeUint64Field_1_eq (v : BitVec 64) :
    Proto.encodeUint64Field 1#32 v = if v == 0#64 then [] else [0x08#8] ++ Proto.encodeVarint v := by
  unfold Proto.encodeUint64Field; rw [show Proto.encodeKey 1#32 .varint = [0x08#8] from rfl]

theorem etv2_encodeBytesField_3_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 3#32 bs = if bs.isEmpty then [] else [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond; rw [show Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] from rfl]

theorem etv2_encodeBytesField_4_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 4#32 bs = if bs.isEmpty then [] else [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond; rw [show Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] from rfl]

theorem etv2_encodeInnerState_keysUnsampled_eq (v : V1State.Chunked.KeysUnsampled) :
    V1State.InnerState.encode (.keysUnsampled v) =
      ([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 v.uc := by
  have hlen : (V1State.Chunked.KeysUnsampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.keysUnsampled v) := by
    dsimp only [V1State.Chunked.KeysUnsampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    exact optKeysUnsampledPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, hlen]
  simp only [V1State.Chunked.KeysUnsampled.encodeRaw, List.append_assoc]

theorem etv2_encodeOptKeysUnsampled_some_eq (u : V1State.Unchunked.KeysUnsampled) :
    Proto.encodeOptMessage V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 (some u) =
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 (some u) =
    Proto.encodeMessage V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl,
    ← V1State.Unchunked.KeysUnsampled.encodedLen, keysUnsampledPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.KeysUnsampled.encodeRaw]; simp only [List.append_assoc]

theorem etv2_encodeInnerState_keysSampled_eq (v : V1State.Chunked.KeysSampled) :
    V1State.InnerState.encode (.keysSampled v) =
      (([0x12#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingHdr := by
  have hlen : (V1State.Chunked.KeysSampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.keysSampled v) := by
    dsimp only [V1State.Chunked.KeysSampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optHeaderSentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingHdr ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] from rfl, hlen]
  dsimp only [V1State.Chunked.KeysSampled.encodeRaw]; simp only [List.append_assoc]

theorem etv2_encodeOptHeaderSent_some_eq (u : V1State.Unchunked.HeaderSent) :
    Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u) =
      (((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++
        Proto.encodeBytesField 3#32 u.ek) ++ Proto.encodeBytesField 4#32 u.dk := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u) =
    Proto.encodeMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl,
    ← V1State.Unchunked.HeaderSent.encodedLen, headerSentPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.HeaderSent.encodeRaw]; simp only [List.append_assoc]

theorem etv2_encodeInnerState_headerSent_eq (v : V1State.Chunked.HeaderSent) :
    V1State.InnerState.encode (.headerSent v) =
      ((([0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))) ++
        Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 v.receivingCt1 := by
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] from rfl,
    ← V1State.Chunked.HeaderSent.encodedLen, chunkedHeaderSentPBEncodedLen_eq_proto]
  dsimp only [V1State.Chunked.HeaderSent.encodeRaw]; simp only [List.append_assoc]

theorem etv2_encodeOptEkSent_some_eq (u : V1State.Unchunked.EkSent) :
    Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) =
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++
        Proto.encodeBytesField 3#32 u.dk := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) =
    Proto.encodeMessage V1State.Unchunked.EkSent.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl,
    ← V1State.Unchunked.EkSent.encodedLen, ekSentPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.EkSent.encodeRaw]; simp only [List.append_assoc]

theorem etv2_bv_msgFieldLen {n : Nat} (hfit : 1 + varintLen (BitVec.ofNat 64 n) + n < 2 ^ 64) :
    let v := BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 n))
    let tot := BitVec.ofNat 64 (1 + varintLen (BitVec.ofNat 64 n) + n)
    BitVec.ofNat 64 n + v + 1#64 = tot ∧ tot.ule v = false ∧ v.ult tot = true := by
  have hb := (varintLen_bounds (BitVec.ofNat 64 n)).1
  refine ⟨by simp only [← BitVec.ofNat_add]; congr 1; omega, ?_, ?_⟩
  · rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hfit]; omega

theorem etv2_optAuth_cap_bounds {A : RustAlloc} {g : AuthenticatorPBGhost} {p : BitVec 64}
    {opt : Option AuthenticatorPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optAuthenticatorPBPinnedAt A g p opt ∗ R) :
    (optAuthCap g opt + 1#64 == 0#64) = !opt.isSome ∧ (optAuthCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optAuthCap, arm64_norm]
  | some a =>
    rw [optAuthenticatorPBPinnedAt_eq] at hm; simp only [optAuthPayload] at hm
    have hbuf : m ⊨ vecU8Buf A g.rootKey.cap g.rootKey.ptr a.rootKey ∗
        (((p ↦₆₄ optAuthCap g (some a)) ∗ ((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗
          ((p + 16#64) ↦₆₄ BitVec.ofNat 64 a.rootKey.length) ∗ ((p + 24#64) ↦₆₄ g.macKey.cap) ∗
          ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗ ((p + 40#64) ↦₆₄ BitVec.ofNat 64 a.macKey.length) ∗
          vecU8Buf A g.macKey.cap g.macKey.ptr a.macKey) ∗ R) := by convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-! ## 2. Variant `idx = 0`: `.keysUnsampled` (`+1896 .. +1976`, `+3168 .. +3352`) -/

/-- Step `+1896 .. +1808` (`0x6d778 .. 0x6d720`) for `is = .keysUnsampled v`. -/

theorem etv2_optEkSentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentPBPinnedAt A g p opt ∗ R) :
    (optEkSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧ (optEkSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optEkSentPBPinnedAt_eq, sepConj_assoc] at hm; exact optEkSentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem etv2_bv_optNoHeaderReceived_some_eq (u : V1State.Unchunked.NoHeaderReceived) :
    BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optNoHeaderReceivedPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv2_encodeOptNoHeaderReceived_some_eq (u : V1State.Unchunked.NoHeaderReceived) :
    Proto.encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 (some u) =
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++
        Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 (some u) =
    Proto.encodeMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl,
    ← V1State.Unchunked.NoHeaderReceived.encodedLen, noHeaderReceivedPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.NoHeaderReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv2_encodeInnerState_noHeaderReceived_eq (v : V1State.Chunked.NoHeaderReceived) :
    V1State.InnerState.encode (.noHeaderReceived v) =
      (([0x32#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 2#32 v.receivingHdr := by
  have hlen : (V1State.Chunked.NoHeaderReceived.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.noHeaderReceived v) := by
    dsimp only [V1State.Chunked.NoHeaderReceived.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optNoHeaderReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingHdr ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 6#32 .lengthDelimited = [0x32#8] from rfl, hlen]
  dsimp only [V1State.Chunked.NoHeaderReceived.encodeRaw]; simp only [List.append_assoc]



end CryptoVerification.SpqrV1.Prost.EncodeToVec
