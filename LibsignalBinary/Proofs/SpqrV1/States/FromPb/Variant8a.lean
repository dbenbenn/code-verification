/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`) — Part A

Helpers and error exits for Variant 8 (`InnerState.ekReceivedCt1Sampled`, tag `0x8000000000000008#64`,
jump-table target `+1764`).
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Pure Model Reduction Lemmas for `InnerState.ekReceivedCt1Sampled` -/

theorem v8_states_from_pb_uc_none_eq {F : ShaCompress}
    (sendingCt1 : Option PolynomialEncoder) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := none, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := rfl

theorem v8_states_from_pb_len_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (sendingCt1 : Option PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_auth_none_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (sendingCt1 : Option PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_sendingCt1_none_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := none }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_sendingCt1_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error .serializationInvalid) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_ok_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder)
    (enc : PolyEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .ok enc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .ok (.ekReceivedCt1Sampled
      { uc := { epoch := u.epoch, auth := Authenticator.fromPb auth,
                es := u.es, ek := u.ek, ct1 := u.ct1 }
        sending_ct1 := enc }) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, spqrAuthApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

/-! ## 2. Error Exit at `+4240` and `sendingCt1` Drop at `+4216` / `+4212` -/

theorem v8_merge_stack_1520_56_728 (fsp : BitVec 64) :
    memRegion fsp 1520 ∗
      memRegion (fsp + 1520#64) 56 ∗
      memRegion (fsp + 1576#64) 728 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

/-- Sixteen 64-bit words of a 128-byte `Option<V1State.Unchunked.Ct1SentEkReceived>` at `a`. -/
@[expose] def v8_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
  ((a + 96#64) ↦₆₄ u104) ∗ ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120) ∗
  ((a + 120#64) ↦₆₄ u128)

theorem v8_ucWordsAt_entails_128
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) :
    v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ⊢
      memRegion a 128 := by
  unfold v8_ucWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Eleven 128-bit (`↦₁₂₈`) chunks plus one 64-bit word covering `pbA + 8..192` (`184` bytes). -/
@[expose] def v8_pb128At (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₁₂₈ (u16 ++ u8)) ∗
  ((pbA + 24#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((pbA + 40#64) ↦₁₂₈ (u48 ++ u40)) ∗
  ((pbA + 56#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((pbA + 72#64) ↦₁₂₈ (u80 ++ u72)) ∗
  ((pbA + 88#64) ↦₁₂₈ (u96 ++ u88)) ∗
  ((pbA + 104#64) ↦₁₂₈ (u112 ++ u104)) ∗
  ((pbA + 120#64) ↦₁₂₈ (u128 ++ u120)) ∗
  ((pbA + 136#64) ↦₁₂₈ (w8 ++ w0)) ∗
  ((pbA + 152#64) ↦₁₂₈ (w24 ++ w16)) ∗
  ((pbA + 168#64) ↦₁₂₈ (w40 ++ w32)) ∗
  ((pbA + 184#64) ↦₆₄ w48)

theorem v8_uc_and_enc_words_eq_pb128
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 =
      v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        w0 w8 w16 w24 w32 w40 w48 := by
  dsimp only [v8_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v8_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v8_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
      v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize := by
  rw [← v8_uc_and_enc_words_eq_pb128]
  have h128 := v8_ucWordsAt_entails_128 (pbA + 8#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48
  have h224 : (pbA ↦₆₄ 0x8000000000000008#64) ∗
      memRegion (pbA + 8#64) 128 ∗
      memRegion (pbA + 136#64) 56 ∗
      memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <|
      collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
    v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 192#64) 32 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono h128 (sepConj_mono_left h56))) h224

/-! ## 4. Error Cleanup for `uc` (`es`, `ek`, `ct1`, `auth`) + `sendingCt1` (`+2100 -> +2148 -> +2208 -> +4216`) -/

theorem v8_merge_stack_896_128_496_1520 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) :
    memRegion fsp 896 ∗
      v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      memRegion (fsp + 1024#64) 496 ⊢
      memRegion fsp 1520 := by
  have h128 := v8_ucWordsAt_entails_128 (fsp + 896#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
  have hm : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 128 ∗ memRegion (fsp + 1024#64) 496 ⊢
      memRegion fsp 1520 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h128)) hm

theorem v8_stackAt_encoder_split_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 :=
  ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)

theorem v8_pack_protoUnchunkedCt1SentEkReceived_auth_none
    (A : RustAlloc) (a : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 : BitVec 64)
    (hu8 : u8.toNat < 2 ^ 63) (hu24 : u24 = (u.es.length : BitVec 64))
    (hu32 : u32.toNat < 2 ^ 63) (hu48 : u48 = (u.ek.length : BitVec 64))
    (hu56 : u56.toNat < 2 ^ 63) (hu72 : u72 = (u.ct1.length : BitVec 64))
    (hauth : u.auth = none) :
    v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u.epoch ∗
      vecU8Payload A u8 u16 u.es ∗
      vecU8Payload A u32 u40 u.ek ∗
      vecU8Payload A u56 u64 u.ct1 ⊢
      protoUnchunkedCt1SentEkReceivedAt A a u := by
  subst hu24 hu48 hu72
  unfold protoUnchunkedCt1SentEkReceivedAt
  rw [hauth, optProtoAuthenticatorAt_none]
  have hes : (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ (u.es.length : BitVec 64)) ∗
      vecU8Payload A u8 u16 u.es ⊢ vecU8 A a u.es := by
    unfold vecU8
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have hek : ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ (u.ek.length : BitVec 64)) ∗
      vecU8Payload A u32 u40 u.ek ⊢ vecU8 A (a + 24#64) u.ek := by
    unfold vecU8
    refine Entails.sepExists_right u32 (Entails.sepExists_right u40 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have hct1 : ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ (u.ct1.length : BitVec 64)) ∗
      vecU8Payload A u56 u64 u.ct1 ⊢ vecU8 A (a + 48#64) u.ct1 := by
    unfold vecU8
    refine Entails.sepExists_right u56 (Entails.sepExists_right u64 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have h40 : ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗ ((a + 96#64) ↦₆₄ u104) ∗
      ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120) ⊢ memRegion (a + 72#64 + 8#64) 40 := by
    have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have h88 : a + 88#64 = (a + 80#64) + 8#64 := by bv_omega
    have h96 : a + 96#64 = (a + 80#64) + 16#64 := by bv_omega
    have h104 : a + 104#64 = (a + 80#64) + 24#64 := by bv_omega
    have h112 : a + 112#64 = (a + 80#64) + 32#64 := by bv_omega
    rw [h80, h88, h96, h104, h112]
    exact collapse_top <|
      collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ (u.es.length : BitVec 64)) ∗
      vecU8Payload A u8 u16 u.es) ∗
    (((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ (u.ek.length : BitVec 64)) ∗
      vecU8Payload A u32 u40 u.ek) ∗
    (((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ (u.ct1.length : BitVec 64)) ∗
      vecU8Payload A u56 u64 u.ct1) ∗
    ((a + 72#64) ↦₆₄ noneCap) ∗
    (((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗ ((a + 96#64) ↦₆₄ u104) ∗
      ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120)) ∗
    ((a + 120#64) ↦₆₄ u.epoch) by
      dsimp only [v8_ucWordsAt]; ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hes (sepConj_mono hek (sepConj_mono hct1 (sepConj_mono_right (sepConj_mono_left h40))))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
