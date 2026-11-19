/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2e
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`)

**Checked by Lean.**

Top-level composition of `InnerState.keysSampled` from `+1104` through `<PolyEncoder>::from_pb`
and the shared `Ok` epilogue (`+8180`).
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
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Variant 1 (`KeysSampled`, `+1104`) Top-Level Composition -/

theorem v1_from_pb_uc_none {F : ShaCompress} (optEnc : Option PolynomialEncoder) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysSampled { uc := none, sendingHdr := optEnc }) } =
    .error (.err .stateDecode) := rfl

theorem v1_from_pb_uc_err {F : ShaCompress} (uc : V1State.Unchunked.HeaderSent)
    (optEnc : Option PolynomialEncoder)
    (herr : (BitVec.ofNat 64 uc.dk.length == 2400#64) = false ∨
      (BitVec.ofNat 64 uc.ek.length == 1152#64) = false ∨ uc.auth = none)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysSampled { uc := some uc, sendingHdr := optEnc }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendEk.KeysSampled.from_pb Unchunked.SendEk.HeaderSent.from_pb
    DECAPSULATION_KEY_SIZE ENCAPSULATION_KEY_SIZE
  rw [ofNat_beq_lit_iff hdk_lt (by decide), ofNat_beq_lit_iff hek_lt (by decide)] at herr
  rcases herr with h | h | h
  · simp [h, Bind.bind, Except.bind, Functor.map, Except.map]
  · simp [h, Bind.bind, Except.bind, Functor.map, Except.map]
  · by_cases hc : (uc.dk.length == 2400 && uc.ek.length == 1152) = true <;>
      simp [hc, h, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v1_from_pb_sendingHdr_none {F : ShaCompress} (uc : V1State.Unchunked.HeaderSent)
    (auth : ProtoAuthenticator) (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysSampled { uc := some uc, sendingHdr := none }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendEk.KeysSampled.from_pb Unchunked.SendEk.HeaderSent.from_pb
    DECAPSULATION_KEY_SIZE ENCAPSULATION_KEY_SIZE
  rw [ofNat_beq_lit_iff hdk_lt (by decide)] at hdk
  rw [ofNat_beq_lit_iff hek_lt (by decide)] at hek
  simp [hdk, hek, hauth, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v1_from_pb_sendingHdr_some {F : ShaCompress} (uc : V1State.Unchunked.HeaderSent)
    (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder) (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysSampled { uc := some uc, sendingHdr := some pbEnc }) } =
    match fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | .ok enc => .ok (.keysSampled
        { uc := { ek := uc.ek, dk := uc.dk,
                  auth := { rootKey := auth.rootKey, macKey := auth.macKey },
                  epoch := uc.epoch },
          sending_hdr := enc })
    | .error _ => .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendEk.KeysSampled.from_pb Unchunked.SendEk.HeaderSent.from_pb
    DECAPSULATION_KEY_SIZE ENCAPSULATION_KEY_SIZE
  rw [ofNat_beq_lit_iff hdk_lt (by decide)] at hdk
  rw [ofNat_beq_lit_iff hek_lt (by decide)] at hek
  simp only [hdk, hek, hauth, Bool.true_and, ↓reduceIte, encoderFromPbStateDecode_some,
    spqrAuthApi, Authenticator.fromPb, Bind.bind, Except.bind, Functor.map, Except.map]
  cases fromPbResult (pbToProtoPolyEncoder pbEnc) <;> rfl

theorem v1_vecU8Payload_extract_len_lt63 (A : RustAlloc) (c p : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ vecU8Payload A c p bs := by
  unfold vecU8Payload
  apply Entails.pure_left; rintro ⟨hle, hlt, hp⟩
  exact Entails.pure_right (Nat.lt_of_le_of_lt hle hlt)
    (Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _))

theorem v1_optProtoUcHeap_some_extract (A : RustAlloc) (uc : V1State.Unchunked.HeaderSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    v1_optProtoUcHeap A (some uc) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.ek.length ∧
        u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.dk.length ∧
        u104 = uc.epoch ∧ uc.ek.length < 2 ^ 63 ∧ uc.dk.length < 2 ^ 63⌝ ∗
      vecU8Payload A u8 u16 uc.ek ∗
      vecU8Payload A u32 u40 uc.dk ∗
      v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96 := by
  dsimp only [v1_optProtoUcHeap]
  apply Entails.pure_left; rintro ⟨hu8, hu24, hu32, hu48, hu104⟩
  refine Entails.trans (sepConj_mono_left (v1_vecU8Payload_extract_len_lt63 A u8 u16 uc.ek)) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; rintro hek_lt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (v1_vecU8Payload_extract_len_lt63 A u32 u40 uc.dk))) ?_
  simp only [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply Entails.pure_left; rintro hdk_lt
  exact Entails.pure_right ⟨hu8, hu24, hu32, hu48, hu104, hek_lt, hdk_lt⟩ (Entails.of_eq (by ac_rfl))

theorem v1_optProtoAuthHeap_some_extract (A : RustAlloc) (auth : ProtoAuthenticator)
    (u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v1_optProtoAuthHeap A (some auth) u56 u64 u72 u80 u88 u96 ⊢
      ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
        u96 = BitVec.ofNat 64 auth.macKey.length ∧ auth.rootKey.length < 2 ^ 63⌝ ∗
      vecU8Payload A u56 u64 auth.rootKey ∗
      vecU8Payload A u80 u88 auth.macKey := by
  dsimp only [v1_optProtoAuthHeap]
  apply Entails.pure_left; rintro ⟨hu56, hu72, hu96⟩
  refine Entails.trans (sepConj_mono_left
    (v1_vecU8Payload_extract_len_lt63 A u56 u64 auth.rootKey)) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; rintro hr_lt63
  exact Entails.pure_right ⟨hu56, hu72, hu96, hr_lt63⟩ (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb

