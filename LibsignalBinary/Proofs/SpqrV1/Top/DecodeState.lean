/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoop
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs

/-!
# Top-Level Verification of `spqr::decode_state` (`0x5349c`)

Verifies `spqr::decode_state` (`0x5349c..0x54040`, 745 instructions) against `Proto.spqrDecodeState`
with `canonicalV1InnerHeap`, proving exact representation equalities with `Drop` and `ProtoRepr`,
a `16,032`-byte stack budget (`0x570` local frame + `14,640` B in `V1State::merge`), and discharging
`x.st.bytes.length < 2 ^ 32` via `DEV-SPQR3`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Symbol Name Unification (`rfl` Bridges to Canonical Callee Modules) -/

@[simp] theorem skipField3Name_eq :
    DecodeState.skipField3Name =
      CryptoVerification.SpqrV1.Varint.skipField3Name := rfl

@[simp] theorem chainParamsMergeName_eq :
    DecodeState.chainParamsMergeName =
      CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName := rfl

@[simp] theorem epochDirectionMergeName_eq :
    DecodeState.epochDirectionMergeName =
      CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName := rfl

@[simp] theorem dropOptProtoInnerStateName_eq :
    DecodeState.dropOptProtoInnerStateName =
      CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStateName := rfl

@[simp] theorem dropProtoPqRatchetStateName_eq :
    DecodeState.dropProtoPqRatchetStateName =
      CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStateName := rfl

/-! ## `Drop.protoInnerStateAt` Entails `protoInnerStateCapAt A a 0` and `of_drop_inner` -/

theorem vecU8_entails_vecU8Cap0 (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A a bs ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜BytesMergeCapOk cap 0⌝ ∗ RustHeap.vecU8At A a cap ptr bs) := by
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.pure_right (bytesMergeCapOk_of_len_lt32 (by decide)) (Entails.refl _)

theorem authenticatorPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBAt A a auth ⊢ Auth.authenticatorPBCapAt A a 0 auth :=
  sepConj_mono (vecU8_entails_vecU8Cap0 A a auth.rootKey)
    (vecU8_entails_vecU8Cap0 A (a + 0x18#64) auth.macKey)

theorem optAuthenticatorPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ Prost.MessageMerge.optAuthenticatorPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBAt_entails_cap0 A a auth

theorem unchunked2At_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) :
    unchunked2At A a epoch auth ⊢ Prost.MessageMerge.unchunked2CapAt A a 0 epoch auth :=
  sepConj_mono_left (optAuthenticatorPBAt_entails_cap0 A a auth)

theorem optKeysUnsampledPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBAt A a opt ⊢ Prost.MessageMerge.optKeysUnsampledPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2At_entails_cap0 A a u.epoch u.auth

theorem optNoHeaderReceivedPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBAt A a opt ⊢ Prost.MessageMerge.optNoHeaderReceivedPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2At_entails_cap0 A a u.epoch u.auth

theorem optCt2SentPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBAt A a opt ⊢ Prost.MessageMerge.optCt2SentPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2At_entails_cap0 A a u.epoch u.auth

theorem unchunked3At_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3At A a epoch auth v3 ⊢ Prost.MessageMerge.unchunked3CapAt A a 0 epoch auth v3 :=
  sepConj_mono (vecU8_entails_vecU8Cap0 A a v3)
    (sepConj_mono_left (optAuthenticatorPBAt_entails_cap0 A (a + 0x18#64) auth))

theorem optHeaderReceivedPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBAt A a opt ⊢ Prost.MessageMerge.optHeaderReceivedPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3At_entails_cap0 A a u.epoch u.auth u.hdr

theorem optEkSentPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBAt A a opt ⊢ Prost.MessageMerge.optEkSentPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3At_entails_cap0 A a u.epoch u.auth u.dk

theorem unchunked4At_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    unchunked4At A a epoch auth v3 v4 ⊢ Prost.MessageMerge.unchunked4CapAt A a 0 epoch auth v3 v4 :=
  sepConj_mono (vecU8_entails_vecU8Cap0 A a v3)
    (sepConj_mono (vecU8_entails_vecU8Cap0 A (a + 0x18#64) v4)
      (sepConj_mono_left (optAuthenticatorPBAt_entails_cap0 A (a + 0x30#64) auth)))

theorem optHeaderSentPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBAt A a opt ⊢ Prost.MessageMerge.optHeaderSentPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked4At_entails_cap0 A a u.epoch u.auth u.ek u.dk

theorem optEkSentCt1ReceivedPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBAt A a opt ⊢ Prost.MessageMerge.optUnchunkedEkSentCt1ReceivedPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked4At_entails_cap0 A a u.epoch u.auth u.dk u.ct1

theorem unchunked5At_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5At A a epoch auth v3 v4 v5 ⊢
      Prost.MessageMerge.unchunked5CapAt A a 0 epoch auth v3 v4 v5 :=
  sepConj_mono (vecU8_entails_vecU8Cap0 A a v3)
    (sepConj_mono (vecU8_entails_vecU8Cap0 A (a + 0x18#64) v4)
      (sepConj_mono (vecU8_entails_vecU8Cap0 A (a + 0x30#64) v5)
        (sepConj_mono_left (optAuthenticatorPBAt_entails_cap0 A (a + 0x48#64) auth))))

theorem optCt1SentEkReceivedPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBAt A a opt ⊢ Prost.MessageMerge.optCt1SentEkReceivedPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked5At_entails_cap0 A a u.epoch u.auth u.es u.ek u.ct1

theorem optCt1SentPBAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    optCt1SentPBAt A a opt ⊢ Prost.MessageMerge.optUnchunkedCt1SentPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked5At_entails_cap0 A a u.epoch u.auth u.hdr u.es u.ct1

theorem protoInnerStateAt_entails_cap0 (A : RustAlloc) (a : BitVec 64)
    (st : V1State.InnerState) :
    CryptoVerification.SpqrV1.Drop.protoInnerStateAt A a st ⊢
      Prost.MessageMerge.protoInnerStateCapAt A a 0 st := by
  cases st with
  | keysUnsampled s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedKeysUnsampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (optKeysUnsampledPBAt_entails_cap0 A (a + 8#64) s.uc))
  | keysSampled s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedKeysSampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optHeaderSentPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | headerSent s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedHeaderSentPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optEkSentPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | ct1Received s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedCt1ReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optEkSentCt1ReceivedPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | ekSentCt1Received s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedEkSentCt1ReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optEkSentCt1ReceivedPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | noHeaderReceived s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedNoHeaderReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (optNoHeaderReceivedPBAt_entails_cap0 A (a + 8#64 + 40#64) s.uc)))
  | headerReceived s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedHeaderReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optHeaderReceivedPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | ct1Sampled s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedCt1SampledPBAt_eq_proto]
    exact sepConj_mono_left (optCt1SentPBAt_entails_cap0 A a s.uc)
  | ekReceivedCt1Sampled s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedEkReceivedCt1SampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optCt1SentEkReceivedPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | ct1Acknowledged s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedCt1AcknowledgedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (optCt1SentPBAt_entails_cap0 A (a + 8#64) s.uc)))
  | ct2Sampled s =>
    unfold CryptoVerification.SpqrV1.Drop.protoInnerStateAt Prost.MessageMerge.protoInnerStateCapAt
    dsimp only; rw [← chunkedCt2SampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (optCt2SentPBAt_entails_cap0 A (a + 8#64 + 56#64) s.uc)))

theorem of_drop_inner_canonical (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt ⊢
      DecodeState.optProtoInnerStateAt canonicalV1InnerHeap A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some is =>
    refine Entails.trans (protoInnerStateAt_entails_cap0 A a is) ?_
    refine Entails.trans (of_cap_inner_canonical A a 0 is) ?_
    unfold DecodeState.optProtoInnerStateAt
    apply Entails.sepExists_elim; intro q
    refine Entails.sepExists_right q ?_
    refine sepConj_mono_right (sepConj_mono_right ?_)
    apply Entails.sepExists_elim; intro H
    apply Entails.pure_left; rintro ⟨_, hH⟩
    exact hH

theorem of_cap_inner_ok (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (opt : Option V1State.InnerState)
    (hpb : OptInnerStatePolyBound remLen opt) :
    Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt ⊢
      optProtoInnerStateCapOkAt canonicalV1InnerHeap A a remLen opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkAt Prost.MessageMerge.optProtoInnerStateCapAt
    exact Entails.pure_right hpb (Entails.refl _)
  | some is =>
    refine Entails.trans (of_cap_inner_canonical A a remLen is) ?_
    unfold optProtoInnerStateCapOkAt optProtoInnerStateCapOkHeap
    dsimp only
    apply Entails.sepExists_elim; intro q
    apply Entails.pure_left; intro hq
    refine Entails.sepExists_right q ?_
    exact sepConj_mono_right (Entails.pure_right ⟨hpb, hq⟩ (Entails.refl _))

/-! ## Propositional Equality Bridges to `Drop.*` and `ProtoRepr.*` / `EncodeToVec.*` -/

theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  ProofLib.sepProp_eq_of_entails h1 h2

theorem optProtoInnerStateAt_canonical_entails_drop (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    DecodeState.optProtoInnerStateAt canonicalV1InnerHeap A a opt ⊢
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some is =>
    unfold DecodeState.optProtoInnerStateAt canonicalV1InnerHeap
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt
    dsimp only
    apply Entails.sepExists_elim; intro q
    apply Entails.pure_left; intro _hq
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H
    rw [sepConj_left_comm (quads28At a q)]
    apply Entails.pure_left; intro hreasm
    exact hreasm a

@[simp] theorem optProtoInnerStateAt_canonical_eq_drop (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    DecodeState.optProtoInnerStateAt canonicalV1InnerHeap A a opt =
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt :=
  sepProp_eq_of_entails
    (optProtoInnerStateAt_canonical_entails_drop A a opt)
    (of_drop_inner_canonical A a opt)

@[simp] theorem optProtoPqRatchetInnerAt_canonical_eq_drop (A : RustAlloc) (a : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    DecodeState.optProtoPqRatchetInnerAt canonicalV1InnerHeap A a opt =
      CryptoVerification.SpqrV1.Drop.optProtoPqRatchetInnerAt A a opt := by
  cases opt with
  | none => rfl
  | some i =>
    cases i with
    | v1 v => exact optProtoInnerStateAt_canonical_eq_drop A a v.innerState

@[simp] theorem protoPqRatchetStateAt_canonical_eq_drop (A : RustAlloc) (a : BitVec 64)
    (msg : PqRatchetState) :
    DecodeState.protoPqRatchetStateAt canonicalV1InnerHeap A a msg =
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateAt A a msg := by
  unfold DecodeState.protoPqRatchetStateAt CryptoVerification.SpqrV1.Drop.protoPqRatchetStateAt
  rw [optProtoPqRatchetInnerAt_canonical_eq_drop]

@[simp] theorem decodeStateResultAt_canonical_ok_eq_drop (A : RustAlloc) (a : BitVec 64)
    (msg : PqRatchetState) :
    decodeStateResultAt canonicalV1InnerHeap A a (.ok msg) =
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateAt A a msg :=
  protoPqRatchetStateAt_canonical_eq_drop A a msg

/-! ## Callee Contract Bridges (`Drop`, `ChainParams`, `EpochDirection`, `SkipField3`, `GrowOne`) -/

end CryptoVerification.SpqrV1.Top.DecodeState
