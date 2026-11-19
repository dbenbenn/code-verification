/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part A

Model reduction lemmas, protobuf unpacking/packing helpers for `HeaderSent` (`176`B), and
shared error epilogues and inline `ProtoPolynomialDecoder` deallocation (`+4420..+9228`).
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
open V1State.Chunked
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## Pure Model Reduction Lemmas for `HeaderSent` -/

theorem v2hs_ptsNeeded_bne_eq (ptsNeeded : BitVec 32) :
    (ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2) = !(ptsNeeded == 480#32) := by
  change (ptsNeeded.toNat != 480) = !(ptsNeeded == 480#32)
  cases h : (ptsNeeded == 480#32)
  · have hne : ptsNeeded.toNat ≠ 480 := by
      intro heq
      have h1 : ptsNeeded = 480#32 := BitVec.eq_of_toNat_eq heq
      rw [h1] at h
      contradiction
    simp [hne]
  · have heq : ptsNeeded = 480#32 := beq_iff_eq.mp h
    subst heq
    rfl

theorem v2hs_from_pb_headerSent_bad_pts_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (d : PolynomialDecoder)
    (hdec : s.receivingCt1 = some d)
    (hpts : (d.ptsNeeded == 480#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .msgDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at hdec
    subst hdec
    simp only [States.from_pb, Chunked.SendEk.HeaderSent.from_pb,
      v2hs_ptsNeeded_bne_eq, hpts, Bool.not_false, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_headerSent_from_pb_after_pts (F : ShaCompress)
    (uc : Option V1State.Unchunked.EkSent)
    (sendingEk : Option PolynomialEncoder)
    (receivingCt1 : Option PolynomialDecoder)
    (hdec : match receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true) :
    Chunked.SendEk.HeaderSent.from_pb spqrPolyApi (spqrAuthApi F)
      { uc := uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } =
    (do
      let u ← match uc with
        | none => Except.error (StatesError.err .stateDecode)
        | some u => Except.ok u
      let uc ← Unchunked.SendEk.EkSent.from_pb (spqrAuthApi F) u
      let sendingEk ← encoderFromPbStateDecode spqrPolyApi sendingEk
      let receivingCt1 ← decoderFromPbStateDecode spqrPolyApi receivingCt1
      Except.ok { uc := uc, sending_ek := sendingEk, receiving_ct1 := receivingCt1 }) := by
  cases receivingCt1 with
  | none =>
    simp only [Chunked.SendEk.HeaderSent.from_pb, Bind.bind, Except.bind]
    cases uc <;> rfl
  | some d =>
    simp only at hdec
    simp only [Chunked.SendEk.HeaderSent.from_pb, v2hs_ptsNeeded_bne_eq, hdec,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    cases uc <;> rfl

theorem v2hs_from_pb_headerSent_uc_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F none sendingEk receivingCt1 hdec,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_bad_dk_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : (BitVec.ofNat 64 u.dk.length == 2400#64) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = false := by
      change (u.dk.length == 2400) = false
      rw [beq_eq_false_iff_ne]
      intro hlen
      rw [hlen] at hdk
      exact Bool.noConfusion hdk
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) sendingEk receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, Bool.false_eq_true, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_auth_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : u.dk.length = 2400)
    (hauth : u.auth = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = true := by
      change (u.dk.length == 2400) = true
      simp [hdk]
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) sendingEk receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, hauth, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_sendingEk_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : u.dk.length = 2400)
    (hauth : u.auth = some auth)
    (henc : s.sendingEk = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec henc
    subst huc henc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = true := by
      change (u.dk.length == 2400) = true
      simp [hdk]
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) none receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, hauth, encoderFromPbStateDecode, ↓reduceIte,
      Pure.pure, Except.pure, Functor.map, Except.map, Bind.bind, Except.bind]

/-! ## Shared Error Epilogue (`+9224/+9228 -> +60 -> s0.x30`) and Decoder Deallocation (`+4420..+4512`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bfm_loByte_eq (x23 x26 : BitVec 64) :
    (((x26 &&& 72057594037927935#64) <<< 8) ||| (x23 &&& 255#64)).extractLsb' 0 8 =
      x23.extractLsb' 0 8 := by
  bv_kernel

theorem v2hs_memRegion_2304_split_232 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 232 ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 2064 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v2hs_memRegion_2304_join_232 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 2064 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

@[expose, reducible]
def v2hs_Saved4436Preserved (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x22 = ptsCap ∧
  s.readReg64 .x23 = x23_val ∧
  TraceCalleeSaved s s0

/-- Five 64-bit words (`40` bytes) of `Option<ProtoPolynomialDecoder>` at `a`. -/
@[expose] def v2hs_optProtoDecoderWordsAt (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ d_w0) ∗ ((a + 8#64) ↦₆₄ d_w8) ∗ ((a + 16#64) ↦₆₄ d_w16) ∗
  ((a + 24#64) ↦₆₄ d_w24) ∗ ((a + 32#64) ↦₆₄ d_w32)

theorem v2hs_optProtoDecoderWordsAt_entails_40
    (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 ⊢ memRegion a 40 := by
  unfold v2hs_optProtoDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Address-independent heap and pure constraints for `Option<ProtoPolynomialDecoder>`
associated with 5 64-bit words `d_w0..d_w32`. -/
@[expose] def v2hs_optProtoDecoderHeap (A : RustAlloc)
    (optDec : Option ProtoPolynomialDecoder)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  v4b_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
    (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32

theorem v2hs_optProtoDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ d_w0 : BitVec 64, ∃∗ d_w8 : BitVec 64, ∃∗ d_w16 : BitVec 64,
      ∃∗ d_w24 : BitVec 64, ∃∗ d_w32 : BitVec 64,
        v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 := by
  refine Entails.trans (v4b_optProtoPolyDecoderAt_unpack A a optDec) ?_
  apply Entails.sepExists_elim; intro d_w0
  apply Entails.sepExists_elim; intro d_w8
  apply Entails.sepExists_elim; intro d_w16
  apply Entails.sepExists_elim; intro d24
  apply Entails.sepExists_elim; intro d28
  apply Entails.sepExists_elim; intro d_w32
  refine Entails.sepExists_right d_w0
    (Entails.sepExists_right d_w8
      (Entails.sepExists_right d_w16
        (Entails.sepExists_right (d28 ++ d24)
          (Entails.sepExists_right d_w32 ?_))))
  unfold v4b_optProtoPolyDecoderWordsAt v2hs_optProtoDecoderWordsAt v2hs_optProtoDecoderHeap
  have hlo : (d28 ++ d24).extractLsb' 0 32 = d24 := by bv_kernel
  have hhi : (d28 ++ d24).extractLsb' 32 32 = d28 := by bv_kernel
  rw [hlo, hhi]
  have h24 := ProofLib.pointsTo32_pair (a + 24#64) d24 d28
  have hadd : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
  rw [hadd] at h24
  rw [← h24]
  exact Entails.of_eq (by ac_rfl)

/-- Ten 64-bit words (`80` bytes) of `Option<ProtoUnchunkedEkSent>` at `a`. -/
@[expose] def v2hs_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80)

theorem v2hs_ucWordsAt_entails_80
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    v2hs_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢ memRegion a 80 := by
  unfold v2hs_ucWordsAt
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
    Drop.pointsTo64_entails_memRegion _ _

theorem v2hs_split_72_words (a : BitVec 64) :
    memRegion (a + 8#64) 72 ⊢
      (∃∗ u16 : BitVec 64, (a + 8#64) ↦₆₄ u16) ∗
      (∃∗ u24 : BitVec 64, (a + 16#64) ↦₆₄ u24) ∗
      (∃∗ u32 : BitVec 64, (a + 24#64) ↦₆₄ u32) ∗
      (∃∗ u40 : BitVec 64, (a + 32#64) ↦₆₄ u40) ∗
      (∃∗ u48 : BitVec 64, (a + 40#64) ↦₆₄ u48) ∗
      (∃∗ u56 : BitVec 64, (a + 48#64) ↦₆₄ u56) ∗
      (∃∗ u64 : BitVec 64, (a + 56#64) ↦₆₄ u64) ∗
      (∃∗ u72 : BitVec 64, (a + 64#64) ↦₆₄ u72) ∗
      (∃∗ u80 : BitVec 64, (a + 72#64) ↦₆₄ u80) := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    mem64_entails _

/-- Address-independent heap and pure constraints for `Option<ProtoUnchunkedEkSent>`
associated with 10 64-bit words `u8..u80`. -/
@[expose] def v2hs_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.EkSent →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, u8, _, _, _, _, _, _, _, _, _ => ⌜u8 = noneCap⌝
  | some st, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80 =>
    v4b_vecU8Heap A st.dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A st.auth u32 u40 u48 u56 u64 u72 ∗
    ⌜u80 = st.epoch⌝

theorem v2hs_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent) :
    optProtoUnchunkedEkSentAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64,
        v2hs_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 := by
  cases optUc with
  | none =>
    simp only [optProtoUnchunkedEkSentAt, v2hs_optProtoUcHeap]
    refine Entails.trans (sepConj_mono_right (v2hs_split_72_words a)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u24
    apply Entails.sepExists_elim; intro u16
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80 ?_)))))))))
    unfold v2hs_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some st =>
    simp only [optProtoUnchunkedEkSentAt, protoUnchunkedEkSentAt, v2hs_optProtoUcHeap]
    have hdk := v4b_vecU8_unpack A a st.dk
    have hauth := v3cr_optProtoAuth_unpack A (a + 24#64) st.auth
    refine Entails.trans (sepConj_mono hdk (sepConj_mono_left hauth)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u8
    apply Entails.sepExists_elim; intro u16
    apply Entails.sepExists_elim; intro u24
    simp only [arm64_norm]
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right st.epoch ?_)))))))))
    unfold v2hs_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : st.epoch = st.epoch) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))

/-- Eleven 128-bit (`↦₁₂₈`) chunks covering `base + 0..176` (`176` bytes). -/
@[expose] def v2hs_pb128At (base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  (base ↦₁₂₈ (u16 ++ u8)) ∗ ((base + 16#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((base + 32#64) ↦₁₂₈ (u48 ++ u40)) ∗ ((base + 48#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((base + 64#64) ↦₁₂₈ (u80 ++ u72)) ∗ ((base + 80#64) ↦₁₂₈ (w8 ++ w0)) ∗
  ((base + 96#64) ↦₁₂₈ (w24 ++ w16)) ∗ ((base + 112#64) ↦₁₂₈ (w40 ++ w32)) ∗
  ((base + 128#64) ↦₁₂₈ (d_w0 ++ w48)) ∗ ((base + 144#64) ↦₁₂₈ (d_w16 ++ d_w8)) ∗
  ((base + 160#64) ↦₁₂₈ (d_w32 ++ d_w24))

theorem v2hs_words_eq_pb128
    (base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_ucWordsAt base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v1_optProtoPolyEncoderWordsAt (base + 80#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (base + 136#64) d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hs_pb128At base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt, v2hs_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v2hs_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000002#64) ∗
      v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize := by
  rw [← v2hs_words_eq_pb128]
  have h80 := v2hs_ucWordsAt_entails_80 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 88#64) w0 w8 w16 w24 w32 w40 w48
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h224 : (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 8#64) 80 ∗
      memRegion (pbA + 88#64) 56 ∗ memRegion (pbA + 144#64) 40 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| Entails.refl _
  simp only [arm64_norm] at h56 h40 ⊢
  exact Entails.trans (sepConj_mono_right (sepConj_mono h80 (sepConj_mono h56 (sepConj_mono_left h40)))) h224

theorem v2hs_memRegion_176_to_128 (base : BitVec 64) :
    memRegion base 176 ⊢
      (∃∗ q0 : BitVec 128, base ↦₁₂₈ q0) ∗ (∃∗ q1 : BitVec 128, (base + 16#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (base + 32#64) ↦₁₂₈ q2) ∗ (∃∗ q3 : BitVec 128, (base + 48#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (base + 64#64) ↦₁₂₈ q4) ∗ (∃∗ q5 : BitVec 128, (base + 80#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (base + 96#64) ↦₁₂₈ q6) ∗ (∃∗ q7 : BitVec 128, (base + 112#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (base + 128#64) ↦₁₂₈ q8) ∗ (∃∗ q9 : BitVec 128, (base + 144#64) ↦₁₂₈ q9) ∗
      (∃∗ q10 : BitVec 128, (base + 160#64) ↦₁₂₈ q10) := by
  exact split_top <|
    split_step0 (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    mem128_entails _

theorem v2hs_memRegion_1032_split_232 (fsp : BitVec 64) :
    memRegion fsp 1032 ⊢
      memRegion fsp 232 ∗ (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _

theorem v2hs_memRegion_1032_unsplit_232 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792 ⊢ memRegion fsp 1032 := by
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v2hs_collapse_frame_2304 (fsp d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    memRegion fsp 1032 ∗ v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 1232 ⊢ memRegion fsp 2304 := by
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h2304 : memRegion fsp 1032 ∗ memRegion (fsp + 1032#64) 40 ∗ memRegion (fsp + 1072#64) 1232 ⊢
      memRegion fsp 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h40)) h2304

end CryptoVerification.SpqrV1.States.FromPb
