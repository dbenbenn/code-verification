/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part H

**Checked by Lean.**

Call and error-branch helpers for `<PolyEncoder>::from_pb` (`+9096`) and `<PolyDecoder>::from_pb`
(`+9384`) on the `+9036 -> ret` path.
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
open V1State.Chunked

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



@[local simp, local arm64_norm, local wp_norm]
theorem v2hsh_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Pure Reduction Lemmas for `States.from_pb` on `HeaderSent` (`sendingEk = some pbEnc`) -/

theorem v2hsh_from_pb_headerSent_some_enc_eq (F : ShaCompress) (s : V1State.Chunked.HeaderSent)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u) (hdk_len : u.dk.length = 2400) (hauth : u.auth = some auth)
    (henc : s.sendingEk = some pbEnc) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) } =
      match fromPbResult (pbToProtoPolyEncoder pbEnc) with
      | .error _ => .error (.err .stateDecode)
      | .ok enc =>
        match s.receivingCt1 with
        | none => .error (.err .stateDecode)
        | some pbDec =>
          match decoderFromPbResult (pbToProtoPolyDecoder pbDec) with
          | .error _ => .error (.err .stateDecode)
          | .ok dec =>
            .ok (.headerSent
              { uc := { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, dk := u.dk, epoch := u.epoch },
                sending_ek := enc, receiving_ct1 := dec }) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec_ok henc
    subst huc henc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = true := by
      change (u.dk.length == 2400) = true
      simp [hdk_len]
    dsimp only [States.from_pb]
    rw [v2hs_headerSent_from_pb_after_pts F (some u) (some pbEnc) receivingCt1 hdec_ok]
    simp only [Unchunked.SendEk.EkSent.from_pb, hdk_eq, hauth, ↓reduceIte,
      encoderFromPbStateDecode_some, spqrAuthApi, Authenticator.fromPb,
      Pure.pure, Except.pure, Functor.map, Except.map, Bind.bind, Except.bind]
    cases fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error e => rfl
    | ok enc =>
      cases hdec : receivingCt1 with
      | none =>
        simp only [decoderFromPbStateDecode_none, Bind.bind, Except.bind, Functor.map, Except.map]
      | some pbDec =>
        simp only [decoderFromPbStateDecode_some, Bind.bind, Except.bind, Functor.map, Except.map]
        cases decoderFromPbResult (pbToProtoPolyDecoder pbDec) <;> rfl

/-! ## Stack & Proto Packing / Splitting Helpers -/

theorem v2hsh_protoPolyEncoder_pack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hse_protoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A (some pb) w0 w8 w16 w24 w32 w40 w48 ⊢
    protoPolynomialEncoderAt A a pb := by
  refine Entails.trans ?_ (v2hse_protoPolyEncoderAt_pack A a pb w0 w8 w16 w24 w32 w40 w48)
  refine sepConj_mono_right ?_
  unfold v1_optProtoPolyEncoderHeap v2hse_protoPolyEncoderHeap
  apply Entails.pure_left; rintro ⟨hw0, hw16, hw40, hw48⟩
  have hpure : v2hse_ProtoPolyEncoderPure pb w16 w40 w48 := ⟨hw16, hw40, hw48⟩
  exact Entails.pure_right hpure (Entails.refl _)

theorem v2hsh_pack64_unpack64 (w : BitVec 64) :
    v1_pack64 (unpack64 w) = w := by
  dsimp only [v1_pack64, unpack64, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  bv_kernel

theorem v2hsh_wordAt_0_eq_of_take8 (bs : List (BitVec 8)) (w8 : BitVec 64)
    (h : bs.take 8 = unpack64 w8) :
    v1_wordAt bs 0 = w8 := by
  unfold v1_wordAt
  rw [List.drop_zero, h, v2hsh_pack64_unpack64]

theorem v2hsh_protoPolyDecoder_pack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 d24 d32 : BitVec 64) :
    ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d8) ∗ ((a + 16#64) ↦₆₄ d16) ∗
      ((a + 24#64) ↦₆₄ d24) ∗ ((a + 32#64) ↦₆₄ d32)) ∗
      v2hs_optProtoDecoderHeap A (some pb) d0 d8 d16 d24 d32 ⊢
    protoPolynomialDecoderAt A a pb := by
  change v2hs_optProtoDecoderWordsAt a d0 d8 d16 d24 d32 ∗
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 (d24.extractLsb' 0 32) (d24.extractLsb' 32 32) d32 ⊢
    protoPolynomialDecoderAt A a pb
  rw [v2hstop_optProtoDecoderWordsAt_eq_v2hsc]
  exact v4b_protoPolyDecoderAt_pack A a pb d0 d8 d16 (d24.extractLsb' 0 32) (d24.extractLsb' 32 32) d32

theorem v2hsh_onPanic_shift {s0 sm : State} (htrace : TraceCalleeSaved sm s0)
    (sf : State) {F : SepProp} :
    encoderFromPbOnPanic sm sf ∗ F ⊢ statesFromPbOnPanic s0 sf := by
  dsimp only [encoderFromPbOnPanic, statesFromPbOnPanic]
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v2hsh_memRegion_1344_960_split (fsp : BitVec 64) :
    memRegion (fsp + 1344#64) 960 ⊢
      memRegion (fsp + 1344#64) 48 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 1888#64) polyEncoderSize ∗
      memRegion (fsp + 2288#64) 16 := by
  dsimp only [polyEncoderSize]
  exact split_top <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    Entails.refl _

theorem v2hsh_stack896ScratchRest_split_56 (fsp : BitVec 64) :
    v2hs_stack896ScratchRest fsp ⊢
      memRegion fsp 56 ∗
      (∃∗ slot56_old : BitVec 64, (fsp + 56#64) ↦₆₄ slot56_old) ∗
      memRegion (fsp + 64#64) 32 ∗
      memRegion (fsp + 104#64) 48 ∗
      memRegion (fsp + 160#64) 16 ∗
      memRegion (fsp + 192#64) 8 ∗
      memRegion (fsp + 208#64) 8 := by
  unfold v2hs_stack896ScratchRest
  have h96 : memRegion fsp 96 ⊢
      memRegion fsp 56 ∗
      (∃∗ slot56_old : BitVec 64, (fsp + 56#64) ↦₆₄ slot56_old) ∗
      memRegion (fsp + 64#64) 32 :=
    split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_left h96) (Entails.of_eq (by ac_rfl))

theorem v2hsh_memRegion_240_736_split_24 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 736 ⊢
      memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712 :=
  split_top <| split_step (Entails.refl _) <| Entails.refl _

/-! ## `<PolyEncoder>::from_pb` Call Helper at `+9096` -/

theorem v2hsh_vecU8Heap_entails_payload (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢ vecU8Payload A cap ptr bs := by
  unfold v4b_vecU8Heap
  exact Entails.pure_left fun _ => Entails.refl _

theorem v2hsh_unchunkedEkSentAt_pack (A : RustAlloc) (F : ShaCompress)
    (a : BitVec 64) (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (u8 u16 u24 u48 u72 u80 pa1 pa2 : BitVec 64)
    (hdk_len : u.dk.length = 2400)
    (hu24 : u24 = 2400#64)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80 : u80 = u.epoch) :
    v2hs_ekSentWordsAt a u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      vecU8Payload A u48 pa1 auth.rootKey ∗
      vecU8Payload A u72 pa2 auth.macKey ⊢
    unchunkedEkSentAt A (F := F) a
      { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, dk := u.dk, epoch := u.epoch } := by
  have hu24' : u24 = BitVec.ofNat 64 u.dk.length := by rw [hu24, hdk_len]
  subst hu24' hu48 hu72 hu80
  unfold v2hs_ekSentWordsAt
  dsimp only [unchunkedEkSentAt, authenticatorAt]
  have hrk := vecU8_of_header_payload A a (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hmk := vecU8_of_header_payload A (a + 24#64) (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hdk := vecU8_of_header_payload A (a + 48#64) u8 u16 u.dk
  simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hrk hmk hdk ⊢
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (v2hsh_vecU8Heap_entails_payload A u.dk u8 u16 (BitVec.ofNat 64 u.dk.length)))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((a + 8#64) ↦₆₄ pa1) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey) ∗
     (((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((a + 32#64) ↦₆₄ pa2) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey)) ∗
    (((a + 48#64) ↦₆₄ u8) ∗ ((a + 56#64) ↦₆₄ u16) ∗
     ((a + 64#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
     vecU8Payload A u8 u16 u.dk) ∗
    ((a + 72#64) ↦₆₄ u.epoch) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono (sepConj_mono hrk hmk) (sepConj_mono_left hdk)) (Entails.of_eq (by ac_rfl))

theorem v2hsh_stack896ScratchRest_pack_56 (fsp tag : BitVec 64) :
    memRegion fsp 56 ∗
      ((fsp + 56#64) ↦₆₄ tag) ∗
      memRegion (fsp + 64#64) 32 ∗
      memRegion (fsp + 104#64) 48 ∗
      memRegion (fsp + 160#64) 16 ∗
      memRegion (fsp + 192#64) 8 ∗
      memRegion (fsp + 208#64) 8 ⊢
    v2hs_stack896ScratchRest fsp := by
  unfold v2hs_stack896ScratchRest
  have h96 : memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ tag) ∗ memRegion (fsp + 64#64) 32 ⊢
      memRegion fsp 96 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ tag) ∗ memRegion (fsp + 64#64) 32) ∗
    memRegion (fsp + 104#64) 48 ∗
    memRegion (fsp + 160#64) 16 ∗
    memRegion (fsp + 192#64) 8 ∗
    memRegion (fsp + 208#64) 8 by ac_rfl)) ?_
  exact sepConj_mono_left h96

theorem v2hsh_memRegion_240_24_712_collapse (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712 ⊢
      memRegion (fsp + 240#64) 736 :=
  collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v2hsh_memRegion_1344_960_collapse (fsp : BitVec 64) :
    memRegion (fsp + 1344#64) 48 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢
    memRegion (fsp + 1344#64) 960 :=
  collapse_top <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v2hsh_memRegion_104_72_collapse (fsp w152 : BitVec 64) :
    memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 160#64) 16 ⊢
    memRegion (fsp + 104#64) 72 :=
  collapse_top <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v2hsh_memRegion_1792_96_collapse (fsp : BitVec 64) :
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ⊢
      memRegion (fsp + 1792#64) 96 :=
  collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v2hsh_ok_dec_mid_stack_collapse (fsp : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (u48 pa1 u72 pa2 u8 u16 u24 u80 tag : BitVec 64) :
    memRegion (fsp + 240#64) 24 ∗
      memRegion (fsp + 264#64) 712 ∗
      memRegion (fsp + 976#64) 56 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 192 ∗
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      memRegion (fsp + 1344#64) 48 ∗
      ((fsp + 1392#64) ↦₆₄ tag) ⊢
    memRegion (fsp + 240#64) 1032 ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      memRegion (fsp + 1280#64) 120 := by
  have hdec40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  unfold v2hs_ekSentWordsAt
  simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  have h1032 :
      memRegion (fsp + 240#64) 24 ∗
        memRegion (fsp + 264#64) 712 ∗
        memRegion (fsp + 976#64) 56 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        ((fsp + 1264#64) ↦₆₄ u48) ⊢
      memRegion (fsp + 240#64) 1032 := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdec40)))) ?_
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h120 :
      ((fsp + 1280#64) ↦₆₄ u48) ∗
        ((fsp + 1288#64) ↦₆₄ u72) ∗
        ((fsp + 1296#64) ↦₆₄ pa2) ∗
        ((fsp + 1304#64) ↦₆₄ u72) ∗
        ((fsp + 1312#64) ↦₆₄ u8) ∗
        ((fsp + 1320#64) ↦₆₄ u16) ∗
        ((fsp + 1328#64) ↦₆₄ u24) ∗
        ((fsp + 1336#64) ↦₆₄ u80) ∗
        memRegion (fsp + 1344#64) 48 ∗
        ((fsp + 1392#64) ↦₆₄ tag) ⊢
      memRegion (fsp + 1280#64) 120 :=
    collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      Drop.pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (fsp + 240#64) 24 ∗
     memRegion (fsp + 264#64) 712 ∗
     memRegion (fsp + 976#64) 56 ∗
     v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
     memRegion (fsp + 1072#64) 192 ∗
     ((fsp + 1264#64) ↦₆₄ u48)) ∗
    ((fsp + 1272#64) ↦₆₄ pa1) ∗
    (((fsp + 1280#64) ↦₆₄ u48) ∗
     ((fsp + 1288#64) ↦₆₄ u72) ∗
     ((fsp + 1296#64) ↦₆₄ pa2) ∗
     ((fsp + 1304#64) ↦₆₄ u72) ∗
     ((fsp + 1312#64) ↦₆₄ u8) ∗
     ((fsp + 1320#64) ↦₆₄ u16) ∗
     ((fsp + 1328#64) ↦₆₄ u24) ∗
     ((fsp + 1336#64) ↦₆₄ u80) ∗
     memRegion (fsp + 1344#64) 48 ∗
     ((fsp + 1392#64) ↦₆₄ tag)) by ac_rfl)) ?_
  exact sepConj_mono h1032 (sepConj_mono_right h120)

theorem v2hsh_enc_words_to_encCellsAt (fsp w8 w16 w24 w392 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (hsplit : (((fsp + 1392#64) + 8#64) ↦ₛ bs) ∗ (((fsp + 1392#64) + 392#64) ↦₆₄ w392) =
      (((fsp + 1392#64) + 8#64) ↦₆₄ w8) ∗ (((fsp + 1392#64) + 16#64) ↦₆₄ w16) ∗
      (((fsp + 1392#64) + 24#64) ↦₆₄ w24) ∗ (((fsp + 1392#64) + 32#64) ↦ₛ tail368.val)) :
    ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗
      ((fsp + 1416#64) ↦₆₄ w24) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ⊢
    v1_encCellsAt (fsp + 1392#64) bs ∗ ((fsp + 1784#64) ↦₆₄ w392) := by
  rw [← v1_bs384_eq_encCells bs hbs (fsp + 1392#64)]
  simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hsplit ⊢
  exact Entails.of_eq hsplit.symm

/-! ## `<PolyDecoder>::from_pb` Call Helper at `+9384` -/

theorem v2hsh_collapse_2304_from_9228
    (fsp u8 u16 u24 u40 u48 u72 u80 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
      ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
      v2hs_stack896ScratchRest fsp ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 192 ∗
      memRegion (fsp + 1264#64) 80 ∗
      memRegion (fsp + 1344#64) 960 ⊢
      memRegion fsp 2304 := by
  dsimp only [v2hs_stack896ScratchRest]
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have hcol :
      memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
      memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
      memRegion (fsp + 976#64) 56 ∗ memRegion (fsp + 1032#64) 40 ∗
      memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80 ∗
      memRegion (fsp + 1344#64) 960 ⊢
      memRegion fsp 2304 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    (memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 48 ∗
     ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
     ((fsp + 184#64) ↦₆₄ pa2) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
     memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
     ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
     memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80 ∗
     memRegion (fsp + 1344#64) 960) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h56 (sepConj_mono_left h40)) ?_
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

theorem v2hsh_polyEncoderAt_pack_from_words (A : RustAlloc)
    (fsp w8 w16 w24 w392 : BitVec 64)
    (bs : List (BitVec 8)) (enc : PolyEncoder) (P_enc_heap : SepProp)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (hsplit : (((fsp + 1392#64) + 8#64) ↦ₛ bs) ∗ (((fsp + 1392#64) + 392#64) ↦₆₄ w392) =
      (((fsp + 1392#64) + 8#64) ↦₆₄ w8) ∗ (((fsp + 1392#64) + 16#64) ↦₆₄ w16) ∗
      (((fsp + 1392#64) + 24#64) ↦₆₄ w24) ∗ (((fsp + 1392#64) + 32#64) ↦ₛ tail368.val))
    (hreloc : ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      (((fsp + 1392#64) + 8#64) ↦ₛ bs) ∗
      (((fsp + 1392#64) + 392#64) ↦₆₄ w392) ∗ P_enc_heap ⊢
      polyEncoderAt A (fsp + 1392#64) enc) :
    ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗
      ((fsp + 1416#64) ↦₆₄ w24) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
      P_enc_heap ⊢
    polyEncoderAt A (fsp + 1392#64) enc := by
  simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hsplit hreloc ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
    (((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗
     ((fsp + 1416#64) ↦₆₄ w24) ∗ ((fsp + 1424#64) ↦ₛ tail368.val)) ∗
    P_enc_heap by ac_rfl)) ?_
  rw [← hsplit]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hreloc

end CryptoVerification.SpqrV1.States.FromPb

