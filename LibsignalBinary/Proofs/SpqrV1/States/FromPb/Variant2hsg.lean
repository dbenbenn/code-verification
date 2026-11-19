/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part G

Error-branch exits and prefix composition (`+508 -> +9036`) reducing `InnerState.headerSent` to
the `sendingEk = some pbEnc` continuation.
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

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Unpack & Stack Split/Collapse Helpers (`v2hstop_*`) -/

theorem v2hstop_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢ vecCapPtrDealloc A cap ptr := by
  dsimp only [v4b_vecU8Heap]; apply Entails.pure_left; intro _
  exact vecU8Payload_entails_dealloc A cap ptr bs

theorem v2hstop_optProtoInnerStateAt_headerSent_unpack (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.HeaderSent) :
    optProtoInnerStateAt A pbA (some (.headerSent s)) ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64, ∃∗ u80 : BitVec 64,
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
      ∃∗ d_w0 : BitVec 64, ∃∗ d_w8 : BitVec 64, ∃∗ d_w16 : BitVec 64,
      ∃∗ d_w24 : BitVec 64, ∃∗ d_w32 : BitVec 64,
        (pbA ↦₆₄ 0x8000000000000002#64) ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (pbA + 184#64) 40 ∗
        v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder)
          d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderSentAt]
  have hu := v2hs_optProtoUcAt_unpack A (pbA + 8#64) s.uc
  have he := v1_optProtoPolyEncoderAt_unpack A (pbA + 88#64) (s.sendingEk.map pbToProtoPolyEncoder)
  have hd := v2hs_optProtoDecoderAt_unpack A (pbA + 144#64) (s.receivingCt1.map pbToProtoPolyDecoder)
  have ha88 : (pbA + 8#64) + 80#64 = pbA + 88#64 := by bv_omega
  have ha144 : (pbA + 8#64) + 136#64 = pbA + 144#64 := by bv_omega
  rw [ha88, ha144]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono hu (sepConj_mono he hd)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d_w0; apply Entails.sepExists_elim; intro d_w8
  apply Entails.sepExists_elim; intro d_w16; apply Entails.sepExists_elim; intro d_w24
  apply Entails.sepExists_elim; intro d_w32
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w32; apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro u8; apply Entails.sepExists_elim; intro u16
  apply Entails.sepExists_elim; intro u24; apply Entails.sepExists_elim; intro u32
  apply Entails.sepExists_elim; intro u40; apply Entails.sepExists_elim; intro u48
  apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64
  apply Entails.sepExists_elim; intro u72; apply Entails.sepExists_elim; intro u80
  refine Entails.sepExists_right u8 (Entails.sepExists_right u16 (Entails.sepExists_right u24
    (Entails.sepExists_right u32 (Entails.sepExists_right u40 (Entails.sepExists_right u48
    (Entails.sepExists_right u56 (Entails.sepExists_right u64 (Entails.sepExists_right u72
    (Entails.sepExists_right u80 (Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right w16 (Entails.sepExists_right w24 (Entails.sepExists_right w32
    (Entails.sepExists_right w40 (Entails.sepExists_right w48 (Entails.sepExists_right d_w0
    (Entails.sepExists_right d_w8 (Entails.sepExists_right d_w16 (Entails.sepExists_right d_w24
    (Entails.sepExists_right d_w32 ?_)))))))))))))))))))))
  have h128 := v2hs_words_eq_pb128 (pbA + 8#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  rw [ha88, ha144] at h128; rw [← h128]; exact Entails.of_eq (by ac_rfl)

theorem v2hstop_optProtoDecoderWordsAt_eq_v2hsc (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hsc_optProtoPolyDecoderWordsAt a d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 := by
  unfold v2hs_optProtoDecoderWordsAt v2hsc_optProtoPolyDecoderWordsAt
  have hpair := ProofLib.pointsTo32_pair (a + 24#64) (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32)
  have hcat : d_w24.extractLsb' 32 32 ++ d_w24.extractLsb' 0 32 = d_w24 := by bv_kernel
  have ha28 : (a + 24#64) + 4#64 = a + 28#64 := by bv_omega
  rw [hcat, ha28] at hpair; rw [← hpair]; ac_rfl

theorem v2hstop_optProtoDecoderHeap_eq_v2hsc (A : RustAlloc)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 := by
  cases optDec <;> rfl

theorem v2hstop_optProtoDecoderHeap_none_extract (A : RustAlloc)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A none d_w0 d_w8 d_w16 d_w24 d_w32 ⊢
      ⌜d_w0 = noneCap⌝ ∗
      v2hs_optProtoDecoderHeap A none d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
  conv_lhs => rw [← sepConj_emp (⌜d_w0 = noneCap⌝)]
  apply Entails.pure_left; intro hd_w0
  refine Entails.pure_right hd_w0 ?_
  rw [← sepConj_emp (⌜d_w0 = noneCap⌝)]
  exact Entails.pure_right hd_w0 (Entails.refl _)

theorem v2hstop_optProtoDecoderHeap_some_extract (A : RustAlloc) (d : PolynomialDecoder)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ⊢
      ⌜d_w0.toNat * 24 < 2 ^ 63 ∧ d_w24.extractLsb' 0 32 = d.ptsNeeded⌝ ∗
      v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
  apply Entails.pure_left; rintro ⟨hd16, hd24, hd28, hle, hcap, hptr, h32⟩
  exact Entails.pure_right ⟨hcap, hd24⟩
    (Entails.pure_right ⟨hd16, hd24, hd28, hle, hcap, hptr, h32⟩ (Entails.refl _))

theorem v2hstop_optProtoUcHeap_some_extract (A : RustAlloc) (u : V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    v2hs_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.dk.length ∧
        u.dk.length < 2 ^ 63 ∧ u80 = u.epoch⌝ ∗
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 := by
  dsimp only [v2hs_optProtoUcHeap, v4b_vecU8Heap, vecU8Payload]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜u24 = BitVec.ofNat 64 u.dk.length ∧ u8.toNat < 2 ^ 63⌝ ∗
    (⌜u.dk.length ≤ u8.toNat ∧ u8.toNat < 2 ^ 63 ∧ u16 ≠ 0#64⌝ ∗
     (⌜u80 = u.epoch⌝ ∗
      ((if u8 = 0#64 then emp
        else A.live u16 u8.toNat 1 ∗ (u16 ↦ₛ u.dk) ∗
          memRegion (u16 + BitVec.ofNat 64 u.dk.length) (u8.toNat - u.dk.length)) ∗
       v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hu24, hcap⟩
  apply Entails.pure_left; rintro ⟨hle, _, hptr⟩
  apply Entails.pure_left; intro hu80
  refine Entails.pure_right ⟨hcap, hu24, Nat.lt_of_le_of_lt hle hcap, hu80⟩ ?_
  rw [← sepConj_assoc]
  exact sepConj_mono_left (Entails.pure_right ⟨hu24, hcap⟩
    (Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _)))

theorem v2hstop_optProtoAuthHeap_some_extract (A : RustAlloc) (auth : ProtoAuthenticator)
    (u32 u40 u48 u56 u64 u72 : BitVec 64) :
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ⊢
      ⌜u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 auth.rootKey.length ∧
        u72 = BitVec.ofNat 64 auth.macKey.length ∧ auth.rootKey.length < 2 ^ 63⌝ ∗
      vecU8Payload A u32 u40 auth.rootKey ∗
      vecU8Payload A u56 u64 auth.macKey := by
  dsimp only [v1_optProtoAuthHeap, vecU8Payload]
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu48, hu72⟩
  apply Entails.pure_left; rintro ⟨hr_le, hr_cap, hr_ptr⟩
  refine Entails.pure_right ⟨hr_cap, hu48, hu72, Nat.lt_of_le_of_lt hr_le hr_cap⟩ ?_
  exact Entails.pure_right
    (show auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧ u40 ≠ 0#64 from
      ⟨hr_le, hr_cap, hr_ptr⟩) (Entails.refl _)

theorem v2hstop_collapse_976_from_err_uc
    (fsp w96 w152 w184 w216 w224 w232 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 176#64) 8 ∗
      ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion fsp 976 := by
  have h184 := Drop.pointsTo64_entails_memRegion (fsp + 184#64) w184
  have h896 := v2hs_memRegion_896_unsplit_scratch fsp w96 w152 w216 w224 w232
  have h976 := v2hs_memRegion_896_ucWords_to_976 fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h184)))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 176#64) 8 ∗
     memRegion (fsp + 184#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
     ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
     v2hs_stack896ScratchRest fsp) ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left h896) h976

theorem v2hstop_ekSentWordsAt_entails_80 (a u48 pa1 u72 pa2 u8 u16 u24 u80 : BitVec 64) :
    v2hs_ekSentWordsAt a u48 pa1 u72 pa2 u8 u16 u24 u80 ⊢ memRegion a 80 := by
  unfold v2hs_ekSentWordsAt
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

theorem v2hstop_collapse_2304_from_9228
    (fsp u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
      ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
      v2hs_stack896ScratchRest fsp ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 192 ∗
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      memRegion (fsp + 1344#64) 960 ⊢
      memRegion fsp 2304 := by
  dsimp only [v2hs_stack896ScratchRest]
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h80 := v2hstop_ekSentWordsAt_entails_80 (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80
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
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    (memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 48 ∗
     ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
     ((fsp + 184#64) ↦₆₄ pa2) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
     memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
     ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
     memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1344#64) 960) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h56 (sepConj_mono h40 (sepConj_mono_left h80))) ?_
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

/-! ## Error Branch Helpers (`+9152 -> s0.x30`, `+3348 (bad dk) -> s0.x30`, `+3348 (auth none) -> s0.x30`) -/

/-- Partially collapsed 224-byte `pbA` region keeping `pbA + 96..144` (`w8..w48` of `sendingEk`) exposed for `+9036`. -/
@[expose] def v2hstop_pbEncTailAt (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  memRegion pbA 96 ∗
  ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
  ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
  memRegion (pbA + 144#64) 80

theorem v2hstop_pb128_entails_pbEncTailAt
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000002#64) ∗
      v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (pbA + 184#64) 40 ⊢
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 := by
  rw [← v2hs_words_eq_pb128]
  dsimp only [v1_optProtoPolyEncoderWordsAt, v2hstop_pbEncTailAt]
  have h80 := v2hs_ucWordsAt_entails_80 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h96 : (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 8#64) 80 ∗ ((pbA + 88#64) ↦₆₄ w0) ⊢
      memRegion pbA 96 :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _
  have h80_tail : memRegion (pbA + 144#64) 40 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion (pbA + 144#64) 80 :=
    collapse_step (Entails.refl _) (Entails.refl _)
  simp only [arm64_norm] at h40 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000002#64) ∗
     v2hs_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
     ((pbA + 88#64) ↦₆₄ w0)) ∗
    ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
    ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
    (v2hs_optProtoDecoderWordsAt (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
     memRegion (pbA + 184#64) 40) by ac_rfl)) ?_
  exact sepConj_mono (Entails.trans (sepConj_mono_right (sepConj_mono_left h80)) h96)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (Entails.trans (sepConj_mono_left h40) h80_tail)))))))

theorem v2hstop_pbEncTailAt_entails_full_224 (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ⊢ memRegion pbA optProtoInnerStateSize := by
  unfold v2hstop_pbEncTailAt
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v2hstop_pbEncTailAt_eq_128 (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 =
      memRegion pbA 96 ∗
      ((pbA + 96#64) ↦₁₂₈ (w16 ++ w8)) ∗
      ((pbA + 112#64) ↦₁₂₈ (w32 ++ w24)) ∗
      ((pbA + 128#64) ↦₁₂₈ (w48 ++ w40)) ∗
      memRegion (pbA + 144#64) 80 := by
  unfold v2hstop_pbEncTailAt
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm, sepConj_assoc]

end CryptoVerification.SpqrV1.States.FromPb
