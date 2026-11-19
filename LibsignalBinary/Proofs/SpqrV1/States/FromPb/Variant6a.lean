/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part A

Header unpacking (`pbA + 8..128`), low-stack layout, `+10396` error epilogue, inline
`ProtoPolynomialDecoder` deallocation (`+10316..+10396`), and entry header-load steps (`+1464 -> +1520 | +3760`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Pure Model & Header Unpacking (`pbA + 8..128`) -/

/-- The 15 header words/subwords at `pbA + 8..128` read by `+1464..+1504`. -/
@[expose] def v6hr_headersAt (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
  ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
  ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
  ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
  ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
  ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
  ((pbA + 104#64) ↦₆₄ w104) ∗
  ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
  ((pbA + 120#64) ↦₆₄ w120)

theorem v6hr_headersAt_entails_memRegion_120 (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) :
    v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ⊢
      memRegion (pbA + 8#64) 120 := by
  unfold v6hr_headersAt
  exact collapse_top <|
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
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v6hr_headersAt_entails_dealloc (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000006#64) ∗
    v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
    memRegion (pbA + 128#64) 96 ⊢
      memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (v6hr_headersAt_entails_memRegion_120 pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120))) ?_
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v6hr_optProtoInnerStateAt_headerReceived (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.HeaderReceived) :
    optProtoInnerStateAt A pbA (some (.headerReceived s)) =
      (pbA ↦₆₄ 0x8000000000000006#64) ∗
      optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) s.uc ∗
      optProtoPolynomialDecoderAt A (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (pbA + 128#64) 96 := by
  have h88 : pbA + 8#64 + 80#64 = pbA + 88#64 := by bv_omega
  simp only [optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedHeaderReceivedAt, h88, sepConj_assoc]

theorem v6hr_uc_none_unpack (A : RustAlloc) (pbA : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) none ⊢
      (∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64,
       ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ noneCap) ∗
        ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24) ∗
        ((pbA + 32#64) ↦₆₄ w32) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
        ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
        ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗
        ((pbA + 80#64) ↦₆₄ w80)) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt
  rw [h16]
  have hsplit : memRegion (pbA + 16#64) 72 ⊢
      (∃∗ w16 : BitVec 64, ((pbA + 16#64) ↦₆₄ w16)) ∗
      (∃∗ w24 : BitVec 64, ((pbA + 24#64) ↦₆₄ w24)) ∗
      (∃∗ w32 : BitVec 64, ((pbA + 32#64) ↦₆₄ w32)) ∗
      (∃∗ w40 : BitVec 64, ((pbA + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((pbA + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((pbA + 56#64) ↦₆₄ w56)) ∗
      (∃∗ w64 : BitVec 64, ((pbA + 64#64) ↦₆₄ w64)) ∗
      (∃∗ w72 : BitVec 64, ((pbA + 72#64) ↦₆₄ w72)) ∗
      (∃∗ w80 : BitVec 64, ((pbA + 80#64) ↦₆₄ w80)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_right w16; apply Entails.sepExists_right w24
  apply Entails.sepExists_right w32; apply Entails.sepExists_right w40
  apply Entails.sepExists_right w48; apply Entails.sepExists_right w56
  apply Entails.sepExists_right w64; apply Entails.sepExists_right w72
  apply Entails.sepExists_right w80
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_uc_some_auth_none_unpack (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := none, epoch := epoch }) ⊢
      (∃∗ cap_hdr : BitVec 64, ∃∗ ptr_hdr : BitVec 64,
       ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ cap_hdr) ∗
        ((pbA + 16#64) ↦₆₄ ptr_hdr) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ noneCap) ∗
        ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
        ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ epoch) ∗
        vecU8Payload A cap_hdr ptr_hdr hdr) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  have h24 : pbA + 8#64 + 16#64 = pbA + 24#64 := by bv_omega
  have h32 : pbA + 8#64 + 24#64 = pbA + 32#64 := by bv_omega
  have h40 : pbA + 32#64 + 8#64 = pbA + 40#64 := by bv_omega
  have h80 : pbA + 8#64 + 72#64 = pbA + 80#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt protoUnchunkedHeaderReceivedAt
    optProtoAuthenticatorAt vecU8 vecU8At vecHeader vecU8Payload
  dsimp only
  rw [h16, h24, h32, h40, h80]
  have hsplit : memRegion (pbA + 40#64) 40 ⊢
      (∃∗ w40 : BitVec 64, ((pbA + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((pbA + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((pbA + 56#64) ↦₆₄ w56)) ∗
      (∃∗ w64 : BitVec 64, ((pbA + 64#64) ↦₆₄ w64)) ∗
      (∃∗ w72 : BitVec 64, ((pbA + 72#64) ↦₆₄ w72)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hsplit))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro cap_hdr
  apply Entails.sepExists_elim; intro ptr_hdr
  apply Entails.sepExists_right cap_hdr; apply Entails.sepExists_right ptr_hdr
  apply Entails.sepExists_right w40; apply Entails.sepExists_right w48
  apply Entails.sepExists_right w56; apply Entails.sepExists_right w64
  apply Entails.sepExists_right w72
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_uc_some_auth_some_unpack (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := some authPb, epoch := epoch }) ⊢
      (∃∗ cap_hdr : BitVec 64, ∃∗ ptr_hdr : BitVec 64,
       ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64,
       ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ cap_hdr) ∗
        ((pbA + 16#64) ↦₆₄ ptr_hdr) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ c1) ∗
        ((pbA + 40#64) ↦₆₄ p1) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 authPb.rootKey.length) ∗
        ((pbA + 56#64) ↦₆₄ c2) ∗
        ((pbA + 64#64) ↦₆₄ p2) ∗
        ((pbA + 72#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
        ((pbA + 80#64) ↦₆₄ epoch) ∗
        vecU8Payload A cap_hdr ptr_hdr hdr ∗
        vecU8Payload A c1 p1 authPb.rootKey ∗
        vecU8Payload A c2 p2 authPb.macKey) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  have h24 : pbA + 8#64 + 16#64 = pbA + 24#64 := by bv_omega
  have h32 : pbA + 8#64 + 24#64 = pbA + 32#64 := by bv_omega
  have h40 : pbA + 32#64 + 8#64 = pbA + 40#64 := by bv_omega
  have h48 : pbA + 32#64 + 16#64 = pbA + 48#64 := by bv_omega
  have h56 : pbA + 32#64 + 24#64 = pbA + 56#64 := by bv_omega
  have h64 : pbA + 56#64 + 8#64 = pbA + 64#64 := by bv_omega
  have h72 : pbA + 56#64 + 16#64 = pbA + 72#64 := by bv_omega
  have h80 : pbA + 8#64 + 72#64 = pbA + 80#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt protoUnchunkedHeaderReceivedAt
    optProtoAuthenticatorAt protoAuthenticatorAt vecU8 vecU8At vecHeader vecU8Payload
  dsimp only
  rw [h16, h24, h32, h40, h48, h56, h64, h72, h80]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro cap_hdr
  apply Entails.sepExists_elim; intro ptr_hdr
  apply Entails.sepExists_right cap_hdr; apply Entails.sepExists_right ptr_hdr
  apply Entails.sepExists_right c1; apply Entails.sepExists_right p1
  apply Entails.sepExists_right c2; apply Entails.sepExists_right p2
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_dec_none_unpack (A : RustAlloc) (pbA : BitVec 64) :
    optProtoPolynomialDecoderAt A (pbA + 88#64) none ⊢
      (∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64,
       ∃∗ d112 : BitVec 32, ∃∗ d116 : BitVec 32, ∃∗ w120 : BitVec 64,
        ((pbA + 88#64) ↦₆₄ noneCap) ∗
        ((pbA + 96#64) ↦₆₄ w96) ∗
        ((pbA + 104#64) ↦₆₄ w104) ∗
        ((pbA + 112#64) ↦₃₂ d112) ∗
        ((pbA + 116#64) ↦₃₂ d116) ∗
        ((pbA + 120#64) ↦₆₄ w120)) := by
  have h96 : pbA + 88#64 + 8#64 = pbA + 96#64 := by bv_omega
  unfold optProtoPolynomialDecoderAt
  rw [h96]
  have hsplit : memRegion (pbA + 96#64) 32 ⊢
      (∃∗ w96 : BitVec 64, ((pbA + 96#64) ↦₆₄ w96)) ∗
      (∃∗ w104 : BitVec 64, ((pbA + 104#64) ↦₆₄ w104)) ∗
      (∃∗ d112 : BitVec 32, ((pbA + 112#64) ↦₃₂ d112)) ∗
      (∃∗ d116 : BitVec 32, ((pbA + 116#64) ↦₃₂ d116)) ∗
      (∃∗ w120 : BitVec 64, ((pbA + 120#64) ↦₆₄ w120)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem32_entails _) <|
      split_step (mem32_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w120
  apply Entails.sepExists_elim; intro d116
  apply Entails.sepExists_elim; intro d112
  apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro w96
  apply Entails.sepExists_right w96; apply Entails.sepExists_right w104
  apply Entails.sepExists_right d112; apply Entails.sepExists_right d116
  apply Entails.sepExists_right w120
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v6hr_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗
      (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) := by
    exact split_top <|
      split_step (mem32_entails _) <|
      split_step (mem16_entails _) <|
      mem8_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  have hlo : EncoderFromPb.loByte w = b := hw0
  refine Entails.pure_right hlo ?_
  rw [v6hr_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v6hr_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v6hr_dec_some_unpack (A : RustAlloc) (pbA : BitVec 64)
    (d : ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A (pbA + 88#64) (some d) ⊢
      (∃∗ ptsCap : BitVec 64, ∃∗ ptsPtr : BitVec 64, ∃∗ w120 : BitVec 64,
        ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64 ∧
         EncoderFromPb.loByte w120 = boolByte d.isComplete⌝ ∗
        ((pbA + 88#64) ↦₆₄ ptsCap) ∗
        ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
        ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗
        ((pbA + 116#64) ↦₃₂ d.polys) ∗
        ((pbA + 120#64) ↦₆₄ w120) ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
             ((ptsCap.toNat - d.pts.length) * 24))) := by
  have h96 : pbA + 88#64 + 8#64 = pbA + 96#64 := by bv_omega
  have h104 : pbA + 88#64 + 16#64 = pbA + 104#64 := by bv_omega
  have h112 : pbA + 88#64 + 24#64 = pbA + 112#64 := by bv_omega
  have h116 : pbA + 88#64 + 28#64 = pbA + 116#64 := by bv_omega
  have h120 : pbA + 88#64 + 32#64 = pbA + 120#64 := by bv_omega
  have h121 : pbA + 88#64 + 33#64 = pbA + 120#64 + 1#64 := by bv_omega
  unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf
    Poly.vecHeaderBytes vecAt vecBuf vecHeader protoPolynomialDecoderPtsNeededOff
    protoPolynomialDecoderPolysOff protoPolynomialDecoderIsCompleteOff
    protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
  rw [h96, h104, h112, h116, h120, h121]
  have h8_64 := v6hr_byte_pad7_entails_64 (pbA + 120#64) (boolByte d.isComplete)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro ptsCap; apply Entails.sepExists_right ptsCap
  apply Entails.sepExists_elim; intro ptsPtr; apply Entails.sepExists_right ptsPtr
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((pbA + 120#64) ↦₈ boolByte d.isComplete) ∗ memRegion (pbA + 120#64 + 1#64) 7) ∗
      (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
       ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64⌝ ∗
       (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
            ((ptsCap.toNat - d.pts.length) * 24)) ∗
       ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗
       ((pbA + 116#64) ↦₃₂ d.polys)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left h8_64) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w120; apply Entails.sepExists_right w120
  simp only [sepConj_assoc]
  apply Entails.pure_left; intro hw120
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64⌝ ∗
      (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
       ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗ ((pbA + 116#64) ↦₃₂ d.polys) ∗
       ((pbA + 120#64) ↦₆₄ w120) ∗
       (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
            ((ptsCap.toNat - d.pts.length) * 24))) by ac_rfl)) ?_
  apply Entails.pure_left; intro ⟨h1, h2, h3⟩
  exact Entails.pure_right ⟨h1, h2, h3, hw120⟩ (Entails.of_eq (by ac_rfl))

/-! ## 2. Low-Stack Layout (`sp + 0..240`), Error Epilogue (`+10396`), & Decoder Deallocation (`+10316..+10396`) -/
@[expose] def v6hr_lowStackGaps (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 2400#64) 80 ∗
  memRegion (sp0 - 2312#64) 40 ∗
  memRegion (sp0 - 2248#64) 32 ∗
  memRegion (sp0 - 2212#64) 4 ∗
  memRegion (sp0 - 2196#64) 4

@[expose] def v6hr_lowStackAt (sp0 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) : SepProp :=
  ((sp0 - 2320#64) ↦₆₄ v80) ∗
  ((sp0 - 2272#64) ↦₆₄ v128) ∗
  ((sp0 - 2264#64) ↦₆₄ v136) ∗
  ((sp0 - 2256#64) ↦₆₄ v144) ∗
  ((sp0 - 2216#64) ↦₃₂ d184) ∗
  ((sp0 - 2208#64) ↦₆₄ v192) ∗
  ((sp0 - 2200#64) ↦₃₂ d200) ∗
  ((sp0 - 2192#64) ↦₆₄ v208) ∗
  ((sp0 - 2184#64) ↦₆₄ v216) ∗
  ((sp0 - 2176#64) ↦₆₄ v224) ∗
  ((sp0 - 2168#64) ↦₆₄ v232) ∗
  v6hr_lowStackGaps sp0

theorem v6hr_memRegion_2304_split_fsp (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 80 ∗
      (∃∗ v80 : BitVec 64, ((fsp + 80#64) ↦₆₄ v80)) ∗
      memRegion (fsp + 88#64) 40 ∗
      (∃∗ v128 : BitVec 64, ((fsp + 128#64) ↦₆₄ v128)) ∗
      (∃∗ v136 : BitVec 64, ((fsp + 136#64) ↦₆₄ v136)) ∗
      (∃∗ v144 : BitVec 64, ((fsp + 144#64) ↦₆₄ v144)) ∗
      memRegion (fsp + 152#64) 32 ∗
      (∃∗ d184 : BitVec 32, ((fsp + 184#64) ↦₃₂ d184)) ∗
      memRegion (fsp + 188#64) 4 ∗
      (∃∗ v192 : BitVec 64, ((fsp + 192#64) ↦₆₄ v192)) ∗
      (∃∗ d200 : BitVec 32, ((fsp + 200#64) ↦₃₂ d200)) ∗
      memRegion (fsp + 204#64) 4 ∗
      (∃∗ v208 : BitVec 64, ((fsp + 208#64) ↦₆₄ v208)) ∗
      (∃∗ v216 : BitVec 64, ((fsp + 216#64) ↦₆₄ v216)) ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗
      (∃∗ v232 : BitVec 64, ((fsp + 232#64) ↦₆₄ v232)) ∗
      memRegion (fsp + 240#64) 2064 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v6hr_memRegion_2304_entails_lowStackAt (sp0 : BitVec 64) :
    memRegion (sp0 - 2400#64) 2304 ⊢
      ∃∗ v80 : BitVec 64, ∃∗ v128 : BitVec 64, ∃∗ v136 : BitVec 64, ∃∗ v144 : BitVec 64,
      ∃∗ d184 : BitVec 32, ∃∗ v192 : BitVec 64, ∃∗ d200 : BitVec 32,
      ∃∗ v208 : BitVec 64, ∃∗ v216 : BitVec 64, ∃∗ v224 : BitVec 64, ∃∗ v232 : BitVec 64,
        v6hr_lowStackAt sp0 v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (sp0 - 2160#64) 2064 := by
  have hsplit := v6hr_memRegion_2304_split_fsp (sp0 - 2400#64)
  rw [show (sp0 - 2400#64) + 80#64 = sp0 - 2320#64 by bv_omega,
      show (sp0 - 2400#64) + 88#64 = sp0 - 2312#64 by bv_omega,
      show (sp0 - 2400#64) + 128#64 = sp0 - 2272#64 by bv_omega,
      show (sp0 - 2400#64) + 136#64 = sp0 - 2264#64 by bv_omega,
      show (sp0 - 2400#64) + 144#64 = sp0 - 2256#64 by bv_omega,
      show (sp0 - 2400#64) + 152#64 = sp0 - 2248#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 188#64 = sp0 - 2212#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 204#64 = sp0 - 2196#64 by bv_omega,
      show (sp0 - 2400#64) + 208#64 = sp0 - 2192#64 by bv_omega,
      show (sp0 - 2400#64) + 216#64 = sp0 - 2184#64 by bv_omega,
      show (sp0 - 2400#64) + 224#64 = sp0 - 2176#64 by bv_omega,
      show (sp0 - 2400#64) + 232#64 = sp0 - 2168#64 by bv_omega,
      show (sp0 - 2400#64) + 240#64 = sp0 - 2160#64 by bv_omega] at hsplit
  refine Entails.trans hsplit ?_
  unfold v6hr_lowStackAt v6hr_lowStackGaps
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro v232
  apply Entails.sepExists_elim; intro v224
  apply Entails.sepExists_elim; intro v216
  apply Entails.sepExists_elim; intro v208
  apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro v192
  apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro v144
  apply Entails.sepExists_elim; intro v136
  apply Entails.sepExists_elim; intro v128
  apply Entails.sepExists_elim; intro v80
  apply Entails.sepExists_right v80; apply Entails.sepExists_right v128
  apply Entails.sepExists_right v136; apply Entails.sepExists_right v144
  apply Entails.sepExists_right d184; apply Entails.sepExists_right v192
  apply Entails.sepExists_right d200; apply Entails.sepExists_right v208
  apply Entails.sepExists_right v216; apply Entails.sepExists_right v224
  apply Entails.sepExists_right v232
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_memRegion_2304_collapse_fsp (fsp : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) :
    memRegion fsp 80 ∗
    ((fsp + 80#64) ↦₆₄ v80) ∗
    memRegion (fsp + 88#64) 40 ∗
    ((fsp + 128#64) ↦₆₄ v128) ∗
    ((fsp + 136#64) ↦₆₄ v136) ∗
    ((fsp + 144#64) ↦₆₄ v144) ∗
    memRegion (fsp + 152#64) 32 ∗
    ((fsp + 184#64) ↦₃₂ d184) ∗
    memRegion (fsp + 188#64) 4 ∗
    ((fsp + 192#64) ↦₆₄ v192) ∗
    ((fsp + 200#64) ↦₃₂ d200) ∗
    memRegion (fsp + 204#64) 4 ∗
    ((fsp + 208#64) ↦₆₄ v208) ∗
    ((fsp + 216#64) ↦₆₄ v216) ∗
    ((fsp + 224#64) ↦₆₄ v224) ∗
    ((fsp + 232#64) ↦₆₄ v232) ∗
    memRegion (fsp + 240#64) 2064 ⊢
    memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v6hr_lowStackAt_entails_memRegion_2304 (sp0 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) :
    v6hr_lowStackAt sp0 v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
    memRegion (sp0 - 2160#64) 2064 ⊢
      memRegion (sp0 - 2400#64) 2304 := by
  have hcol := v6hr_memRegion_2304_collapse_fsp (sp0 - 2400#64)
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
  rw [show (sp0 - 2400#64) + 80#64 = sp0 - 2320#64 by bv_omega,
      show (sp0 - 2400#64) + 88#64 = sp0 - 2312#64 by bv_omega,
      show (sp0 - 2400#64) + 128#64 = sp0 - 2272#64 by bv_omega,
      show (sp0 - 2400#64) + 136#64 = sp0 - 2264#64 by bv_omega,
      show (sp0 - 2400#64) + 144#64 = sp0 - 2256#64 by bv_omega,
      show (sp0 - 2400#64) + 152#64 = sp0 - 2248#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 188#64 = sp0 - 2212#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 204#64 = sp0 - 2196#64 by bv_omega,
      show (sp0 - 2400#64) + 208#64 = sp0 - 2192#64 by bv_omega,
      show (sp0 - 2400#64) + 216#64 = sp0 - 2184#64 by bv_omega,
      show (sp0 - 2400#64) + 224#64 = sp0 - 2176#64 by bv_omega,
      show (sp0 - 2400#64) + 232#64 = sp0 - 2168#64 by bv_omega,
      show (sp0 - 2400#64) + 240#64 = sp0 - 2160#64 by bv_omega] at hcol
  unfold v6hr_lowStackAt v6hr_lowStackGaps
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

@[expose, reducible]
def v6hr_Saved10324Preserved (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x21 = ptsPtr ∧
  s.readReg64 .x28 = ptsCap ∧
  s.readReg64 .x25 = x25_val ∧
  TraceCalleeSaved s s0

@[expose, reducible]
def v6hr_Regs1508 (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) : Prop :=
  s.sp = s0.sp - 2400#64 ∧
  s.readReg64 .x8 = w80 ∧
  s.readReg64 .x9 = w16 ∧
  s.readReg64 .x10 = w24 ∧
  s.readReg64 .x11 = d112.zeroExtend 64 ∧
  s.readReg64 .x12 = d116.zeroExtend 64 ∧
  s.readReg64 .x13 = w120 ∧
  s.readReg64 .x14 = w64 ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = w8 ∧
  s.readReg64 .x21 = w56 ∧
  s.readReg64 .x22 = w48 ∧
  s.readReg64 .x23 = w104 ∧
  s.readReg64 .x24 = w32 ∧
  s.readReg64 .x25 = w72 ∧
  s.readReg64 .x26 = w40 ∧
  s.readReg64 .x28 = w88 ∧
  TraceCalleeSaved s s0

end CryptoVerification.SpqrV1.States.FromPb
