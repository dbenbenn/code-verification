/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 1: Heap Exposure, Arm 0 (`keysUnsampled`), and Call Helpers

**Checked by Lean.**

Address-independent heap exposure predicates for `Authenticator`, `Vec<u8>`, `ProtoPolynomialEncoder`,
and `ProtoPolynomialDecoder`, the Arm 0 (`States.keysUnsampled`, tag `2`) proof, and shared `SepWPp`
call helpers for `<PolyEncoder>::into_pb` and `<PolyDecoder>::into_pb`.
-/

public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Address Normalization and `Authenticator` / `outWords28` Helpers -/

@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_208 (sp : BitVec 64) : (sp - 96#64) - 208#64 = sp - 304#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_192 (sp : BitVec 64) : (sp - 96#64) - 192#64 = sp - 288#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_176 (sp : BitVec 64) : (sp - 96#64) - 176#64 = sp - 272#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_168 (sp : BitVec 64) : (sp - 96#64) - 168#64 = sp - 264#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_480_add_200 (sp : BitVec 64) : (sp - 480#64) + 200#64 = sp - 280#64 := by bv_omega

/-- Heap payload + bounds of a `Vec<u8>` separated from its 3 header words. -/
@[expose] def vecU8Payload (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Payload
  ac_rfl

theorem vecU8_of_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_payload]
  exact Entails.refl _

/-- Address-independent heap predicate for an `Authenticator` separated from its 6 header words. -/
@[expose] def authenticatorHeap (A : RustAlloc) (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (auth : Authenticator) : SepProp :=
  ⌜a2 = BitVec.ofNat 64 auth.rootKey.length ∧
    a5 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
  vecU8Payload A a0 a1 auth.rootKey ∗
  vecU8Payload A a3 a4 auth.macKey

theorem authenticatorAt_expose (A : RustAlloc) (a : BitVec 64) (auth : Authenticator) :
    authenticatorAt A a auth ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
        ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 auth := by
  unfold authenticatorAt
  nth_rw 1 [vecU8]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  nth_rw 1 [vecU8]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 auth.rootKey.length)
      (Entails.sepExists_right c2 (Entails.sepExists_right p2
        (Entails.sepExists_right (BitVec.ofNat 64 auth.macKey.length) ?_)))))
  rw [vecU8At_eq_header_payload A a c1 p1 auth.rootKey,
      vecU8At_eq_header_payload A (a + 24#64) c2 p2 auth.macKey]
  unfold authenticatorHeap
  simp only [BitVec.add_assoc, eq_self, and_self, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem authenticatorAt_of_words_heap (A : RustAlloc) (a : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (auth : Authenticator) :
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 auth ⊢
    authenticatorAt A a auth := by
  unfold authenticatorHeap authenticatorAt
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜a2 = BitVec.ofNat 64 auth.rootKey.length ∧
      a5 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
    ((a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
     ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
     vecU8Payload A a0 a1 auth.rootKey ∗
     vecU8Payload A a3 a4 auth.macKey) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl⟩
  have hv1 := vecU8_of_header_payload A a a0 a1 auth.rootKey
  have hv2 := vecU8_of_header_payload A (a + 24#64) a3 a4 auth.macKey
  simp only [BitVec.add_assoc] at hv1 hv2 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗
     ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     vecU8Payload A a0 a1 auth.rootKey) ∗
    (((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗
     ((a + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A a3 a4 auth.macKey) by ac_rfl)) ?_
  exact sepConj_mono hv1 hv2

/-- Address-independent heap predicate for a `Vec<u8>` separated from its 3 header words. -/
@[expose] def vecU8Heap (A : RustAlloc) (v0 v1 v2 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜v2 = BitVec.ofNat 64 bs.length⌝ ∗
  vecU8Payload A v0 v1 bs

theorem vecU8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        vecU8Heap A v0 v1 v2 bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  rw [vecU8At_eq_header_payload A a cap ptr bs]
  unfold vecU8Heap
  simp only [eq_self, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_of_words_heap (A : RustAlloc) (a v0 v1 v2 : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
    vecU8Heap A v0 v1 v2 bs ⊢
    vecU8 A a bs := by
  unfold vecU8Heap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v2 = BitVec.ofNat 64 bs.length⌝ ∗
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
     vecU8Payload A v0 v1 bs) by ac_rfl)) ?_
  apply Entails.pure_left; rintro rfl
  exact vecU8_of_header_payload A a v0 v1 bs

/-- Address-independent heap predicate for a 56-byte `ProtoPolynomialEncoder` separated from its
    7 header words `e0..e6`. -/
@[expose] def protoPolynomialEncoderHeap (A : RustAlloc)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64) (pb : ProtoPolynomialEncoder) : SepProp :=
  ⌜e2 = BitVec.ofNat 64 pb.pts.length ∧
    e5 = BitVec.ofNat 64 pb.polys.length ∧
    (∃ hi : BitVec 32, e6 = hi ++ pb.idx)⌝ ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e0 e1 pb.pts ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e3 e4 pb.polys

theorem protoPolynomialEncoder_expose (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A a pb ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
      ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
        (a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
        ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
        ((a + 48#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  rw [ProofLib.memRegion_four (a + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro hi
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
      (Entails.sepExists_right c2 (Entails.sepExists_right p2
        (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
          (Entails.sepExists_right (hi ++ pb.idx) ?_))))))
  have hpair : ((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi) =
      ((a + 0x30#64) ↦₆₄ (hi ++ pb.idx)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x30#64) pb.idx hi
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  unfold protoPolynomialEncoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    (((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi)) ∗
    ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c2 p2 pb.polys) by ac_rfl)) ?_
  rw [hpair]
  refine Entails.trans (Entails.of_eq (show _ =
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((a + 48#64) ↦₆₄ (hi ++ pb.idx)) ∗
    (vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c2 p2 pb.polys) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨rfl, rfl, ⟨hi, rfl⟩⟩ (Entails.refl _))))))))

theorem protoPolynomialEncoder_of_words_heap (A : RustAlloc)
    (a e0 e1 e2 e3 e4 e5 e6 : BitVec 64) (pb : ProtoPolynomialEncoder) :
    (a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
    ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
    ((a + 48#64) ↦₆₄ e6) ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 pb ⊢
    protoPolynomialEncoderAt A a pb := by
  unfold protoPolynomialEncoderHeap protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜e2 = BitVec.ofNat 64 pb.pts.length ∧
      e5 = BitVec.ofNat 64 pb.polys.length ∧
      (∃ hi : BitVec 32, e6 = hi ++ pb.idx)⌝ ∗
    ((a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
     ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
     ((a + 48#64) ↦₆₄ e6) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e0 e1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e3 e4 pb.polys) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, ⟨hi, rfl⟩⟩
  rw [ProofLib.memRegion_four (a + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right hi (Entails.sepExists_right e3
    (Entails.sepExists_right e4 (Entails.sepExists_right e0
      (Entails.sepExists_right e1 ?_))))
  have hpair : ((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi) =
      ((a + 0x30#64) ↦₆₄ (hi ++ pb.idx)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x30#64) pb.idx hi
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  rw [← hpair]
  exact Entails.of_eq (by ac_rfl)

/-- Address-independent heap predicate for a 40-byte `ProtoPolynomialDecoder` separated from its
    5 header words `d0..d4`. -/
@[expose] def protoPolynomialDecoderHeap (A : RustAlloc)
    (d0 d1 d2 d3 d4 : BitVec 64) (pb : ProtoPolynomialDecoder) : SepProp :=
  ⌜d2 = BitVec.ofNat 64 pb.pts.length ∧
    d3 = pb.polys ++ pb.ptsNeeded ∧
    (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d4)⌝ ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) d0 d1 pb.pts

theorem protoPolynomialDecoder_expose (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    protoPolynomialDecoderAt A a pb ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
      ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
        ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 pb := by
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  rw [ProofLib.memRegion_eq_exists_bytes (a + 0x21#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length = 7⌝ ∗
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     (((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys)) ∗
     (((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs))) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlen
  have h8 : (boolByte pb.isComplete :: bs).length = 8 := by simp [hlen]
  obtain ⟨d4, hd4⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hw3 : ((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys) =
      ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x18#64) pb.ptsNeeded pb.polys
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw4 : ((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs) =
      ((a + 32#64) ↦₆₄ d4) := by
    have h := ProofLib.pointsToBytes_cons (a + 0x20#64) (boolByte pb.isComplete) bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    rw [← h, hd4, ← ProofLib.pointsTo64_eq_pointsToBytes]
  rw [hw3, hw4]
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
      (Entails.sepExists_right (pb.polys ++ pb.ptsNeeded)
        (Entails.sepExists_right d4 ?_))))
  unfold protoPolynomialDecoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) ∗ ((a + 32#64) ↦₆₄ d4) ∗
    vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.pure_right ⟨rfl, rfl, ⟨bs, hlen, hd4⟩⟩ (Entails.refl _))))))

theorem protoPolynomialDecoder_of_words_heap (A : RustAlloc)
    (a d0 d1 d2 d3 d4 : BitVec 64) (pb : ProtoPolynomialDecoder) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
    ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 pb ⊢
    protoPolynomialDecoderAt A a pb := by
  unfold protoPolynomialDecoderHeap protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜d2 = BitVec.ofNat 64 pb.pts.length ∧
      d3 = pb.polys ++ pb.ptsNeeded ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d4)⌝ ∗
    ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
     ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) d0 d1 pb.pts) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, ⟨bs, hlen, hd4⟩⟩
  rw [ProofLib.memRegion_eq_exists_bytes (a + 0x21#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right bs (Entails.sepExists_right d0
    (Entails.sepExists_right d1 ?_))
  have hw3 : ((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys) =
      ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x18#64) pb.ptsNeeded pb.polys
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw4 : ((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs) =
      ((a + 32#64) ↦₆₄ d4) := by
    have h := ProofLib.pointsToBytes_cons (a + 0x20#64) (boolByte pb.isComplete) bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    rw [← h, hd4, ← ProofLib.pointsTo64_eq_pointsToBytes]
  rw [← hw3, ← hw4]
  refine Entails.trans (Entails.pure_right hlen (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem chunkedKeysUnsampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A stA (.keysUnsampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (stA ↦₆₄ 2#64) ∗
        ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        memRegion (stA + 64#64) 864 := by
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (authenticatorAt_expose A (stA + 8#64) s.uc.auth)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_words8_and_864_entails_928 (stA w0 w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (stA ↦₆₄ w0) ∗
    ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
    ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
    ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
    ((stA + 56#64) ↦₆₄ w56) ∗
    memRegion (stA + 64#64) 864 ⊢
    memRegion stA chunkedStatesSize := by
  have hc8 :
      (stA ↦₆₄ w0) ∗
      ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
      ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
      ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
      ((stA + 56#64) ↦₆₄ w56) ⊢
      memRegion stA 64 := by
    rw [ProofLib.memRegion_cells stA 8 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56 (Entails.refl _))))))))
  rw [ProofLib.memRegion_split' (b := stA) (n := 64) (k := 864)
        (b' := stA + 64#64) rfl rfl (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    ((stA ↦₆₄ w0) ∗
     ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
     ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
     ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
     ((stA + 56#64) ↦₆₄ w56)) ∗
    memRegion (stA + 64#64) 864 by ac_rfl)) ?_
  exact sepConj_mono_left hc8

theorem outWords28_entails_keysUnsampled (A : RustAlloc) {F : ShaCompress}
    (out a0 a1 a2 a3 a4 a5 : BitVec 64)
    (w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000000#64
      a0 a1 a2 a3 a4 a5
      s.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ⊢
    optProtoInnerStateAt A out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
    Unchunked.SendEk.KeysUnsampled.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedKeysUnsampledAt, optProtoUnchunkedKeysUnsampledAt,
    protoUnchunkedKeysUnsampledAt, optProtoAuthenticatorAt_some_into_pb]
  have hauth := authenticatorAt_of_words_heap A (out + 8#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc] at hauth ⊢
  have hc20 :
      ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗
      ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
      ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗
      ((out + 112#64) ↦₆₄ w112) ∗ ((out + 120#64) ↦₆₄ w120) ∗
      ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
      ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
      ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 64#64) 160 := by
    rw [ProofLib.memRegion_cells (out + 64#64) 20 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc]
    exact Entails.sepExists_right w64 (Entails.sepExists_right w72
      (Entails.sepExists_right w80 (Entails.sepExists_right w88
        (Entails.sepExists_right w96 (Entails.sepExists_right w104
          (Entails.sepExists_right w112 (Entails.sepExists_right w120
            (Entails.sepExists_right w128 (Entails.sepExists_right w136
              (Entails.sepExists_right w144 (Entails.sepExists_right w152
                (Entails.sepExists_right w160 (Entails.sepExists_right w168
                  (Entails.sepExists_right w176 (Entails.sepExists_right w184
                    (Entails.sepExists_right w192 (Entails.sepExists_right w200
                      (Entails.sepExists_right w208 (Entails.sepExists_right w216
                        (Entails.refl _))))))))))))))))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000000#64) ∗
    (((out + 8#64) ↦₆₄ a0) ∗ ((out + 16#64) ↦₆₄ a1) ∗
     ((out + 24#64) ↦₆₄ a2) ∗ ((out + 32#64) ↦₆₄ a3) ∗
     ((out + 40#64) ↦₆₄ a4) ∗ ((out + 48#64) ↦₆₄ a5) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((out + 56#64) ↦₆₄ s.uc.epoch) ∗
    (((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗
     ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
     ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗
     ((out + 112#64) ↦₆₄ w112) ∗ ((out + 120#64) ↦₆₄ w120) ∗
     ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
     ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
     ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
     ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
     ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
     ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hauth (sepConj_mono_right hc20))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Arm 0: `States.keysUnsampled` (`+0 -> +60 -> +100 -> +1544 -> ret`) -/

theorem fnAddr_fwd_eq {c : Program} {f1 f2 : String} {o1 o2 d : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o1 + d = o2) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 d = (c.rebase b X).fnAddr f2 := by
  have hback : (c.rebase b X).fnAddr f1 = (c.rebase b X).fnAddr f2 - BitVec.ofNat 64 d :=
    Program.fnAddr_back (d := d) (b := b) (X := X) ho2 ho1 hd
  rw [hback]
  bv_omega

abbrev offStatesIntoPbJumpTable : Nat := 660548

/-- Read-only separation-logic assertion for the 22-byte jump table of `<States>::into_pb`. -/
@[expose] def statesIntoPbJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% offStatesIntoPbJumpTable) ↦ᵣ statesIntoPbJumpTableBytes

/-- Return postcondition of `<States>::into_pb` for `SepWPp`. -/
@[expose] def StatesIntoPbPost (A : RustAlloc) {F : ShaCompress} (b : BitVec 64)
    (s0 : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

/-- Panic postcondition of `<States>::into_pb` for `SepWPp`. -/
@[expose] def StatesIntoPbPanic (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)

/-- Sequence a non-panicking `SepWP` segment before a `SepWPp` continuation. -/
theorem statesIntoPb_seq_sepWP {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP (mid := mid) ?_
  refine SepWP.mono hstep ?_
  intro s' P1 hpc' hrun' ⟨hent, hpost⟩
  exact SepWPp.weaken_pre hent (hnext s' hpc' hrun' hpost)

end CryptoVerification.SpqrV1.States.IntoPb

