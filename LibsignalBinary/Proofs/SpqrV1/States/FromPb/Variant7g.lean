/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part G

Covers the `s.sendingCt1 = none` cleanup path (`+3552 -> +7100 -> +4632`), `<PolyEncoder>::from_pb`
56-byte copy and call (`+3652 -> +3716 -> +32996`), and `<PolyEncoder>::from_pb = Err` cleanup
(`+3720 -> +3732 -> +4632`).
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero


/-! ## 1. `s.sendingCt1 = none` Path (`+3552 -> +7100 -> +4632`) -/

theorem v7_memRegion_1792_split_encCopy (fsp : BitVec 64) :
    memRegion (fsp + 1792#64) 56 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 1792#64) ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 1800#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 1801#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 1809#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1817#64) 7 ∗
      (∃∗ d32 : BitVec 64, (fsp + 1824#64) ↦₆₄ d32) ∗
      (∃∗ d40 : BitVec 64, (fsp + 1832#64) ↦₆₄ d40) ∗
      (∃∗ d48 : BitVec 64, (fsp + 1840#64) ↦₆₄ d48) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v7_encTailWordsAt_to_step3652
    (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v7_encTailWordsAt (pbA + 128#64) w8 w16 w24 w32 w40 w48 ⊢
      ((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 137#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
      ((pbA + 144#64) ↦₆₄ w16) ∗
      ((pbA + 152#64) ↦₆₄ w24) ∗
      ((pbA + 160#64) ↦₆₄ w32) ∗
      ((pbA + 168#64) ↦₆₄ w40) ∗
      ((pbA + 176#64) ↦₆₄ w48) := by
  unfold v7_encTailWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h8 := pointsTo64_split_1_7 (pbA + 136#64) w8
  have ha9 : pbA + 136#64 + 1#64 = pbA + 137#64 := by bv_omega
  rw [ha9] at h8
  rw [h8]
  exact Entails.of_eq (by ac_rfl)

theorem v7_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

theorem v7_1888_tag_392_to_memRegion_400 (fsp tag : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 1896#64) 392 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
        (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

@[expose] def v7_polyEncoderTag (enc : PolyEncoder) : BitVec 64 :=
  match enc.s with
  | .points _ => 0#64
  | .polys _ => 1#64

theorem v7_polyEncoderTag_eq (enc : PolyEncoder) :
    v7_polyEncoderTag enc = 0#64 ∨ v7_polyEncoderTag enc = 1#64 := by
  unfold v7_polyEncoderTag
  cases enc.s <;> simp

theorem v7_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v7_polyEncoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜((a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize v7_polyEncoderTag
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hpts_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len.1]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v7_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_))
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v7_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hpts_len (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v7_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_))
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v7_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

theorem v7_bs384_w392_split_368 (bs : List (BitVec 8)) (hbs : bs.length = 384) (w392 : BitVec 64) :
    ∃ (w8 w16 w24 : BitVec 64) (tail368 : { l : List (BitVec 8) // l.length = 368 }),
      ∀ a : BitVec 64,
        ((a + 8#64) ↦ₛ bs) ∗ ((a + 392#64) ↦₆₄ w392) =
          ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
          ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ tail368.val) := by
  have ht0 : (bs.take 8).length = 8 := by rw [List.length_take, hbs]; decide
  have ht1 : ((bs.drop 8).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  have ht2 : ((bs.drop 16).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  obtain ⟨w8, hw8⟩ := ProofLib.exists_unpack64_of_length_8 ht0
  obtain ⟨w16, hw16⟩ := ProofLib.exists_unpack64_of_length_8 ht1
  obtain ⟨w24, hw24⟩ := ProofLib.exists_unpack64_of_length_8 ht2
  have htail_len : (bs.drop 24 ++ unpack64 w392).length = 368 := by
    rw [List.length_append, List.length_drop, hbs, unpack64_length]
  refine ⟨w8, w16, w24, ⟨bs.drop 24 ++ unpack64 w392, htail_len⟩, fun a => ?_⟩
  have hbs0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have hbs1 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    change bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop (8 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hbs2 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    change bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop (16 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hp0 : ((a + 8#64) ↦ₛ bs) =
      ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦ₛ bs.drop 8) := by
    conv_lhs => rw [hbs0]
    rw [ProofLib.pointsToBytes_append (a + 8#64) (bs.take 8) (bs.drop 8), ht0,
        hw8, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha16 : (a + 8#64) + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
    rw [ha16]
  have hp1 : ((a + 16#64) ↦ₛ bs.drop 8) =
      ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦ₛ bs.drop 16) := by
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append (a + 16#64) ((bs.drop 8).take 8) (bs.drop 16), ht1,
        hw16, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha24 : (a + 16#64) + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
    rw [ha24]
  have hp2 : ((a + 24#64) ↦ₛ bs.drop 16) =
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ bs.drop 24) := by
    conv_lhs => rw [hbs2]
    rw [ProofLib.pointsToBytes_append (a + 24#64) ((bs.drop 16).take 8) (bs.drop 24), ht2,
        hw24, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha32 : (a + 24#64) + BitVec.ofNat 64 8 = a + 32#64 := by bv_omega
    rw [ha32]
  have hp3 : ((a + 32#64) ↦ₛ bs.drop 24) ∗ ((a + 392#64) ↦₆₄ w392) =
      ((a + 32#64) ↦ₛ (bs.drop 24 ++ unpack64 w392)) := by
    rw [ProofLib.pointsToBytes_append (a + 32#64) (bs.drop 24) (unpack64 w392),
        List.length_drop, hbs, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha392 : (a + 32#64) + BitVec.ofNat 64 (384 - 24) = a + 392#64 := by bv_omega
    rw [ha392]
  rw [hp0, hp1, hp2]
  simp only [sepConj_assoc, hp3]

theorem v7_polyEncoderAt_relocate_368 (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ tail368 : { l : List (BitVec 8) // l.length = 368 },
      ∃∗ P_heap : SepProp,
        ⌜((a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗ ((a2 + 24#64) ↦₆₄ w24) ∗
          ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
        ((a1 + 8#64) ↦₆₄ w8) ∗
        ((a1 + 16#64) ↦₆₄ w16) ∗
        ((a1 + 24#64) ↦₆₄ w24) ∗
        ((a1 + 32#64) ↦ₛ tail368.val) ∗
        P_heap := by
  refine Entails.trans (v7_polyEncoderAt_relocate A a1 a2 enc) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro hi32
  apply Entails.sepExists_elim; intro P_heap
  apply Entails.pure_left; intro hreloc
  obtain ⟨w8, w16, w24, tail368, hsplit⟩ := v7_bs384_w392_split_368 bs.val bs.property (hi32 ++ enc.idx)
  have h1 := hsplit a1
  have h2 := hsplit a2
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right tail368
      (Entails.sepExists_right P_heap ?_))))
  refine Entails.pure_right ?_ ?_
  · refine Entails.trans ?_ hreloc
    refine Entails.of_eq ?_
    calc
      (a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
        ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap
        = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
           ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val)) ∗ P_heap := by ac_rfl
      _ = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a2 + 8#64) ↦ₛ bs.val) ∗ ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx))) ∗ P_heap := by rw [← h2]
      _ = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
          ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap := by ac_rfl
  · refine Entails.of_eq ?_
    calc
      (a1 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap
        = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a1 + 8#64) ↦ₛ bs.val) ∗ ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx))) ∗ P_heap := by ac_rfl
      _ = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a1 + 8#64) ↦₆₄ w8) ∗ ((a1 + 16#64) ↦₆₄ w16) ∗
           ((a1 + 24#64) ↦₆₄ w24) ∗ ((a1 + 32#64) ↦ₛ tail368.val)) ∗ P_heap := by rw [h1]
      _ = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a1 + 8#64) ↦₆₄ w8) ∗
          ((a1 + 16#64) ↦₆₄ w16) ∗ ((a1 + 24#64) ↦₆₄ w24) ∗
          ((a1 + 32#64) ↦ₛ tail368.val) ∗ P_heap := by ac_rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v7_polyEncoderTag_sub_two_beq_zero (enc : PolyEncoder) :
    (v7_polyEncoderTag enc - 2#64 == 0#64) = false := by
  rcases v7_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x20_add_105_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (105#64).signExtend 64 = fsp + 1897#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x20_add_105 (fsp : BitVec 64) :
    fsp + 1792#64 + 105#64 = fsp + 1897#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1897_add_8 (fsp : BitVec 64) :
    fsp + 1897#64 + 8#64 = fsp + 1905#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x25_add_32 (fsp : BitVec 64) :
    fsp + 1888#64 + 32#64 = fsp + 1920#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_896_add_8 (fsp : BitVec 64) :
    fsp + 896#64 + 8#64 = fsp + 904#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x23_add_63_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (63#64).signExtend 64 = fsp + 911#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x23_add_63 (fsp : BitVec 64) :
    fsp + 848#64 + 63#64 = fsp + 911#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_32 (fsp : BitVec 64) :
    fsp + 1392#64 + 32#64 = fsp + 1424#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1264_add_137_sext (fsp : BitVec 64) :
    (fsp + 1264#64) + (137#64).signExtend 64 = fsp + 1401#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1264_add_137 (fsp : BitVec 64) :
    fsp + 1264#64 + 137#64 = fsp + 1401#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1401_add_8 (fsp : BitVec 64) :
    fsp + 1401#64 + 8#64 = fsp + 1409#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by bv_kernel

theorem v7_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

theorem v7_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by
  bv_kernel

theorem v7_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte
  bv_kernel

theorem v7_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v7_unshift_lsr56 w0 w8, v7_lsr8_lsl8 w8]
  bv_kernel

theorem v7_pointsTo64_split_7_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [(w >>> 56).setWidth 8]) := by
  rw [pointsTo64_eq_pointsToBytes]
  change (a ↦ₛ unpack64 w) =
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗
    ((a + BitVec.ofNat 64 (EncoderFromPb.loBytes7 w).length) ↦ₛ [(w >>> 56).setWidth 8])
  rw [← ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [(w >>> 56).setWidth 8]]
  rfl

theorem v7_pointsTo64_split_7_1_entails_8 (a w : BitVec 64) (b7 : BitVec 8) :
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [b7]) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_split a 7 1 (by decide)]
  refine sepConj_mono ?_ ?_
  · have hlen : (EncoderFromPb.loBytes7 w).length = 7 := rfl
    exact hlen ▸ ProofLib.pointsToBytes_entails_memRegion a (EncoderFromPb.loBytes7 w)
  · have hlen1 : ([b7] : List (BitVec 8)).length = 1 := rfl
    exact hlen1 ▸ ProofLib.pointsToBytes_entails_memRegion (a + 7#64) [b7]

theorem v7_fsp_1896_triple_rest (fsp w8 w16 w24 : BitVec 64) (R : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ R =
      ((fsp + 1896#64) ↦₈ loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ R := by
  have h := v7_triple64_to_byte_qword_tail7 (fsp + 1896#64) w8 w16 w24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 1896#64) + 1#64)
        (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ R =
        (((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v7_fsp_1905_realign_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
      ((fsp + 1905#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest := by
  have ha1912 : (fsp + 1905#64) + 7#64 = fsp + 1912#64 := by bv_omega
  have ha1913 : (fsp + 1905#64) + 8#64 = fsp + 1913#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1905#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)
  rw [ha1913, ha1912, ← v7_hiBytes7_eq_loBytes7_lsr8 w24,
      v7_overlapWord7_unshift_lsr8 w16 w24] at h
  rw [← sepConj_assoc ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)), h]
  simp only [sepConj_assoc]

theorem v7_fsp_904_realign_rest (fsp u1 d16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ u1) ∗ ((fsp + 912#64) ↦₆₄ d16) ∗ Rest =
      ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 911#64) ↦₆₄ overlapWord7 u1 d16) ∗
      ((fsp + 919#64) ↦ₛ [(d16 >>> 56).setWidth 8]) ∗ Rest := by
  have hsplit := v7_pointsTo64_split_7_1 (fsp + 912#64) d16
  have ha919 : (fsp + 912#64) + 7#64 = fsp + 919#64 := by bv_omega
  rw [ha919] at hsplit
  have hover := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 904#64) u1 d16
  have ha912 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have ha911 : (fsp + 904#64) + 7#64 = fsp + 911#64 := by bv_omega
  rw [ha912, ha911] at hover
  rw [hsplit]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc ((fsp + 904#64) ↦₆₄ u1), hover]
  simp only [sepConj_assoc]

theorem v7_fsp_904_unrealign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 911#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 912#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest := by
  have hover := (pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 904#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)).symm
  have ha912 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have ha911 : (fsp + 904#64) + 7#64 = fsp + 911#64 := by bv_omega
  rw [ha912, ha911, v7_overlapWord7_unshift_lsr8 w16 w24] at hover
  rw [← sepConj_assoc ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))), hover]
  simp only [sepConj_assoc]

theorem v7_fsp_904_realign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 912#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest =
      ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 911#64) ↦₆₄ w24) ∗ Rest :=
  (v7_fsp_904_unrealign_w24_rest fsp w16 w24 Rest).symm

theorem v7_fsp_1400_triple_rest (fsp e8 e16 e24 : BitVec 64) (R : SepProp) :
    ((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24) ∗ R =
      ((fsp + 1400#64) ↦₈ loByte e8) ∗
      ((fsp + 1401#64) ↦₆₄ unshiftWord e8 (loByte e16)) ∗
      ((fsp + 1409#64) ↦₆₄ unshiftWord e16 (loByte e24)) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ R := by
  have h := v7_triple64_to_byte_qword_tail7 (fsp + 1400#64) e8 e16 e24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 1400#64) + 1#64)
        (unshiftWord e8 (loByte e16)) (unshiftWord e16 (loByte e24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24) ∗ R =
        (((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v7_fsp_1409_realign_rest (fsp u1 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1409#64) ↦₆₄ u1) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest =
      ((fsp + 1409#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 1416#64) ↦₆₄ overlapWord7 u1 (e24 >>> 8)) ∗ Rest := by
  have ha1416 : (fsp + 1409#64) + 7#64 = fsp + 1416#64 := by bv_omega
  have ha1417 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1409#64) u1 (e24 >>> 8)
  rw [ha1417, ha1416, ← v7_hiBytes7_eq_loBytes7_lsr8 e24] at h
  rw [← sepConj_assoc ((fsp + 1409#64) ↦₆₄ u1), h]
  simp only [sepConj_assoc]

end CryptoVerification.SpqrV1.States.FromPb

