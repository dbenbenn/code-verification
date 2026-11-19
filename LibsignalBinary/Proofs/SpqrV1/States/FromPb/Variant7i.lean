/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) Part I

Proves the `<PolyDecoder>::from_pb = Ok(dec)` success tail (`+7404 -> +8180 -> s0.x30`)
for Variant 7 (`Ct1Sampled`, `+1056`).
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



theorem v7_resultPolyDecoder_ok_eq (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    resultPolyDecoderFromPbAt A a (.ok dec) = polyDecoderAt A a dec := rfl

/-! ## 1. `PolyDecoder` & `PolyEncoder` Cell Unpacking and Relocation -/

/-- Concatenated 24-byte `Vec` headers for `pins` and `SortedSetPt` slices. -/
@[expose] def v7_ptHeadersBytesOf : List VecPin → List SortedSetPt → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, s :: ss => vecHeaderBytesOf pin s.vec.length ++ v7_ptHeadersBytesOf pins ss

theorem v7_length_ptHeadersBytesOf :
    ∀ (pins : List VecPin) (ss : List SortedSetPt),
      pins.length = ss.length →
      (v7_ptHeadersBytesOf pins ss).length = ss.length * 24
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | pin :: pins, s :: ss, h => by
    simp only [List.length_cons] at h
    have ih := v7_length_ptHeadersBytesOf pins ss (Nat.succ.inj h)
    simp only [v7_ptHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, ih, List.length_cons]
    omega

/-- Separating conjunction of `vecBuf A ptStride ptAlign ptAt` across `pins` and `ss`. -/
def v7_ptHeapList (A : RustAlloc) : List VecPin → List SortedSetPt → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, s :: ss =>
    vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v7_ptHeapList A pins ss

theorem v7_sortedSetPtOf_entails_pin (A : RustAlloc) (a : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A a s ⊢
      ∃∗ pin : VecPin,
        ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
        (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
        vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec := by
  unfold sortedSetPtOf vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ s.vec.length]
  have hcap : vecBuf A ptStride ptAlign ptAt cap ptr s.vec ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecBuf A ptStride ptAlign ptAt cap ptr s.vec := by
    unfold vecBuf ptStride
    apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    have hlt' : cap.toNat < 2 ^ 63 := by omega
    exact Entails.pure_right hlt' (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  exact Entails.trans (sepConj_mono_right hcap) (Entails.of_eq (by ac_rfl))

theorem v7_pin_entails_sortedSetPtOf (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (s : SortedSetPt) :
    (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
      vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ⊢
      sortedSetPtOf A a s := by
  rw [← vecHeader_eq_pointsToBytes a pin s.vec.length]
  unfold sortedSetPtOf vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem v7_sortedSetPtListOf_entails_headers_heaps (A : RustAlloc) :
    ∀ (ss : List SortedSetPt) (a : BitVec 64),
      sortedSetPtListOf A a ss ⊢
        ∃∗ pins : List VecPin,
          ⌜pins.length = ss.length ∧ (∀ pin ∈ pins.head?, pin.cap.toNat < 2 ^ 63)⌝ ∗
          (a ↦ₛ v7_ptHeadersBytesOf pins ss) ∗
          v7_ptHeapList A pins ss
  | [], a => by
    simp only [sortedSetPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [v7_ptHeadersBytesOf, v7_ptHeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | s :: ss, a => by
    simp only [sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (sepConj_mono (v7_sortedSetPtOf_entails_pin A a s)
      (v7_sortedSetPtListOf_entails_headers_heaps A ss (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    apply Entails.pure_left; intro hcap0
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, _⟩
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (s :: ss).length := by simp [hlen]
    have hhead : ∀ p ∈ (pin :: pins).head?, p.cap.toNat < 2 ^ 63 := by
      intro p hp; simp at hp; subst hp; exact hcap0
    refine Entails.pure_right ⟨hlen', hhead⟩ ?_
    simp only [v7_ptHeadersBytesOf, v7_ptHeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v7_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    exact Entails.of_eq (by ac_rfl)

theorem v7_headers_heaps_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (ss : List SortedSetPt) (a : BitVec 64),
      pins.length = ss.length →
      (a ↦ₛ v7_ptHeadersBytesOf pins ss) ∗ v7_ptHeapList A pins ss ⊢
        sortedSetPtListOf A a ss
  | [], [], a, _ => by
    simp [v7_ptHeadersBytesOf, v7_ptHeapList, sortedSetPtListOf, arrayAt, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | pin :: pins, s :: ss, a, h => by
    simp only [List.length_cons] at h
    simp only [v7_ptHeadersBytesOf, v7_ptHeapList, sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v7_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ ((a + 24#64) ↦ₛ v7_ptHeadersBytesOf pins ss)) ∗
        (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v7_ptHeapList A pins ss) =
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec) ∗
        (((a + 24#64) ↦ₛ v7_ptHeadersBytesOf pins ss) ∗ v7_ptHeapList A pins ss) by ac_rfl)) ?_
    exact sepConj_mono (v7_pin_entails_sortedSetPtOf A a pin s)
      (v7_headers_heaps_entails_sortedSetPtListOf A pins ss (a + 24#64) (Nat.succ.inj h))

/-- Pack 8 bytes (little-endian) from `bs` into a `BitVec 64`. -/
@[expose] def v7_pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 7 0#8) ++ (bs.getD 6 0#8) ++ (bs.getD 5 0#8) ++ (bs.getD 4 0#8) ++
  (bs.getD 3 0#8) ++ (bs.getD 2 0#8) ++ (bs.getD 1 0#8) ++ (bs.getD 0 0#8)

theorem v7_unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (v7_pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  change [_, _, _, _, _, _, _, _] = [b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp only [v7_pack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v7_pack64_unpack64 (w : BitVec 64) :
    v7_pack64 (unpack64 w) = w := by
  dsimp only [v7_pack64, unpack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  bv_kernel

theorem v7_pointsToBytes_eq_pack64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ v7_pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, v7_unpack64_pack64 bs h]

/-- Pack 16 bytes (little-endian) from `bs` into a `BitVec 128`. -/
@[expose] def v7_pack128 (bs : List (BitVec 8)) : BitVec 128 :=
  v7_pack64 (bs.drop 8) ++ v7_pack64 (bs.take 8)

theorem v7_pointsToBytes_eq_pack128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₁₂₈ v7_pack128 bs) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  nth_rw 1 [← List.take_append_drop 8 bs]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1]
  change (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) = (a ↦₁₂₈ v7_pack128 bs)
  rw [v7_pointsToBytes_eq_pack64 a (bs.take 8) h1,
      v7_pointsToBytes_eq_pack64 (a + 8#64) (bs.drop 8) h2,
      pointsTo64_pair_eq_pointsTo128]
  rfl

/-- 8-byte word at byte offset `i` within `bs`. -/
@[expose] def v7_wordAt (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  v7_pack64 ((bs.drop i).take 8)

/-- 16-byte quadword at byte offset `i` within `bs`. -/
@[expose] def v7_quadAt (bs : List (BitVec 8)) (i : Nat) : BitVec 128 :=
  v7_pack128 ((bs.drop i).take 16)

theorem v7_wordAt_0_ptHeadersBytesOf (pin : VecPin) (pins : List VecPin)
    (s : SortedSetPt) (ss : List SortedSetPt) :
    v7_wordAt (v7_ptHeadersBytesOf (pin :: pins) (s :: ss)) 0 = pin.cap := by
  unfold v7_wordAt v7_ptHeadersBytesOf vecHeaderBytesOf
  rw [List.drop_zero, List.append_assoc, List.append_assoc,
      List.take_append_of_le_length (by rw [unpack64_length]),
      List.take_of_length_le (by rw [unpack64_length]),
      v7_pack64_unpack64]

theorem v7_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
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

theorem v7_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
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
  rw [v7_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v7_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v7_polyDecoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a1 dec ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
        ⌜(v7_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
          ((a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A a2 dec)⌝ ∗
        (a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  have ha1_393 : a1 + 0x189#64 = (a1 + 0x188#64) + 1#64 := by bv_omega
  rw [ha1_393]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (v7_sortedSetPtListOf_entails_headers_heaps A dec.pts a1)
      (sepConj_mono_right (v7_byte_pad7_entails_64 (a1 + 0x188#64) (boolByte dec.isComplete))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w392; apply Entails.sepExists_elim; intro pins
  apply Entails.pure_left; rintro ⟨hpts_len, hpts_lt⟩; apply Entails.pure_left; rintro ⟨hpins_len, hpin0⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw392
  have hbs_len : (v7_ptHeadersBytesOf pins dec.pts).length = 384 := by
    rw [v7_length_ptHeadersBytesOf pins dec.pts hpins_len, hpts_len]; rfl
  have hw0_lt : (v7_wordAt (v7_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 := by
    rcases pins with _ | ⟨pin, pins'⟩
    · rw [hpts_len] at hpins_len; simp [NUM_POLYS, CHUNK_SIZE] at hpins_len
    · rcases hpts : dec.pts with _ | ⟨s, ss⟩
      · rw [hpts] at hpts_len; simp [NUM_POLYS, CHUNK_SIZE] at hpts_len
      · rw [v7_wordAt_0_ptHeadersBytesOf]; exact hpin0 pin rfl
  refine Entails.sepExists_right ⟨v7_ptHeadersBytesOf pins dec.pts, hbs_len⟩
    (Entails.sepExists_right w392 (Entails.sepExists_right (v7_ptHeapList A pins dec.pts) ?_))
  change _ ⊢ ⌜(v7_wordAt (v7_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 ∧
      EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
      ((a2 ↦ₛ v7_ptHeadersBytesOf pins dec.pts) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((a2 + 392#64) ↦₆₄ w392) ∗ v7_ptHeapList A pins dec.pts ⊢
        ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ sortedSetPtListOf A a2 dec.pts ∗
        ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₈ boolByte dec.isComplete) ∗
        memRegion (a2 + 393#64) 7)⌝ ∗
    (a1 ↦ₛ v7_ptHeadersBytesOf pins dec.pts) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((a1 + 392#64) ↦₆₄ w392) ∗ v7_ptHeapList A pins dec.pts
  refine Entails.pure_right ⟨hw0_lt, hw392, ?_⟩ (Entails.of_eq (by ac_rfl))
  have hss2 := v7_headers_heaps_entails_sortedSetPtListOf A pins dec.pts a2 hpins_len
  have ha2_393 : (a2 + 392#64) + 1#64 = a2 + 393#64 := by bv_omega
  have hm392 := v7_pointsTo64_entails_byte_pad7 (a2 + 392#64) w392 (boolByte dec.isComplete) hw392
  rw [ha2_393] at hm392
  refine Entails.trans (Entails.of_eq (show _ =
    ((a2 ↦ₛ v7_ptHeadersBytesOf pins dec.pts) ∗ v7_ptHeapList A pins dec.pts) ∗
    ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₆₄ w392) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hss2 (sepConj_mono_right hm392)) ?_
  exact Entails.pure_right ⟨hpts_len, hpts_lt⟩ (Entails.of_eq (by ac_rfl))

theorem v7_bs384_w384_to_w0_bs384 (bs : List (BitVec 8)) (hbs : bs.length = 384) (w384 : BitVec 64) :
    ∃ (bs' : { l : List (BitVec 8) // l.length = 384 }),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) ∗ ((a + 384#64) ↦₆₄ w384) =
          (a ↦₆₄ v7_wordAt bs 0) ∗ ((a + 8#64) ↦ₛ bs'.val) := by
  have ht0 : (bs.take 8).length = 8 := by rw [List.length_take, hbs]; decide
  have hbs'_len : (bs.drop 8 ++ unpack64 w384).length = 384 := by
    rw [List.length_append, List.length_drop, hbs, unpack64_length]
  refine ⟨⟨bs.drop 8 ++ unpack64 w384, hbs'_len⟩, fun a => ?_⟩
  have hbs0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have hp0 : (a ↦ₛ bs) = (a ↦₆₄ v7_wordAt bs 0) ∗ ((a + 8#64) ↦ₛ bs.drop 8) := by
    conv_lhs => rw [hbs0]
    rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), ht0,
        v7_pointsToBytes_eq_pack64 a (bs.take 8) ht0]
    rfl
  have hp1 : ((a + 8#64) ↦ₛ bs.drop 8) ∗ ((a + 384#64) ↦₆₄ w384) =
      ((a + 8#64) ↦ₛ (bs.drop 8 ++ unpack64 w384)) := by
    rw [ProofLib.pointsToBytes_append (a + 8#64) (bs.drop 8) (unpack64 w384),
        List.length_drop, hbs, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha384 : (a + 8#64) + BitVec.ofNat 64 (384 - 8) = a + 384#64 := by bv_omega
    rw [ha384]
  rw [hp0, sepConj_assoc, hp1]

theorem v7_tail368_split_328 (tail368 : List (BitVec 8)) (htail : tail368.length = 368) :
    ∃ (bs328 : { l : List (BitVec 8) // l.length = 328 })
      (q328 q344 : BitVec 128) (w360 : BitVec 64),
      ∀ a : BitVec 64,
        (a ↦ₛ tail368) =
          (a ↦ₛ bs328.val) ∗
          ((a + 328#64) ↦₁₂₈ q328) ∗
          ((a + 344#64) ↦₁₂₈ q344) ∗
          ((a + 360#64) ↦₆₄ w360) := by
  have ht328 : (tail368.take 328).length = 328 := by rw [List.length_take, htail]; decide
  have ht16a : ((tail368.drop 328).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, htail]; decide
  have ht16b : ((tail368.drop 344).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, htail]; decide
  have ht8 : (tail368.drop 360).length = 8 := by
    rw [List.length_drop, htail]
  refine ⟨⟨tail368.take 328, ht328⟩,
    v7_pack128 ((tail368.drop 328).take 16),
    v7_pack128 ((tail368.drop 344).take 16),
    v7_pack64 (tail368.drop 360), fun a => ?_⟩
  have hs0 : tail368 = tail368.take 328 ++ tail368.drop 328 := (List.take_append_drop 328 tail368).symm
  have hs1 : tail368.drop 328 = (tail368.drop 328).take 16 ++ tail368.drop 344 := by
    change tail368.drop 328 = (tail368.drop 328).take 16 ++ tail368.drop (328 + 16)
    rw [← List.drop_drop, List.take_append_drop]
  have hs2 : tail368.drop 344 = (tail368.drop 344).take 16 ++ tail368.drop 360 := by
    change tail368.drop 344 = (tail368.drop 344).take 16 ++ tail368.drop (344 + 16)
    rw [← List.drop_drop, List.take_append_drop]
  have hp0 : (a ↦ₛ tail368) = (a ↦ₛ tail368.take 328) ∗ ((a + 328#64) ↦ₛ tail368.drop 328) := by
    conv_lhs => rw [hs0]
    rw [ProofLib.pointsToBytes_append a (tail368.take 328) (tail368.drop 328), ht328]
  have hp1 : ((a + 328#64) ↦ₛ tail368.drop 328) =
      ((a + 328#64) ↦₁₂₈ v7_pack128 ((tail368.drop 328).take 16)) ∗
      ((a + 344#64) ↦ₛ tail368.drop 344) := by
    conv_lhs => rw [hs1]
    rw [ProofLib.pointsToBytes_append (a + 328#64) ((tail368.drop 328).take 16) (tail368.drop 344),
        ht16a, v7_pointsToBytes_eq_pack128 (a + 328#64) ((tail368.drop 328).take 16) ht16a]
    have ha344 : (a + 328#64) + BitVec.ofNat 64 16 = a + 344#64 := by bv_omega
    rw [ha344]
  have hp2 : ((a + 344#64) ↦ₛ tail368.drop 344) =
      ((a + 344#64) ↦₁₂₈ v7_pack128 ((tail368.drop 344).take 16)) ∗
      ((a + 360#64) ↦₆₄ v7_pack64 (tail368.drop 360)) := by
    conv_lhs => rw [hs2]
    rw [ProofLib.pointsToBytes_append (a + 344#64) ((tail368.drop 344).take 16) (tail368.drop 360),
        ht16b, v7_pointsToBytes_eq_pack128 (a + 344#64) ((tail368.drop 344).take 16) ht16b]
    have ha360 : (a + 344#64) + BitVec.ofNat 64 16 = a + 360#64 := by bv_omega
    rw [ha360, v7_pointsToBytes_eq_pack64 (a + 360#64) (tail368.drop 360) ht8]
  rw [hp0, hp1, hp2]

theorem v7_polyDecoderAt_relocate_368 (A : RustAlloc) (a1 a2 : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a1 dec ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ tail368 : { l : List (BitVec 8) // l.length = 368 },
      ∃∗ P_heap : SepProp,
        ⌜w0.toNat < 2 ^ 63 ∧
          ((a2 ↦₆₄ w0) ∗
           ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗ ((a2 + 24#64) ↦₆₄ w24) ∗
           ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap ⊢
             polyDecoderAt A a2 dec)⌝ ∗
        (a1 ↦₆₄ w0) ∗
        ((a1 + 8#64) ↦₆₄ w8) ∗
        ((a1 + 16#64) ↦₆₄ w16) ∗
        ((a1 + 24#64) ↦₆₄ w24) ∗
        ((a1 + 32#64) ↦ₛ tail368.val) ∗
        P_heap := by
  refine Entails.trans (v7_polyDecoderAt_relocate A a1 a2 dec) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro w392
  apply Entails.sepExists_elim; intro P_heap
  apply Entails.pure_left; rintro ⟨hw0_lt, _, hreloc⟩
  obtain ⟨bs', hbs'⟩ := v7_bs384_w384_to_w0_bs384 bs.val bs.property (BitVec.ofNat 64 dec.ptsNeeded)
  obtain ⟨w8, w16, w24, tail368, hsplit⟩ := v7_bs384_w392_split_368 bs'.val bs'.property w392
  have h1a := hbs' a1
  have h2a := hbs' a2
  have h1b := hsplit a1
  have h2b := hsplit a2
  refine Entails.sepExists_right (v7_wordAt bs.val 0)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16
      (Entails.sepExists_right w24 (Entails.sepExists_right tail368
        (Entails.sepExists_right P_heap ?_)))))
  refine Entails.pure_right ⟨hw0_lt, ?_⟩ ?_
  · refine Entails.trans ?_ hreloc
    refine Entails.of_eq ?_
    calc
      (a2 ↦₆₄ v7_wordAt bs.val 0) ∗ ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
        ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap
        = (a2 ↦₆₄ v7_wordAt bs.val 0) ∗
          (((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
           ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val)) ∗ P_heap := by ac_rfl
      _ = ((a2 ↦₆₄ v7_wordAt bs.val 0) ∗ ((a2 + 8#64) ↦ₛ bs'.val)) ∗
          ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap := by rw [← h2b]; ac_rfl
      _ = (a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap := by rw [← h2a]; ac_rfl
  · refine Entails.of_eq ?_
    calc
      (a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap
        = ((a1 ↦₆₄ v7_wordAt bs.val 0) ∗ ((a1 + 8#64) ↦ₛ bs'.val)) ∗
          ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap := by rw [← h1a]; ac_rfl
      _ = (a1 ↦₆₄ v7_wordAt bs.val 0) ∗
          (((a1 + 8#64) ↦ₛ bs'.val) ∗ ((a1 + 392#64) ↦₆₄ w392)) ∗ P_heap := by ac_rfl
      _ = (a1 ↦₆₄ v7_wordAt bs.val 0) ∗ ((a1 + 8#64) ↦₆₄ w8) ∗
          ((a1 + 16#64) ↦₆₄ w16) ∗ ((a1 + 24#64) ↦₆₄ w24) ∗
          ((a1 + 32#64) ↦ₛ tail368.val) ∗ P_heap := by rw [h1b]; ac_rfl

theorem v7_bs_drop_step8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 8)) = Q)
    (hi : i + 8 ≤ 384 := by decide)
    (ho : o1 + 8#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₆₄ v7_wordAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 8 ++ bs.drop (i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 8).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 8) (bs.drop (i + 8)),
      ha, v7_pointsToBytes_eq_pack64 (a + o1) ((bs.drop i).take 8) htake_len, hrest]
  rfl

theorem v7_bs_drop_step16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 16)) = Q)
    (hi : i + 16 ≤ 384 := by decide)
    (ho : o1 + 16#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₁₂₈ v7_quadAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 16 ++ bs.drop (i + 16) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 16).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 16) (bs.drop (i + 16)),
      ha, v7_pointsToBytes_eq_pack128 (a + o1) ((bs.drop i).take 16) htake_len, hrest]
  rfl

theorem v7_bs_drop_end16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 : BitVec 64) :
    ((a + o1) ↦ₛ bs.drop 368) = ((a + o1) ↦₁₂₈ v7_quadAt bs 368) := by
  have hlen : (bs.drop 368).length = 16 := by rw [List.length_drop, hbs]
  have htake : (bs.drop 368).take 16 = bs.drop 368 := List.take_of_length_le (by omega)
  rw [v7_pointsToBytes_eq_pack128 (a + o1) (bs.drop 368) hlen]
  unfold v7_quadAt
  rw [htake]

/-- The 384-byte `PolyEncoder` vector-headers region at `a + 8 .. a + 392` decomposed into
20 64-bit words (`a + 8 .. a + 168`) and 14 128-bit quadwords (`a + 168 .. a + 392`), matching
both the stack reads at `a = fsp + 1392` (`+7468..+7816`) and the epilogue writes at `a = out`. -/
@[expose] def v7_encCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ v7_wordAt bs 0) ∗
  ((a + 16#64) ↦₆₄ v7_wordAt bs 8) ∗
  ((a + 24#64) ↦₆₄ v7_wordAt bs 16) ∗
  ((a + 32#64) ↦₆₄ v7_wordAt bs 24) ∗
  ((a + 40#64) ↦₆₄ v7_wordAt bs 32) ∗
  ((a + 48#64) ↦₆₄ v7_wordAt bs 40) ∗
  ((a + 56#64) ↦₆₄ v7_wordAt bs 48) ∗
  ((a + 64#64) ↦₆₄ v7_wordAt bs 56) ∗
  ((a + 72#64) ↦₆₄ v7_wordAt bs 64) ∗
  ((a + 80#64) ↦₆₄ v7_wordAt bs 72) ∗
  ((a + 88#64) ↦₆₄ v7_wordAt bs 80) ∗
  ((a + 96#64) ↦₆₄ v7_wordAt bs 88) ∗
  ((a + 104#64) ↦₆₄ v7_wordAt bs 96) ∗
  ((a + 112#64) ↦₆₄ v7_wordAt bs 104) ∗
  ((a + 120#64) ↦₆₄ v7_wordAt bs 112) ∗
  ((a + 128#64) ↦₆₄ v7_wordAt bs 120) ∗
  ((a + 136#64) ↦₆₄ v7_wordAt bs 128) ∗
  ((a + 144#64) ↦₆₄ v7_wordAt bs 136) ∗
  ((a + 152#64) ↦₆₄ v7_wordAt bs 144) ∗
  ((a + 160#64) ↦₆₄ v7_wordAt bs 152) ∗
  ((a + 168#64) ↦₁₂₈ v7_quadAt bs 160) ∗
  ((a + 184#64) ↦₁₂₈ v7_quadAt bs 176) ∗
  ((a + 200#64) ↦₁₂₈ v7_quadAt bs 192) ∗
  ((a + 216#64) ↦₁₂₈ v7_quadAt bs 208) ∗
  ((a + 232#64) ↦₁₂₈ v7_quadAt bs 224) ∗
  ((a + 248#64) ↦₁₂₈ v7_quadAt bs 240) ∗
  ((a + 264#64) ↦₁₂₈ v7_quadAt bs 256) ∗
  ((a + 280#64) ↦₁₂₈ v7_quadAt bs 272) ∗
  ((a + 296#64) ↦₁₂₈ v7_quadAt bs 288) ∗
  ((a + 312#64) ↦₁₂₈ v7_quadAt bs 304) ∗
  ((a + 328#64) ↦₁₂₈ v7_quadAt bs 320) ∗
  ((a + 344#64) ↦₁₂₈ v7_quadAt bs 336) ∗
  ((a + 360#64) ↦₁₂₈ v7_quadAt bs 352) ∗
  ((a + 376#64) ↦₁₂₈ v7_quadAt bs 368)

theorem v7_bs384_eq_encCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    ((a + 8#64) ↦ₛ bs) = v7_encCellsAt a bs := by
  unfold v7_encCellsAt
  change ((a + 8#64) ↦ₛ bs.drop 0) = _
  exact
    v7_bs_drop_step8 hbs a 8#64 16#64 0 <| v7_bs_drop_step8 hbs a 16#64 24#64 8 <|
    v7_bs_drop_step8 hbs a 24#64 32#64 16 <| v7_bs_drop_step8 hbs a 32#64 40#64 24 <|
    v7_bs_drop_step8 hbs a 40#64 48#64 32 <| v7_bs_drop_step8 hbs a 48#64 56#64 40 <|
    v7_bs_drop_step8 hbs a 56#64 64#64 48 <| v7_bs_drop_step8 hbs a 64#64 72#64 56 <|
    v7_bs_drop_step8 hbs a 72#64 80#64 64 <| v7_bs_drop_step8 hbs a 80#64 88#64 72 <|
    v7_bs_drop_step8 hbs a 88#64 96#64 80 <| v7_bs_drop_step8 hbs a 96#64 104#64 88 <|
    v7_bs_drop_step8 hbs a 104#64 112#64 96 <| v7_bs_drop_step8 hbs a 112#64 120#64 104 <|
    v7_bs_drop_step8 hbs a 120#64 128#64 112 <| v7_bs_drop_step8 hbs a 128#64 136#64 120 <|
    v7_bs_drop_step8 hbs a 136#64 144#64 128 <| v7_bs_drop_step8 hbs a 144#64 152#64 136 <|
    v7_bs_drop_step8 hbs a 152#64 160#64 144 <| v7_bs_drop_step8 hbs a 160#64 168#64 152 <|
    v7_bs_drop_step16 hbs a 168#64 184#64 160 <| v7_bs_drop_step16 hbs a 184#64 200#64 176 <|
    v7_bs_drop_step16 hbs a 200#64 216#64 192 <| v7_bs_drop_step16 hbs a 216#64 232#64 208 <|
    v7_bs_drop_step16 hbs a 232#64 248#64 224 <| v7_bs_drop_step16 hbs a 248#64 264#64 240 <|
    v7_bs_drop_step16 hbs a 264#64 280#64 256 <| v7_bs_drop_step16 hbs a 280#64 296#64 272 <|
    v7_bs_drop_step16 hbs a 296#64 312#64 288 <| v7_bs_drop_step16 hbs a 312#64 328#64 304 <|
    v7_bs_drop_step16 hbs a 328#64 344#64 320 <| v7_bs_drop_step16 hbs a 344#64 360#64 336 <|
    v7_bs_drop_step16 hbs a 360#64 376#64 352 <| v7_bs_drop_end16 hbs a 376#64

/-! ## 2. Address & Realignment Lemmas for `+7404..+7900` -/

@[expose] def v7_midQ128 (w0 w8 w16 : BitVec 64) : BitVec 128 :=
  unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8)

theorem v7_overlapWord7_midQ128_lsr8 (w0 w8 w16 : BitVec 64) :
    overlapWord7 ((v7_midQ128 w0 w8 w16).extractLsb' 64 64) (w16 >>> 8) = w16 := by
  have hhi : (v7_midQ128 w0 w8 w16).extractLsb' 64 64 = unshiftWord w8 (loByte w16) := by
    unfold v7_midQ128; bv_kernel
  rw [hhi, v7_overlapWord7_unshift_lsr8]

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_add_591_sext (fsp : BitVec 64) : fsp + (591#64).signExtend 64 = fsp + 591#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_576_add_8 (fsp : BitVec 64) : fsp + 576#64 + 8#64 = fsp + 584#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_145_sext (fsp : BitVec 64) : (fsp + 1392#64) + (145#64).signExtend 64 = fsp + 1537#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_145 (fsp : BitVec 64) : fsp + 1392#64 + 145#64 = fsp + 1537#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1537_add_8 (fsp : BitVec 64) : fsp + 1537#64 + 8#64 = fsp + 1545#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_121_sext (fsp : BitVec 64) : (fsp + 1392#64) + (121#64).signExtend 64 = fsp + 1513#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_121 (fsp : BitVec 64) : fsp + 1392#64 + 121#64 = fsp + 1513#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_97_sext (fsp : BitVec 64) : (fsp + 1392#64) + (97#64).signExtend 64 = fsp + 1489#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_97 (fsp : BitVec 64) : fsp + 1392#64 + 97#64 = fsp + 1489#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_101_sext (fsp : BitVec 64) : (fsp + 1392#64) + (101#64).signExtend 64 = fsp + 1493#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_101 (fsp : BitVec 64) : fsp + 1392#64 + 101#64 = fsp + 1493#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_103_sext (fsp : BitVec 64) : (fsp + 1392#64) + (103#64).signExtend 64 = fsp + 1495#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_103 (fsp : BitVec 64) : fsp + 1392#64 + 103#64 = fsp + 1495#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_848_add_39_sext (fsp : BitVec 64) : (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_848_add_39 (fsp : BitVec 64) : fsp + 848#64 + 39#64 = fsp + 887#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_848_add_15_sext (fsp : BitVec 64) : (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_848_add_15 (fsp : BitVec 64) : fsp + 848#64 + 15#64 = fsp + 863#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_168 (fsp : BitVec 64) : fsp + 1392#64 + 168#64 = fsp + 1560#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1560_add_96 (fsp : BitVec 64) : fsp + 1560#64 + 96#64 = fsp + 1656#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1656_add_16 (fsp : BitVec 64) : fsp + 1656#64 + 16#64 = fsp + 1672#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1560_add_128 (fsp : BitVec 64) : fsp + 1560#64 + 128#64 = fsp + 1688#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1688_add_16 (fsp : BitVec 64) : fsp + 1688#64 + 16#64 = fsp + 1704#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1560_add_160 (fsp : BitVec 64) : fsp + 1560#64 + 160#64 = fsp + 1720#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1720_add_16 (fsp : BitVec 64) : fsp + 1720#64 + 16#64 = fsp + 1736#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1560_add_192 (fsp : BitVec 64) : fsp + 1560#64 + 192#64 = fsp + 1752#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1752_add_16 (fsp : BitVec 64) : fsp + 1752#64 + 16#64 = fsp + 1768#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_orr_x27_w88 (w88 : BitVec 64) :
    ((w88.extractLsb' 8 32).zeroExtend 64 |||
      ((((w88.extractLsb' 40 16).zeroExtend 32 |||
        ((w88.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) =
      (w88.extractLsb' 8 56).zeroExtend 64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_w88_d97 (w88 : BitVec 64) :
    ((w88.extractLsb' 8 56).zeroExtend 64).setWidth 32 = w88.extractLsb' 8 32 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_w88_h101 (w88 : BitVec 64) :
    ((((w88.extractLsb' 8 56).zeroExtend 64) >>> 32).setWidth 32).setWidth 16 =
      w88.extractLsb' 40 16 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_w88_b103 (w88 : BitVec 64) :
    ((((w88.extractLsb' 8 56).zeroExtend 64) >>> 48).setWidth 32).setWidth 8 =
      w88.extractLsb' 56 8 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1888_add_32 (fsp : BitVec 64) : fsp + 1888#64 + 32#64 = fsp + 1920#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_896_add_328 (fsp : BitVec 64) : fsp + 896#64 + 328#64 = fsp + 1224#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1224_add_16 (fsp : BitVec 64) : fsp + 1224#64 + 16#64 = fsp + 1240#64 := by bv_omega

theorem v7_triple64_eq_byte_q128_tail7 (a w0 w8 w16 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) =
      (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w16) := by
  have h2 := pair64_to_byte_word_tail7 (a + 8#64) w8 w16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h2
  have h1b :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ loByte w8) =
        (a ↦₈ loByte w0) ∗ ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w0 (loByte w8),
        ProofLib.pointsToBytes_append a (unpack64 w0) [loByte w8], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha1_8 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha1_8] at hq
  rw [h2, ← sepConj_assoc, ← sepConj_assoc, h1b,
      sepConj_assoc (a ↦₈ loByte w0), sepConj_assoc, hq]

theorem v7_right64_eq_unshift_hiBytes7 (p ptr len : BitVec 64) :
    (p ↦ₛ EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))) ∗ ((p + 7#64) ↦₆₄ len) =
      (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ ((p + 8#64) ↦ₛ EncoderFromPb.hiBytes7 len) := by
  rw [pointsTo64_eq_pointsToBytes (p + 7#64) len]
  have h7 : p + BitVec.ofNat 64 (EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))).length = p + 7#64 := by
    rw [length_loBytes7]
  rw [← h7, ← ProofLib.pointsToBytes_append p (EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))) (unpack64 len),
      loBytes7_unshiftWord_append_unpack64 ptr len,
      ProofLib.pointsToBytes_append p (unpack64 (unshiftWord ptr (loByte len))) (EncoderFromPb.hiBytes7 len),
      unpack64_length, ← pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len))]

theorem v7_fsp_584_realign_low7_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 591#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 584#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest := by
  have h := v7_right64_eq_unshift_hiBytes7 (fsp + 584#64) w16 w24
  have ha7 : (fsp + 584#64) + 7#64 = fsp + 591#64 := by bv_omega
  have ha8 : (fsp + 584#64) + 8#64 = fsp + 592#64 := by bv_omega
  rw [ha7, ha8, v7_hiBytes7_eq_loBytes7_lsr8 w24] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

/-! ## 3. `<PolyDecoder>::from_pb = Ok(dec)` First Copy (`+7404 -> +7468`) -/

theorem v7_fsp_1488_split_rest (fsp w88 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1488#64) ↦₆₄ w88) ∗ Rest =
      ((fsp + 1488#64) ↦₈ w88.extractLsb' 0 8) ∗
      ((fsp + 1489#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((fsp + 1493#64) ↦₁₆ w88.extractLsb' 40 16) ∗
      ((fsp + 1495#64) ↦₈ w88.extractLsb' 56 8) ∗ Rest := by
  have h := v7_pointsTo64_split_1_4_2_1 (fsp + 1488#64) w88
  have ha1 : (fsp + 1488#64) + 1#64 = fsp + 1489#64 := by bv_omega
  have ha5 : (fsp + 1488#64) + 5#64 = fsp + 1493#64 := by bv_omega
  have ha7 : (fsp + 1488#64) + 7#64 = fsp + 1495#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v7_fsp_1488_unsplit_rest (fsp w88 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1488#64) ↦₈ w88.extractLsb' 0 8) ∗
      ((fsp + 1489#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((fsp + 1493#64) ↦₁₆ w88.extractLsb' 40 16) ∗
      ((fsp + 1495#64) ↦₈ w88.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1488#64) ↦₆₄ w88) ∗ Rest :=
  (v7_fsp_1488_split_rest fsp w88 Rest).symm

theorem v7_fsp_1536_realign_rest (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1536#64) ↦₆₄ w136) ∗ ((fsp + 1544#64) ↦₆₄ w144) ∗ ((fsp + 1552#64) ↦₆₄ w152) ∗ Rest =
      ((fsp + 1536#64) ↦₈ loByte w136) ∗
      ((fsp + 1537#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 0 64) ∗
      ((fsp + 1545#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 64 64) ∗
      ((fsp + 1553#64) ↦ₛ EncoderFromPb.hiBytes7 w152) ∗ Rest := by
  have h := v7_triple64_eq_byte_q128_tail7 (fsp + 1536#64) w136 w144 w152
  have ha8 : (fsp + 1536#64) + 8#64 = fsp + 1544#64 := by bv_omega
  have ha16 : (fsp + 1536#64) + 16#64 = fsp + 1552#64 := by bv_omega
  have ha1 : (fsp + 1536#64) + 1#64 = fsp + 1537#64 := by bv_omega
  have ha17 : (fsp + 1536#64) + 17#64 = fsp + 1553#64 := by bv_omega
  have ha1545 : (fsp + 1537#64) + 8#64 = fsp + 1545#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1536#64) ↦₈ loByte w136) ∗
    ((fsp + 1537#64) ↦₁₂₈ v7_midQ128 w136 w144 w152) ∗
    ((fsp + 1553#64) ↦ₛ EncoderFromPb.hiBytes7 w152) at h
  unfold pointsTo128 at h
  rw [ha1545] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v7_fsp_1536_unrealign_rest (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1536#64) ↦₈ loByte w136) ∗
      ((fsp + 1537#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 0 64) ∗
      ((fsp + 1545#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 64 64) ∗
      ((fsp + 1553#64) ↦ₛ EncoderFromPb.hiBytes7 w152) ∗ Rest =
    ((fsp + 1536#64) ↦₆₄ w136) ∗ ((fsp + 1544#64) ↦₆₄ w144) ∗ ((fsp + 1552#64) ↦₆₄ w152) ∗ Rest :=
  (v7_fsp_1536_realign_rest fsp w136 w144 w152 Rest).symm

theorem v7_fsp_1536_split_1_7_rest (fsp w136 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1536#64) ↦₆₄ w136) ∗ Rest =
      ((fsp + 1536#64) ↦₈ loByte w136) ∗
      ((fsp + 1537#64) ↦ₛ EncoderFromPb.hiBytes7 w136) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1536#64) w136
  have ha1 : (fsp + 1536#64) + 1#64 = fsp + 1537#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v7_fsp_1536_unsplit_1_7_rest (fsp w136 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1536#64) ↦₈ loByte w136) ∗
      ((fsp + 1537#64) ↦ₛ EncoderFromPb.hiBytes7 w136) ∗ Rest =
      ((fsp + 1536#64) ↦₆₄ w136) ∗ Rest :=
  (v7_fsp_1536_split_1_7_rest fsp w136 Rest).symm

theorem v7_fsp_1512_realign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1512#64) ↦₆₄ w112) ∗ ((fsp + 1520#64) ↦₆₄ w120) ∗ Rest =
      ((fsp + 1512#64) ↦₈ loByte w112) ∗
      ((fsp + 1513#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((fsp + 1521#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 1512#64) w112 w120
  have ha8 : (fsp + 1512#64) + 8#64 = fsp + 1520#64 := by bv_omega
  have ha1 : (fsp + 1512#64) + 1#64 = fsp + 1513#64 := by bv_omega
  have ha9 : (fsp + 1512#64) + 9#64 = fsp + 1521#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v7_fsp_1512_unrealign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1512#64) ↦₈ loByte w112) ∗
      ((fsp + 1513#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((fsp + 1521#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest =
      ((fsp + 1512#64) ↦₆₄ w112) ∗ ((fsp + 1520#64) ↦₆₄ w120) ∗ Rest :=
  (v7_fsp_1512_realign_rest fsp w112 w120 Rest).symm

theorem v7_fsp_880_realign_64_rest (fsp w880 w888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v7_fsp_880_unrealign_unshift_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w112 (loByte w120))) ∗
      ((fsp + 887#64) ↦₆₄ w120) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w120 >>> 8)) ∗ Rest := by
  have h := v7_right64_eq_unshift_hiBytes7 (fsp + 880#64) w112 w120
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8, v7_hiBytes7_eq_loBytes7_lsr8 w120] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v7_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v7_fsp_856_unrealign_midQ128_rest (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v7_midQ128 w136 w144 w152).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w152) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w152 >>> 8)) ∗ Rest := by
  have h := (v7_fsp_856_realign_rest fsp ((v7_midQ128 w136 w144 w152).extractLsb' 64 64)
    (w152 >>> 8) Rest).symm
  rwa [v7_overlapWord7_midQ128_lsr8 w136 w144 w152] at h

end CryptoVerification.SpqrV1.States.FromPb

