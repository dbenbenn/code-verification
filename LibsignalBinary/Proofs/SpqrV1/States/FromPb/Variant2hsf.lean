/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part F

**Checked by Lean.**

`Ok` output staging (`+9404 -> +9484 -> +8180`) and shared epilogue composition for
`InnerState.headerSent`.
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



@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by bv_omega

/-! ## `PolyDecoder` Relocation Helpers (`fsp + 1888 -> out + 488`) -/

/-- Concatenate the `Vec<(u16, u16)>` headers (24 bytes each) for a list of `SortedSetPt`. -/
@[expose] def v2hsf_ptHeadersBytesOf : List VecPin → List SortedSetPt → List (BitVec 8)
  | pin :: pins, s :: ss => vecHeaderBytesOf pin s.vec.length ++ v2hsf_ptHeadersBytesOf pins ss
  | _, _ => []

/-- Separate heap allocations for a list of `SortedSetPt` pinned by `pins`. -/
def v2hsf_ptHeapList (A : RustAlloc) : List VecPin → List SortedSetPt → SepProp
  | pin :: pins, s :: ss => vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v2hsf_ptHeapList A pins ss
  | _, _ => emp

theorem v2hsf_length_ptHeadersBytesOf :
    ∀ (pins : List VecPin) (ss : List SortedSetPt),
      pins.length = ss.length → (v2hsf_ptHeadersBytesOf pins ss).length = ss.length * 24
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | pin :: pins, s :: ss, h => by
    simp only [List.length_cons] at h
    simp only [v2hsf_ptHeadersBytesOf, List.length_append, length_vecHeaderBytesOf,
      v2hsf_length_ptHeadersBytesOf pins ss (Nat.succ.inj h), List.length_cons]; omega

theorem v2hsf_sortedSetPtOf_entails_pin (A : RustAlloc) (a : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A a s ⊢
      ∃∗ pin : VecPin, ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
        vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec := by
  unfold sortedSetPtOf vecOf vecAt
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ s.vec.length]
  have hcap : vecBuf A ptStride ptAlign ptAt cap ptr s.vec ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecBuf A ptStride ptAlign ptAt cap ptr s.vec := by
    unfold vecBuf ptStride; apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    have hlt' : cap.toNat < 2 ^ 63 := by omega
    exact Entails.pure_right hlt' (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  exact Entails.trans (sepConj_mono_right hcap) (Entails.of_eq (by ac_rfl))

theorem v2hsf_pin_entails_sortedSetPtOf (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (s : SortedSetPt) :
    (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
      vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ⊢ sortedSetPtOf A a s := by
  rw [← vecHeader_eq_pointsToBytes a pin s.vec.length]
  unfold sortedSetPtOf vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem v2hsf_sortedSetPtListOf_entails_headers_heaps (A : RustAlloc) :
    ∀ (ss : List SortedSetPt) (a : BitVec 64),
      sortedSetPtListOf A a ss ⊢
        ∃∗ pins : List VecPin,
          ⌜pins.length = ss.length ∧ (∀ pin ∈ pins.head?, pin.cap.toNat < 2 ^ 63)⌝ ∗
          (a ↦ₛ v2hsf_ptHeadersBytesOf pins ss) ∗ v2hsf_ptHeapList A pins ss
  | [], a => by
    simp only [sortedSetPtListOf, arrayAt]; refine Entails.sepExists_right [] ?_
    simp [v2hsf_ptHeadersBytesOf, v2hsf_ptHeapList, ProofLib.pointsToBytes_nil]; exact Entails.refl _
  | s :: ss, a => by
    simp only [sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (sepConj_mono (v2hsf_sortedSetPtOf_entails_pin A a s)
      (v2hsf_sortedSetPtListOf_entails_headers_heaps A ss (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro pins; apply Entails.sepExists_elim; intro pin
    apply Entails.pure_left; intro hcap0
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, _⟩
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (s :: ss).length := by simp [hlen]
    have hhead : ∀ p ∈ (pin :: pins).head?, p.cap.toNat < 2 ^ 63 := by
      intro p hp; simp at hp; subst hp; exact hcap0
    refine Entails.pure_right ⟨hlen', hhead⟩ ?_
    simp only [v2hsf_ptHeadersBytesOf, v2hsf_ptHeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v2hsf_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    exact Entails.of_eq (by ac_rfl)

theorem v2hsf_headers_heaps_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (ss : List SortedSetPt) (a : BitVec 64),
      pins.length = ss.length →
      (a ↦ₛ v2hsf_ptHeadersBytesOf pins ss) ∗ v2hsf_ptHeapList A pins ss ⊢ sortedSetPtListOf A a ss
  | [], [], a, _ => by
    simp [v2hsf_ptHeadersBytesOf, v2hsf_ptHeapList, sortedSetPtListOf, arrayAt, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | pin :: pins, s :: ss, a, h => by
    simp only [List.length_cons] at h
    simp only [v2hsf_ptHeadersBytesOf, v2hsf_ptHeapList, sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v2hsf_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ ((a + 24#64) ↦ₛ v2hsf_ptHeadersBytesOf pins ss)) ∗
        (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v2hsf_ptHeapList A pins ss) =
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec) ∗
        (((a + 24#64) ↦ₛ v2hsf_ptHeadersBytesOf pins ss) ∗ v2hsf_ptHeapList A pins ss) by ac_rfl)) ?_
    exact sepConj_mono (v2hsf_pin_entails_sortedSetPtOf A a pin s)
      (v2hsf_headers_heaps_entails_sortedSetPtListOf A pins ss (a + 24#64) (Nat.succ.inj h))

theorem v2hsf_wordAt_0_ptHeadersBytesOf (pin : VecPin) (pins : List VecPin)
    (s : SortedSetPt) (ss : List SortedSetPt) :
    v1_wordAt (v2hsf_ptHeadersBytesOf (pin :: pins) (s :: ss)) 0 = pin.cap := by
  unfold v1_wordAt v2hsf_ptHeadersBytesOf vecHeaderBytesOf
  rw [List.drop_zero, List.append_assoc, List.append_assoc,
      List.take_append_of_le_length (by rw [unpack64_length]),
      List.take_of_length_le (by rw [unpack64_length])]
  dsimp only [v1_pack64, unpack64, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  bv_kernel

theorem v2hsf_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗ (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) :=
    split_top (split_step (mem32_entails _) (split_step (mem16_entails _) (mem8_entails _)))
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7; apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  refine Entails.pure_right (show EncoderFromPb.loByte w = b from hw0) ?_
  rw [v1_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]; exact Entails.refl _

theorem v2hsf_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v2hsf_polyDecoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a1 dec ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
        ⌜(v1_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
          ((a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A a2 dec)⌝ ∗
        (a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  have ha1_393 : a1 + 0x189#64 = (a1 + 0x188#64) + 1#64 := by bv_omega
  rw [ha1_393]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (v2hsf_sortedSetPtListOf_entails_headers_heaps A dec.pts a1)
      (sepConj_mono_right (v2hsf_byte_pad7_entails_64 (a1 + 0x188#64) (boolByte dec.isComplete))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w392; apply Entails.sepExists_elim; intro pins
  apply Entails.pure_left; rintro ⟨hpts_len, hpts_lt⟩; apply Entails.pure_left; rintro ⟨hpins_len, hpin0⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw392
  have hbs_len : (v2hsf_ptHeadersBytesOf pins dec.pts).length = 384 := by
    rw [v2hsf_length_ptHeadersBytesOf pins dec.pts hpins_len, hpts_len]; rfl
  have hw0_lt : (v1_wordAt (v2hsf_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 := by
    rcases pins with _ | ⟨pin, pins'⟩
    · rw [hpts_len] at hpins_len; simp [NUM_POLYS, CHUNK_SIZE] at hpins_len
    · rcases hpts : dec.pts with _ | ⟨s, ss⟩
      · rw [hpts] at hpts_len; simp [NUM_POLYS, CHUNK_SIZE] at hpts_len
      · rw [v2hsf_wordAt_0_ptHeadersBytesOf]; exact hpin0 pin rfl
  refine Entails.sepExists_right ⟨v2hsf_ptHeadersBytesOf pins dec.pts, hbs_len⟩
    (Entails.sepExists_right w392 (Entails.sepExists_right (v2hsf_ptHeapList A pins dec.pts) ?_))
  change _ ⊢ ⌜(v1_wordAt (v2hsf_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 ∧
      EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
      ((a2 ↦ₛ v2hsf_ptHeadersBytesOf pins dec.pts) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((a2 + 392#64) ↦₆₄ w392) ∗ v2hsf_ptHeapList A pins dec.pts ⊢
        ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ sortedSetPtListOf A a2 dec.pts ∗
        ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₈ boolByte dec.isComplete) ∗
        memRegion (a2 + 393#64) 7)⌝ ∗
    (a1 ↦ₛ v2hsf_ptHeadersBytesOf pins dec.pts) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((a1 + 392#64) ↦₆₄ w392) ∗ v2hsf_ptHeapList A pins dec.pts
  refine Entails.pure_right ⟨hw0_lt, hw392, ?_⟩ (Entails.of_eq (by ac_rfl))
  have hss2 := v2hsf_headers_heaps_entails_sortedSetPtListOf A pins dec.pts a2 hpins_len
  have ha2_393 : (a2 + 392#64) + 1#64 = a2 + 393#64 := by bv_omega
  have hm392 := v2hsf_pointsTo64_entails_byte_pad7 (a2 + 392#64) w392 (boolByte dec.isComplete) hw392
  rw [ha2_393] at hm392
  refine Entails.trans (Entails.of_eq (show _ =
    ((a2 ↦ₛ v2hsf_ptHeadersBytesOf pins dec.pts) ∗ v2hsf_ptHeapList A pins dec.pts) ∗
    ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₆₄ w392) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hss2 (sepConj_mono_right hm392)) ?_
  exact Entails.pure_right ⟨hpts_len, hpts_lt⟩ (Entails.of_eq (by ac_rfl))

theorem v2hsf_bs384_w384_w392_split_328 (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (w384 w392 : BitVec 64) :
    ∃ (dbs328 : { l : List (BitVec 8) // l.length = 328 }), ∀ a : BitVec 64,
      (a ↦ₛ bs) ∗ ((a + 384#64) ↦₆₄ w384) ∗ ((a + 392#64) ↦₆₄ w392) =
        (a ↦₆₄ v1_wordAt bs 0) ∗ ((a + 8#64) ↦₆₄ v1_wordAt bs 8) ∗ ((a + 16#64) ↦₆₄ v1_wordAt bs 16) ∗
        ((a + 24#64) ↦₆₄ v1_wordAt bs 24) ∗ ((a + 32#64) ↦₆₄ v1_wordAt bs 32) ∗
        ((a + 40#64) ↦₆₄ v1_wordAt bs 40) ∗ ((a + 48#64) ↦₆₄ v1_wordAt bs 48) ∗
        ((a + 56#64) ↦₆₄ v1_wordAt bs 56) ∗ ((a + 64#64) ↦₆₄ v1_wordAt bs 64) ∗
        ((a + 72#64) ↦ₛ dbs328.val) := by
  have hdlen : ((bs.drop 72 ++ unpack64 w384) ++ unpack64 w392).length = 328 := by
    rw [List.length_append, List.length_append, List.length_drop, hbs, unpack64_length, unpack64_length]
  refine ⟨⟨(bs.drop 72 ++ unpack64 w384) ++ unpack64 w392, hdlen⟩, fun a => ?_⟩
  have h9 : (a ↦ₛ bs) =
      (a ↦₆₄ v1_wordAt bs 0) ∗ ((a + 8#64) ↦₆₄ v1_wordAt bs 8) ∗ ((a + 16#64) ↦₆₄ v1_wordAt bs 16) ∗
      ((a + 24#64) ↦₆₄ v1_wordAt bs 24) ∗ ((a + 32#64) ↦₆₄ v1_wordAt bs 32) ∗
      ((a + 40#64) ↦₆₄ v1_wordAt bs 40) ∗ ((a + 48#64) ↦₆₄ v1_wordAt bs 48) ∗
      ((a + 56#64) ↦₆₄ v1_wordAt bs 56) ∗ ((a + 64#64) ↦₆₄ v1_wordAt bs 64) ∗
      ((a + 72#64) ↦ₛ bs.drop 72) := by
    have h :=
      v1_bs_drop_step8 hbs a 0#64 8#64 0 <| v1_bs_drop_step8 hbs a 8#64 16#64 8 <|
      v1_bs_drop_step8 hbs a 16#64 24#64 16 <| v1_bs_drop_step8 hbs a 24#64 32#64 24 <|
      v1_bs_drop_step8 hbs a 32#64 40#64 32 <| v1_bs_drop_step8 hbs a 40#64 48#64 40 <|
      v1_bs_drop_step8 hbs a 48#64 56#64 48 <| v1_bs_drop_step8 hbs a 56#64 64#64 56 <|
      v1_bs_drop_step8 hbs a 64#64 72#64 64 rfl
    change ((a + 0#64) ↦ₛ bs) = _ at h
    simpa only [BitVec.add_zero, Nat.reduceAdd, sepConj_assoc] using h
  have htail1 : ((a + 72#64) ↦ₛ bs.drop 72) ∗ ((a + 384#64) ↦₆₄ w384) =
      ((a + 72#64) ↦ₛ (bs.drop 72 ++ unpack64 w384)) := by
    rw [ProofLib.pointsToBytes_append (a + 72#64) (bs.drop 72) (unpack64 w384),
        List.length_drop, hbs, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha384 : (a + 72#64) + BitVec.ofNat 64 (384 - 72) = a + 384#64 := by bv_omega
    rw [ha384]
  have htail2 : ((a + 72#64) ↦ₛ (bs.drop 72 ++ unpack64 w384)) ∗ ((a + 392#64) ↦₆₄ w392) =
      ((a + 72#64) ↦ₛ ((bs.drop 72 ++ unpack64 w384) ++ unpack64 w392)) := by
    rw [ProofLib.pointsToBytes_append (a + 72#64) (bs.drop 72 ++ unpack64 w384) (unpack64 w392),
        List.length_append, List.length_drop, hbs, unpack64_length,
        ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha392 : (a + 72#64) + BitVec.ofNat 64 (384 - 72 + 8) = a + 392#64 := by bv_omega
    rw [ha392]
  rw [h9]; simp only [sepConj_assoc]
  rw [← sepConj_assoc ((a + 72#64) ↦ₛ bs.drop 72), htail1, htail2]

theorem v2hsf_polyDecoderAt_relocate_328 (A : RustAlloc) (a1 a2 : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a1 dec ⊢
      ∃∗ dw0 : BitVec 64, ∃∗ dw8 : BitVec 64, ∃∗ dw16 : BitVec 64,
      ∃∗ dw24 : BitVec 64, ∃∗ dw32 : BitVec 64, ∃∗ dw40 : BitVec 64,
      ∃∗ dw48 : BitVec 64, ∃∗ dw56 : BitVec 64, ∃∗ dw64 : BitVec 64,
      ∃∗ dbs328 : { l : List (BitVec 8) // l.length = 328 }, ∃∗ P_heap : SepProp,
        ⌜dw0.toNat < 2 ^ 63 ∧
          ((a2 ↦₆₄ dw0) ∗ ((a2 + 8#64) ↦₆₄ dw8) ∗ ((a2 + 16#64) ↦₆₄ dw16) ∗
           ((a2 + 24#64) ↦₆₄ dw24) ∗ ((a2 + 32#64) ↦₆₄ dw32) ∗ ((a2 + 40#64) ↦₆₄ dw40) ∗
           ((a2 + 48#64) ↦₆₄ dw48) ∗ ((a2 + 56#64) ↦₆₄ dw56) ∗ ((a2 + 64#64) ↦₆₄ dw64) ∗
           ((a2 + 72#64) ↦ₛ dbs328.val) ∗ P_heap ⊢ polyDecoderAt A a2 dec)⌝ ∗
        (a1 ↦₆₄ dw0) ∗ ((a1 + 8#64) ↦₆₄ dw8) ∗ ((a1 + 16#64) ↦₆₄ dw16) ∗
        ((a1 + 24#64) ↦₆₄ dw24) ∗ ((a1 + 32#64) ↦₆₄ dw32) ∗ ((a1 + 40#64) ↦₆₄ dw40) ∗
        ((a1 + 48#64) ↦₆₄ dw48) ∗ ((a1 + 56#64) ↦₆₄ dw56) ∗ ((a1 + 64#64) ↦₆₄ dw64) ∗
        ((a1 + 72#64) ↦ₛ dbs328.val) ∗ P_heap := by
  refine Entails.trans (v2hsf_polyDecoderAt_relocate A a1 a2 dec) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.sepExists_elim; intro w392
  apply Entails.sepExists_elim; intro P_heap; apply Entails.pure_left; rintro ⟨hw0_lt, _, hreloc⟩
  obtain ⟨dbs328, hsplit⟩ := v2hsf_bs384_w384_w392_split_328 bs.val bs.property
    (BitVec.ofNat 64 dec.ptsNeeded) w392
  have h1 := hsplit a1; have h2 := hsplit a2
  refine Entails.sepExists_right (v1_wordAt bs.val 0)
    (Entails.sepExists_right (v1_wordAt bs.val 8) (Entails.sepExists_right (v1_wordAt bs.val 16)
      (Entails.sepExists_right (v1_wordAt bs.val 24) (Entails.sepExists_right (v1_wordAt bs.val 32)
        (Entails.sepExists_right (v1_wordAt bs.val 40) (Entails.sepExists_right (v1_wordAt bs.val 48)
          (Entails.sepExists_right (v1_wordAt bs.val 56) (Entails.sepExists_right (v1_wordAt bs.val 64)
            (Entails.sepExists_right dbs328 (Entails.sepExists_right P_heap ?_))))))))))
  refine Entails.pure_right ⟨hw0_lt, ?_⟩ ?_
  · refine Entails.trans ?_ hreloc
    refine Entails.of_eq ?_
    calc
      (a2 ↦₆₄ v1_wordAt bs.val 0) ∗ ((a2 + 8#64) ↦₆₄ v1_wordAt bs.val 8) ∗
        ((a2 + 16#64) ↦₆₄ v1_wordAt bs.val 16) ∗ ((a2 + 24#64) ↦₆₄ v1_wordAt bs.val 24) ∗
        ((a2 + 32#64) ↦₆₄ v1_wordAt bs.val 32) ∗ ((a2 + 40#64) ↦₆₄ v1_wordAt bs.val 40) ∗
        ((a2 + 48#64) ↦₆₄ v1_wordAt bs.val 48) ∗ ((a2 + 56#64) ↦₆₄ v1_wordAt bs.val 56) ∗
        ((a2 + 64#64) ↦₆₄ v1_wordAt bs.val 64) ∗ ((a2 + 72#64) ↦ₛ dbs328.val) ∗ P_heap
        = ((a2 ↦₆₄ v1_wordAt bs.val 0) ∗ ((a2 + 8#64) ↦₆₄ v1_wordAt bs.val 8) ∗
           ((a2 + 16#64) ↦₆₄ v1_wordAt bs.val 16) ∗ ((a2 + 24#64) ↦₆₄ v1_wordAt bs.val 24) ∗
           ((a2 + 32#64) ↦₆₄ v1_wordAt bs.val 32) ∗ ((a2 + 40#64) ↦₆₄ v1_wordAt bs.val 40) ∗
           ((a2 + 48#64) ↦₆₄ v1_wordAt bs.val 48) ∗ ((a2 + 56#64) ↦₆₄ v1_wordAt bs.val 56) ∗
           ((a2 + 64#64) ↦₆₄ v1_wordAt bs.val 64) ∗ ((a2 + 72#64) ↦ₛ dbs328.val)) ∗ P_heap := by ac_rfl
      _ = ((a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           ((a2 + 392#64) ↦₆₄ w392)) ∗ P_heap := by rw [← h2]
      _ = (a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap := by ac_rfl
  · refine Entails.of_eq ?_
    calc
      (a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap
        = ((a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           ((a1 + 392#64) ↦₆₄ w392)) ∗ P_heap := by ac_rfl
      _ = ((a1 ↦₆₄ v1_wordAt bs.val 0) ∗ ((a1 + 8#64) ↦₆₄ v1_wordAt bs.val 8) ∗
           ((a1 + 16#64) ↦₆₄ v1_wordAt bs.val 16) ∗ ((a1 + 24#64) ↦₆₄ v1_wordAt bs.val 24) ∗
           ((a1 + 32#64) ↦₆₄ v1_wordAt bs.val 32) ∗ ((a1 + 40#64) ↦₆₄ v1_wordAt bs.val 40) ∗
           ((a1 + 48#64) ↦₆₄ v1_wordAt bs.val 48) ∗ ((a1 + 56#64) ↦₆₄ v1_wordAt bs.val 56) ∗
           ((a1 + 64#64) ↦₆₄ v1_wordAt bs.val 64) ∗ ((a1 + 72#64) ↦ₛ dbs328.val)) ∗ P_heap := by rw [h1]
      _ = (a1 ↦₆₄ v1_wordAt bs.val 0) ∗ ((a1 + 8#64) ↦₆₄ v1_wordAt bs.val 8) ∗
          ((a1 + 16#64) ↦₆₄ v1_wordAt bs.val 16) ∗ ((a1 + 24#64) ↦₆₄ v1_wordAt bs.val 24) ∗
          ((a1 + 32#64) ↦₆₄ v1_wordAt bs.val 32) ∗ ((a1 + 40#64) ↦₆₄ v1_wordAt bs.val 40) ∗
          ((a1 + 48#64) ↦₆₄ v1_wordAt bs.val 48) ∗ ((a1 + 56#64) ↦₆₄ v1_wordAt bs.val 56) ∗
          ((a1 + 64#64) ↦₆₄ v1_wordAt bs.val 64) ∗ ((a1 + 72#64) ↦ₛ dbs328.val) ∗ P_heap := by ac_rfl

/-! ## Segment `+9404 -> +9484` (`0x5c560 .. 0x5c5b0`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x25_add_145 (fsp : BitVec 64) :
    (fsp + 1792#64) + 145#64 = fsp + 1937#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x25_add_145_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (145#64).signExtend 64 = fsp + 1937#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_fsp_576_add_15 (fsp : BitVec 64) :
    (fsp + 576#64) + 15#64 = fsp + 591#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_fsp_576_add_15_sext (fsp : BitVec 64) :
    (fsp + 576#64) + (15#64).signExtend 64 = fsp + 591#64 := by bv_kernel

theorem v2hsf_fsp_1936_realign_rest (fsp dw48 dw56 dw64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗ Rest =
      ((fsp + 1936#64) ↦₈ loByte dw48) ∗
      ((fsp + 1937#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 0 64) ∗
      ((fsp + 1945#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) ∗
      ((fsp + 1953#64) ↦ₛ EncoderFromPb.hiBytes7 dw64) ∗ Rest := by
  have h := v1_triple64_eq_byte_q128_tail7 (fsp + 1936#64) dw48 dw56 dw64
  have ha8 : (fsp + 1936#64) + 8#64 = fsp + 1944#64 := by bv_omega
  have ha16 : (fsp + 1936#64) + 16#64 = fsp + 1952#64 := by bv_omega
  have ha1 : (fsp + 1936#64) + 1#64 = fsp + 1937#64 := by bv_omega
  have ha17 : (fsp + 1936#64) + 17#64 = fsp + 1953#64 := by bv_omega
  have ha1945 : (fsp + 1937#64) + 8#64 = fsp + 1945#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1936#64) ↦₈ loByte dw48) ∗
    ((fsp + 1937#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
    ((fsp + 1953#64) ↦ₛ EncoderFromPb.hiBytes7 dw64) at h
  unfold pointsTo128 at h; rw [ha1945] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hsf_fsp_1936_unrealign_rest (fsp dw48 dw56 dw64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1936#64) ↦₈ loByte dw48) ∗
      ((fsp + 1937#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 0 64) ∗
      ((fsp + 1945#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) ∗
      ((fsp + 1953#64) ↦ₛ EncoderFromPb.hiBytes7 dw64) ∗ Rest =
    ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗ Rest :=
  (v2hsf_fsp_1936_realign_rest fsp dw48 dw56 dw64 Rest).symm

theorem v2hsf_fsp_1936_split_1_7_rest (fsp dw48 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1936#64) ↦₆₄ dw48) ∗ Rest =
      ((fsp + 1936#64) ↦₈ loByte dw48) ∗ ((fsp + 1937#64) ↦ₛ EncoderFromPb.hiBytes7 dw48) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1936#64) dw48
  have ha1 : (fsp + 1936#64) + 1#64 = fsp + 1937#64 := by bv_omega
  rw [ha1] at h; rw [← sepConj_assoc, h, sepConj_assoc]

theorem v2hsf_fsp_1936_unsplit_1_7_rest (fsp dw48 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1936#64) ↦₈ loByte dw48) ∗ ((fsp + 1937#64) ↦ₛ EncoderFromPb.hiBytes7 dw48) ∗ Rest =
      ((fsp + 1936#64) ↦₆₄ dw48) ∗ Rest :=
  (v2hsf_fsp_1936_split_1_7_rest fsp dw48 Rest).symm

theorem v2hsf_fsp_584_realign_rest (fsp w584 u592 : BitVec 64) (Rest : SepProp) :
    ((fsp + 584#64) ↦₆₄ w584) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 u592) ∗ Rest =
      ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 w584) ∗
      ((fsp + 591#64) ↦₆₄ overlapWord7 w584 u592) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 584#64) w584 u592
  have ha8 : (fsp + 584#64) + 8#64 = fsp + 592#64 := by bv_omega
  have ha7 : (fsp + 584#64) + 7#64 = fsp + 591#64 := by bv_omega
  rw [ha8, ha7] at h; rw [← sepConj_assoc, h, sepConj_assoc]

theorem v2hsf_fsp_584_unrealign_midQ128_rest (fsp dw48 dw56 dw64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64)) ∗
      ((fsp + 591#64) ↦₆₄ dw64) ∗ Rest =
    ((fsp + 584#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) ∗
      ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (dw64 >>> 8)) ∗ Rest := by
  have h := (v2hsf_fsp_584_realign_rest fsp ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64)
    (dw64 >>> 8) Rest).symm
  rwa [v1_overlapWord7_midQ128_lsr8 dw48 dw56 dw64] at h

theorem v2hsf_fsp_1888_entails_epilogue (fsp dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328) :
    ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
      ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
      ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
      ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
      ((fsp + 1920#64) ↦₆₄ dw32) ∗ memRegion (fsp + 1928#64) 376 := by
  have hq1888 : ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) =
      ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) := by
    have ha : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ dw16) ∗ ((fsp + 1912#64) ↦₆₄ dw24) =
      ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hm376 :
      ((fsp + 1928#64) ↦₆₄ dw40) ∗ ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗
        ((fsp + 1952#64) ↦₆₄ dw64) ∗ ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (bs328_entails_memRegion_328 _ dbs328 hdbs328) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8)) ∗
    (((fsp + 1904#64) ↦₆₄ dw16) ∗ ((fsp + 1912#64) ↦₆₄ dw24)) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗
    (((fsp + 1928#64) ↦₆₄ dw40) ∗ ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗
     ((fsp + 1952#64) ↦₆₄ dw64) ∗ ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x21_add_137 (fsp : BitVec 64) : (fsp + 1392#64) + 137#64 = fsp + 1529#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x21_add_137_sext (fsp : BitVec 64) : (fsp + 1392#64) + (137#64).signExtend 64 = fsp + 1529#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_221 (fsp : BitVec 64) : (fsp + 1264#64) + 221#64 = fsp + 1485#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_221_sext (fsp : BitVec 64) : (fsp + 1264#64) + (221#64).signExtend 64 = fsp + 1485#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_217 (fsp : BitVec 64) : (fsp + 1264#64) + 217#64 = fsp + 1481#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_217_sext (fsp : BitVec 64) : (fsp + 1264#64) + (217#64).signExtend 64 = fsp + 1481#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_141 (fsp : BitVec 64) : (fsp + 1264#64) + 141#64 = fsp + 1405#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_141_sext (fsp : BitVec 64) : (fsp + 1264#64) + (141#64).signExtend 64 = fsp + 1405#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_241 (fsp : BitVec 64) : (fsp + 1264#64) + 241#64 = fsp + 1505#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_241_sext (fsp : BitVec 64) : (fsp + 1264#64) + (241#64).signExtend 64 = fsp + 1505#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_137 (fsp : BitVec 64) : (fsp + 1264#64) + 137#64 = fsp + 1401#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x15_add_137_sext (fsp : BitVec 64) : (fsp + 1264#64) + (137#64).signExtend 64 = fsp + 1401#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x23_add_39 (fsp : BitVec 64) : (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x23_add_39_sext (fsp : BitVec 64) : (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x23_add_15 (fsp : BitVec 64) : (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_x23_add_15_sext (fsp : BitVec 64) : (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel

theorem v2hsf_fsp_1400_split_rest (fsp w0 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₆₄ w0) ∗ Rest =
      ((fsp + 1400#64) ↦₈ w0.extractLsb' 0 8) ∗ ((fsp + 1401#64) ↦₃₂ w0.extractLsb' 8 32) ∗
      ((fsp + 1405#64) ↦₁₆ w0.extractLsb' 40 16) ∗ ((fsp + 1407#64) ↦₈ w0.extractLsb' 56 8) ∗ Rest := by
  have h := v1_pointsTo64_split_1_4_2_1 (fsp + 1400#64) w0
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h; rw [h, sepConj_assoc, sepConj_assoc, sepConj_assoc]

theorem v2hsf_fsp_1400_unsplit_rest (fsp w0 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ w0.extractLsb' 0 8) ∗ ((fsp + 1401#64) ↦₃₂ w0.extractLsb' 8 32) ∗
      ((fsp + 1405#64) ↦₁₆ w0.extractLsb' 40 16) ∗ ((fsp + 1407#64) ↦₈ w0.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1400#64) ↦₆₄ w0) ∗ Rest := (v2hsf_fsp_1400_split_rest fsp w0 Rest).symm

theorem v2hsf_fsp_1480_split_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1480#64) ↦₆₄ w80) ∗ Rest =
      ((fsp + 1480#64) ↦₈ w80.extractLsb' 0 8) ∗ ((fsp + 1481#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1485#64) ↦₁₆ w80.extractLsb' 40 16) ∗ ((fsp + 1487#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest := by
  have h := v1_pointsTo64_split_1_4_2_1 (fsp + 1480#64) w80
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h; rw [h, sepConj_assoc, sepConj_assoc, sepConj_assoc]

theorem v2hsf_fsp_1480_unsplit_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1480#64) ↦₈ w80.extractLsb' 0 8) ∗ ((fsp + 1481#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1485#64) ↦₁₆ w80.extractLsb' 40 16) ∗ ((fsp + 1487#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1480#64) ↦₆₄ w80) ∗ Rest := (v2hsf_fsp_1480_split_rest fsp w80 Rest).symm

theorem v2hsf_fsp_1504_realign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1504#64) ↦₆₄ w104) ∗ ((fsp + 1512#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 1504#64) ↦₈ loByte w104) ∗ ((fsp + 1505#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 1513#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 1504#64) w104 w112
  have ha8 : (fsp + 1504#64) + 8#64 = fsp + 1512#64 := by bv_omega
  have ha1 : (fsp + 1504#64) + 1#64 = fsp + 1505#64 := by bv_omega
  have ha9 : (fsp + 1504#64) + 9#64 = fsp + 1513#64 := by bv_omega
  rw [ha8, ha1, ha9] at h; exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hsf_fsp_1504_unrealign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1504#64) ↦₈ loByte w104) ∗ ((fsp + 1505#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 1513#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest =
      ((fsp + 1504#64) ↦₆₄ w104) ∗ ((fsp + 1512#64) ↦₆₄ w112) ∗ Rest :=
  (v2hsf_fsp_1504_realign_rest fsp w104 w112 Rest).symm

theorem v2hsf_fsp_1528_realign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₆₄ w128) ∗ ((fsp + 1536#64) ↦₆₄ w136) ∗ ((fsp + 1544#64) ↦₆₄ w144) ∗ Rest =
      ((fsp + 1528#64) ↦₈ loByte w128) ∗
      ((fsp + 1529#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 1537#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 1545#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest := by
  have h := v1_triple64_eq_byte_q128_tail7 (fsp + 1528#64) w128 w136 w144
  have ha8 : (fsp + 1528#64) + 8#64 = fsp + 1536#64 := by bv_omega
  have ha16 : (fsp + 1528#64) + 16#64 = fsp + 1544#64 := by bv_omega
  have ha1 : (fsp + 1528#64) + 1#64 = fsp + 1529#64 := by bv_omega
  have ha17 : (fsp + 1528#64) + 17#64 = fsp + 1545#64 := by bv_omega
  have ha1537 : (fsp + 1529#64) + 8#64 = fsp + 1537#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1528#64) ↦₈ loByte w128) ∗ ((fsp + 1529#64) ↦₁₂₈ v1_midQ128 w128 w136 w144) ∗
    ((fsp + 1545#64) ↦ₛ EncoderFromPb.hiBytes7 w144) at h
  unfold pointsTo128 at h; rw [ha1537] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hsf_fsp_1528_unrealign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₈ loByte w128) ∗
      ((fsp + 1529#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 1537#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 1545#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest =
      ((fsp + 1528#64) ↦₆₄ w128) ∗ ((fsp + 1536#64) ↦₆₄ w136) ∗ ((fsp + 1544#64) ↦₆₄ w144) ∗ Rest :=
  (v2hsf_fsp_1528_realign_rest fsp w128 w136 w144 Rest).symm

theorem v2hsf_fsp_1528_split_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₆₄ w128) ∗ Rest =
      ((fsp + 1528#64) ↦₈ loByte w128) ∗ ((fsp + 1529#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1528#64) w128
  have ha : (fsp + 1528#64) + 1#64 = fsp + 1529#64 := by bv_omega
  rw [ha] at h; rw [h, sepConj_assoc]

theorem v2hsf_fsp_1528_unsplit_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₈ loByte w128) ∗ ((fsp + 1529#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest =
      ((fsp + 1528#64) ↦₆₄ w128) ∗ Rest := (v2hsf_fsp_1528_split_1_7_rest fsp w128 Rest).symm

theorem v2hsf_fsp_880_realign_64_rest (fsp w880 w888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗ ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8] at h; rw [← sepConj_assoc, h, sepConj_assoc]

theorem v2hsf_fsp_1400_entails_memRegion_392 (fsp w1784 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    v1_encCellsAt (fsp + 1392#64) bs ∗ ((fsp + 1784#64) ↦₆₄ w1784) ⊢ memRegion (fsp + 1400#64) 392 := by
  rw [← v1_bs384_eq_encCells bs hbs (fsp + 1392#64)]
  have ha1400 : (fsp + 1392#64) + 8#64 = fsp + 1400#64 := by bv_omega
  rw [ha1400]
  have hbs384 : ((fsp + 1400#64) ↦ₛ bs) ⊢ memRegion (fsp + 1400#64) 384 :=
    hbs ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1400#64) bs
  exact collapse_top (collapse_step hbs384 (Drop.pointsTo64_entails_memRegion _ _))

theorem v2hsf_fsp_1400_entails_memRegion_392_rest (fsp w1784 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (Rest : SepProp) :
    v1_encCellsAt (fsp + 1392#64) bs ∗ ((fsp + 1784#64) ↦₆₄ w1784) ∗ Rest ⊢ memRegion (fsp + 1400#64) 392 ∗ Rest := by
  rw [← sepConj_assoc]; exact sepConj_mono_left (v2hsf_fsp_1400_entails_memRegion_392 fsp w1784 bs hbs)

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_reconstruct_w0 (w0 : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.extractLsb' 8 32 w0) <<< 8 |||
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 w0) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 w0) <<< 16))) <<< 40 |||
      BitVec.zeroExtend 64 (loByte w0)) = w0 := by unfold loByte; bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsf_orr_x27_w80 (w80 : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.extractLsb' 8 32 w80) |||
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 w80) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 w80) <<< 16))) <<< 32) =
      (w80.extractLsb' 8 56).zeroExtend 64 := by bv_kernel

attribute [local simp, local arm64_norm, local wp_norm]
  v1_w80_d97 v1_w80_h101 v1_w80_b103 v1_zext32_setWidth8

theorem v2hsf_out_536_realign (out dw48 dw56 dw64 : BitVec 64) :
    ((out + 536#64) ↦₈ (((loByte dw48).zeroExtend 32).setWidth 8)) ∗
      ((out + 537#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) (dw64 >>> 8))) =
      ((out + 536#64) ↦₆₄ dw48) ∗ ((out + 544#64) ↦₆₄ dw56) ∗ ((out + 552#64) ↦₆₄ dw64) := by
  rw [v1_zext32_setWidth8, v1_overlapWord7_midQ128_lsr8 dw48 dw56 dw64]
  have h := (v1_triple64_eq_byte_q128_tail7 (out + 536#64) dw48 dw56 dw64).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h ⊢; exact h

theorem v2hsf_unchunkedEkSentAt_408_pack (A : RustAlloc) {F : ShaCompress}
    (out l1 pa1 l2 pa2 cap_dk ptr_dk len_dk ep : BitVec 64) (dk rootKey macKey : List (BitVec 8))
    (hdk : len_dk = BitVec.ofNat 64 dk.length) (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length) :
    ((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
    ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
    ((out + 456#64) ↦₆₄ cap_dk) ∗ ((out + 464#64) ↦₆₄ ptr_dk) ∗ ((out + 472#64) ↦₆₄ len_dk) ∗
    ((out + 480#64) ↦₆₄ ep) ∗
    vecU8Payload A cap_dk ptr_dk dk ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ⊢
      unchunkedEkSentAt A (F := F) (out + 408#64)
        { auth := { rootKey := rootKey, macKey := macKey }, dk := dk, epoch := ep } := by
  subst hdk hl1 hl2; dsimp only [unchunkedEkSentAt, authenticatorAt]
  have hrk_v := vecU8_of_header_payload A (out + 408#64) (BitVec.ofNat 64 rootKey.length) pa1 rootKey
  have hmk_v := vecU8_of_header_payload A (out + 432#64) (BitVec.ofNat 64 macKey.length) pa2 macKey
  have hdk_v := vecU8_of_header_payload A (out + 456#64) cap_dk ptr_dk dk
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk_v hmk_v hdk_v ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 408#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗ ((out + 416#64) ↦₆₄ pa1) ∗
     ((out + 424#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗ vecU8Payload A (BitVec.ofNat 64 rootKey.length) pa1 rootKey) ∗
    (((out + 432#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ ((out + 440#64) ↦₆₄ pa2) ∗
     ((out + 448#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ vecU8Payload A (BitVec.ofNat 64 macKey.length) pa2 macKey) ∗
    (((out + 456#64) ↦₆₄ cap_dk) ∗ ((out + 464#64) ↦₆₄ ptr_dk) ∗
     ((out + 472#64) ↦₆₄ BitVec.ofNat 64 dk.length) ∗ vecU8Payload A cap_dk ptr_dk dk) ∗
    ((out + 480#64) ↦₆₄ ep) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono hrk_v (sepConj_mono hmk_v (sepConj_mono_left hdk_v))) (Entails.of_eq (by ac_rfl))

theorem v2hsf_epilogueOutFull_entails_headerSent (A : RustAlloc) {F : ShaCompress}
    (out tag l1 pa1 l2 pa2 cap_dk ptr_dk len_dk ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (enc : PolyEncoder) (P_enc_heap : SepProp)
    (henc_reloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
      (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢ polyEncoderAt A (out + 8#64) enc)
    (dk rootKey macKey : List (BitVec 8)) (hdk : len_dk = BitVec.ofNat 64 dk.length)
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328) (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hdec_reloc : ((out + 488#64) ↦₆₄ dw0) ∗ (((out + 488#64) + 8#64) ↦₆₄ dw8) ∗
      (((out + 488#64) + 16#64) ↦₆₄ dw16) ∗ (((out + 488#64) + 24#64) ↦₆₄ dw24) ∗
      (((out + 488#64) + 32#64) ↦₆₄ dw32) ∗ (((out + 488#64) + 40#64) ↦₆₄ dw40) ∗
      (((out + 488#64) + 48#64) ↦₆₄ dw48) ∗ (((out + 488#64) + 56#64) ↦₆₄ dw56) ∗
      (((out + 488#64) + 64#64) ↦₆₄ dw64) ∗ (((out + 488#64) + 72#64) ↦ₛ dbs328) ∗
      P_dec_heap ⊢ polyDecoderAt A (out + 488#64) dec)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out 4#64 tag (v1_wordAt bs 0) (v1_wordAt bs 8)
      (v1_wordAt bs 16) (v1_wordAt bs 24) (v1_wordAt bs 32) (v1_wordAt bs 40)
      (v1_wordAt bs 48) (v1_wordAt bs 56) (v1_wordAt bs 64) (v1_wordAt bs 72)
      ((v1_wordAt bs 80).extractLsb' 0 8) ((v1_wordAt bs 80).extractLsb' 8 32)
      ((v1_wordAt bs 80).extractLsb' 40 16) ((v1_wordAt bs 80).extractLsb' 56 8)
      (v1_wordAt bs 88) (v1_wordAt bs 96) (loByte (v1_wordAt bs 104))
      (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8))
      (v1_wordAt bs 120) (((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
      (overlapWord7
        ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
        (v1_wordAt bs 144 >>> 8))
      (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
      (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
      (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
      (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376) (hi32 ++ enc.idx)
      l1 pa1 l1 l2 pa2 l2 cap_dk ptr_dk len_dk ep dw0 dw8 dw16 dw24 dw32 dw40
      (((loByte dw48).zeroExtend 32).setWidth 8) (v1_midQ128 dw48 dw56 dw64)
      (overlapWord7 ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) (dw64 >>> 8))
      dbs328 q888 q904 w920 ∗
      P_enc_heap ∗ P_dec_heap ∗
      vecU8Payload A cap_dk ptr_dk dk ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.headerSent
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, dk := dk, epoch := ep },
          sending_ek := enc, receiving_ct1 := dec })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedHeaderSentAt]
  have hbs_eq := v1_out_16_to_400_eq_bs out bs hbs
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbs_eq
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at henc_reloc hdec_reloc ⊢
  unfold epilogueOutFull
  have huc := v2hsf_unchunkedEkSentAt_408_pack A (F := F) out
    l1 pa1 l2 pa2 cap_dk ptr_dk len_dk ep dk rootKey macKey hdk hl1 hl2
  have hdec' :
      ((out + 488#64) ↦₆₄ dw0) ∗ ((out + 496#64) ↦₆₄ dw8) ∗ ((out + 504#64) ↦₆₄ dw16) ∗
      ((out + 512#64) ↦₆₄ dw24) ∗ ((out + 520#64) ↦₆₄ dw32) ∗ ((out + 528#64) ↦₆₄ dw40) ∗
      (((out + 536#64) ↦₈ (((loByte dw48).zeroExtend 32).setWidth 8)) ∗
       ((out + 537#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
       ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) (dw64 >>> 8)))) ∗
      ((out + 560#64) ↦ₛ dbs328) ∗ P_dec_heap ⊢ polyDecoderAt A (out + 488#64) dec := by
    rw [v2hsf_out_536_realign out dw48 dw56 dw64]; simpa only [sepConj_assoc] using hdec_reloc
  have htail := epilogueOut_tail_888_entails_40 out q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 4#64) ∗ (((out + 8#64) ↦₆₄ tag) ∗
     (((out + 16#64) ↦₆₄ v1_wordAt bs 0) ∗ ((out + 24#64) ↦₆₄ v1_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v1_wordAt bs 16) ∗ ((out + 40#64) ↦₆₄ v1_wordAt bs 24) ∗
      ((out + 48#64) ↦₆₄ v1_wordAt bs 32) ∗ ((out + 56#64) ↦₆₄ v1_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v1_wordAt bs 48) ∗ ((out + 72#64) ↦₆₄ v1_wordAt bs 56) ∗
      ((out + 80#64) ↦₆₄ v1_wordAt bs 64) ∗ ((out + 88#64) ↦₆₄ v1_wordAt bs 72) ∗
      (((out + 96#64) ↦₈ (v1_wordAt bs 80).extractLsb' 0 8) ∗ ((out + 97#64) ↦₃₂ (v1_wordAt bs 80).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v1_wordAt bs 80).extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ (v1_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v1_wordAt bs 88) ∗ ((out + 112#64) ↦₆₄ v1_wordAt bs 96) ∗
      (((out + 120#64) ↦₈ loByte (v1_wordAt bs 104)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v1_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄ (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄ overlapWord7
         ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
         (v1_wordAt bs 144 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((out + 184#64) ↦₁₂₈ v1_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((out + 216#64) ↦₁₂₈ v1_quadAt bs 200) ∗
      ((out + 232#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((out + 248#64) ↦₁₂₈ v1_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((out + 280#64) ↦₁₂₈ v1_quadAt bs 264) ∗
      ((out + 296#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((out + 312#64) ↦₁₂₈ v1_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((out + 344#64) ↦₁₂₈ v1_quadAt bs 328) ∗
      ((out + 360#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((out + 376#64) ↦₁₂₈ v1_quadAt bs 360) ∗
      ((out + 392#64) ↦₆₄ v1_wordAt bs 376)) ∗
     ((out + 400#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap) ∗
    (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
     ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
     ((out + 456#64) ↦₆₄ cap_dk) ∗ ((out + 464#64) ↦₆₄ ptr_dk) ∗ ((out + 472#64) ↦₆₄ len_dk) ∗
     ((out + 480#64) ↦₆₄ ep) ∗
     vecU8Payload A cap_dk ptr_dk dk ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey) ∗
    (((out + 488#64) ↦₆₄ dw0) ∗ ((out + 496#64) ↦₆₄ dw8) ∗ ((out + 504#64) ↦₆₄ dw16) ∗
     ((out + 512#64) ↦₆₄ dw24) ∗ ((out + 520#64) ↦₆₄ dw32) ∗ ((out + 528#64) ↦₆₄ dw40) ∗
     (((out + 536#64) ↦₈ (((loByte dw48).zeroExtend 32).setWidth 8)) ∗
      ((out + 537#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) (dw64 >>> 8)))) ∗
     ((out + 560#64) ↦ₛ dbs328) ∗ P_dec_heap) ∗
    (((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono henc_reloc (sepConj_mono huc (sepConj_mono hdec' htail)))

theorem v2hsf_memRegion_64_32_split (fsp : BitVec 64) :
    memRegion (fsp + 64#64) 32 ⊢ memRegion (fsp + 64#64) 28 ∗ (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) :=
  split_top (split_step (Entails.refl _) (mem32_entails _))

theorem v2hsf_memRegion_104_72_split (fsp : BitVec 64) :
    memRegion (fsp + 104#64) 72 ⊢
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗ (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗ memRegion (fsp + 128#64) 32 ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗ memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) :=
  split_top <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| mem32_entails _

theorem v2hsf_memRegion_240_1032_split (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1032 ⊢
      memRegion (fsp + 240#64) 328 ∗ memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, (fsp + 576#64) ↦₁₂₈ q576) ∗
      ((∃∗ w592 : BitVec 64, (fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, (fsp + 608#64) ↦₁₂₈ q608) ∗ (∃∗ q624 : BitVec 128, (fsp + 624#64) ↦₁₂₈ q624) ∗
      (∃∗ q640 : BitVec 128, (fsp + 640#64) ↦₁₂₈ q640) ∗ (∃∗ q656 : BitVec 128, (fsp + 656#64) ↦₁₂₈ q656) ∗
      (∃∗ q672 : BitVec 128, (fsp + 672#64) ↦₁₂₈ q672) ∗ (∃∗ q688 : BitVec 128, (fsp + 688#64) ↦₁₂₈ q688) ∗
      (∃∗ q704 : BitVec 128, (fsp + 704#64) ↦₁₂₈ q704) ∗ (∃∗ q720 : BitVec 128, (fsp + 720#64) ↦₁₂₈ q720) ∗
      (∃∗ q736 : BitVec 128, (fsp + 736#64) ↦₁₂₈ q736) ∗ (∃∗ q752 : BitVec 128, (fsp + 752#64) ↦₁₂₈ q752) ∗
      (∃∗ q768 : BitVec 128, (fsp + 768#64) ↦₁₂₈ q768) ∗ (∃∗ q784 : BitVec 128, (fsp + 784#64) ↦₁₂₈ q784) ∗
      (∃∗ q800 : BitVec 128, (fsp + 800#64) ↦₁₂₈ q800) ∗ (∃∗ q816 : BitVec 128, (fsp + 816#64) ↦₁₂₈ q816) ∗
      (∃∗ w832 : BitVec 64, (fsp + 832#64) ↦₆₄ w832) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, (fsp + 848#64) ↦₁₂₈ q848) ∗
      ((∃∗ w864 : BitVec 64, (fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, (fsp + 880#64) ↦₆₄ w880) ∗
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ memRegion (fsp + 895#64) 377) :=
  split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <| split_step (mem64_entails _) <|
    memRegion_loBytes7_gap_at fsp 888#64 895#64 376

theorem v2hsf_epilogueStackGaps_pack (fsp tag la3 pa3 pa2 ca1 dw0 pa1 : BitVec 64) :
    memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ tag) ∗ memRegion (fsp + 64#64) 28 ∗
    ((fsp + 96#64) ↦₆₄ la3) ∗ memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 168#64) 4 ∗
    ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
    ((fsp + 216#64) ↦₆₄ dw0) ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 377 ∗
    ((fsp + 1272#64) ↦₆₄ pa1) ∗ memRegion (fsp + 1280#64) 120 ∗ memRegion (fsp + 1400#64) 392 ∗
    memRegion (fsp + 1792#64) 96 ∗ memRegion (fsp + 1928#64) 376 ⊢ epilogueStackGaps fsp := by
  unfold epilogueStackGaps
  have h92 : memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ tag) ∗ memRegion (fsp + 64#64) 28 ⊢ memRegion fsp 92 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h96 : ((fsp + 96#64) ↦₆₄ la3) ⊢ memRegion (fsp + 96#64) 8 := Drop.pointsTo64_entails_memRegion _ _
  have h176 : ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _
  have h200 : ((fsp + 200#64) ↦₆₄ ca1) ⊢ memRegion (fsp + 200#64) 8 := Drop.pointsTo64_entails_memRegion _ _
  have h216 : ((fsp + 216#64) ↦₆₄ dw0) ⊢ memRegion (fsp + 216#64) 8 := Drop.pointsTo64_entails_memRegion _ _
  have h895 : memRegion (fsp + 895#64) 377 ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
      memRegion (fsp + 1280#64) 120 ∗ memRegion (fsp + 1400#64) 392 ∗ memRegion (fsp + 1792#64) 96 ⊢
      memRegion (fsp + 895#64) 993 :=
    collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ tag) ∗ memRegion (fsp + 64#64) 28) ∗
    ((fsp + 96#64) ↦₆₄ la3) ∗ memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 168#64) 4 ∗
    (((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2)) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
    ((fsp + 216#64) ↦₆₄ dw0) ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
    (memRegion (fsp + 895#64) 377 ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
     memRegion (fsp + 1280#64) 120 ∗ memRegion (fsp + 1400#64) 392 ∗ memRegion (fsp + 1792#64) 96) ∗
    memRegion (fsp + 1928#64) 376 by ac_rfl)) ?_
  exact sepConj_mono h92 (sepConj_mono h96 (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left h895)))))))))))

end CryptoVerification.SpqrV1.States.FromPb
