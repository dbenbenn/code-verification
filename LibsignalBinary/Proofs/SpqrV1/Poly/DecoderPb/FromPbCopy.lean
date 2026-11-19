/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Success Copy and Deallocation

**Checked by Lean.**

Proves the 16-slot `SortedSet<Pt>` header `memcpy` relocation, unrolled 16-slot `Vec<u8>`
deallocation (`+904..+1236`), and success exit (`+876 → s0.lr`) of `<PolyDecoder>::from_pb`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `Vec<Pt>` Array Header Relocation (`memcpy` of 16 `Vec<Pt>` Slots, 384 Bytes) -/

/-- 24-byte serialized `Vec` header `(cap, ptr, len)`. -/
@[expose] def vecHeaderBytesOf (pin : VecPin) (len : Nat) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)

@[simp] theorem length_vecHeaderBytesOf (pin : VecPin) (len : Nat) :
    (vecHeaderBytesOf pin len).length = 24 := rfl

/-- Concatenated 24-byte `Vec` headers for `pins` and `vecs`. -/
@[expose] def vecHeadersBytesOf : List VecPin → List (List Pt) → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, cs :: vecs => vecHeaderBytesOf pin cs.length ++ vecHeadersBytesOf pins vecs

theorem length_vecHeadersBytesOf (pins : List VecPin) (vecs : List (List Pt))
    (h : pins.length = vecs.length) :
    (vecHeadersBytesOf pins vecs).length = vecs.length * 24 := by
  induction pins generalizing vecs with
  | nil =>
    cases vecs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons pin pins ih =>
    cases vecs with
    | nil => simp at h
    | cons cs vecs =>
      simp only [List.length_cons] at h
      have hih := ih vecs (Nat.succ.inj h)
      simp only [vecHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, hih, List.length_cons]
      omega

/-- Separating conjunction of `vecBuf A ptStride ptAlign ptAt` across `pins` and `vecs`. -/
@[expose] def vecPtHeapList (A : RustAlloc) : List VecPin → List (List Pt) → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, cs :: vecs =>
    vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs

theorem vecHeader_eq_pointsToBytes (a : BitVec 64) (pin : VecPin) (len : Nat) :
    vecHeader a pin.cap pin.ptr (BitVec.ofNat 64 len) =
      (a ↦ₛ vecHeaderBytesOf pin len) := by
  unfold vecHeader vecHeaderBytesOf
  rw [List.append_assoc,
      ProofLib.pointsToBytes_append a (unpack64 pin.cap)
        (unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)),
      unpack64_length,
      ProofLib.pointsToBytes_append (a + 8#64) (unpack64 pin.ptr) (unpack64 (BitVec.ofNat 64 len)),
      unpack64_length]
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h16, ← pointsTo64_eq_pointsToBytes a pin.cap,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) pin.ptr,
      ← pointsTo64_eq_pointsToBytes (a + 16#64) (BitVec.ofNat 64 len)]

theorem vecPtOf_entails_pin (A : RustAlloc) (a : BitVec 64) (cs : List Pt) :
    vecPtOf A a cs ⊢
      ∃∗ pin : VecPin,
        (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
          vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs := by
  unfold vecPtOf vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ cs.length]
  exact Entails.refl _

theorem pin_entails_vecPtOf (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (cs : List Pt) :
    (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
      vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ⊢
      vecPtOf A a cs := by
  rw [← vecHeader_eq_pointsToBytes a pin cs.length]
  unfold vecPtOf vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem vecPtListOf_entails_headers_heaps (A : RustAlloc)
    (vecs : List (List Pt)) (a : BitVec 64) :
    vecPtListOf A a vecs ⊢
      ∃∗ pins : List VecPin,
        ⌜pins.length = vecs.length⌝ ∗
          (a ↦ₛ vecHeadersBytesOf pins vecs) ∗
          vecPtHeapList A pins vecs := by
  induction vecs generalizing a with
  | nil =>
    simp only [vecPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [vecHeadersBytesOf, vecPtHeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | cons cs vecs ih =>
    simp only [vecPtListOf, arrayAt, vecHeaderBytes]
    refine Entails.trans (sepConj_mono (vecPtOf_entails_pin A a cs) (ih (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs) ∗
        (⌜pins.length = vecs.length⌝ ∗
          ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs) =
      ⌜pins.length = vecs.length⌝ ∗
        (((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (cs :: vecs).length := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    simp only [vecHeadersBytesOf, vecPtHeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    exact Entails.refl _

theorem headers_heaps_entails_vecPtListOf (A : RustAlloc)
    (pins : List VecPin) (vecs : List (List Pt)) (a : BitVec 64)
    (h : pins.length = vecs.length) :
    (a ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs ⊢
      vecPtListOf A a vecs := by
  induction pins generalizing vecs a with
  | nil =>
    cases vecs with
    | nil =>
      simp [vecHeadersBytesOf, vecPtHeapList, vecPtListOf, arrayAt, ProofLib.pointsToBytes_nil]
      exact Entails.refl _
    | cons _ _ => simp at h
  | cons pin pins ih =>
    cases vecs with
    | nil => simp at h
    | cons cs vecs =>
      simp only [List.length_cons] at h
      simp only [vecHeadersBytesOf, vecPtHeapList, vecPtListOf, arrayAt, vecHeaderBytes]
      rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
          length_vecHeaderBytesOf]
      refine Entails.trans (Entails.of_eq (show
        ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs) =
        ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs) ∗
          (((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs) by ac_rfl)) ?_
      exact sepConj_mono (pin_entails_vecPtOf A a pin cs)
        (ih vecs (a + 24#64) (Nat.succ.inj h))

/-! ## Unrolled 16-Slot `Vec<u8>` Deallocation (`+904 -> +1236`) and Success Exit (`+876 -> s0.lr`) -/

/-- `arrayAt (fun bs addr => vecU8 A addr bs) 24` step helper for slot 0 (`ptsPtr + 0`). -/
theorem vecU8_frame_entails (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) :
    vecU8 A a bs ∗ Rest ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗ Rest := by
  refine Entails.trans (sepConj_mono_left (vecU8_entails_capPtr_dealloc A a bs)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem vecU8_step_entails (A : RustAlloc) (arrA off off8 off16 : BitVec 64)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (bs : List (BitVec 8)) (Rest : SepProp) :
    vecU8 A (arrA + off) bs ∗ Rest ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗ Rest := by
  have h := vecU8_frame_entails A (arrA + off) bs Rest
  rwa [hoff8, hoff16] at h

theorem SepWP.dealloc_u8_list_cons_step {A : RustAlloc} {prog : Program} {target_pc : BitVec 64} {s : State}
    (arrA off off8 off16 offNext : BitVec 64) (n m : Nat)
    (hoff : arrA + BitVec.ofNat 64 n = arrA + off)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (hoffNext : (arrA + off) + 24#64 = arrA + offNext)
    (hm : n + 24 = m) (hbound : m ≤ 2 ^ 64)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) (Tail : SepProp) {Q : State → Prop}
    (h : ∀ cap ptr : BitVec 64,
      SepWP prog target_pc s
        ((((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗
          (memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)))
        (fun sm Pm =>
          (Pm ⊢ (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗
            memRegion (arrA + off16) 8) ∗
            memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)) ∧
          Q sm)) :
    SepWP prog target_pc s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + off) (bs :: rest) ∗ (memRegion arrA n ∗ Tail))
      (fun sm Pm =>
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ (memRegion arrA m ∗ Tail)) ∧
        Q sm) := by
  have hpre : arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + off) (bs :: rest) ∗ (memRegion arrA n ∗ Tail) =
      vecU8 A (arrA + off) bs ∗ (memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)) := by
    show (vecU8 A (arrA + off) bs ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ((arrA + off) + 24#64) rest) ∗ (memRegion arrA n ∗ Tail) = _
    rw [hoffNext]
    ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecU8_step_entails A arrA off off8 off16 hoff8 hoff16 bs _) ?_
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpost :
      (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗
        memRegion (arrA + off16) 8) ∗
        memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail) ⊢
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ (memRegion arrA m ∗ Tail) := by
    refine Entails.trans (slot_join_memRegion_at arrA off off8 off16 cap ptr n m hoff hoff8 hoff16 hm hbound _) ?_
    exact Entails.of_eq (by ac_rfl)
  exact SepWP.strengthen_entails_const hpost (h cap ptr)

@[local simp, local arm64_norm, local wp_norm]
theorem truncate8_truncate32_zeroExtend64 (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.truncate 32 (b.zeroExtend 64)) = b := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem fromPb_bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl

local macro "dealloc_u8_slot_step " ptsPtr:term:max off0:term:max off8:term:max off16:term:max off24:term:max k:term:max k24:term:max c:term:max hsp:ident : tactic =>
  `(tactic| (
    refine SepWP.dealloc_u8_list_cons_step $ptsPtr $off0 $off8 $off16 $off24 $k $k24
      rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) $c _ _ ?_
    intro cap ptr; dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [$hsp:ident]; ac_rfl) ?_; wp_done))

theorem list_length_16_elim {α : Type} {xs : List α} (h : xs.length = 16) :
    ∃ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15,
      xs = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] := by
  match xs, h with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15], _ =>
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩

theorem memRegion_400_split_ok (out : BitVec 64) :
    memRegion out 400 =
      memRegion out 384 ∗
      (∃∗ d384 : BitVec 64, (out + 384#64) ↦₆₄ d384) ∗
      (∃∗ b392 : BitVec 8, (out + 392#64) ↦₈ b392) ∗
      memRegion (out + 393#64) 7 := by
  have h392 : (out + 384#64) + 8#64 = out + 392#64 := by bv_omega
  have h393 : (out + 392#64) + 1#64 = out + 393#64 := by bv_omega
  rw [show (400 : Nat) = 384 + (8 + (1 + 7)) by rfl,
      ProofLib.memRegion_split out 384 16 (by decide),
      ProofLib.memRegion_split (out + 384#64) 8 8 (by decide), h392,
      ProofLib.memRegion_split (out + 392#64) 1 7 (by decide), h393,
      ProofLib.memRegion_eight, ProofLib.memRegion_one]

theorem u32_zeroExtend64_eq_ofNat_toNat (v : BitVec 32) :
    v.zeroExtend 64 = BitVec.ofNat 64 v.toNat := by
  bv_omega

end CryptoVerification.SpqrV1.Poly.DecoderPb
