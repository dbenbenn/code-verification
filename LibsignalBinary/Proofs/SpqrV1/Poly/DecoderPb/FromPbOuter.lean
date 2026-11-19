/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInner -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Inner Chunk Loop and Outer Slot Steps

**Checked by Lean.**

Proves the 4-byte big-endian point decoding loop (`+304..+672`), outer-iteration completion
(`+672 → +204 / +876`), OOM panic block (`+1288`), and valid / invalid outer-loop steps (`+204`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Drop (vecPtOf vecPtListOf
  sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf)
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L37a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  fp_add_448_sub_32 fp_add_448_sub_32_int
  fp_add_448_sub_24 fp_add_448_sub_24_int
  fp_add_448_sub_16 fp_add_448_sub_16_int
  truncate16_truncate32 and_ffff_truncate32 and_ffff_zeroExtend64_truncate32
  ofNat_add_one madd_24_eq

@[simp, local arm64_norm, local wp_norm]
theorem fsp_add_416_add_8 (fsp : BitVec 64) :
    fsp + 416#64 + 8#64 = fsp + 424#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fsp_add_416_add_16 (fsp : BitVec 64) :
    fsp + 416#64 + 16#64 = fsp + 432#64 := by bv_omega

/-! ## 4-Byte Big-Endian Point Decoding and Inner Loop (`+304 -> +672`) -/

theorem pointsToBytes_four_cons (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    (a ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) =
      (a ↦₃₂ (b3 ++ (b2 ++ (b1 ++ b0)))) ∗ ((a + 4#64) ↦ₛ rest) := by
  rw [pointsTo32_eq_pointsToBytes]
  have hsplit : (b0 :: b1 :: b2 :: b3 :: rest) = [b0, b1, b2, b3] ++ rest := rfl
  conv_lhs => rw [hsplit, pointsToBytes_append]
  dsimp only [List.length_cons, List.length_nil]
  congr 2
  simp only [unpack32, List.cons.injEq, and_true]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem bv64_mul4_succ_sub_four (n : Nat) :
    BitVec.ofNat 64 (4 * (n + 1)) - 4#64 = BitVec.ofNat 64 (4 * n) := by
  have h : 4 * (n + 1) = 4 * n + 4 := by omega
  rw [h, BitVec.ofNat_add]
  bv_omega

/-- A 24-byte `Default::default()` `SortedSet<Pt>` header `(cap = 0, ptr = 2, len = 0)`. -/
@[expose] def emptySlotAt (addr : BitVec 64) : SepProp :=
  (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 2#64) ∗ ((addr + 16#64) ↦₆₄ 0#64)

/-- `n` consecutive `emptySlotAt` headers starting at `base`. -/
@[expose] def emptySlotsAt (base : BitVec 64) (n : Nat) : SepProp :=
  arrayAt (fun _ a => emptySlotAt a) 24 base (List.replicate n ())

theorem emptySlotsAt_zero (base : BitVec 64) :
    emptySlotsAt base 0 = emp := by
  simp [emptySlotsAt, arrayAt]

theorem emptySlotsAt_succ (base : BitVec 64) (n : Nat) :
    emptySlotsAt base (n + 1) =
      emptySlotAt base ∗ emptySlotsAt (base + 24#64) n := by
  simp [emptySlotsAt, List.replicate_succ, arrayAt_cons]

theorem emptySlotsAt_off_succ (base : BitVec 64) (i n : Nat) :
    emptySlotsAt (base + BitVec.ofNat 64 (24 * i)) (n + 1) =
      emptySlotAt (base + BitVec.ofNat 64 (24 * i)) ∗
        emptySlotsAt (base + BitVec.ofNat 64 (24 * (i + 1))) n := by
  rw [emptySlotsAt_succ, off_24_succ]

theorem emptySlotAt_entails_sortedSetPtOf (A : RustAlloc) (addr : BitVec 64) :
    emptySlotAt addr ⊢ sortedSetPtOf A addr { vec := [] } := by
  rw [sortedSetPtOf_eq_vecPtOf]
  refine Entails.trans ?_ (vecPtOf_intro A addr 0#64 2#64 [])
  unfold emptySlotAt vecPtTail
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 4 < 2 ^ 63 ∧
      0 * 4 < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 := by decide
  dsimp only [List.length_nil, arrayAt_nil, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_emp, emp_sepConj]
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem emptySlotsAt_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      emptySlotsAt base n ⊢ sortedSetPtListOf A base (List.replicate n { vec := [] })
  | 0, base => by
    simp [emptySlotsAt, sortedSetPtListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    rw [emptySlotsAt_succ]
    change emptySlotAt base ∗ emptySlotsAt (base + 24#64) n ⊢
      sortedSetPtOf A base { vec := [] } ∗
        sortedSetPtListOf A (base + 24#64) (List.replicate n { vec := [] })
    exact sepConj_mono (emptySlotAt_entails_sortedSetPtOf A base)
      (emptySlotsAt_entails_sortedSetPtListOf A n (base + 24#64))

theorem tempVecPtAt_into_sortedSetPtOf (A : RustAlloc) (fsp addr cap ptr : BitVec 64)
    (s : SortedSetPt)
    (hle : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hpos : 0 < cap.toNat) (hptr : ptr ≠ 0) :
    (tempVecPtAt A fsp cap ptr s ∗
      (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
      ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ⊢
      sortedSetPtOf A addr s ∗
        ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 424#64) ↦₆₄ ptr) ∗
        ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) := by
  rw [sortedSetPtOf_eq_vecPtOf]
  unfold tempVecPtAt ptSliceAt
  rw [fsp_add_416_add_8, fsp_add_416_add_16]
  have hcap_ne : cap ≠ 0 := by
    intro hc; subst hc
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    omega
  have hp : s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧
      s.vec.length * 4 < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, by omega, hptr⟩
  have htail :
      (A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)) ⊢
      vecPtTail A cap ptr s.vec.length := by
    unfold vecPtTail
    simp only [hcap_ne, ↓reduceIte]
    exact Entails.pure_right hp (Entails.refl _)
  have hintro := Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right htail))))
    (vecPtOf_intro A addr cap ptr s.vec)
  refine Entails.trans ?_ (sepConj_mono_left hintro)
  exact Entails.of_eq (by ac_rfl)

abbrev fromPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem bv64_lsr2_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem and_neg4_of_mod4_zero {n : Nat} (hmod : n % 4 = 0) :
    (BitVec.ofNat 64 n) &&& 18446744073709551612#64 = BitVec.ofNat 64 n := by
  have hdiv : n = (n / 4) * 4 := by omega
  rw [hdiv, BitVec.ofNat_mul]
  change (BitVec.ofNat 64 (n / 4) * 4#64) &&& 18446744073709551612#64 =
    BitVec.ofNat 64 (n / 4) * 4#64
  bv_kernel

theorem and_3_of_mod4 {n : Nat} (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n) &&& 3#64 == 0#64) = decide (n % 4 = 0) := by
  have h1 : (BitVec.ofNat 64 n) &&& 3#64 = BitVec.ofNat 64 (n % 4) := by
    apply BitVec.eq_of_toNat_eq
    have h3 : (3#64 : BitVec 64).toNat = 2 ^ 2 - 1 := rfl
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h3,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n % 4 < 2 ^ 64)]
  rw [h1]
  by_cases hm : n % 4 = 0
  · simp [hm]
  · simp only [hm, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n % 4 < 2 ^ 64)] at ht
    exact hm ht

/-! ## `vecU8` Expose / Reassemble -/

/-- Remaining buffer and allocator block of a `Vec<u8>` after splitting out `(ptr ↦ₛ bs)`. -/
@[expose] def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len))

theorem vecU8_expose (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          vecU8Tail A cap ptr bs.length := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Tail
  refine Entails.trans (Entails.of_eq (show
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  have hlen : bs.length < 2 ^ 63 := by omega
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl))
  apply Entails.pure_right ⟨hlen, hptr⟩
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8_intro (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      vecU8Tail A cap ptr bs.length) ⊢
    vecU8 A v bs := by
  refine Entails.trans ?_ (vecU8At_entails_vecU8 A v cap ptr bs)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Tail
  refine Entails.trans (Entails.of_eq (show
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl))
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem tempVecPtAt_empty_intro (A : RustAlloc) (fsp : BitVec 64) (n : Nat) (ptr : BitVec 64)
    (hn : 4 * (n + 1) < 2 ^ 63) :
    (((fsp + 416#64) ↦₆₄ BitVec.ofNat 64 (n + 1)) ∗
      ((fsp + 424#64) ↦₆₄ ptr) ∗
      ((fsp + 432#64) ↦₆₄ 0#64) ∗
      A.live ptr (4 * (n + 1)) 2 ∗
      memRegion ptr (4 * (n + 1))) =
    tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr { vec := [] } := by
  unfold tempVecPtAt ptSliceAt
  rw [fsp_add_416_add_8, fsp_add_416_add_16]
  have htoNat : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmul : (n + 1) * 4 = 4 * (n + 1) := by omega
  dsimp only [List.length_nil]
  simp only [htoNat, Nat.sub_zero, hmul, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, arrayAt_nil, sepConj_emp]
  ac_rfl

theorem stackAt_zero_of_aligned {sp : BitVec 64} (hal : (sp &&& 15#64 == 0#64) = true) :
    stackAt sp 0 = emp := by
  unfold stackAt
  simp [hal, ProofLib.memRegion_zero]

theorem stackAt_split_zero_right {sp : BitVec 64} (hal : (sp &&& 15#64 == 0#64) = true) (sz : Nat) :
    stackAt sp sz = stackAt sp sz ∗ stackAt sp 0 := by
  rw [stackAt_zero_of_aligned hal, sepConj_emp]

/-! ## OOM Panic Helper (`+0x508 = +1288`) and Outer Loop (`+204`) -/

end CryptoVerification.SpqrV1.Poly.DecoderPb

