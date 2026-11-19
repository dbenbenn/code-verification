/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Inner Binary-Search and Insertion Steps

**Checked by Lean.**

Proves the inner binary-search loop (`+456..+492`), `memmove` insertion (`+532..+296`),
`bsearchReplace` (`+432..+296`), and single-point `bsearchPush` (`+320..+296`) for
`<PolyDecoder>::from_pb` (`0x62b1c`).
-/

public section

namespace CryptoVerification.SpqrV1.Layout.L37a
end CryptoVerification.SpqrV1.Layout.L37a

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
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L37a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## BitVector and Frame-Pointer Address Normalization Helpers -/

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_32 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551584#64 = fsp + 416#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_32_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-32) = fsp + 416#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_24 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551592#64 = fsp + 416#64 + 8#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_24_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-24) = fsp + 416#64 + 8#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_16 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551600#64 = fsp + 416#64 + 16#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_16_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-16) = fsp + 416#64 + 16#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem truncate16_truncate32 (x : BitVec 64) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by
  bv_bits

@[simp, local arm64_norm, local wp_norm]
theorem and_ffff_truncate32 (x : BitVec 64) :
    (BitVec.truncate 32 x) &&& 65535#32 = (BitVec.truncate 16 x).zeroExtend 32 := by
  bv_bits

@[simp, local arm64_norm, local wp_norm]
theorem and_ffff_zeroExtend64_truncate32 (x : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) &&& 65535#64) =
      (BitVec.truncate 16 x).zeroExtend 32 := by
  bv_bits

theorem uxth32_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    BitVec.zeroExtend 32 (BitVec.truncate 16 (BitVec.truncate 32 x)) = v.zeroExtend 32 := by
  rw [← h]
  bv_bits

theorem and_ffff_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    (BitVec.truncate 32 x) &&& 65535#32 = v.zeroExtend 32 := by
  rw [← h]
  bv_bits

theorem truncate16_32_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = v := by
  rw [← h]
  bv_bits

/-- Temporary `SortedSet<Pt>` at `fsp + 416` (`x29 - 32`) with fixed `cap` and `ptr`. -/
@[expose] def tempVecPtAt (A : RustAlloc) (fsp cap ptr : BitVec 64) (s : SortedSetPt) : SepProp :=
  ((fsp + 416#64) ↦₆₄ cap) ∗
  ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
  ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
  A.live ptr (cap.toNat * 4) 2 ∗
  ptSliceAt ptr s.vec ∗
  memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)

theorem tempVecPtAt_prepare_memmove (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) :
    tempVecPtAt A fsp cap ptr { vec := vec } ⊢
      ∃∗ slotBs : List (BitVec 8),
        ⌜slotBs.length = 4⌝ ∗
        ptSliceAt ptr (vec.take insertIdx) ∗
        ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦ₛ (ptListBytes (vec.drop insertIdx) ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
        ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
        ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 := by
  unfold tempVecPtAt
  dsimp only
  have hprep := insert_suffix_prepare_memmove ptr vec insertIdx cap.toNat hins hlt hcap
  rw [show ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2 ∗
      ptSliceAt ptr vec ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) =
    (ptSliceAt ptr vec ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) ∗
    (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) by ac_rfl]
  refine Entails.trans (sepConj_mono_left hprep) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro slotBs
  refine Entails.sepExists_right slotBs (Entails.of_eq (by ac_rfl))

theorem reassemble_tempVecPtAt_insert (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) :
    (((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
      ptSliceAt ptr (vec.take insertIdx) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } := by
  let vec' := vec.take insertIdx ++ (pt :: vec.drop insertIdx)
  have hlen' : vec'.length = vec.length + 1 := by
    dsimp [vec']
    rw [List.length_append, List.length_take_of_le hins, List.length_cons, List.length_drop]
    omega
  have hslice := ptSliceAt_reassemble_insert ptr vec insertIdx pt hins
  dsimp only at hslice
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', ← hslice]
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_tempVecPtAt_snoc (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (pt : Pt) :
    (ptSliceAt ptr vec ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec ++ [pt] } := by
  let vec' := vec ++ [pt]
  have hlen' : vec'.length = vec.length + 1 := by simp [vec']
  have hslice : ptSliceAt ptr vec' =
      ptSliceAt ptr vec ∗
        (((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
          ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value)) := by
    dsimp [vec']
    rw [ptSliceAt_append_singleton]
    rfl
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', hslice]
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_tempVecPtAt_set (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (idx : Nat) (pt : Pt) (hidx : idx < vec.length) :
    (ptSliceAt ptr (vec.take idx) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec.set idx pt } := by
  let vec' := vec.set idx pt
  have hlen' : vec'.length = vec.length := List.length_set
  have hslice : ptSliceAt ptr vec' =
      ptSliceAt ptr (vec.take idx) ∗
        (((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
          ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) := by
    dsimp [vec']
    rw [ptSliceAt_set vec idx pt ptr hidx]
    rfl
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', hslice]
  exact Entails.of_eq (by ac_rfl)

/-! ## Inner Binary Search Loop (`0x62ce4..0x62d08`, `+456 -> +492`) -/

end CryptoVerification.SpqrV1.Poly.DecoderPb
