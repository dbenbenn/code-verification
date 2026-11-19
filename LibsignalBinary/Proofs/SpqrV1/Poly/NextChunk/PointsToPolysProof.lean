/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Conversion Loop

Verifies per-iteration slot cleanup (`0x6b328..0x6b38c`, `+4004 -> +976 / +4424`) and the
16-iteration `pointsToPolysLoop_sepWPp` (`0x6a754..0x6b38c`, `+976 -> +4424`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_p2p :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem add_8_add_8_eq (a : BitVec 64) : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega

/-! ## 1. Pure Polynomial Conversion and Slicing Helpers -/

/-- Pure polynomial interpolated from a `Point` (`ys = pt.value`). -/
@[expose] def pointToPolyPure (pt : Point) : Poly :=
  if pt.value.length = 0 then
    Poly.zero
  else
    let pts := PolyEncoder.enumeratePts 0 pt.value
    Poly.lagrangeSum pts (completePointsBasisPure pts)

theorem fromCompletePoints_enumeratePts_eq (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 pt.value) =
      .ok (.ok (pointToPolyPure pt)) := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  by_cases hn0 : pt.value.length = 0
  · have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hn0
    unfold pointToPolyPure
    simp only [hn0, ↓reduceIte]
    rw [hnil]
    rfl
  · have hcomp : Poly.checkCompletePoints 0 (PolyEncoder.enumeratePts 0 pt.value) = true :=
      checkCompletePoints_enumeratePts 0 pt.value
    have hbound' : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    rw [fromCompletePoints_eq_ok (PolyEncoder.enumeratePts 0 pt.value) hcomp hbound']
    unfold pointToPolyPure
    simp [hn0]

theorem lagrangeSumFoldPoly_length {n : Nat} :
    ∀ (pts : List Pt) (polys : List Poly) (acc : Poly),
      acc.coefficients.length = n →
      (∀ p ∈ polys, p.coefficients.length = n) →
      (lagrangeSumFoldPoly acc pts polys).coefficients.length = n
  | [], _, acc, hacc, _ => hacc
  | _ :: _, [], acc, hacc, _ => hacc
  | pt :: ptsRest, poly :: polysRest, acc, hacc, hplen => by
    have hp : poly.coefficients.length = n := hplen poly (List.mem_cons_self ..)
    have hacc' : (acc.addAssign (poly.multAssign pt.y)).coefficients.length = n := by
      unfold Poly.addAssign
      rw [addAssignCoeffs_length_eq (by rw [hacc, multAssign_length, hp]), hacc]
    exact lagrangeSumFoldPoly_length ptsRest polysRest _ hacc'
      (fun p hp' => hplen p (List.mem_cons_of_mem poly hp'))

theorem lagrangeSum_coefficients_length (pts : List Pt) (polys : List Poly) (n : Nat)
    (hpts : pts ≠ []) (hpolys : polys ≠ [])
    (hplen : ∀ p ∈ polys, p.coefficients.length = n) :
    (Poly.lagrangeSum pts polys).coefficients.length = n := by
  cases pts with
  | nil => contradiction
  | cons pt0 ptsRest =>
    cases polys with
    | nil => contradiction
    | cons poly0 polysRest =>
      rw [lagrangeSum_eq_foldPoly, lagrangeSumFoldPoly_cons]
      have hp0 : poly0.coefficients.length = n := hplen poly0 (List.mem_cons_self ..)
      have hacc0 : (Poly.zero.addAssign (poly0.multAssign pt0.y)).coefficients.length = n := by
        unfold Poly.addAssign Poly.zero
        rw [addAssignCoeffs_nil_left, multAssign_length, hp0]
      exact lagrangeSumFoldPoly_length ptsRest polysRest _ hacc0
        (fun p hp' => hplen p (List.mem_cons_of_mem poly0 hp'))

theorem pointToPolyPure_coefficients_length (pt : Point) :
    (pointToPolyPure pt).coefficients.length = pt.value.length := by
  unfold pointToPolyPure
  split
  · rename_i hn0
    simp [Poly.zero, hn0]
  · rename_i hn0
    have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
      enumeratePts_length 0 pt.value
    have hpts_ne : PolyEncoder.enumeratePts 0 pt.value ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hbasis_len :
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value)).length =
          (PolyEncoder.enumeratePts 0 pt.value).length :=
      completePointsBasisPure_length _
    have hbasis_ne : completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value) ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hplen : ∀ p ∈ completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value),
        p.coefficients.length = (PolyEncoder.enumeratePts 0 pt.value).length :=
      completePointsBasisPure_mem_length (PolyEncoder.enumeratePts 0 pt.value)
    rw [lagrangeSum_coefficients_length _ _ _ hpts_ne hbasis_ne hplen, hlen]

/-- Dynamic buffer ownership of the newly constructed polynomial before writing its header to `slot`. -/
@[expose] def newPolyBufAt (A : RustAlloc) (ptr : BitVec 64) (pt : Point) : SepProp :=
  if pt.value.length = 0 then
    ⌜ptr = 2#64⌝
  else
    ⌜ptr ≠ 0#64⌝ ∗
    A.live ptr (2 * pt.value.length) 2 ∗
    gf16SliceAt ptr (pointToPolyPure pt).coefficients

theorem polyOf_of_newPolyBufAt (A : RustAlloc) (slot ptr : BitVec 64) (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    (slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
    ((slot + 8#64) ↦₆₄ ptr) ∗
    ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
    newPolyBufAt A ptr pt ⊢
    polyOf A slot (pointToPolyPure pt) := by
  have hplen : (pointToPolyPure pt).coefficients.length = pt.value.length :=
    pointToPolyPure_coefficients_length pt
  unfold newPolyBufAt
  by_cases hn0 : pt.value.length = 0
  · simp only [hn0, ↓reduceIte]
    have hpull :
        (slot ↦₆₄ 0#64) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64) ∗ ⌜ptr = 2#64⌝ =
        ⌜ptr = 2#64⌝ ∗ ((slot ↦₆₄ 0#64) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64)) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hptr
    subst hptr
    have hp0 : pointToPolyPure pt = Poly.zero := by
      unfold pointToPolyPure; simp [hn0]
    rw [hp0]
    unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align Poly.zero
    apply Entails.sepExists_right 0#64
    apply Entails.sepExists_right 2#64
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_mul, ↓reduceIte, sepConj_emp]
    rw [sepConj_comm (slot ↦₆₄ 0#64 ∗ (slot + 8#64) ↦₆₄ 2#64 ∗ (slot + 16#64) ↦₆₄ 0#64)]
    exact Entails.pure_right ⟨Nat.le_refl 0, by decide, by decide⟩ (Entails.refl _)
  · simp only [hn0, ↓reduceIte]
    have hpull :
        (slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((slot + 8#64) ↦₆₄ ptr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        (⌜ptr ≠ 0#64⌝ ∗ A.live ptr (2 * pt.value.length) 2 ∗
          gf16SliceAt ptr (pointToPolyPure pt).coefficients) =
        ⌜ptr ≠ 0#64⌝ ∗
        ((slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((slot + 8#64) ↦₆₄ ptr) ∗
         ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         A.live ptr (2 * pt.value.length) 2 ∗
         gf16SliceAt ptr (pointToPolyPure pt).coefficients) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hptr_ne
    rw [gf16SliceAt_eq_pointsToBytes]
    exact polyOf_of_pointsToBytes A slot ptr (pointToPolyPure pt) pt.value.length
      (by omega) (by omega) hptr_ne hplen

theorem polyOf_empty_unfold (A : RustAlloc) (slot : BitVec 64) :
    polyOf A slot ⟨[]⟩ ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (slot ↦₆₄ cap) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64) ∗
        (if cap = 0#64 then emp else A.live ptr (cap.toNat * 2) 2 ∗ memRegion ptr (cap.toNat * 2)) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  simp only [List.length_nil, Nat.zero_le, true_and, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.sub_zero, arrayAt, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem ptVecBufAt_pos_entails (A : RustAlloc) (ptr : BitVec 64) (ys : List GF16)
    (hpos : 0 < ys.length) (hbound : ys.length ≤ 0x0555555555555555) :
    ptVecBufAt A ptr ys ⊢
      ⌜ptr ≠ 0#64⌝ ∗ A.live ptr (4 * ys.length) 2 ∗ memRegion ptr (4 * ys.length) := by
  have hne0 : ys.length ≠ 0 := by omega
  have hlen_enum : (PolyEncoder.enumeratePts 0 ys).length = ys.length :=
    enumeratePts_length 0 ys
  unfold ptVecBufAt
  simp only [hne0, ↓reduceIte]
  have hmem := ptSliceAt_entails_memRegion ptr (PolyEncoder.enumeratePts 0 ys) (by omega)
  rw [hlen_enum] at hmem
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hmem)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem pointsToPolysLoop_eq_map (pts : List Point)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = pts.length →
      PolyEncoder.pointsToPolysLoop pts i rem acc =
        .ok (acc ++ (pts.drop i).map pointToPolyPure)
  | 0, i, acc, hlen => by
    have hi : i = pts.length := by omega
    subst hi
    simp [PolyEncoder.pointsToPolysLoop]
  | rem + 1, i, acc, hlen => by
    have hi : i < pts.length := by omega
    have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
    have hbound_i : (pts[i]'hi).value.length ≤ 0x0555555555555555 :=
      hbounds (pts[i]'hi) (List.getElem_mem hi)
    have hfc := fromCompletePoints_enumeratePts_eq (pts[i]'hi) hbound_i
    have ih := pointsToPolysLoop_eq_map pts hbounds rem (i + 1)
      (acc ++ [pointToPolyPure (pts[i]'hi)]) (by omega)
    have hdrop : pts.drop i = (pts[i]'hi) :: pts.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    unfold PolyEncoder.pointsToPolysLoop
    simp only [hpt, hfc, ih, hdrop, List.map_cons, List.append_assoc, List.singleton_append,
      Bind.bind, Except.bind]

/-! ## 2. Per-Iteration Cleanup (`0x6b328..0x6b38c`, `+4004 -> +976 / +4424`) -/

theorem cmn_one_ne_zero {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n + 1#64 == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h1 : (BitVec.ofNat 64 n + 1#64).toNat = 0 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)] at h1
  omega

theorem shl1_oldCap_eq {cap : BitVec 64} (h : cap.toNat * 2 < 2 ^ 63) :
    cap <<< (1 : Nat) = BitVec.ofNat 64 (cap.toNat * 2) ∧
    (cap <<< 1#64) = BitVec.ofNat 64 (cap.toNat * 2) ∧
    (BitVec.ofNat 64 (cap.toNat * 2)).toNat = cap.toNat * 2 := by
  have hto : (cap <<< 1#64).toNat = cap.toNat * 2 :=
    CryptoVerification.SpqrV1.Drop.shiftLeft_one_toNat h
  have hmod : (BitVec.ofNat 64 (cap.toNat * 2)).toNat = cap.toNat * 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heq : cap <<< 1#64 = BitVec.ofNat 64 (cap.toNat * 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [hto, hmod]
  exact ⟨heq, heq, hmod⟩

theorem shl2_len_eq {n : Nat} (hn : n ≤ 0x0555555555555555) :
    BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) ∧
    BitVec.ofNat 64 n <<< 2#64 = BitVec.ofNat 64 (4 * n) ∧
    (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := by
  have hmod : (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmod_n : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hto : (BitVec.ofNat 64 n <<< (2 : Nat)).toNat = 4 * n := by
    rw [BitVec.toNat_shiftLeft, hmod_n, Nat.shiftLeft_eq]
    have hs : n * 2 ^ 2 = 4 * n := by omega
    rw [hs, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [hto, hmod]
  exact ⟨h1, h1, hmod⟩

theorem ptVecBufAt_zero_drop (A : RustAlloc) (ptr : BitVec 64) (ys : List GF16)
    (hn0 : ys.length = 0) (Rest : SepProp) :
    ptVecBufAt A ptr ys ∗ Rest ⊢ Rest := by
  have hnil : ys = [] := List.eq_nil_of_length_eq_zero hn0
  subst hnil
  unfold ptVecBufAt PolyEncoder.enumeratePts ptSliceAt arrayAt
  simp only [List.length_nil, ↓reduceIte, emp_sepConj, sepConj_emp]
  apply Entails.pure_left; intro _
  exact Entails.refl _

theorem stackAt_lagrangePrepare_fold_alloc (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack) (lagrangePrepareStack - allocHookStack) ⊢
    stackAt fsp lagrangePrepareStack := by
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

theorem memRegion_112_split_216 (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u216 : BitVec 64, ∃∗ u224 : BitVec 64,
        memRegion (fsp + 112#64) 104 ∗
        ((fsp + 216#64) ↦₆₄ u216) ∗
        ((fsp + 224#64) ↦₆₄ u224) := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 104) (k := 16) (b' := fsp + 216#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u224
  apply Entails.sepExists_elim; intro u216
  exact Entails.sepExists_right u216 (Entails.sepExists_right u224 (Entails.of_eq (by ac_rfl)))

theorem memRegion_112_fold_216 (fsp u216 u224 : BitVec 64) :
    memRegion (fsp + 112#64) 104 ∗
    ((fsp + 216#64) ↦₆₄ u216) ∗
    ((fsp + 224#64) ↦₆₄ u224) ⊢
    memRegion (fsp + 112#64) 120 := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 104) (k := 16) (b' := fsp + 216#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u224
  apply Entails.sepExists_right u216
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_656_fold (fsp u656 u664 u672 : BitVec 64) :
    ((fsp + 656#64) ↦₆₄ u656) ∗
    ((fsp + 664#64) ↦₆₄ u664) ∗
    ((fsp + 672#64) ↦₆₄ u672) ⊢
    memRegion (fsp + 656#64) 24 := by
  rw [memRegion24_off_eq_polyHeader fsp]
  exact Entails.sepExists_right u672
    (Entails.sepExists_right u664
      (Entails.sepExists_right u656 (Entails.of_eq (by ac_rfl))))

theorem newPolyBufAt_n0_intro (A : RustAlloc) (pt : Point) (hn0 : pt.value.length = 0)
    (Rest : SepProp) :
    Rest ⊢ newPolyBufAt A 2#64 pt ∗ Rest := by
  unfold newPolyBufAt
  simp only [hn0, ↓reduceIte, pure_true, emp_sepConj]
  exact Entails.refl _

theorem newPolyBufAt_pos_intro (A : RustAlloc) (accPtr : BitVec 64) (pt : Point)
    (hn0 : pt.value.length ≠ 0) (hacc_ne : accPtr ≠ 0#64) (Rest : SepProp) :
    A.live accPtr (2 * (PolyEncoder.enumeratePts 0 pt.value).length) 2 ∗
    gf16SliceAt accPtr
      (Poly.lagrangeSum (PolyEncoder.enumeratePts 0 pt.value)
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value))).coefficients ∗
    Rest ⊢
    newPolyBufAt A accPtr pt ∗ Rest := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  have hp : pointToPolyPure pt =
      Poly.lagrangeSum (PolyEncoder.enumeratePts 0 pt.value)
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value)) := by
    unfold pointToPolyPure
    simp [hn0]
  unfold newPolyBufAt
  simp only [hn0, ↓reduceIte, hlen, ← hp]
  rw [sepConj_assoc]
  refine Entails.pure_right hacc_ne ?_
  exact Entails.of_eq (by ac_rfl)

theorem ptVecBufAt_pos_fold (A : RustAlloc) (ptVecPtr : BitVec 64) (pt : Point)
    (hn0 : pt.value.length ≠ 0) (hpt_ne : ptVecPtr ≠ 0#64) (Rest : SepProp) :
    ptSliceAt ptVecPtr (PolyEncoder.enumeratePts 0 pt.value) ∗
    A.live ptVecPtr (4 * pt.value.length) 2 ∗
    Rest ⊢
    ptVecBufAt A ptVecPtr pt.value ∗ Rest := by
  unfold ptVecBufAt
  simp only [hn0, ↓reduceIte]
  rw [sepConj_assoc]
  refine Entails.pure_right hpt_ne ?_
  exact Entails.of_eq (by ac_rfl)

theorem pointListOf_cons_mul24_off (A : RustAlloc) (base : BitVec 64) (j : Nat)
    (pt : Point) (pts : List Point) :
    pointListOf A (base + BitVec.ofNat 64 (24 * j)) (pt :: pts) =
      pointOf A (base + BitVec.ofNat 64 (24 * j)) pt ∗
      pointListOf A (base + BitVec.ofNat 64 (24 * (j + 1))) pts := by
  dsimp only [pointListOf, arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
    bv_omega
  rw [haddr]

theorem polyListOf_cons_mul24_off (A : RustAlloc) (base : BitVec 64) (j : Nat)
    (p : Poly) (ps : List Poly) :
    polyListOf A (base + BitVec.ofNat 64 (24 * j)) (p :: ps) =
      polyOf A (base + BitVec.ofNat 64 (24 * j)) p ∗
      polyListOf A (base + BitVec.ofNat 64 (24 * (j + 1))) ps := by
  dsimp only [polyListOf, arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
    bv_omega
  rw [haddr]

end CryptoVerification.SpqrV1.Poly.NextChunk

