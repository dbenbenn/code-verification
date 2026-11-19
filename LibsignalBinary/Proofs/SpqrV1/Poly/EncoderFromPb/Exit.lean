/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Epilogue and Exit Blocks

**Checked by Lean.**

Proves `protoPolynomialEncoderAt` open/close bridges, the shared `drop_glue::<ProtoPolynomialEncoder>`
tail-call epilogue (`+1460`), error exits (`+1448`, `+1496`, `+1612`), and shared success header copy
(`+1572 → s0.lr`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

@[local arm64_norm, local wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] theorem bv8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl

/-! ## Address Normalization and Stack / Memory Splitting Lemmas -/

@[local arm64_norm, local wp_norm] theorem sp_sub_1024_add_928 (sp : BitVec 64) :
    (sp - 1024#64) + 928#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_88_add_8 (sp : BitVec 64) : (sp - 88#64) + 8#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8 (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_72_add_8 (sp : BitVec 64) : (sp - 72#64) + 8#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_56_add_8 (sp : BitVec 64) : (sp - 56#64) + 8#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_40_add_8 (sp : BitVec 64) : (sp - 40#64) + 8#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_24_add_8 (sp : BitVec 64) : (sp - 24#64) + 8#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega

/-- The 12 saved register cells at `s0.sp - 96#64 .. s0.sp - 8#64`. -/
@[expose] def savedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_encoderFromPb_split_96 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) ∗ cells (sp - 96#64) 12 := by
  have hEq : encoderFromPbStack = (dropGluePoly16Stack + 928) + 8 * 12 := rfl
  rw [hEq]
  exact ProofLib.stackAt_split_cells sp (dropGluePoly16Stack + 928) 12 (by decide)

theorem stackAt_96_split_928 (sp : BitVec 64) :
    stackAt (sp - 96#64) (dropGluePoly16Stack + 928) =
      stackAt (sp - 1024#64) dropGluePoly16Stack ∗ memRegion (sp - 1024#64) 928 := by
  simp only [stackAt]
  rw [memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928))
    dropGluePoly16Stack 928 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928) =
      (sp - 1024#64) - BitVec.ofNat 64 dropGluePoly16Stack := by
    change (sp - 96#64) - 5056#64 = (sp - 1024#64) - 4128#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928) +
      BitVec.ofNat 64 dropGluePoly16Stack = sp - 1024#64 := by
    change (sp - 96#64) - 5056#64 + 4128#64 = sp - 1024#64
    bv_omega
  rw [h2, h1]

theorem stackAt_dropGluePoly16_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropGluePoly16Stack =
      memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 32 (by decide)

theorem stackAt_encoderFromPb_split_dropStack48 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      memRegion (sp - 5152#64) 1008 ∗ stackAt sp dropStack48 :=
  stackAt_split_bottom sp dropStack48 1008 (by decide)

theorem savedCells_entails_cells12 (s0 : State) :
    savedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold savedCells
  refine cells_sub_succ_entails 96 12 ?_
  refine cells_sub_succ_entails 88 11 ?_
  refine cells_sub_succ_entails 80 10 ?_
  refine cells_sub_succ_entails 72 9 ?_
  refine cells_sub_succ_entails 64 8 ?_
  refine cells_sub_succ_entails 56 7 ?_
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)

theorem savedCells_restore_stack (s0 : State) (R : SepProp) :
    savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗ R ⊢
      R ∗ stackAt s0.sp encoderFromPbStack := by
  rw [stackAt_encoderFromPb_split_96 s0.sp]
  refine Entails.trans (sepConj_mono_left (savedCells_entails_cells12 s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_928_split (fsp : BitVec 64) :
    memRegion fsp 928 =
      cells fsp 9 ∗
      memRegion (fsp + 72#64) 384 ∗
      cells (fsp + 456#64) 3 ∗
      memRegion (fsp + 480#64) 384 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 72) (k := 856)
        (b' := fsp + 72#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 384) (k := 472)
        (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 24) (k := 448)
        (b' := fsp + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 480#64) (n := 384) (k := 64)
        (b' := fsp + 864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 864#64) (n := 32) (k := 32)
        (b' := fsp + 896#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 896#64) (n := 24) (k := 8)
        (b' := fsp + 920#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_cells (fsp + 456#64) 3 (by decide),
      ProofLib.memRegion_cells (fsp + 864#64) 4 (by decide),
      ProofLib.memRegion_cells (fsp + 896#64) 3 (by decide)]

theorem frame_928_rejoin (sp : BitVec 64) :
    cells (sp - 1024#64) 9 ∗
    memRegion ((sp - 1024#64) + 72#64) 384 ∗
    cells ((sp - 1024#64) + 456#64) 3 ∗
    memRegion ((sp - 1024#64) + 480#64) 384 ∗
    cells ((sp - 1024#64) + 864#64) 4 ∗
    cells ((sp - 1024#64) + 896#64) 3 ∗
    memRegion ((sp - 1024#64) + 920#64) 8 ∗
    memRegion ((sp - 1024#64) - 4128#64) 32 ∗
    stackAt (sp - 1024#64) allocHookStack ⊢
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) := by
  rw [stackAt_96_split_928 sp, stackAt_dropGluePoly16_split_bottom (sp - 1024#64),
      memRegion_928_split (sp - 1024#64)]
  exact Entails.of_eq (by ac_rfl)

theorem frame_928_rejoin_dropGlue (sp : BitVec 64) :
    cells (sp - 1024#64) 9 ∗
    memRegion ((sp - 1024#64) + 72#64) 384 ∗
    cells ((sp - 1024#64) + 456#64) 3 ∗
    memRegion ((sp - 1024#64) + 480#64) 384 ∗
    cells ((sp - 1024#64) + 864#64) 4 ∗
    cells ((sp - 1024#64) + 896#64) 3 ∗
    memRegion ((sp - 1024#64) + 920#64) 8 ∗
    stackAt (sp - 1024#64) dropGluePoly16Stack ⊢
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) := by
  rw [stackAt_96_split_928 sp, memRegion_928_split (sp - 1024#64)]
  exact Entails.of_eq (by ac_rfl)

theorem cells9_split_4_5 (fsp : BitVec 64) :
    cells fsp 9 = cells fsp 4 ∗ cells (fsp + 32#64) 5 := by
  rw [← ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_split' (b := fsp) (n := 32) (k := 40)
        (b' := fsp + 32#64) rfl rfl (by decide),
      ProofLib.memRegion_cells fsp 4 (by decide),
      ProofLib.memRegion_cells (fsp + 32#64) 5 (by decide)]

theorem cells9_split_7_1_1 (fsp : BitVec 64) :
    cells fsp 9 =
      cells fsp 7 ∗
      (∃∗ v56 : BitVec 64, (fsp + 56#64) ↦₆₄ v56) ∗
      (∃∗ v64 : BitVec 64, (fsp + 64#64) ↦₆₄ v64) := by
  rw [← ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_split' (b := fsp) (n := 56) (k := 16)
        (b' := fsp + 56#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 56#64) (n := 8) (k := 8)
        (b' := fsp + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells fsp 7 (by decide),
      ProofLib.memRegion_eight (fsp + 56#64),
      ProofLib.memRegion_eight (fsp + 64#64)]

theorem cells7_56_64_entails_cells9 (fsp v56 v64 : BitVec 64) :
    cells fsp 7 ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 64#64) ↦₆₄ v64) ⊢
      cells fsp 9 := by
  rw [cells9_split_7_1_1 fsp]
  exact sepConj_mono_right
    (sepConj_mono (Entails.sepExists_right v56 (Entails.refl _))
      (Entails.sepExists_right v64 (Entails.refl _)))

theorem memRegion_out_err_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d8 : BitVec 8,
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ d8) ∗ memRegion (out + 9#64) 391 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 391)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_one (out + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d8
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d8 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_out_ok_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d392 : BitVec 32,
        (out ↦₆₄ d0) ∗ memRegion (out + 8#64) 384 ∗
          ((out + 392#64) ↦₃₂ d392) ∗ memRegion (out + 396#64) 4 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 384) (k := 8)
        (b' := out + 392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 392#64) (n := 4) (k := 4)
        (b' := out + 396#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_four (out + 392#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d392
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d392 ?_)
  exact Entails.of_eq (by ac_rfl)

/-! ## `protoPolynomialEncoderAt` Open / Close Helpers and Subroutine Contracts -/

/-- Remaining parts of `protoPolynomialEncoderAt A pbA pb` after exposing `pbA + 8`, `pbA + 16`,
    `pbA + 32`, `pbA + 40`, `pbA + 48`, and the `pts` and `polys` element arrays. -/
@[expose] def protoPolyEncoderRest (A : RustAlloc) (pbA ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) : SepProp :=
  ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
    pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
  (pbA ↦₆₄ ptsCap) ∗
  (if ptsCap = 0 then emp
   else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
     memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
       ((ptsCap.toNat - pb.pts.length) * 24)) ∗
  ((pbA + 24#64) ↦₆₄ polysCap) ∗
  (if polysCap = 0 then emp
   else A.live polysPtr (polysCap.toNat * 24) 8 ∗
     memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
       ((polysCap.toNat - pb.polys.length) * 24)) ∗
  memRegion (pbA + 52#64) 4

theorem vecBuf_vecU8_entails_sepConj (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) :
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) cap ptr bss ⊢
      ⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 24) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hc : cap = 0
  · subst hc
    have hbss : bss = [] := by
      cases bss with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbss
    simp [arrayAt]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem sepConj_entails_vecBuf_vecU8 (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) :
    ⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗
       memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) ⊢
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) cap ptr bss := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hc : cap = 0
  · subst hc
    have hbss : bss = [] := by
      cases bss with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbss
    simp [arrayAt]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem protoPolyEncoder_open (A : RustAlloc) (pbA : BitVec 64) (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A pbA pb ⊢
      ∃∗ ptsCap : BitVec 64, ∃∗ ptsPtr : BitVec 64,
      ∃∗ polysCap : BitVec 64, ∃∗ polysPtr : BitVec 64,
        ⌜pb.pts.length < 2 ^ 63 ∧ pb.polys.length < 2 ^ 63⌝ ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro polysCap
  apply Entails.sepExists_elim; intro polysPtr
  apply Entails.sepExists_elim; intro ptsCap
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ptsCap (Entails.sepExists_right ptsPtr
    (Entails.sepExists_right polysCap (Entails.sepExists_right polysPtr ?_)))
  unfold vecAt vecHeader protoPolyEncoderRest
  refine Entails.trans (sepConj_mono (sepConj_mono_right (vecBuf_vecU8_entails_sepConj A ptsCap ptsPtr pb.pts))
    (sepConj_mono_left (sepConj_mono_right (vecBuf_vecU8_entails_sepConj A polysCap polysPtr pb.polys)))) ?_
  have ha1 : (pbA + 24#64) + 8#64 = pbA + 32#64 := by bv_omega
  have ha2 : (pbA + 24#64) + 16#64 = pbA + 40#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       ((pbA ↦₆₄ ptsCap) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        ((pbA + 24#64) ↦₆₄ polysCap) ∗
        (if polysCap = 0 then emp
         else A.live polysPtr (polysCap.toNat * 24) 8 ∗
           memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((polysCap.toNat - pb.polys.length) * 24)) ∗
        memRegion (pbA + 52#64) 4)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  apply Entails.pure_left; rintro ⟨h4, h5, h6⟩
  have hlt1 : pb.pts.length < 2 ^ 63 := by omega
  have hlt2 : pb.polys.length < 2 ^ 63 := by omega
  refine Entails.pure_right ⟨hlt1, hlt2⟩ ?_
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
        pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       ((pbA ↦₆₄ ptsCap) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        ((pbA + 24#64) ↦₆₄ polysCap) ∗
        (if polysCap = 0 then emp
         else A.live polysPtr (polysCap.toNat * 24) 8 ∗
           memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((polysCap.toNat - pb.polys.length) * 24)) ∗
        memRegion (pbA + 52#64) 4)) = _ by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6⟩ (Entails.refl _)

theorem protoPolyEncoder_close (A : RustAlloc) (pbA ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
    ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((pbA + 32#64) ↦₆₄ polysPtr) ∗
    ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((pbA + 48#64) ↦₃₂ pb.idx) ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
    protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ⊢
      protoPolynomialEncoderAt A pbA pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right polysCap (Entails.sepExists_right polysPtr
    (Entails.sepExists_right ptsCap (Entails.sepExists_right ptsPtr ?_)))
  unfold vecAt vecHeader protoPolyEncoderRest
  refine Entails.trans ?_
    (sepConj_mono (sepConj_mono_right (sepConj_entails_vecBuf_vecU8 A ptsCap ptsPtr pb.pts))
      (sepConj_mono_left (sepConj_mono_right (sepConj_entails_vecBuf_vecU8 A polysCap polysPtr pb.polys))))
  have ha1 : (pbA + 24#64) + 8#64 = pbA + 32#64 := by bv_omega
  have ha2 : (pbA + 24#64) + 16#64 = pbA + 40#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
        pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      ((pbA ↦₆₄ ptsCap) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
            ((ptsCap.toNat - pb.pts.length) * 24)) ∗
       ((pbA + 24#64) ↦₆₄ polysCap) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       (if polysCap = 0 then emp
        else A.live polysPtr (polysCap.toNat * 24) 8 ∗
          memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
            ((polysCap.toNat - pb.polys.length) * 24)) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (pbA + 52#64) 4) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6⟩
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      ((pbA ↦₆₄ ptsCap) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
            ((ptsCap.toNat - pb.pts.length) * 24)) ∗
       ((pbA + 24#64) ↦₆₄ polysCap) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       (if polysCap = 0 then emp
        else A.live polysPtr (polysCap.toNat * 24) 8 ∗
          memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
            ((polysCap.toNat - pb.polys.length) * 24)) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (pbA + 52#64) 4) = _ by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.pure_right ⟨h4, h5, h6⟩ (Entails.refl _))

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
