/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder>::into_pb`: Outer Serialization Loops

**Checked by Lean.**

Verification of the `.polys` (`+188 -> +616`) and `.points` (`+452 -> +616`) outer allocation and
serialization loops and branch dispatch for `<spqr::encoding::polynomial::PolyEncoder>::into_pb`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop (vecGF16Of vecGF16ListOf
  pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  fp_sub_48 fp_sub_32 fp_sub_24 fp_sub_16 fp_sub_8 fp_sub_40
  fp_sub_48_int fp_sub_32_int fp_sub_24_int fp_sub_16_int fp_sub_8_int fp_sub_40_int
  sp_add_56_add_8 sp_add_80_add_8 sp_add_104_add_8
  ofNat_add_one madd_24_eq

theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## `SepWPp` Sequencing and Extraction Helpers -/

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem sepWPp_pure_head2 {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B) Q Qp) :
    SepWPp prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp := by
  rw [show A ∗ ⌜φ⌝ ∗ B = ⌜φ⌝ ∗ A ∗ B by ac_rfl]
  exact SepWPp.pure_elim h

theorem SepWPp.seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

structure HiddenEq {α : Type} (a b : α) : Prop where
  eq : a = b

theorem arrayAt_24_off_cons {α : Type} (elemPred : α → BitVec 64 → SepProp)
    (base : BitVec 64) (j : Nat) (x : α) (xs : List α) :
    arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * j)) (x :: xs) =
      (elemPred x (base + BitVec.ofNat 64 (24 * j)) ∗
        arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * (j + 1))) xs) := by
  rw [arrayAt_cons, off_24_succ]

theorem arrayAt_24_off_singleton {α : Type} (elemPred : α → BitVec 64 → SepProp)
    (base : BitVec 64) (j : Nat) (x : α) :
    arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * j)) [x] =
      elemPred x (base + BitVec.ofNat 64 (24 * j)) := by
  rw [arrayAt_cons, arrayAt_nil, sepConj_emp]

section PlacedDispatch

variable [LibsignalPlacement]

/-- Branch dispatch for `.points` (`+88 -> +452`) in `[LibsignalPlacement]`. -/
theorem into_pb_dispatch_points_placed
    {ext : String → Option (State → State)}
    (s0 : State) (fsp out encA ptr_points ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (idx : BitVec 32)
    (v0 v1 v2 v3 v4 v5 v6 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = encA)
    (hx20 : s.readReg64 .x20 = out)
    (hx21 : s.readReg64 .x21 = ptr_points)
    (hx0 : s.readReg64 .x0 = ptr_polys)
    (hx22 : s.readReg64 .x22 = idx.zeroExtend 64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 452#64) s
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
        ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
        ((fsp + 48#64) ↦₆₄ v6) ∗ (encA ↦₆₄ 0#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          memRegion encA 8 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = encA ∧ sm.readReg64 .x20 = out ∧
        sm.readReg64 .x22 = encA + 8#64 ∧ sm.readReg64 .x23 = 0#64 ∧
        sm.readReg64 .x24 = 24#64 ∧ sm.readReg64 .x25 = 1#64 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  conv => arg 4; rw [pointsTo64_off48_split32 fsp v6, pointsTo64_split32 encA 0#64]
  wp_steps
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (pointsTo64_split32_tag encA 0#64
          ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
            ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗ Frame))
        (Entails.of_eq (by ac_rfl)))) ?_
  wp_done

/-- Branch dispatch for `.polys` (`+88 -> +188`) in `[LibsignalPlacement]`. -/
theorem into_pb_dispatch_polys_placed
    {ext : String → Option (State → State)}
    (s0 : State) (fsp out encA ptr_points ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (idx : BitVec 32)
    (v0 v1 v2 v3 v4 v5 v6 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = encA)
    (hx20 : s.readReg64 .x20 = out)
    (hx21 : s.readReg64 .x21 = ptr_points)
    (hx0 : s.readReg64 .x0 = ptr_polys)
    (hx22 : s.readReg64 .x22 = idx.zeroExtend 64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 188#64) s
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
        ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
        ((fsp + 48#64) ↦₆₄ v6) ∗ (encA ↦₆₄ 1#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          memRegion encA 8 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = encA ∧
        sm.readReg64 .x20 = out ∧
        sm.readReg64 .x22 = encA + 8#64 ∧
        sm.readReg64 .x23 = 0#64 ∧
        sm.readReg64 .x28 = 0#64 ∧
        sm.readReg64 .x24 = fsp ∧
        sm.readReg64 .x25 = 24#64 ∧
        sm.readReg64 .x26 = 1#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  conv => arg 4; rw [pointsTo64_off48_split32 fsp v6, pointsTo64_split32 encA 1#64]
  wp_steps
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (pointsTo64_split32_tag encA 1#64
          ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
            ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗ Frame))
        (Entails.of_eq (by ac_rfl)))) ?_
  wp_done

end PlacedDispatch

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb

