/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.NextChunkCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.GF.AcceleratedMul
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed `gf::parallel_mult` Shift Table and Odd Tail

**Checked by Lean.**

Relocatable `[LibsignalPlacement]` shift-table representation, bitvector normalization rules,
shift-table initialization (`+2752 -> +3384`), and odd trailing element multiplication
(`+3608 -> +3784`) for `gf::parallel_mult`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_sm1 (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_sm1 (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
private theorem pstate_setMem_sm1 (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem trace_setMem_sm1 (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
private theorem calleeSavedVRegs_setMem_sm1 (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm, local wp_norm]
theorem fsp_1104_sub_32 (fsp : BitVec 64) : (fsp + 1104#64) - 32#64 = fsp + 1072#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_1104_sub_64 (fsp : BitVec 64) : (fsp + 1104#64) - 64#64 = fsp + 1040#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_1104_add_neg32 (fsp : BitVec 64) :
    (fsp + 1104#64) + 18446744073709551584#64 = fsp + 1072#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_1104_add_neg64 (fsp : BitVec 64) :
    (fsp + 1104#64) + 18446744073709551552#64 = fsp + 1040#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero ls_resolve_blk_416
  Arm64.Obj.pageOf_add_lo12Of conditionHolds_eq_subsPState32 conditionHolds_ne_subsPState32
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_sm1 status_setMem_sm1 pstate_setMem_sm1 trace_setMem_sm1
  calleeSavedVRegs_setMem_sm1 readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

/-- Frame scratch slots used by the two `Once::call` slow paths inside Block `416`
    (`gf::parallel_mult` pair step `[sp, #4]`, `[x29, #-0x40]`, `[x29, #-0x20]`, and odd tail
    `[x29, #-0x40]`, `[x29, #-0x20]`, where `x29 = fsp + 1104#64`). -/
@[expose] def onceScratch416 (fsp : BitVec 64) : SepProp :=
  memRegion fsp 8 ∗ memRegion (fsp + 1040#64) 8 ∗ memRegion (fsp + 1064#64) 40

theorem onceScratch416_split_pair (fsp : BitVec 64) :
    onceScratch416 fsp =
      (∃∗ w0 : BitVec 32, fsp ↦₃₂ w0) ∗
      (∃∗ w4 : BitVec 32, (fsp + 4#64) ↦₃₂ w4) ∗
      (∃∗ d : BitVec 64, (fsp + 1040#64) ↦₆₄ d) ∗
      memRegion (fsp + 1064#64) 8 ∗
      (∃∗ sl : BitVec 64, (fsp + 1072#64) ↦₆₄ sl) ∗
      memRegion (fsp + 1080#64) 24 := by
  unfold onceScratch416
  rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 4) (b' := fsp + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_four fsp, ProofLib.memRegion_four (fsp + 4#64),
      ProofLib.memRegion_eight (fsp + 1040#64),
      ProofLib.memRegion_split' (b := fsp + 1064#64) (n := 8) (k := 32) (b' := fsp + 1072#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1072#64) (n := 8) (k := 24) (b' := fsp + 1080#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1072#64)]
  simp only [sepConj_assoc]

theorem onceScratch416_merge_pair (fsp : BitVec 64) (w0 w4 : BitVec 32) (d sl : BitVec 64) :
    (fsp ↦₃₂ w0) ∗ ((fsp + 4#64) ↦₃₂ w4) ∗ ((fsp + 1040#64) ↦₆₄ d) ∗
    memRegion (fsp + 1064#64) 8 ∗ ((fsp + 1072#64) ↦₆₄ sl) ∗ memRegion (fsp + 1080#64) 24 ⊢
      onceScratch416 fsp := by
  rw [onceScratch416_split_pair fsp]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w4)
      (sepConj_mono (Entails.sepExists_intro d)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.sepExists_intro sl) (Entails.refl _)))))

theorem onceScratch416_split_odd (fsp : BitVec 64) :
    onceScratch416 fsp =
      memRegion fsp 8 ∗
      (∃∗ d : BitVec 64, (fsp + 1040#64) ↦₆₄ d) ∗
      memRegion (fsp + 1064#64) 8 ∗
      (∃∗ sl : BitVec 64, (fsp + 1072#64) ↦₆₄ sl) ∗
      memRegion (fsp + 1080#64) 24 := by
  unfold onceScratch416
  rw [ProofLib.memRegion_eight (fsp + 1040#64),
      ProofLib.memRegion_split' (b := fsp + 1064#64) (n := 8) (k := 32) (b' := fsp + 1072#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1072#64) (n := 8) (k := 24) (b' := fsp + 1080#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1072#64)]

theorem onceScratch416_merge_odd (fsp : BitVec 64) (d sl : BitVec 64) :
    memRegion fsp 8 ∗ ((fsp + 1040#64) ↦₆₄ d) ∗
    memRegion (fsp + 1064#64) 8 ∗ ((fsp + 1072#64) ↦₆₄ sl) ∗ memRegion (fsp + 1080#64) 24 ⊢
      onceScratch416 fsp := by
  rw [onceScratch416_split_odd fsp]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.sepExists_intro d)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.sepExists_intro sl) (Entails.refl _))))

theorem allocHookStack_split_once (fsp : BitVec 64) :
    stackAt fsp allocHookStack =
      memRegion (fsp - 4096#64) (allocHookStack - 160) ∗ stackAt fsp 160 := by
  have h := ProofLib.stackAt_split_bottom fsp 160 (allocHookStack - 160) (by decide)
  rw [show 160 + (allocHookStack - 160) = allocHookStack by decide] at h
  exact h

theorem allocHookStack_merge_once (fsp : BitVec 64) :
    memRegion (fsp - 4096#64) (allocHookStack - 160) ∗ stackAt fsp 160 ⊢
      stackAt fsp allocHookStack :=
  Entails.of_eq (allocHookStack_split_once fsp).symm

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_sm_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_sm_pl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

@[local arm64_norm, local wp_norm]
private theorem shl_one_ofNat_eq_nat_sm_pl (n : Nat) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  have h1 : (BitVec.ofNat 64 n <<< 1).toNat = (BitVec.ofNat 64 (2 * n)).toNat := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    have hsh : ∀ x : Nat, x <<< 1 = 2 * x := fun x => by rw [Nat.shiftLeft_eq]; omega
    rw [hsh]
    exact Nat.mul_mod_mod 2 n (2 ^ 64)
  exact BitVec.eq_of_toNat_eq h1

/-! ## 1. Pure Lemmas for `parallelMult` -/

@[simp]
theorem parallelMult_nil_pl (a : GF16) : parallelMult a [] = [] := rfl

@[simp]
theorem parallelMult_singleton_pl (a x : GF16) :
    parallelMult a [x] = [⟨unaccelerated.mul x.value a.value⟩] := rfl

@[simp]
theorem parallelMult_pair_cons_pl (a x1 x2 : GF16) (rest : List GF16) :
    parallelMult a (x1 :: x2 :: rest) =
      ⟨unaccelerated.mul a.value x1.value⟩ ::
      ⟨unaccelerated.mul a.value x2.value⟩ ::
      parallelMult a rest := rfl

theorem parallelMult_length_pl (a : GF16) :
    ∀ cs : List GF16, (parallelMult a cs).length = cs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp [parallelMult_pair_cons_pl, parallelMult_length_pl a rest]

/-! ## 2. Stack-Slot Bundle for `parallel_mult` (`fsp + 112..232`) -/

/-- The 15 precomputed 32-bit shifts of `yv` stored on the stack at `fsp + 148..228` by
    `+2752..+3380` and read on every iteration of `+3384..+3572`. -/
@[expose] def shiftTableAt_pl (fsp : BitVec 64) (yv : BitVec 16) : SepProp :=
  let y32 := BitVec.zeroExtend 32 yv
  ((fsp + 148#64) ↦₃₂ (y32 <<< 15)) ∗ ((fsp + 152#64) ↦₃₂ (y32 <<< 14)) ∗
  ((fsp + 156#64) ↦₃₂ (y32 <<< 13)) ∗ ((fsp + 160#64) ↦₃₂ (y32 <<< 12)) ∗
  ((fsp + 164#64) ↦₃₂ (y32 <<< 11)) ∗ ((fsp + 168#64) ↦₃₂ (y32 <<< 10)) ∗
  ((fsp + 172#64) ↦₃₂ (y32 <<< 9)) ∗ ((fsp + 176#64) ↦₃₂ (y32 <<< 8)) ∗
  ((fsp + 180#64) ↦₃₂ (y32 <<< 7)) ∗ ((fsp + 184#64) ↦₃₂ (y32 <<< 6)) ∗
  ((fsp + 192#64) ↦₃₂ (y32 <<< 5)) ∗ ((fsp + 200#64) ↦₃₂ (y32 <<< 4)) ∗
  ((fsp + 208#64) ↦₃₂ (y32 <<< 3)) ∗ ((fsp + 216#64) ↦₃₂ (y32 <<< 2)) ∗
  ((fsp + 224#64) ↦₃₂ (y32 <<< 1))

/-- Raw 32-bit stack slots at `fsp + 148..228`. -/
@[expose] def shiftSlotsRawAt_pl (fsp : BitVec 64) : SepProp :=
  ∃∗ d148 : BitVec 32, ∃∗ d152 : BitVec 32, ∃∗ d156 : BitVec 32, ∃∗ d160 : BitVec 32,
  ∃∗ d164 : BitVec 32, ∃∗ d168 : BitVec 32, ∃∗ d172 : BitVec 32, ∃∗ d176 : BitVec 32,
  ∃∗ d180 : BitVec 32, ∃∗ d184 : BitVec 32, ∃∗ d192 : BitVec 32, ∃∗ d200 : BitVec 32,
  ∃∗ d208 : BitVec 32, ∃∗ d216 : BitVec 32, ∃∗ d224 : BitVec 32,
    ((fsp + 148#64) ↦₃₂ d148) ∗ ((fsp + 152#64) ↦₃₂ d152) ∗ ((fsp + 156#64) ↦₃₂ d156) ∗
    ((fsp + 160#64) ↦₃₂ d160) ∗ ((fsp + 164#64) ↦₃₂ d164) ∗ ((fsp + 168#64) ↦₃₂ d168) ∗
    ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 176#64) ↦₃₂ d176) ∗ ((fsp + 180#64) ↦₃₂ d180) ∗
    ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₃₂ d192) ∗ ((fsp + 200#64) ↦₃₂ d200) ∗
    ((fsp + 208#64) ↦₃₂ d208) ∗ ((fsp + 216#64) ↦₃₂ d216) ∗ ((fsp + 224#64) ↦₃₂ d224)

theorem shiftTableAt_entails_raw_pl (fsp : BitVec 64) (yv : BitVec 16) :
    shiftTableAt_pl fsp yv ⊢ shiftSlotsRawAt_pl fsp := by
  unfold shiftTableAt_pl shiftSlotsRawAt_pl; dsimp only
  iterate 15 apply Entails.sepExists_right
  exact Entails.refl _

/-- Unused 4-byte padding cells in `fsp + 144..232`. -/
@[expose] def shiftTablePadAt_pl (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 144#64) 4 ∗ memRegion (fsp + 188#64) 4 ∗ memRegion (fsp + 196#64) 4 ∗
  memRegion (fsp + 204#64) 4 ∗ memRegion (fsp + 212#64) 4 ∗ memRegion (fsp + 220#64) 4 ∗
  memRegion (fsp + 228#64) 4

theorem memRegion_112_split_sum_pl (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u112 : BitVec 64, ∃∗ u120 : BitVec 64, ∃∗ u128 : BitVec 64, ∃∗ u136 : BitVec 64,
        ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
        ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
        shiftSlotsRawAt_pl fsp ∗ shiftTablePadAt_pl fsp := by
  unfold shiftSlotsRawAt_pl shiftTablePadAt_pl
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 8) (k := 112) (b' := fsp + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 120#64) (n := 8) (k := 104) (b' := fsp + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 8) (k := 96) (b' := fsp + 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 136#64) (n := 8) (k := 88) (b' := fsp + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 144#64) (n := 4) (k := 84) (b' := fsp + 148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 148#64) (n := 4) (k := 80) (b' := fsp + 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 152#64) (n := 4) (k := 76) (b' := fsp + 156#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 156#64) (n := 4) (k := 72) (b' := fsp + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 160#64) (n := 4) (k := 68) (b' := fsp + 164#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 164#64) (n := 4) (k := 64) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 168#64) (n := 4) (k := 60) (b' := fsp + 172#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 172#64) (n := 4) (k := 56) (b' := fsp + 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 4) (k := 52) (b' := fsp + 180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 180#64) (n := 4) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 4) (k := 44) (b' := fsp + 188#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 188#64) (n := 4) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 4) (k := 36) (b' := fsp + 196#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 196#64) (n := 4) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 4) (k := 28) (b' := fsp + 204#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 204#64) (n := 4) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 4) (k := 20) (b' := fsp + 212#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 212#64) (n := 4) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 4) (k := 12) (b' := fsp + 220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 220#64) (n := 4) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 4) (k := 4) (b' := fsp + 228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 112#64), ProofLib.memRegion_eight (fsp + 120#64),
      ProofLib.memRegion_eight (fsp + 128#64), ProofLib.memRegion_eight (fsp + 136#64),
      ProofLib.memRegion_four (fsp + 148#64), ProofLib.memRegion_four (fsp + 152#64),
      ProofLib.memRegion_four (fsp + 156#64), ProofLib.memRegion_four (fsp + 160#64),
      ProofLib.memRegion_four (fsp + 164#64), ProofLib.memRegion_four (fsp + 168#64),
      ProofLib.memRegion_four (fsp + 172#64), ProofLib.memRegion_four (fsp + 176#64),
      ProofLib.memRegion_four (fsp + 180#64), ProofLib.memRegion_four (fsp + 184#64),
      ProofLib.memRegion_four (fsp + 192#64), ProofLib.memRegion_four (fsp + 200#64),
      ProofLib.memRegion_four (fsp + 208#64), ProofLib.memRegion_four (fsp + 216#64),
      ProofLib.memRegion_four (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d224; apply Entails.sepExists_elim; intro d216
  apply Entails.sepExists_elim; intro d208; apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro d192; apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro d180; apply Entails.sepExists_elim; intro d176
  apply Entails.sepExists_elim; intro d172; apply Entails.sepExists_elim; intro d168
  apply Entails.sepExists_elim; intro d164; apply Entails.sepExists_elim; intro d160
  apply Entails.sepExists_elim; intro d156; apply Entails.sepExists_elim; intro d152
  apply Entails.sepExists_elim; intro d148; apply Entails.sepExists_elim; intro u136
  apply Entails.sepExists_elim; intro u128; apply Entails.sepExists_elim; intro u120
  apply Entails.sepExists_elim; intro u112
  apply Entails.sepExists_right u112; apply Entails.sepExists_right u120
  apply Entails.sepExists_right u128; apply Entails.sepExists_right u136
  apply Entails.sepExists_right d148; apply Entails.sepExists_right d152
  apply Entails.sepExists_right d156; apply Entails.sepExists_right d160
  apply Entails.sepExists_right d164; apply Entails.sepExists_right d168
  apply Entails.sepExists_right d172; apply Entails.sepExists_right d176
  apply Entails.sepExists_right d180; apply Entails.sepExists_right d184
  apply Entails.sepExists_right d192; apply Entails.sepExists_right d200
  apply Entails.sepExists_right d208; apply Entails.sepExists_right d216
  apply Entails.sepExists_right d224
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_112_fold_sum_pl (fsp u112 u120 u128 u136 : BitVec 64) :
    ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
    ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
    shiftSlotsRawAt_pl fsp ∗ shiftTablePadAt_pl fsp ⊢
    memRegion (fsp + 112#64) 120 := by
  unfold shiftSlotsRawAt_pl shiftTablePadAt_pl
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d148; apply Entails.sepExists_elim; intro d152
  apply Entails.sepExists_elim; intro d156; apply Entails.sepExists_elim; intro d160
  apply Entails.sepExists_elim; intro d164; apply Entails.sepExists_elim; intro d168
  apply Entails.sepExists_elim; intro d172; apply Entails.sepExists_elim; intro d176
  apply Entails.sepExists_elim; intro d180; apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro d192; apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro d208; apply Entails.sepExists_elim; intro d216
  apply Entails.sepExists_elim; intro d224
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 8) (k := 112) (b' := fsp + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 120#64) (n := 8) (k := 104) (b' := fsp + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 8) (k := 96) (b' := fsp + 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 136#64) (n := 8) (k := 88) (b' := fsp + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 144#64) (n := 4) (k := 84) (b' := fsp + 148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 148#64) (n := 4) (k := 80) (b' := fsp + 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 152#64) (n := 4) (k := 76) (b' := fsp + 156#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 156#64) (n := 4) (k := 72) (b' := fsp + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 160#64) (n := 4) (k := 68) (b' := fsp + 164#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 164#64) (n := 4) (k := 64) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 168#64) (n := 4) (k := 60) (b' := fsp + 172#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 172#64) (n := 4) (k := 56) (b' := fsp + 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 4) (k := 52) (b' := fsp + 180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 180#64) (n := 4) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 4) (k := 44) (b' := fsp + 188#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 188#64) (n := 4) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 4) (k := 36) (b' := fsp + 196#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 196#64) (n := 4) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 4) (k := 28) (b' := fsp + 204#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 204#64) (n := 4) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 4) (k := 20) (b' := fsp + 212#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 212#64) (n := 4) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 4) (k := 12) (b' := fsp + 220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 220#64) (n := 4) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 4) (k := 4) (b' := fsp + 228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 112#64), ProofLib.memRegion_eight (fsp + 120#64),
      ProofLib.memRegion_eight (fsp + 128#64), ProofLib.memRegion_eight (fsp + 136#64),
      ProofLib.memRegion_four (fsp + 148#64), ProofLib.memRegion_four (fsp + 152#64),
      ProofLib.memRegion_four (fsp + 156#64), ProofLib.memRegion_four (fsp + 160#64),
      ProofLib.memRegion_four (fsp + 164#64), ProofLib.memRegion_four (fsp + 168#64),
      ProofLib.memRegion_four (fsp + 172#64), ProofLib.memRegion_four (fsp + 176#64),
      ProofLib.memRegion_four (fsp + 180#64), ProofLib.memRegion_four (fsp + 184#64),
      ProofLib.memRegion_four (fsp + 192#64), ProofLib.memRegion_four (fsp + 200#64),
      ProofLib.memRegion_four (fsp + 208#64), ProofLib.memRegion_four (fsp + 216#64),
      ProofLib.memRegion_four (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right d224; apply Entails.sepExists_right d216
  apply Entails.sepExists_right d208; apply Entails.sepExists_right d200
  apply Entails.sepExists_right d192; apply Entails.sepExists_right d184
  apply Entails.sepExists_right d180; apply Entails.sepExists_right d176
  apply Entails.sepExists_right d172; apply Entails.sepExists_right d168
  apply Entails.sepExists_right d164; apply Entails.sepExists_right d160
  apply Entails.sepExists_right d156; apply Entails.sepExists_right d152
  apply Entails.sepExists_right d148; apply Entails.sepExists_right u136
  apply Entails.sepExists_right u128; apply Entails.sepExists_right u120
  apply Entails.sepExists_right u112
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Bitvector Normalization Rules for `parallel_mult` Pair Loop -/

@[expose] def pmTerm_sm_pl (cv yv : BitVec 16) (i : Nat) : BitVec 32 :=
  (BitVec.zeroExtend 32 cv <<< i) &&& (if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32)

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zext64_sm_pl (v : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zext64_16_sm_pl (v : BitVec 16) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v) = BitVec.zeroExtend 32 v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_shl_zext64_32_sm_pl (v : BitVec 32) (k : Nat) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v <<< k) = v <<< k := by
  ext i hi; simp [hi, show i - k < 32 by omega]

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate16_zext64_16_sm_pl (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 v) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem zext16_trunc32_zext64_16_sm_pl (v : BitVec 16) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 (BitVec.zeroExtend 64 v)) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_xor_zext64_sm_pl (a b : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 a ^^^ BitVec.zeroExtend 64 b) = a ^^^ b := by bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_and_zext64_sm_pl (a b : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 a &&& BitVec.zeroExtend 64 b) = a &&& b := by bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate64_sxth32_16_sm_pl (x : BitVec 16) :
    BitVec.truncate 32 (BitVec.signExtend 64 x) = BitVec.signExtend 32 x := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem sbfx_bit0_sxth32_sm_pl (x : BitVec 16) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.signExtend 32 x) >>> 0 &&& 1#64 |||
        (if (BitVec.zeroExtend 64 (BitVec.signExtend 32 x)).getLsbD 0 = true then
            0xffffffffffffffff#64
          else 0#64) &&&
          0xfffffffffffffffe#64) =
      if x.getLsbD 0 = true then 0xffffffff#32 else 0#32 := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_sm_pl (yv x : BitVec 16) :
    (if x.getLsbD 0 = true then 0xffffffff#32 else 0#32) &&& BitVec.zeroExtend 32 yv =
      pmTerm_sm_pl yv x 0 := by
  dsimp only [pmTerm_sm_pl]; rw [BitVec.shiftLeft_zero, BitVec.and_comm]

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_zext64_sm_pl (yv x : BitVec 16) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (if x.getLsbD 0 = true then 0xffffffff#32 else 0#32) &&&
        BitVec.zeroExtend 64 yv) =
      pmTerm_sm_pl yv x 0 := by
  dsimp only [pmTerm_sm_pl]; generalize x.getLsbD 0 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate16_truncate32_64_sm_pl (x : BitVec 64) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by bv_bits

private theorem getLsbD_ffff_sm_pl (j : Fin 32) : (0xffffffff#32).getLsbD j.1 = true := by
  revert j; decide

private theorem getLsbD_zero_sm_pl (j : Fin 32) : (0#32).getLsbD j.1 = false := by
  revert j; decide

private theorem sshiftRight31_eq_ite_sm_pl (w : BitVec 32) :
    w.sshiftRight 31 = if w.getLsbD 31 = true then 0xffffffff#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega : ¬32 ≤ j), Bool.not_false,
      Bool.true_and, BitVec.msb_eq_getLsbD_last]
  have h31 : (if 31 + j < 32 then w.getLsbD (31 + j) else w.getLsbD (32 - 1)) = w.getLsbD 31 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rfl
    · simp [show ¬(31 + j < 32) by omega]
  rw [h31]
  cases w.getLsbD 31
  · exact (getLsbD_zero_sm_pl ⟨j, hj⟩).symm
  · exact (getLsbD_ffff_sm_pl ⟨j, hj⟩).symm

@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl30_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 30).sshiftRight 31 = if x.getLsbD 1 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 30).getLsbD 31 = x.getLsbD 1 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl29_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 29).sshiftRight 31 = if x.getLsbD 2 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 29).getLsbD 31 = x.getLsbD 2 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl28_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 28).sshiftRight 31 = if x.getLsbD 3 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 28).getLsbD 31 = x.getLsbD 3 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl27_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 27).sshiftRight 31 = if x.getLsbD 4 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 27).getLsbD 31 = x.getLsbD 4 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl26_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 26).sshiftRight 31 = if x.getLsbD 5 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 26).getLsbD 31 = x.getLsbD 5 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl25_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 25).sshiftRight 31 = if x.getLsbD 6 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 25).getLsbD 31 = x.getLsbD 6 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl24_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 24).sshiftRight 31 = if x.getLsbD 7 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 24).getLsbD 31 = x.getLsbD 7 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl23_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 23).sshiftRight 31 = if x.getLsbD 8 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 23).getLsbD 31 = x.getLsbD 8 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl22_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 22).sshiftRight 31 = if x.getLsbD 9 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 22).getLsbD 31 = x.getLsbD 9 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl21_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 21).sshiftRight 31 = if x.getLsbD 10 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 21).getLsbD 31 = x.getLsbD 10 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl20_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 20).sshiftRight 31 = if x.getLsbD 11 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 20).getLsbD 31 = x.getLsbD 11 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl19_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 19).sshiftRight 31 = if x.getLsbD 12 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 19).getLsbD 31 = x.getLsbD 12 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl18_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 18).sshiftRight 31 = if x.getLsbD 13 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 18).getLsbD 31 = x.getLsbD 13 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl17_asr31_pl (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 17).sshiftRight 31 = if x.getLsbD 14 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm_pl]; have h : (BitVec.signExtend 32 x <<< 17).getLsbD 31 = x.getLsbD 14 := by bv_bits
  rw [h]

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_mid_sm_pl (yv x : BitVec 16) (i : Nat) :
    (BitVec.zeroExtend 32 yv <<< i) &&& (if x.getLsbD i = true then 0xffffffff#32 else 0#32) =
      pmTerm_sm_pl yv x i := rfl

private theorem sxth32_trunc16_sm_pl (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 32 yv) = yv := by bv_bits
private theorem sxth32_shr16_sm_pl (yv : BitVec 16) :
    (BitVec.signExtend 32 yv) >>> 16 = if yv.getLsbD 15 then 0xffff#32 else 0#32 := by bv_bits
private theorem sxth33_trunc16_sm_pl (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) = yv := by bv_bits
private theorem sxth33_shr16_sm_pl (yv : BitVec 16) :
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) >>> 16 =
      if yv.getLsbD 15 then 131071#33 else 0#33 := by bv_bits
private theorem yv_shr15_sm_pl (yv : BitVec 16) :
    yv >>> 15 = if yv.getLsbD 15 then 1#16 else 0#16 := by bv_bits
private theorem beq_bne_self_sm_pl (a b : Bool) : (b == (a != b)) = !a := by
  cases a <;> cases b <;> rfl

private theorem adds_sxth_one_gt_sm_pl (yv : BitVec 16) :
    ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = !yv.getLsbD 15 := by
  have hlo32 := congrArg BitVec.toNat (sxth32_trunc16_sm_pl yv)
  have hhi32 := congrArg BitVec.toNat (sxth32_shr16_sm_pl yv)
  have hlo33 := congrArg BitVec.toNat (sxth33_trunc16_sm_pl yv)
  have hhi33 := congrArg BitVec.toNat (sxth33_shr16_sm_pl yv)
  have hb15 := congrArg BitVec.toNat (yv_shr15_sm_pl yv)
  rw [BitVec.toNat_setWidth] at hlo32 hlo33
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hhi32 hhi33 hb15
  have hlt16 : yv.toNat < 2 ^ 16 := yv.isLt
  have hlt32 : (BitVec.signExtend 32 yv).toNat < 2 ^ 32 := (BitVec.signExtend 32 yv).isLt
  have hlt33 : (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat < 2 ^ 33 :=
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).isLt
  unfold ConditionHolds addsPState32 AddWithCarry32; dsimp only; rw [beq_bne_self_sm_pl]
  cases hb : yv.getLsbD 15 <;>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hhi32 hhi33 hb15 ⊢
  · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', beq_eq_false_iff_ne]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 0 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 0 at hhi33
    change yv.toNat / 32768 = 0 at hb15
    refine ⟨fun h => ?_, ?_⟩
    · have ht := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
    · rw [BitVec.msb_eq_false_iff_two_mul_lt]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]; omega
  · rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', beq_iff_eq]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 65535 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 131071 at hhi33
    change yv.toNat / 32768 = 1 at hb15
    by_cases hy : yv.toNat = 65535
    · left; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · right; rw [BitVec.msb_eq_true_iff_two_mul_ge]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]; omega

@[local arm64_norm ↓, local wp_norm ↓]
theorem csel_gt_cmn1_sxth32_sm_pl (yv x : BitVec 16) :
    (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 x) 1#32) = true then 0#64
     else BitVec.truncate 64 (BitVec.zeroExtend 32 yv <<< 15)) =
      BitVec.zeroExtend 64 (pmTerm_sm_pl yv x 15) := by
  dsimp only [pmTerm_sm_pl]; rw [adds_sxth_one_gt_sm_pl]; generalize x.getLsbD 15 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem csel_gt_cmn1_sxth32_zext_sm_pl (yv x : BitVec 16) :
    (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 x) 1#32) = true then 0#64
     else BitVec.zeroExtend 64 (BitVec.zeroExtend 32 yv <<< 15)) =
      BitVec.zeroExtend 64 (pmTerm_sm_pl yv x 15) := by
  dsimp only [pmTerm_sm_pl]; rw [adds_sxth_one_gt_sm_pl]; generalize x.getLsbD 15 = b; cases b <;> bv_slice

private theorem ite_xor_eq_xor_and_mask_sm_pl (b : Bool) (acc x : BitVec 32) :
    (if b = true then acc ^^^ x else acc) =
      acc ^^^ (x &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

private theorem test_bit16_eq_getLsbD_sm_pl (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (0#16 != yv &&& (1#16 <<< i)) = yv.getLsbD i := by
  match i, hi with
  | 0, _ => bv_slice | 1, _ => bv_slice | 2, _ => bv_slice | 3, _ => bv_slice
  | 4, _ => bv_slice | 5, _ => bv_slice | 6, _ => bv_slice | 7, _ => bv_slice
  | 8, _ => bv_slice | 9, _ => bv_slice | 10, _ => bv_slice | 11, _ => bv_slice
  | 12, _ => bv_slice | 13, _ => bv_slice | 14, _ => bv_slice | 15, _ => bv_slice
  | n + 16, hi => omega

private theorem pmTerm_rhs_0_sm_pl (cv yv : BitVec 16) :
    (if (0#16 != yv &&& (1#16 <<< 0)) = true then BitVec.zeroExtend 32 cv <<< 0 else 0#32) =
      pmTerm_sm_pl cv yv 0 := by
  dsimp only [pmTerm_sm_pl]; rw [test_bit16_eq_getLsbD_sm_pl yv 0 (by decide)]
  generalize yv.getLsbD 0 = b; cases b <;> bv_slice

private theorem pmTerm_rhs_sm_pl (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (BitVec.zeroExtend 32 cv <<< i) &&&
      (if (0#16 != yv &&& (1#16 <<< i)) = true then 0xffff_ffff#32 else 0#32) =
      pmTerm_sm_pl cv yv i := by
  dsimp only [pmTerm_sm_pl]; rw [test_bit16_eq_getLsbD_sm_pl yv i hi]

attribute [local irreducible] pmTerm_sm_pl in
theorem unaccelerated_polyMul_eq_pmTerms_sm_pl (cv yv : BitVec 16) :
    unaccelerated.polyMul cv yv =
      pmTerm_sm_pl cv yv 0 ^^^ pmTerm_sm_pl cv yv 1 ^^^ pmTerm_sm_pl cv yv 2 ^^^ pmTerm_sm_pl cv yv 3 ^^^
      pmTerm_sm_pl cv yv 4 ^^^ pmTerm_sm_pl cv yv 5 ^^^ pmTerm_sm_pl cv yv 6 ^^^ pmTerm_sm_pl cv yv 7 ^^^
      pmTerm_sm_pl cv yv 8 ^^^ pmTerm_sm_pl cv yv 9 ^^^ pmTerm_sm_pl cv yv 10 ^^^ pmTerm_sm_pl cv yv 11 ^^^
      pmTerm_sm_pl cv yv 12 ^^^ pmTerm_sm_pl cv yv 13 ^^^ pmTerm_sm_pl cv yv 14 ^^^ pmTerm_sm_pl cv yv 15 := by
  simp only [unaccelerated.polyMul, unaccelerated.polyMulLoop,
    ite_xor_eq_xor_and_mask_sm_pl, Nat.reduceAdd, BitVec.zero_xor,
    pmTerm_rhs_0_sm_pl cv yv, pmTerm_rhs_sm_pl cv yv 1 (by decide),
    pmTerm_rhs_sm_pl cv yv 2 (by decide), pmTerm_rhs_sm_pl cv yv 3 (by decide),
    pmTerm_rhs_sm_pl cv yv 4 (by decide), pmTerm_rhs_sm_pl cv yv 5 (by decide),
    pmTerm_rhs_sm_pl cv yv 6 (by decide), pmTerm_rhs_sm_pl cv yv 7 (by decide),
    pmTerm_rhs_sm_pl cv yv 8 (by decide), pmTerm_rhs_sm_pl cv yv 9 (by decide),
    pmTerm_rhs_sm_pl cv yv 10 (by decide), pmTerm_rhs_sm_pl cv yv 11 (by decide),
    pmTerm_rhs_sm_pl cv yv 12 (by decide), pmTerm_rhs_sm_pl cv yv 13 (by decide),
    pmTerm_rhs_sm_pl cv yv 14 (by decide), pmTerm_rhs_sm_pl cv yv 15 (by decide)]

attribute [irreducible] pmTerm_sm_pl

@[local arm64_norm ↓, local wp_norm ↓]
theorem polyMul_pair_c1_eq_pl (yv x : BitVec 16) :
    (((pmTerm_sm_pl yv x 0 ^^^ pmTerm_sm_pl yv x 15 ^^^ pmTerm_sm_pl yv x 1 ^^^
        (pmTerm_sm_pl yv x 2 ^^^ pmTerm_sm_pl yv x 3)) ^^^
       (pmTerm_sm_pl yv x 4 ^^^ pmTerm_sm_pl yv x 5 ^^^ pmTerm_sm_pl yv x 6)) ^^^
      ((pmTerm_sm_pl yv x 7 ^^^ pmTerm_sm_pl yv x 8 ^^^ pmTerm_sm_pl yv x 9) ^^^
       pmTerm_sm_pl yv x 10)) ^^^
     (((pmTerm_sm_pl yv x 11 ^^^ pmTerm_sm_pl yv x 12) ^^^ pmTerm_sm_pl yv x 13) ^^^
      pmTerm_sm_pl yv x 14) =
      unaccelerated.polyMul yv x := by
  rw [unaccelerated_polyMul_eq_pmTerms_sm_pl]; ac_rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem polyMul_pair_c2_eq_pl (yv x : BitVec 16) :
    ((((pmTerm_sm_pl yv x 0 ^^^ pmTerm_sm_pl yv x 15) ^^^ pmTerm_sm_pl yv x 1) ^^^
       (pmTerm_sm_pl yv x 2 ^^^ pmTerm_sm_pl yv x 3)) ^^^
      ((pmTerm_sm_pl yv x 4 ^^^ pmTerm_sm_pl yv x 5) ^^^ pmTerm_sm_pl yv x 6)) ^^^
     (((pmTerm_sm_pl yv x 7 ^^^ pmTerm_sm_pl yv x 8) ^^^ pmTerm_sm_pl yv x 9) ^^^
      pmTerm_sm_pl yv x 10) ^^^
     ((((pmTerm_sm_pl yv x 11 ^^^ pmTerm_sm_pl yv x 12) ^^^ pmTerm_sm_pl yv x 13) ^^^
       pmTerm_sm_pl yv x 14)) =
      unaccelerated.polyMul yv x := by
  rw [unaccelerated_polyMul_eq_pmTerms_sm_pl]; ac_rfl

/-! ## 4. Precomputed Shift-Table Setup (`(blkPl_416).base + 2752#64 -> + 3384#64`) -/

theorem shiftTableInit_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat) (yv : BitVec 16)
    (s : State) (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u112 u136 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_416).base + 3384#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      VmPreserved s s1 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x18 = lsρ reduceTableSym →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = clonePtr →
      s1.readReg64 .x26 = 2#64 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (shiftTableAt_pl fsp yv ∗ ((fsp + 112#64) ↦₆₄ clonePtr) ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (shiftSlotsRawAt_pl fsp ∗ ((fsp + 112#64) ↦₆₄ u112) ∗
       ((fsp + 136#64) ↦₆₄ u136) ∗ Frame) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  unfold shiftSlotsRawAt_pl
  apply sepWP_exists_left_sep; intro d148; apply sepWP_exists_left_sep; intro d152
  apply sepWP_exists_left_sep; intro d156; apply sepWP_exists_left_sep; intro d160
  apply sepWP_exists_left_sep; intro d164; apply sepWP_exists_left_sep; intro d168
  apply sepWP_exists_left_sep; intro d172; apply sepWP_exists_left_sep; intro d176
  apply sepWP_exists_left_sep; intro d180; apply sepWP_exists_left_sep; intro d184
  apply sepWP_exists_left_sep; intro d192; apply sepWP_exists_left_sep; intro d200
  apply sepWP_exists_left_sep; intro d208; apply sepWP_exists_left_sep; intro d216
  apply sepWP_exists_left_sep; intro d224
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3384#64)
  intro _m_strip
  wp_steps 32
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ :=
    _hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp])
  unfold shiftTableAt_pl at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm]) hvm (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx22])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))

/-! ## 5. Odd Trailing Element (`(blkPl_416).base + 3608#64 -> + 3784#64`) -/

attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  polyReduce_setWidth16_eq polyReduce_setWidth16_comm_eq mul2UnreducedWord_truncate32

@[local arm64_norm, local wp_norm]
private theorem zext64_trunc32_shr32_mul2Unreduced_sm1 (a b1 b2 : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32)) =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc32_shr32_mul2Unreduced_sm1 (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32) =
      unaccelerated.polyMul a b1 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem polyReduce_asm_eq_trunc_sm1 (a b_arg : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul a b_arg ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8) >>> 16))) ^^^
        (unaccelerated.polyMul a b_arg ^^^
          BitVec.zeroExtend 32
              (reduce.reduceByteEntry
                (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8).zeroExtend 64) =
      unaccelerated.mul a b_arg := by
  rw [← zeroExtend_16_truncate_32_64]
  exact polyReduce_asm_eq a b_arg

set_option maxHeartbeats 1600000 in
theorem parallelMultOddTail_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (idx : Nat) (yv : BitVec 16) (last : GF16) (hidx_lt : 2 * idx < 2 ^ 63)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 idx)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 : State,
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      VmPreserved s s1 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (gf16At ⟨unaccelerated.mul last.value yv⟩ (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
         onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (gf16At last (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
       onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
  apply sepWP_seq_lscl (mid := (blkPl_416).base + 3784#64) hcl
  have halign := GF.Mul2U16.aligned_tokenOnce_placed
  have honce : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  have hlsl : BitVec.ofNat 64 idx <<< 1 = BitVec.ofNat 64 (2 * idx) := shl_one_ofNat_eq_nat_sm_pl idx
  unfold gf16At
  wp_simp_pre [tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`)
    wp_simp_pre [tokenUnprobedPlacedAt, onceScratch416_split_odd fsp, allocHookStack_split_once fsp]
    wp_pull_exists
    apply sepWP_seq_lscl (mid := (blkPl_416).base + 3648#64) hcl
    wp_steps 2
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [arm64_norm]; rfl
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    apply sepWP_seg_416 (mid := (blkPl_416).base + 3748#64)
    intro _m_strip
    wp_steps 13
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_once0 : VmPreserved s _ :=
      (by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans
        (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp]))
    wp_steps 1
    wp_call honce
    have hvm_once1 : VmPreserved s sf :=
      (hvm_once0.trans (by
        unfold VmPreserved LibsignalBinary.Heap.PoolPreserved LibsignalBinary.Heap.FdsHiFrame
        exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)).trans (by assumption)
    have htr_once1 : sf.trace = s.trace :=
      (by assumption : sf.trace = _).trans (by simp only [wp_norm, arm64_norm])
    have _hsp_once : sf.sp = fsp := by simp only [arm64_norm, wp_norm, *]
    have _hx19_once : sf.readReg64 .x19 = BitVec.ofNat 64 idx := by simp only [arm64_norm, wp_norm, *]
    have _hx21_once : sf.readReg64 .x21 = BitVec.zeroExtend 64 yv := by simp only [arm64_norm, wp_norm, *]
    have _hx22_once : sf.readReg64 .x22 = clonePtr := by simp only [arm64_norm, wp_norm, *]
    wp_steps 7
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl_once
    apply SepWP.fold (allocHookStack_merge_once fsp) (by sep_focus)
    apply SepWP.fold (onceScratch416_merge_odd fsp _ _) (by sep_focus)
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    have hmul_after := lscall_blk (callerProg := (blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl_once
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec, BitVec.ofNat_eq_ofNat] at hmul_after
    wp_steps 1
    wp_call hmul_after (last.value, yv, 0#16)
    have hvm_mul : VmPreserved s sf_1 := by
      apply VmPreserved.trans; swap; assumption
      exact hvm_once1.trans (by simp only [arm64_norm, wp_norm])
    have htr_mul : sf_1.trace = s.trace :=
      (by assumption : sf_1.trace = _).trans (by simpa [arm64_norm, wp_norm] using htr_once1)
    have _hsp_mul : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
    have _hx19_mul : sf_1.readReg64 .x19 = BitVec.ofNat 64 idx := by simp only [arm64_norm, wp_norm, *]
    have _hx22_mul : sf_1.readReg64 .x22 = clonePtr := by simp only [arm64_norm, wp_norm, *]
    apply sepWP_seg_416 (mid := (blkPl_416).base + 3784#64)
    intro _m_strip2
    wp_steps 4
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24)),
          uxtx1_hi_idx1_nomask_eq last.value yv 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq last.value yv 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul last.value yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul last.value yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 3
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm_tot : VmPreserved s _ :=
      hvm_mul.trans (_hnsp2.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun_sf_1]))
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    unfold gf16At at hcont; dsimp only at hcont
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ hcl1 (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        hvm_tot
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))
  · -- Probed fast path (`probed = true`)
    have hmul := lscall_blk (callerProg := (blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec, BitVec.ofNat_eq_ofNat] at hmul
    wp_simp_pre [tokenProbedPlacedAt]
    wp_steps 2
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [arm64_norm]; rfl
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 9
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul (last.value, yv, 0#16)
    have hvm_mul : VmPreserved s sf := by
      apply VmPreserved.trans; swap; assumption
      simp only [arm64_norm, wp_norm]
    have htr_mul : sf.trace = s.trace :=
      (by assumption : sf.trace = _).trans (by simp only [arm64_norm, wp_norm])
    have _hsp_mul : sf.sp = fsp := by simp only [arm64_norm, wp_norm, ‹sf.sp = _›, hsp]
    have _hx19_mul : sf.readReg64 .x19 = BitVec.ofNat 64 idx := by simp only [arm64_norm, wp_norm, *]
    have _hx22_mul : sf.readReg64 .x22 = clonePtr := by simp only [arm64_norm, wp_norm, *]
    apply sepWP_seg_416 (mid := (blkPl_416).base + 3784#64)
    intro _m_strip
    wp_steps 4
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24)),
          uxtx1_hi_idx1_nomask_eq last.value yv 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq last.value yv 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul last.value yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul last.value yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul last.value yv >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 3
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_tot : VmPreserved s _ :=
      hvm_mul.trans (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun_sf]))
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    unfold gf16At at hcont; dsimp only at hcont
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ hcl1 (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, ‹sf.sp = _›, hsp])
        (by simp only [arm64_norm, wp_norm, htr_mul])
        hvm_tot
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))
