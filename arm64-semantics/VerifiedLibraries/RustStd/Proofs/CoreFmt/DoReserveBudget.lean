/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FinishGrowBudget
public meta import ProofLib.ProgramReflection

/-!
# Budgeted `RawVecInner::reserve::do_reserve_and_handle`

Placement-generic, budget-threaded verification of
`<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<Global>` (`allocBlocks[1]`)
over `RustAllocBudget` (`budgetDoReserveSpec`, `budgetDoReserveAndHandle_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open VerifiedLibraries.Mallocng (AllocEvent)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern PureSegPreserved
   sepWP_seg_lib_block_pureWhere sepWPp_seg_lib_block_pureWhere)

/-- Budget-threaded, panic-aware contract for
    `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<Global>` (`allocBlocks[1]`)
    over `A : RustAllocBudget` and `fmtBufVecAt A`. -/
def budgetDoReserveSpec (A : RustAllocBudget)
    (reserveStack : Nat := defaultAllocReserveStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × A.σ) where
  pre := fun (vecPtr, ptr, cap, bs, additional, st) s0 =>
    ⌜s0.readReg64 .x0 = vecPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 additional ∧
      additional < 2 ^ 64 ∧
      cap.toNat - bs.length < additional⌝ ∗
    (stackAt s0.sp reserveStack ∗
      (vecPtr ↦₆₄ cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
      fmtBufVecAt A cap ptr bs ∗
      A.pool st s0)
  post := fun (vecPtr, _, cap, bs, additional, st) s0 sf =>
    let growCap := stringGrowCap cap.toNat bs.length additional
    ∃∗ newPtr : BitVec 64,
      ⌜AllocCallPreserved s0 sf ∧ growCap < 2 ^ 63⌝ ∗
      (stackAt s0.sp reserveStack ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 growCap) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
        fmtBufVecAt A (BitVec.ofNat 64 growCap) newPtr bs ∗
        A.pool (A.stepEvents (stringGrowStepEvents cap growCap) st) sf)
  onPanic := fun (_, _, cap, bs, additional, _) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      (2 ^ 64 ≤ bs.length + additional ∨
        NullAllowed (stringGrowCap cap.toNat bs.length additional) 1)⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom  := fun (_, _, cap, bs, additional, st) s0 sf =>
    ⌜¬ A.FitsEvents st
        (stringGrowStepEvents cap (stringGrowCap cap.toNat bs.length additional)) ∧
      OomPreserved s0 sf⌝

section DoReserveProof
arm64_proof_prelude

private theorem budgetDoReserve_finishGrow_pc [AllocPlacement] :
    allocPl01.base + reloc_call_off% allocLib01.text.relocs
        "<alloc::raw_vec::RawVecInner>::finish_grow [rust_alloc]" +
      (allocPl01.ρ allocFinishGrowSym - allocPl01.base -
        reloc_call_off% allocLib01.text.relocs
          "<alloc::raw_vec::RawVecInner>::finish_grow [rust_alloc]") =
      allocMultiLib.resolve AllocPlacement.mpl allocFinishGrowSym := by
  change allocPl01.base + _ +
    (allocMultiLib.resolve AllocPlacement.mpl allocFinishGrowSym - allocPl01.base - _) =
    allocMultiLib.resolve AllocPlacement.mpl allocFinishGrowSym
  bv_lin

private theorem budgetDoReserve_handleError0_pc [AllocPlacement] :
    allocPl01.base + reloc_call_off% allocLib01.text.relocs
        "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error" 0 +
      (allocPl01.ρ allocBudgetHandleErrorSym - allocPl01.base -
        reloc_call_off% allocLib01.text.relocs
          "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error" 0) =
      allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym := by
  change allocPl01.base + _ +
    (allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym - allocPl01.base - _) =
    allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym
  bv_lin

private theorem budgetDoReserve_handleError1_pc [AllocPlacement] :
    allocPl01.base + reloc_call_off% allocLib01.text.relocs
        "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error" 1 +
      (allocPl01.ρ allocBudgetHandleErrorSym - allocPl01.base -
        reloc_call_off% allocLib01.text.relocs
          "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error" 1) =
      allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym := by
  change allocPl01.base + _ +
    (allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym - allocPl01.base - _) =
    allocMultiLib.resolve AllocPlacement.mpl allocBudgetHandleErrorSym
  bv_lin

private abbrev budgetDoReserveSavedSlots (s0 : State) (st0 : BitVec 64) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ st0) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem budgetCsel_hi_ofNat_eq_max {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = true
     then BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (max a b) := by
  by_cases h : b < a
  · have hult : (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, h]
    rw [hult]; simp [Nat.max_eq_left (Nat.le_of_lt h)]
  · have hult : (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; omega
    rw [hult]; simp [Nat.max_eq_right (by omega : a ≤ b)]

private theorem budgetAdds_ult_true_of_ge64 {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hge : 2 ^ 64 ≤ a + b) :
    (BitVec.ofNat 64 (a + b)).ult (BitVec.ofNat 64 a) = true ∧
      (BitVec.ofNat 64 (a + b)).ult (BitVec.ofNat 64 b) = true := by
  have hm : (a + b) % 2 ^ 64 = a + b - 2 ^ 64 := by omega
  constructor <;>
  · rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hm]
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; omega

private theorem budgetAdds_ult_false_of_lt64 {a b : Nat} (hlt : a + b < 2 ^ 64) :
    (BitVec.ofNat 64 (a + b)).ult (BitVec.ofNat 64 a) = false ∧
      (BitVec.ofNat 64 (a + b)).ult (BitVec.ofNat 64 b) = false := by
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  constructor <;>
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

set_option maxHeartbeats 800000 in
theorem budgetDoReserveAndHandle_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl)
    {P : Program} {reserveStack : Nat}
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : defaultAllocReserveStack ≤ reserveStack ∧ reserveStack ≤ 2 ^ 64 := by decide)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocDoReserveSym)
      (allocWithCodeLoadedWhere keep mpl (budgetDoReserveSpec A reserveStack)) := by
  letI : AllocPlacement := ⟨mpl, hpl⟩
  rw [allocResolve_eq_base hpl 1 allocDoReserveSym (by decide) allocDoReserve_lookup]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨vecPtr, ptr, cap, bs, additional, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere,
    budgetDoReserveSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hadd_lt, hgt⟩, hmem⟩
  have ⟨hbs_le, hcap_lt, _⟩ : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 :=
    satisfies_fmtBufVecAt_bounds (m := s0.mem)
      (R := stackAt s0.sp reserveStack ∗ (vecPtr ↦₆₄ cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗ A.pool st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  conv =>
    arg 4
    rw [stackAt_shrink s0.sp reserveStack defaultAllocReserveStack hstk.1 hstk.2,
      show defaultAllocReserveStack = (32 + Rust.hookStack) + 8 * 8 by decide,
      stackAt_split_cells s0.sp (32 + Rust.hookStack) 8 (by decide)]
    dsimp only [cells]
    simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun st0 => SepWPp.exists_elim fun st1 =>
    SepWPp.exists_elim fun st2 => SepWPp.exists_elim fun st3 =>
    SepWPp.exists_elim fun st4 => SepWPp.exists_elim fun st5 =>
    SepWPp.exists_elim fun st6 => SepWPp.exists_elim fun st7 => ?_
  have hadd_bv1 : BitVec.ofNat 64 additional + BitVec.ofNat 64 bs.length =
      BitVec.ofNat 64 (bs.length + additional) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd_bv2 : BitVec.ofNat 64 bs.length + BitVec.ofNat 64 additional =
      BitVec.ofNat 64 (bs.length + additional) := by rw [← BitVec.ofNat_add]
  by_cases hge64 : 2 ^ 64 ≤ bs.length + additional
  · have ⟨hult_b, hult_a⟩ := budgetAdds_ult_true_of_ge64 (by omega) hadd_lt hge64
    apply sepWPp_seg_lib_block_pureWhere (lib := allocMultiLib) 1 ⟨by decide, hk1⟩ hext1 allocBlockNoSvc0_01 hcl0
      (mid := allocMultiLib.resolve mpl allocBudgetHandleErrorSym)
    intro s1' hcpu1
    change SepWP (allocPC01.rebase allocPl01.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = allocPl01.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = vecPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx1_1' : s1'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 bs.length := (hcpu1.readReg64 .x1).trans hx1
    have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 additional := (hcpu1.readReg64 .x2).trans hx2
    wp_conv_pre => simp only [← hsp1_in]
    wp_sym_steps
    refine SepWP.done budgetDoReserve_handleError0_pc (by simpa [arm64_norm] using hrun1')
      fun sm_pan hcpu_pan _hcl_pan hseg_pan => ?_
    have ⟨hacp_0pan, _⟩ :=
      allocCall_vm_of_pureSeg hcpu1 hcpu_pan hseg_pan (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc_pan : sm_pan.pc = allocMultiLib.resolve mpl allocBudgetHandleErrorSym :=
      hcpu_pan.pc_eq.trans budgetDoReserve_handleError0_pc
    have hrun_pan : sm_pan.status = .Running := hcpu_pan.status_eq.trans hrun1'
    exact SepWPp.panic hrun_pan (hpc_pan.symm ▸ hpanic) fun hm_pan =>
      allowPanic_panicked ⟨by simpa [Rust.panicked] using hacp_0pan.1,
        by simpa [Rust.panicked] using hacp_0pan.2.1, Or.inl hge64⟩ hm_pan
  · have hlt64 : bs.length + additional < 2 ^ 64 := Nat.lt_of_not_ge hge64
    have ⟨hult_b, hult_a⟩ := budgetAdds_ult_false_of_lt64 hlt64
    let growCap := stringGrowCap cap.toNat bs.length additional
    have hgrow_ge8 : 8 ≤ growCap := by show 8 ≤ stringGrowCap ..; unfold stringGrowCap; omega
    have hgrow_lt64 : growCap < 2 ^ 64 := by show stringGrowCap .. < 2 ^ 64; unfold stringGrowCap; omega
    have hbs_le_grow : bs.length ≤ growCap := by show bs.length ≤ stringGrowCap ..; unfold stringGrowCap; omega
    have hlsl_cap : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 2 * cap.toNat < 2 ^ 64), Nat.shiftLeft_eq]
      omega
    apply sepWPp_seg_lib_block_pureWhere (lib := allocMultiLib) 1 ⟨by decide, hk1⟩ hext1 allocBlockNoSvc0_01 hcl0
      (mid := allocMultiLib.resolve mpl allocFinishGrowSym)
    intro s1' hcpu1
    change SepWP (allocPC01.rebase allocPl01.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = allocPl01.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = vecPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx1_1' : s1'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 bs.length := (hcpu1.readReg64 .x1).trans hx1
    have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 additional := (hcpu1.readReg64 .x2).trans hx2
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [← hsp1_in]
    wp_sym_steps
    refine SepWP.done budgetDoReserve_finishGrow_pc (by simpa [arm64_norm] using hrun1')
      fun sm1 hcpu_m1 hcl_m1 hseg_m1 => ?_
    have ⟨hacp_01, hvm_01⟩ :=
      allocCall_vm_of_pureSeg hcpu1 hcpu_m1 hseg_m1 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_01 : A.pool st s0 = A.pool st sm1 := (A.pool_transport st s0 sm1 hvm_01).symm
    have hpc_m1 : sm1.pc = allocMultiLib.resolve mpl allocFinishGrowSym :=
      hcpu_m1.pc_eq.trans budgetDoReserve_finishGrow_pc
    have hrun_m1 : sm1.status = .Running := hcpu_m1.status_eq.trans hrun1'
    have hsp_m1_eq : sm1.sp = s0.sp - 64#64 := hcpu_m1.sp_eq.trans (by simp [arm64_norm])
    have hsp_m1 : sm1.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_m1_eq]; exact s0.spAligned_sub 64#64 hsp0
    have hlr_m1 : sm1.readReg64 .lr =
        allocPl01.base + (reloc_call_off% allocLib01.text.relocs
          "<alloc::raw_vec::RawVecInner>::finish_grow [rust_alloc]" + 4#64) := by
      rw [hcpu_m1.readReg64 .lr]; simp [arm64_norm]
    have hx0_m1 : sm1.readReg64 .x0 = s0.sp - 56#64 := by rw [hcpu_m1.readReg64 .x0]; simp [arm64_norm]
    have hx1_m1 : sm1.readReg64 .x1 = cap := by rw [hcpu_m1.readReg64 .x1]; simp [arm64_norm]
    have hx2_m1 : sm1.readReg64 .x2 = ptr := by rw [hcpu_m1.readReg64 .x2]; simp [arm64_norm]
    have hgrow_bv :
        (if (8#64).ult
            (if (BitVec.ofNat 64 (2 * cap.toNat)).ult (BitVec.ofNat 64 (bs.length + additional)) = true
             then BitVec.ofNat 64 (bs.length + additional)
             else BitVec.ofNat 64 (2 * cap.toNat)) = true
         then
           if (BitVec.ofNat 64 (2 * cap.toNat)).ult (BitVec.ofNat 64 (bs.length + additional)) = true
           then BitVec.ofNat 64 (bs.length + additional)
           else BitVec.ofNat 64 (2 * cap.toNat)
         else 8#64) = BitVec.ofNat 64 growCap := by
      rw [budgetCsel_hi_ofNat_eq_max (a := bs.length + additional) (b := 2 * cap.toNat) hlt64 (by omega),
        budgetCsel_hi_ofNat_eq_max (a := max (bs.length + additional) (2 * cap.toNat)) (b := 8) (by omega) (by decide)]
      congr 1
      show max (max (bs.length + additional) (2 * cap.toNat)) 8 = stringGrowCap cap.toNat bs.length additional
      unfold stringGrowCap; omega
    have hx3_m1 : sm1.readReg64 .x3 = BitVec.ofNat 64 growCap := by
      rw [hcpu_m1.readReg64 .x3]; simp only [arm64_norm, hlsl_cap]; exact hgrow_bv
    have hx20_m1 : sm1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap := by
      rw [hcpu_m1.readReg64]; simp only [arm64_norm, hlsl_cap]; exact hgrow_bv
    have hx19_m1 : sm1.readReg64 (.gpr 19#5) = vecPtr := by rw [hcpu_m1.readReg64]; simp [arm64_norm]
    have hgprs_m1 : BudgetGrowHighGprs s0 sm1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hcpu_m1.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _
    have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
      hcpu_m1.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    refine SepWPp.weaken_pre (P' :=
        stackAt sm1.sp (32 + Rust.hookStack) ∗
        vecHeader (s0.sp - 56#64) st1 st2 st3 ∗
        fmtBufVecAt A cap ptr bs ∗ A.pool st sm1 ∗
        budgetDoReserveSavedSlots s0 st0 ∗
        (vecPtr ↦₆₄ cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
        memRegion (s0.sp - BitVec.ofNat 64 reserveStack) (reserveStack - defaultAllocReserveStack))
      (by
        rw [hsp1_in, hpool_eq_01, hsp_m1_eq]
        dsimp only [vecHeader, budgetDoReserveSavedSlots]
        sep_entail) ?_
    have hfg := budgetFinishGrow_ok A hk2 hpl hext2 hshim halloc hrealloc
    apply (SepWPp.call_wpp hfg
      (x := (s0.sp - 56#64, st1, st2, st3, cap, ptr, bs, growCap, st))
      hpc_m1 hrun_m1 hsp_m1 hlr_m1
      (hoom := fun sf_oom R' _ hm_oom => by
        have hm' := Satisfies.drop_mid hm_oom
        dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere,
          budgetFinishGrowSpec] at hm'
        rw [satisfies_pure_sepConj] at hm' ⊢
        exact ⟨⟨hm'.1.1, oomPreserved_of_allocCall hacp_01 hm'.1.2⟩, hm'.2⟩))
    · intro R' hm'
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetFinishGrowSpec]
      rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl sm1.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcl_m1, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_m1, hx1_m1, hx2_m1, hx3_m1, by omega, hgrow_lt64, hbs_le_grow⟩,
        Satisfies.mono (by sep_frame) hm'⟩
    · intro _ _ _ _ h; exact not_satisfies_false_sepConj h
    · intro _ _ _ h
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetFinishGrowSpec] at h
      rw [sepConj_assoc] at h
      exact False.elim (not_satisfies_false_sepConj h)
    · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetFinishGrowSpec]
      conv =>
        arg 4
        simp only [sepExists_sepConj_left, sepConj_assoc, hsp_m1_eq]
      apply SepWPp.pure_elim; intro hcl_sf1
      refine SepWPp.exists_elim fun isErr => SepWPp.exists_elim fun newPtr =>
        SepWPp.exists_elim fun errW1 => SepWPp.exists_elim fun errW2 => ?_
      apply SepWPp.pure_elim; intro hacp_1f
      have hacp_0f1 : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hacp_01 hacp_1f
      have hsp_sf1_eq : sf1.sp = s0.sp - 64#64 := hsp_sf1.trans hsp_m1_eq
      have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = vecPtr := hcs_sf1.readReg64_x19.trans hx19_m1
      have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap :=
        hcs_sf1.readReg64_x20.trans hx20_m1
      have hgprs_sf1 : BudgetGrowHighGprs s0 sf1 :=
        hgprs_m1.trans (BudgetGrowHighGprs.of_calleeSaved hcs_sf1)
      have hvregs_sf1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hcs_sf1.vregs.trans hvregs_m1
      cases isErr
      · conv =>
          arg 4
          simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
          rw [sepConj_left_comm (stackAt (s0.sp - 64#64) (32 + Rust.hookStack)) ⌜growCap < 2 ^ 63⌝]
        apply SepWPp.pure_elim; intro hgrow_lt63
        apply SepWPp.of_sepWP_ret
        apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 1 ⟨by decide, hk1⟩ hext1 allocBlockNoSvc0_01 hcl_sf1
          (mid := s0.readReg64 .lr)
        intro s2' hcpu2
        change SepWP (allocPC01.rebase allocPl01.base (fun _ => none)) _ _ _ _
        have hpc2' := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hsp2_in : s2'.sp = s0.sp - 64#64 := hcpu2.sp_eq.trans hsp_sf1_eq
        have hsp2' : s2'.spAligned = true := by
          simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 64#64 hsp0
        have hx19_2' : s2'.readReg64 (.gpr 19#5) = vecPtr := (hcpu2.readReg64 _).trans hx19_sf1
        have hx20_2' : s2'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap :=
          (hcpu2.readReg64 _).trans hx20_sf1
        wp_conv_pre => simp only [budgetDoReserveSavedSlots, vecHeader, ← hsp2_in,
          show s0.sp - 56#64 = s2'.sp + 8#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 48#64 = s2'.sp + 16#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 40#64 = s2'.sp + 24#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 32#64 = s2'.sp + 32#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 24#64 = s2'.sp + 40#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 16#64 = s2'.sp + 48#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 8#64 = s2'.sp + 56#64 by rw [hsp2_in]; bv_lin]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2')
          fun sf hcpu_f hcl_f hseg_f => ?_
        have ⟨hacp_f, hvm_f⟩ :=
          allocCall_vm_of_pureSeg hcpu2 hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
        have hacp_end : AllocCallPreserved s0 sf := allocCallPreserved_trans hacp_0f1 hacp_f
        have hpool_eq_end :
            A.pool (A.stepEvents (stringGrowStepEvents cap growCap) st) sf1 =
            A.pool (A.stepEvents (stringGrowStepEvents cap growCap) st) sf :=
          (A.pool_transport _ sf1 sf hvm_f).symm
        have hpc_end : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
        have hrun_end : sf.status = .Running := hcpu_f.status_eq.trans hrun2'
        have hsp_end : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
        have hcs_end : CalleeSavedPreserved s0 sf := by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨by rw [hcpu_f.readReg64]; simp [arm64_norm],
            by rw [hcpu_f.readReg64]; simp [arm64_norm],
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.2.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.2.2.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.2.2.2.2.1,
            by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu2.readReg64 _).trans hgprs_sf1.2.2.2.2.2.2.2,
            by rw [hcpu_f.readReg64]; simp [arm64_norm],
            hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s2').trans
              (hcpu2.calleeSavedVRegs.trans hvregs_sf1))⟩
        refine SepWP.done hpc_end hrun_end
          ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_end, hcs_end⟩
        rw [pure_sepConj_of_true hcl_f]
        refine Entails.sepExists_right newPtr ?_
        rw [pure_sepConj_of_true ⟨hacp_end, hgrow_lt63⟩, hpool_eq_end, hsp2_in,
          stackAt_shrink s0.sp reserveStack defaultAllocReserveStack hstk.1 hstk.2,
          show defaultAllocReserveStack = (32 + Rust.hookStack) + 8 * 8 by decide,
          stackAt_split_cells s0.sp (32 + Rust.hookStack) 8 (by decide)]
        dsimp only [cells]
        simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_lin_norm]
        exact Entails.sepExists_right st0 <| Entails.sepExists_right 0#64 <|
          Entails.sepExists_right newPtr <| Entails.sepExists_right (BitVec.ofNat 64 growCap) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)
      · conv =>
          arg 4
          simp only [↓reduceIte, sepConj_assoc]
          rw [sepConj_left_comm (stackAt (s0.sp - 64#64) (32 + Rust.hookStack)) ⌜NullAllowed growCap 1⌝]
        apply SepWPp.pure_elim; intro hnull
        apply sepWPp_seg_lib_block_pureWhere (lib := allocMultiLib) 1 ⟨by decide, hk1⟩ hext1 allocBlockNoSvc0_01 hcl_sf1
          (mid := allocMultiLib.resolve mpl allocBudgetHandleErrorSym)
        intro s2' hcpu2
        change SepWP (allocPC01.rebase allocPl01.base (fun _ => none)) _ _ _ _
        have hpc2' := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hsp2_in : s2'.sp = s0.sp - 64#64 := hcpu2.sp_eq.trans hsp_sf1_eq
        have hsp2' : s2'.spAligned = true := by
          simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 64#64 hsp0
        wp_conv_pre => simp only [budgetDoReserveSavedSlots, vecHeader, ← hsp2_in,
          show s0.sp - 56#64 = s2'.sp + 8#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 48#64 = s2'.sp + 16#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 40#64 = s2'.sp + 24#64 by rw [hsp2_in]; bv_lin]
        wp_sym_steps
        refine SepWP.done budgetDoReserve_handleError1_pc (by simpa [arm64_norm] using hrun2')
          fun sm_pan hcpu_pan _hcl_pan hseg_pan => ?_
        have ⟨hacp_2pan, _⟩ :=
          allocCall_vm_of_pureSeg hcpu2 hcpu_pan hseg_pan (by simp [arm64_norm]) (by simp [arm64_norm])
        have hacp_0pan := allocCallPreserved_trans hacp_0f1 hacp_2pan
        have hpc_pan : sm_pan.pc = allocMultiLib.resolve mpl allocBudgetHandleErrorSym :=
          hcpu_pan.pc_eq.trans budgetDoReserve_handleError1_pc
        have hrun_pan : sm_pan.status = .Running := hcpu_pan.status_eq.trans hrun2'
        exact SepWPp.panic hrun_pan (hpc_pan.symm ▸ hpanic) fun hm_pan =>
          allowPanic_panicked ⟨by simpa [Rust.panicked] using hacp_0pan.1,
            by simpa [Rust.panicked] using hacp_0pan.2.1, Or.inr hnull⟩ hm_pan

end DoReserveProof

end VerifiedLibraries.RustStd
