/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.DoReserveBudget
public meta import ProofLib.ProgramReflection

/-!
# Budgeted `<String as core::fmt::Write>::write_str` Proofs

Proves that `allocMultiLib` block `7` (`<alloc::string::String as core::fmt::Write>::write_str`)
satisfies `fmtWriteStrCallSpec` (`budgetWriteStr_fmtWriteStrCall_ok`) and `fmtWriterStrSpec`
(`budgetWriteStr_fmtWriterStr_ok`) over `RustAllocBudget`.
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

section WriterHelpers
arm64_proof_prelude

abbrev budgetWriterSavedSlots (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem budgetWriter_stack_split (sp : BitVec 64) :
    stackAt sp (48 + defaultAllocReserveStack) =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3, ∃∗ st4, ∃∗ st5,
        stackAt (sp - 48#64) defaultAllocReserveStack ∗
        (((sp - 48#64) ↦₆₄ st0) ∗ ((sp - 40#64) ↦₆₄ st1) ∗ ((sp - 32#64) ↦₆₄ st2) ∗
          ((sp - 24#64) ↦₆₄ st3) ∗ ((sp - 16#64) ↦₆₄ st4) ∗ ((sp - 8#64) ↦₆₄ st5)) := by
  rw [show 48 + defaultAllocReserveStack = defaultAllocReserveStack + 8 * 6 by decide,
    stackAt_split_cells sp defaultAllocReserveStack 6 (by decide)]
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, bv_lin_norm]

theorem budgetWriter_stack_refold (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    stackAt (sp - 48#64) defaultAllocReserveStack ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
        ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      stackAt sp (48 + defaultAllocReserveStack) := by
  rw [budgetWriter_stack_split sp]
  exact Entails.sepExists_right w0 <| Entails.sepExists_right w1 <| Entails.sepExists_right w2 <|
    Entails.sepExists_right w3 <| Entails.sepExists_right w4 <| Entails.sepExists_right w5 <| Entails.refl _

private theorem budgetWriter_stackFrame_refold (sp : BitVec 64) (stackBytes : Nat)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (Rest : SepProp) :
    Rest ∗ (stackAt (sp - 48#64) defaultAllocReserveStack ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
        ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ∗
      memRegion (sp - BitVec.ofNat 64 stackBytes) (stackBytes - stringWriterStack)) ⊢
      Rest ∗ stackFrameAt sp stackBytes := by
  refine sepConj_mono_right ?_
  rw [← stackAt_eq_stackFrameAt sp stackBytes hstk.2,
    stackAt_shrink sp stackBytes stringWriterStack hstk.1 hstk.2,
    show stringWriterStack = 48 + defaultAllocReserveStack from rfl, ← sepConj_assoc]
  exact Entails.trans (sepConj_mono_left (budgetWriter_stack_refold sp w0 w1 w2 w3 w4 w5))
    (Entails.of_eq (by ac_rfl))

def BudgetWriterHighGprs (s0 s1 : State) : Prop :=
  s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)

theorem BudgetWriterHighGprs.trans {s0 s1 s2 : State}
    (h01 : BudgetWriterHighGprs s0 s1) (h12 : BudgetWriterHighGprs s1 s2) :
    BudgetWriterHighGprs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.trans h01.2.2.2.2.2⟩

theorem BudgetWriterHighGprs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    BudgetWriterHighGprs s0 s1 :=
  ⟨h.readReg64_x23, h.readReg64_x24, h.readReg64_x25, h.readReg64_x26, h.readReg64_x27, h.readReg64_x28⟩

private theorem budgetWriteStr_memcpy_pc [AllocPlacement] :
    allocPl07.base + 60#64 + (allocPl07.ρ "memcpy" - allocPl07.base - 60#64) =
      allocMultiLib.resolve AllocPlacement.mpl "memcpy" := by
  change allocPl07.base + 60#64 + (allocMultiLib.resolve AllocPlacement.mpl "memcpy" - allocPl07.base - 60#64) = _; bv_lin

private theorem budgetWriteStr_reserve_pc [AllocPlacement] :
    allocPl07.base + 108#64 + (allocPl07.ρ allocDoReserveSym - allocPl07.base - 108#64) =
      allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym := by
  change allocPl07.base + 108#64 + (allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym - allocPl07.base - 108#64) = _; bv_lin

private theorem budgetWriter_bhi_cond {cap : BitVec 64} {len slen : Nat}
    (hlen : len ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hslen : slen < 2 ^ 64) :
    ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 slen)) = decide (cap.toNat - len < slen) := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]; · omega
    · rw [BitVec.le_def, hlen_bv]; exact hlen
  simp [BitVec.ult, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslen]

private theorem budgetReadReg32_x0_zero {s : State} (h : s.readReg64 .x0 = 0#64) :
    s.readReg32 .x0 = 0#32 := by
  simp [State.readReg32, State.readReg64] at h ⊢; rw [h]; rfl

theorem budgetIoCall_of_acp {t0 s0 sf : State}
    (h0 : IoCallFrame t0 s0 ∧ s0.fs = t0.fs ∧ s0.trace = t0.trace)
    (hacp : AllocCallPreserved s0 sf) :
    IoCallFrame t0 sf ∧ sf.fs = t0.fs ∧ sf.trace = t0.trace := by
  rcases hacp with ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩
  exact ⟨⟨hsig.trans h0.1.1, htp.trans h0.1.2.1, hbrkS.trans h0.1.2.2.1,
    horc.trans h0.1.2.2.2.1, hsym.trans h0.1.2.2.2.2⟩, hfs.trans h0.2.1, htr.trans h0.2.2⟩

private theorem budgetWriteStr_from_memcpy [AllocPlacement]
    (A : RustAllocBudget) {keep : Nat → Bool} (hk7 : keep 7 = true) {P : Program} {ro : Bool}
    (hext7 : LibBlockNoExtern allocMultiLib allocMpl P 7)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve allocMpl "memcpy") (budgetMemcpySpec ro))
    {s0 sm_mc : State} {self cap' ptr' slicePtr : BitVec 64}
    {bs sbs : List (BitVec 8)} {st_ev : A.σ} {Frame : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : allocMultiLib.CodeLoadedWhere keep allocMpl sm_mc.mem)
    (hpc : sm_mc.pc = allocMultiLib.resolve allocMpl "memcpy")
    (hrun : sm_mc.status = .Running) (hsp0 : s0.spAligned = true) (hsp_eq : sm_mc.sp = s0.sp - 48#64)
    (hlr : sm_mc.readReg64 .lr = allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64))
    (hx0 : sm_mc.readReg64 .x0 = ptr' + BitVec.ofNat 64 bs.length)
    (hx1 : sm_mc.readReg64 .x1 = slicePtr) (hx2 : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length)
    (hx19 : sm_mc.readReg64 (.gpr 19#5) = self)
    (hx20 : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length)
    (hx21 : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length)
    (hgprs : BudgetWriterHighGprs s0 sm_mc) (hvregs : calleeSavedVRegs sm_mc = calleeSavedVRegs s0)
    (hsbs_pos : 0 < sbs.length) (hfit : sbs.length ≤ cap'.toNat - bs.length)
    (hcont : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      AllocCallPreserved sm_mc sf → sf.readReg64 .x0 = 0#64 →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp (48 + defaultAllocReserveStack) ∗
          vecHeader self cap' ptr' (BitVec.ofNat 64 (bs.length + sbs.length)) ∗
          fmtBufVecAt A cap' ptr' (bs ++ sbs) ∗
          fmtSrcBytes ro slicePtr sbs ∗ A.pool st_ev sf ∗ Frame) → post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sm_mc
      (fmtBufVecAt A cap' ptr' bs ∗
        (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗ budgetWriterSavedSlots s0 ∗
          vecHeader self cap' ptr' (BitVec.ofNat 64 bs.length) ∗
          fmtSrcBytes ro slicePtr sbs ∗ A.pool st_ev sm_mc ∗ Frame))
      post oomProp := by
  wp_conv_pre => simp only [fmtBufVecAt, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hbs_le, hcap'_lt, hptr'_ne⟩
  have hcap'_pos : 0 < cap'.toNat := by omega
  have hcap'_ne0 : cap' ≠ 0#64 := by rintro rfl; simp at hcap'_pos
  wp_conv_pre => simp only [hcap'_ne0, ↓reduceIte, sepConj_assoc]
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 48#64 hsp0
  wp_conv_pre =>
    rw [memRegion_split_le (ptr' + BitVec.ofNat 64 bs.length) sbs.length (cap'.toNat - bs.length)
      hfit (by omega)]
  apply seqCodeLoadedWhere hcl (mid := allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64))
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr' + BitVec.ofNat 64 bs.length, slicePtr, sbs))
    hpc hrun hsp_mc hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [budgetMemcpySpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, by omega⟩, Satisfies.mono (by sep_frame) hm'⟩
  · intro sf_mc hpc_sfmc hrun_sfmc hsp_sfmc hcs_sfmc
    refine SepWP.done hpc_sfmc hrun_sfmc fun hcl_sfmc => ?_
    dsimp only [budgetMemcpySpec]; wp_conv_pre => simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hacp_mc, hvm_mc⟩
    have hpool_eq_mc : A.pool st_ev sm_mc = A.pool st_ev sf_mc := (A.pool_transport _ sm_mc sf_mc hvm_mc).symm
    have hsp_sfmc_eq : sf_mc.sp = s0.sp - 48#64 := hsp_sfmc.trans hsp_eq
    have hx19_sfmc : sf_mc.readReg64 (.gpr 19#5) = self := hcs_sfmc.readReg64_x19.trans hx19
    have hx20_sfmc : sf_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := hcs_sfmc.readReg64_x20.trans hx20
    have hx21_sfmc : sf_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := hcs_sfmc.readReg64_x21.trans hx21
    have hgprs_sfmc := hgprs.trans (BudgetWriterHighGprs.of_calleeSaved hcs_sfmc)
    have hvregs_sfmc := hcs_sfmc.vregs.trans hvregs
    apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 7 ⟨by decide, hk7⟩ hext7 allocBlockNoSvc0_07 hcl_sfmc
      (mid := s0.readReg64 .lr)
    intro se' hcpu_e
    change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
    have hpc_e' : se'.pc = allocPl07.base + 64#64 := hcpu_e.pc_eq.trans hpc_sfmc
    have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun_sfmc
    have hsp_e_in : se'.sp = s0.sp - 48#64 := hcpu_e.sp_eq.trans hsp_sfmc_eq
    have hsp_e' : se'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_e_in]; exact s0.spAligned_sub 48#64 hsp0
    have hx19_e' : se'.readReg64 (.gpr 19#5) = self := (hcpu_e.readReg64 _).trans hx19_sfmc
    have hx20_e' : se'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := (hcpu_e.readReg64 _).trans hx20_sfmc
    have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := (hcpu_e.readReg64 _).trans hx21_sfmc
    wp_conv_pre =>
      simp only [budgetWriterSavedSlots, vecHeader, hpool_eq_mc, ← hsp_e_in,
        show s0.sp - 40#64 = se'.sp + 8#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 32#64 = se'.sp + 16#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 24#64 = se'.sp + 24#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 16#64 = se'.sp + 32#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 8#64 = se'.sp + 40#64 by rw [hsp_e_in]; bv_lin]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
      fun sf hcpu_f _hcl_f hseg_f => ?_
    have ⟨hacp_ef, hvm_ef⟩ :=
      allocCall_vm_of_pureSeg hcpu_e hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_ef : A.pool st_ev sf_mc = A.pool st_ev sf := (A.pool_transport _ sf_mc sf hvm_ef).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun_e')
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hx0_f : sf.readReg64 .x0 = 0#64 := hcpu_f.readReg64 .x0 |>.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨by rw [hcpu_f.readReg64]; simp [arm64_norm], by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simp [arm64_norm], by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs_sfmc.2.2.2.2.2,
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs_sfmc))⟩
    refine SepWP.done hpc_f hrun_f (hcont sf hsp_f hcs_f (allocCallPreserved_trans hacp_mc hacp_ef) hx0_f ?_)
    have hstk_back := budgetWriter_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 22#5))
      (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    dsimp only [fmtBufVecAt, vecHeader]
    simp only [hcap'_ne0, ↓reduceIte, hsp_e_in]
    rw [pure_sepConj_of_true ⟨by simp [List.length_append]; omega, hcap'_lt, hptr'_ne⟩,
      pointsToBytes_append (a := ptr'),
      show ptr' + BitVec.ofNat 64 (bs ++ sbs).length =
        ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sbs.length by
        rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc],
      show cap'.toNat - (bs ++ sbs).length = cap'.toNat - bs.length - sbs.length by
        simp [List.length_append]; omega,
      show BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sbs.length =
        BitVec.ofNat 64 (bs.length + sbs.length) by rw [BitVec.ofNat_add],
      hpool_eq_ef]
    simp only [bv_lin_norm]
    exact Entails.trans (by sep_entail) (sepConj_mono_left hstk_back)

/-- Unified budgeted `write_str` contract over `fmtInnerBudgetW` and `fmtSrcBytes ro ptr sbs`,
    from which both `fmtWriteStrCallSpec` (`ro = true`) and `fmtWriterStrSpec` follow directly. -/
def budgetWriteStrCoreSpec (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs)
    (R : SepProp) (t0 : State) (stackBytes : Nat) (out : BitVec 64) (ro : Bool)
    (ptr : BitVec 64) (sbs : List (BitVec 8)) : Spec FmtBuf where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ptr ∧ (s.readReg64 .x2).toNat = sbs.length⌝ ∗
      fmtSrcBytes ro ptr sbs ∗ fmtInnerBudgetW A st0 va R t0 out st s ∗
      stackFrameAt s.sp stackBytes
  post := fun st s0 sf =>
    ∃∗ st' : FmtBuf,
      ⌜sf.readReg32 .x0 = 0#32 ∧ StringBufAppend st sbs st'⌝ ∗
        fmtSrcBytes ro ptr sbs ∗ fmtInnerBudgetW A st0 va R t0 out st' sf ∗
        stackFrameAt s0.sp stackBytes
  onPanic := fun st _ sf => ⌜StringBufWriterPanic t0 st sbs.length sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜StringBufWriterOom A st0 st sbs.length sf⌝

private theorem stringAppendEvents_of_gt {st : FmtBuf} {n : Nat}
    (hgt : ¬ st.bytes.length + n ≤ st.cap.toNat) :
    stringAppendEvents st n =
      st.evs ++ stringGrowStepEvents st.cap (stringGrowCap st.cap.toNat st.bytes.length n) := by
  simp [stringAppendEvents, stringGrowStepEvents, hgt]

set_option maxHeartbeats 800000 in
theorem budgetWriteStr_core_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true) (hk7 : keep 7 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl) {P : Program}
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (stackBytes : Nat) (out : BitVec 64) (ro : Bool) (ptr : BitVec 64) (sbs : List (BitVec 8))
    (hext7 : LibBlockNoExtern allocMultiLib mpl P 7)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve mpl "memcpy") (budgetMemcpySpec ro))
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocStringWriteStrSym)
      (allocMultiLib.withCodeLoadedWhere keep mpl
        (budgetWriteStrCoreSpec A st0 va R t0 stackBytes out ro ptr sbs)) := by
  letI : AllocPlacement := ⟨mpl, hpl⟩
  rw [allocResolve_eq_base hpl 7 allocStringWriteStrSym (by decide) allocWriteStr_lookup]
  apply subroutine_ok_of_sepWPp_init
  intro st R₀ s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, budgetWriteStrCoreSpec, fmtInnerBudgetW] at hpre ⊢
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat⟩, hpre⟩
  have hsbs_lt : sbs.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hpure0 : s0.mem ⊨ ⌜IoCallFrame t0 s0 ∧ s0.fs = t0.fs ∧ s0.trace = t0.trace⌝ ∗
      (fmtSrcBytes ro ptr sbs ∗ vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) s0 ∗
        stringWriteVtableAt va ∗ R ∗ stackFrameAt s0.sp stackBytes ∗ R₀) :=
    Satisfies.mono (by sep_entail) hpre
  rw [satisfies_pure_sepConj] at hpure0
  rcases hpure0 with ⟨hio0, hmem⟩
  have ⟨hbs_le, hcap_lt, _⟩ : st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63 ∧ st.ptr ≠ 0#64 :=
    satisfies_fmtBufVecAt_bounds (m := s0.mem)
    (R := fmtSrcBytes ro ptr sbs ∗ vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      A.pool (A.stepEvents st.evs st0) s0 ∗ stringWriteVtableAt va ∗ R ∗
      stackFrameAt s0.sp stackBytes ∗ R₀)
    (Satisfies.mono (by sep_entail) hmem)
  let stkRem : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - stringWriterStack)
  let Frame : SepProp := stringWriteVtableAt va ∗ R ∗ stkRem
  have hmem' : s0.mem ⊨
      (stackAt s0.sp (48 + defaultAllocReserveStack) ∗
        vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗ fmtSrcBytes ro ptr sbs ∗
        A.pool (A.stepEvents st.evs st0) s0 ∗ Frame) ∗ R₀ := by
    rw [← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
      stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2] at hmem
    exact Satisfies.mono (by dsimp only [Frame, stkRem, stringWriterStack]; sep_entail) hmem
  refine ⟨_, hmem', ?_⟩
  conv => arg 4; rw [budgetWriter_stack_split s0.sp]; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  by_cases hgt : st.cap.toNat - st.bytes.length < sbs.length
  · have hnle : ¬ st.bytes.length + sbs.length ≤ st.cap.toNat := by omega
    have hsbs_pos : 0 < sbs.length := by omega
    have hbhi : ((st.cap - BitVec.ofNat 64 st.bytes.length).ult (BitVec.ofNat 64 sbs.length)) = true := by
      rw [budgetWriter_bhi_cond hbs_le hcap_lt hsbs_lt, decide_eq_true hgt]
    apply sepWPp_seg_lib_block_pureWhere (lib := allocMultiLib) 7 ⟨by decide, hk7⟩ hext7 allocBlockNoSvc0_07 hcl0
      (mid := allocMultiLib.resolve mpl allocDoReserveSym)
    intro s1' hcpu1
    change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = out := (hcpu1.readReg64 .x0).trans hx0
    have hx1_1' : s1'.readReg64 (.gpr 1#5) = ptr := (hcpu1.readReg64 .x1).trans hx1
    have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 sbs.length := (hcpu1.readReg64 .x2).trans hx2
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done budgetWriteStr_reserve_pc (by simpa [arm64_norm] using hrun1')
      fun sm_res hcpu_mres hcl_mres hseg_mres => ?_
    have ⟨hacp_0res, hvm_0res⟩ :=
      allocCall_vm_of_pureSeg hcpu1 hcpu_mres hseg_mres (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0res : A.pool (A.stepEvents st.evs st0) s0 = A.pool (A.stepEvents st.evs st0) sm_res :=
      (A.pool_transport _ s0 sm_res hvm_0res).symm
    have hpc_mres : sm_res.pc = allocMultiLib.resolve mpl allocDoReserveSym :=
      hcpu_mres.pc_eq.trans budgetWriteStr_reserve_pc
    have hrun_mres : sm_res.status = .Running := hcpu_mres.status_eq.trans hrun1'
    have hsp_mres_eq : sm_res.sp = s0.sp - 48#64 := hcpu_mres.sp_eq.trans (by simp [arm64_norm])
    have hsp_mres : sm_res.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_mres_eq]; exact s0.spAligned_sub 48#64 hsp0
    have hlr_mres : sm_res.readReg64 .lr =
        allocPl07.base + (reloc_call_off% allocLib07.text.relocs
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]" + 4#64) := by
      rw [hcpu_mres.readReg64 .lr]; simp [arm64_norm]
    have hx0_mres : sm_res.readReg64 .x0 = out := by rw [hcpu_mres.readReg64 .x0]; simp [arm64_norm]
    have hx1_mres : sm_res.readReg64 .x1 = BitVec.ofNat 64 st.bytes.length := by
      rw [hcpu_mres.readReg64 .x1]; simp [arm64_norm]
    have hx2_mres : sm_res.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
      rw [hcpu_mres.readReg64 .x2]; simp [arm64_norm]
    have hx19_mres : sm_res.readReg64 (.gpr 19#5) = out := by rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hx20_mres : sm_res.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
      rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hx22_mres : sm_res.readReg64 (.gpr 22#5) = ptr := by rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hgprs_mres : BudgetWriterHighGprs s0 sm_res := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hcpu_mres.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _
    have hvregs_mres : calleeSavedVRegs sm_res = calleeSavedVRegs s0 :=
      hcpu_mres.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    have hsaved_mres : (((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) = budgetWriterSavedSlots s0 := by
      simp only [budgetWriterSavedSlots, hcpu1.readReg64]
    have hres := budgetDoReserveAndHandle_ok A hk1 hk2 hpl hext1 hext2 ⟨Nat.le_refl _, by decide⟩
      hpanic hshim halloc hrealloc
    refine SepWPp.weaken_pre (P' :=
        stackAt sm_res.sp defaultAllocReserveStack ∗
        (out ↦₆₄ st.cap) ∗ ((out + 8#64) ↦₆₄ st.ptr) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) sm_res ∗
        budgetWriterSavedSlots s0 ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
        fmtSrcBytes ro ptr sbs ∗ Frame)
      (by rw [hsp1_in, hpool_eq_0res, hsp_mres_eq, ← hsaved_mres]; sep_entail) ?_
    apply (SepWPp.call_wpp hres
      (x := (out, st.ptr, st.cap, st.bytes, sbs.length, A.stepEvents st.evs st0))
      hpc_mres hrun_mres hsp_mres hlr_mres
      (hoom := fun sf_oom R' _ hm_oom => by
        have hm' := Satisfies.drop_mid hm_oom
        dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec] at hm'
        rw [satisfies_pure_sepConj] at hm' ⊢
        refine ⟨fun hfit => hm'.1.1 ?_, hm'.2⟩
        rw [stringAppendEvents_of_gt hnle, A.fitsEvents_append] at hfit
        exact hfit.2))
    · intro R' hm'
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec]
      rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl sm_res.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcl_mres, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_mres, hx1_mres, hx2_mres, hsbs_lt, hgt⟩, Satisfies.mono (by sep_frame) hm'⟩
    · intro _ _ _ _ h; exact not_satisfies_false_sepConj h
    · intro sf_pan _ _ hm_pan
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec] at hm_pan
      exact allowPanic_frame
        (fun ⟨hfs, htr, hp⟩ => ⟨hfs.trans (hacp_0res.1.trans hio0.2.1),
          htr.trans (hacp_0res.2.1.trans hio0.2.2), by omega, hp⟩) hm_pan
    · intro sf_res hpc_sfres hrun_sfres hsp_sfres hcs_sfres
      apply SepWPp.of_sepWP_ret
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec]
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; intro hcl_sfres
      wp_conv_pre => rw [sepExists_sepConj_left]
      refine SepWP.exists_elim fun newPtr => ?_
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hacp_res, hgrow_lt63⟩
      have hsp_sfres_eq : sf_res.sp = s0.sp - 48#64 := hsp_sfres.trans hsp_mres_eq
      have hx19_sfres : sf_res.readReg64 (.gpr 19#5) = out := hcs_sfres.readReg64_x19.trans hx19_mres
      have hx20_sfres : sf_res.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length :=
        hcs_sfres.readReg64_x20.trans hx20_mres
      have hx22_sfres : sf_res.readReg64 (.gpr 22#5) = ptr := hcs_sfres.readReg64_x22.trans hx22_mres
      have hgprs_sfres := hgprs_mres.trans (BudgetWriterHighGprs.of_calleeSaved hcs_sfres)
      have hvregs_sfres := hcs_sfres.vregs.trans hvregs_mres
      let growCap := stringGrowCap st.cap.toNat st.bytes.length sbs.length
      have hgrow_toNat : (BitVec.ofNat 64 growCap).toNat = growCap := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : growCap < 2 ^ 64)]
      have hfit_grow : sbs.length ≤ (BitVec.ofNat 64 growCap).toNat - st.bytes.length := by
        have : st.bytes.length + sbs.length ≤ growCap := by show _ ≤ stringGrowCap ..; unfold stringGrowCap; omega
        rw [hgrow_toNat]; omega
      apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 7 ⟨by decide, hk7⟩ hext7 allocBlockNoSvc0_07 hcl_sfres
        (mid := allocMultiLib.resolve mpl "memcpy")
      intro sj' hcpu_j
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = allocPl07.base + 112#64 := hcpu_j.pc_eq.trans hpc_sfres
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_sfres
      have hsp_j_in : sj'.sp = s0.sp - 48#64 := hcpu_j.sp_eq.trans hsp_sfres_eq
      have hsp_j' : sj'.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_j_in]; exact s0.spAligned_sub 48#64 hsp0
      have hx19_j' : sj'.readReg64 (.gpr 19#5) = out := (hcpu_j.readReg64 _).trans hx19_sfres
      have hx20_j' : sj'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := (hcpu_j.readReg64 _).trans hx20_sfres
      have hx22_j' : sj'.readReg64 (.gpr 22#5) = ptr := (hcpu_j.readReg64 _).trans hx22_sfres
      wp_sym_steps
      refine SepWP.done budgetWriteStr_memcpy_pc (by simpa [arm64_norm] using hrun_j')
        fun sm_mc hcpu_mc hcl_mc hseg_mc => ?_
      have ⟨hacp_jmc, hvm_jmc⟩ :=
        allocCall_vm_of_pureSeg hcpu_j hcpu_mc hseg_mc (by simp [arm64_norm]) (by simp [arm64_norm])
      have hev_eq : A.stepEvents (stringGrowStepEvents st.cap growCap) (A.stepEvents st.evs st0) =
          A.stepEvents (stringAppendEvents st sbs.length) st0 := by
        rw [stringAppendEvents_of_gt hnle, A.stepEvents_append]
      have hpool_eq_jmc :
          A.pool (A.stepEvents (stringGrowStepEvents st.cap growCap) (A.stepEvents st.evs st0)) sf_res =
          A.pool (A.stepEvents (stringAppendEvents st sbs.length) st0) sm_mc := by
        rw [hev_eq]; exact (A.pool_transport _ sf_res sm_mc hvm_jmc).symm
      have hpc_mc : sm_mc.pc = allocMultiLib.resolve mpl "memcpy" := hcpu_mc.pc_eq.trans budgetWriteStr_memcpy_pc
      have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_j'
      have hsp_mc_eq : sm_mc.sp = s0.sp - 48#64 := (hcpu_mc.sp_eq.trans (by simp [arm64_norm])).trans hsp_j_in
      have hlr_mc : sm_mc.readReg64 .lr =
          allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64) := by
        rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
      have hx0_mc : sm_mc.readReg64 .x0 = newPtr + BitVec.ofNat 64 st.bytes.length := by
        rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
      have hx1_mc : sm_mc.readReg64 .x1 = ptr := by rw [hcpu_mc.readReg64 .x1]; simp [arm64_norm]
      have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm]
      have hx19_mc : sm_mc.readReg64 (.gpr 19#5) = out := by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using hx19_j'
      have hx20_mc : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64]; simpa [arm64_norm] using hx20_j'
      have hx21_mc : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 st.bytes.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hgprs_mc : BudgetWriterHighGprs s0 sm_mc :=
        ⟨by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.1,
         by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.1,
         by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.1,
         by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.1,
         by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.2.1,
         by rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.2.2⟩
      have hvregs_mc : calleeSavedVRegs sm_mc = calleeSavedVRegs s0 :=
        hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans hvregs_sfres))
      have hacp_0mc := allocCallPreserved_trans hacp_0res (allocCallPreserved_trans hacp_res hacp_jmc)
      refine SepWP.weaken_pre (by
        rw [hsp_mres_eq, hpool_eq_jmc]; dsimp only [budgetWriterSavedSlots, vecHeader, Frame, stkRem]; sep_entail) <|
        budgetWriteStr_from_memcpy (Frame := Frame) A hk7 hext7 hmemcpy hcl_mc hpc_mc hrun_mc hsp0 hsp_mc_eq
          hlr_mc hx0_mc hx1_mc hx2_mc hx19_mc hx20_mc hx21_mc hgprs_mc hvregs_mc hsbs_pos hfit_grow
          fun sf hsp_f hcs_f hacp_mcf hx0_f {_Pre_f} hent =>
            ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent (by
              let st' : FmtBuf :=
                { bytes := st.bytes ++ sbs, cap := BitVec.ofNat 64 growCap,
                  ptr := newPtr, evs := stringAppendEvents st sbs.length }
              refine Entails.sepExists_right st' ?_
              have happ : StringBufAppend st sbs st' :=
                ⟨rfl, by simp [st', stringNextCap, hnle, growCap], rfl, fun h => False.elim (hnle h)⟩
              dsimp only [st']
              rw [pure_sepConj_of_true ⟨budgetReadReg32_x0_zero hx0_f, happ⟩,
                pure_sepConj_of_true (budgetIoCall_of_acp hio0 (allocCallPreserved_trans hacp_0mc hacp_mcf)),
                List.length_append, ← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
                stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2]
              dsimp only [Frame, stkRem, stringWriterStack]
              sep_entail))) hm_out, hsp_f, hcs_f⟩
  · apply SepWPp.of_sepWP_ret
    have hle : sbs.length ≤ st.cap.toNat - st.bytes.length := Nat.le_of_not_lt hgt
    have hle_sum : st.bytes.length + sbs.length ≤ st.cap.toNat := by omega
    have hbhi : ((st.cap - BitVec.ofNat 64 st.bytes.length).ult (BitVec.ofNat 64 sbs.length)) = false := by
      rw [budgetWriter_bhi_cond hbs_le hcap_lt hsbs_lt, decide_eq_false hgt]
    by_cases hsbs0 : sbs.length = 0
    · have hsbs_nil : sbs = [] := List.eq_nil_of_length_eq_zero hsbs0
      apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 7 ⟨by decide, hk7⟩ hext7 allocBlockNoSvc0_07 hcl0
        (mid := s0.readReg64 .lr)
      intro s1' hcpu1
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = out := (hcpu1.readReg64 .x0).trans hx0
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = 0#64 := (hcpu1.readReg64 .x2).trans (hx2.trans (by simp [hsbs0]))
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 .lr := hcpu1.readReg64 .lr
      have hbhi0 : ((st.cap - BitVec.ofNat 64 st.bytes.length).ult 0#64) = false := by simp [BitVec.ult]
      wp_conv_pre => simp only [vecHeader, ← hsp1_in]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
        fun sf hcpu_f _hcl_f hseg_f => ?_
      have ⟨hacp_0f, hvm_0f⟩ :=
        allocCall_vm_of_pureSeg hcpu1 hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0f : A.pool (A.stepEvents st.evs st0) s0 = A.pool (A.stepEvents st.evs st0) sf :=
        (A.pool_transport _ s0 sf hvm_0f).symm
      have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
      have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun1')
      have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
      have hx0_f : sf.readReg64 .x0 = 0#64 := hcpu_f.readReg64 .x0 |>.trans (by simp [arm64_norm])
      have hcs_f : CalleeSavedPreserved s0 sf := by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          by rw [hcpu_f.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _,
          hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)⟩
      refine SepWP.done hpc_f hrun_f
        ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
      refine Entails.sepExists_right st ?_
      have happ : StringBufAppend st sbs st := by
        simp [StringBufAppend, hsbs_nil, stringNextCap, stringAppendEvents, hbs_le,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [pure_sepConj_of_true ⟨budgetReadReg32_x0_zero hx0_f, happ⟩,
        pure_sepConj_of_true (budgetIoCall_of_acp hio0 hacp_0f), hsp1_in, hpool_eq_0f]
      have hstk_back := budgetWriter_stackFrame_refold s0.sp stackBytes hstk
        (s1'.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s1'.readReg64 (.gpr 22#5))
        (s1'.readReg64 (.gpr 21#5)) (s1'.readReg64 (.gpr 20#5)) (s1'.readReg64 (.gpr 19#5))
        (fmtSrcBytes ro ptr sbs ∗ vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
          fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) sf ∗
          stringWriteVtableAt va ∗ R)
      exact Entails.trans (by dsimp only [vecHeader, Frame, stkRem, Reg.lr]; simp only [bv_lin_norm]; sep_entail)
        (Entails.trans hstk_back (by dsimp only [vecHeader]; sep_entail))
    · have hsbs_pos : 0 < sbs.length := Nat.pos_of_ne_zero hsbs0
      have hsbs_beq0 : (BitVec.ofNat 64 sbs.length == 0#64) = false := beq_false_of_ne (by bv_omega)
      apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 7 ⟨by decide, hk7⟩ hext7 allocBlockNoSvc0_07 hcl0
        (mid := allocMultiLib.resolve mpl "memcpy")
      intro s1' hcpu1
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = out := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = ptr := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 sbs.length := (hcpu1.readReg64 .x2).trans hx2
      wp_conv_pre => simp only [vecHeader, ← hsp1_in]
      wp_sym_steps
      refine SepWP.done budgetWriteStr_memcpy_pc (by simpa [arm64_norm] using hrun1')
        fun sm_mc hcpu_mc hcl_mc hseg_mc => ?_
      have ⟨hacp_0mc, hvm_0mc⟩ :=
        allocCall_vm_of_pureSeg hcpu1 hcpu_mc hseg_mc (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0mc : A.pool (A.stepEvents st.evs st0) s0 = A.pool (A.stepEvents st.evs st0) sm_mc :=
        (A.pool_transport _ s0 sm_mc hvm_0mc).symm
      have hpc_mc : sm_mc.pc = allocMultiLib.resolve mpl "memcpy" := hcpu_mc.pc_eq.trans budgetWriteStr_memcpy_pc
      have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun1'
      have hsp_mc_eq : sm_mc.sp = s0.sp - 48#64 := hcpu_mc.sp_eq.trans (by simp [arm64_norm])
      have hlr_mc : sm_mc.readReg64 .lr =
          allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64) := by
        rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
      have hx0_mc : sm_mc.readReg64 .x0 = st.ptr + BitVec.ofNat 64 st.bytes.length := by
        rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
      have hx1_mc : sm_mc.readReg64 .x1 = ptr := by rw [hcpu_mc.readReg64 .x1]; simpa [arm64_norm] using hx1_1'
      have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm]
      have hx19_mc : sm_mc.readReg64 (.gpr 19#5) = out := by rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hx20_mc : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hx21_mc : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 st.bytes.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hgprs_mc : BudgetWriterHighGprs s0 sm_mc := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _
      have hvregs_mc : calleeSavedVRegs sm_mc = calleeSavedVRegs s0 :=
        hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      refine SepWP.weaken_pre (by
        rw [hsp1_in, hpool_eq_0mc]; simp only [budgetWriterSavedSlots, vecHeader, hcpu1.readReg64]; sep_entail) <|
        budgetWriteStr_from_memcpy (Frame := Frame) A hk7 hext7 hmemcpy hcl_mc hpc_mc hrun_mc hsp0 hsp_mc_eq
          hlr_mc hx0_mc hx1_mc hx2_mc hx19_mc hx20_mc hx21_mc hgprs_mc hvregs_mc hsbs_pos hle
          fun sf hsp_f hcs_f hacp_mcf hx0_f {_Pre_f} hent =>
            ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent (by
              let st' : FmtBuf := { bytes := st.bytes ++ sbs, cap := st.cap, ptr := st.ptr, evs := st.evs }
              refine Entails.sepExists_right st' ?_
              have happ : StringBufAppend st sbs st' :=
                ⟨rfl, by simp [st', stringNextCap, hle_sum, BitVec.ofNat_toNat, BitVec.setWidth_eq],
                 by simp [st', stringAppendEvents, hle_sum], fun _ => rfl⟩
              dsimp only [st']
              rw [pure_sepConj_of_true ⟨budgetReadReg32_x0_zero hx0_f, happ⟩,
                pure_sepConj_of_true (budgetIoCall_of_acp hio0 (allocCallPreserved_trans hacp_0mc hacp_mcf)),
                List.length_append, ← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
                stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2]
              dsimp only [Frame, stkRem, stringWriterStack]
              sep_entail))) hm_out, hsp_f, hcs_f⟩

/-- Budgeted `<String as fmt::Write>::write_str` (`allocBlocks[7]`) meets `fmtWriterStrSpec`
    over `fmtInnerBudgetW A st0 va R t0 out`. -/
theorem budgetWriteStr_fmtWriterStr_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true) (hk7 : keep 7 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl) {P : Program}
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (stackBytes : Nat) (out : BitVec 64) (ro : Bool) (ptr : BitVec 64) (sbs : List (BitVec 8))
    (hext7 : LibBlockNoExtern allocMultiLib mpl P 7)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve mpl "memcpy") (budgetMemcpySpec ro))
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocStringWriteStrSym)
      (allocMultiLib.withCodeLoadedWhere keep mpl
        (fmtWriterStrSpec (fmtInnerBudgetW A st0 va R t0 out) StringBufStrStep
          (StringBufWriterPanic t0) (StringBufWriterOom A st0) stackBytes out ro ptr sbs)) := by
  have hcore := budgetWriteStr_core_ok A hk1 hk2 hk7 hpl st0 va R t0 stackBytes out ro ptr sbs
    hext7 hext1 hext2 hstk hpanic hmemcpy hshim halloc hrealloc
  apply subroutine_ok_outcome_intro
  intro st R₀ s0 hpc hrun hpre hsp0
  have hpre' : s0.mem ⊨
      (allocMultiLib.withCodeLoadedWhere keep mpl
        (budgetWriteStrCoreSpec A st0 va R t0 stackBytes out ro ptr sbs)).pre st s0 ∗ R₀ := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, fmtWriterStrSpec, budgetWriteStrCoreSpec] at hpre ⊢
    rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hp := hpre.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩
  refine hcore.mono_outcome st R₀ s0 hpc hrun hpre' hsp0 fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, budgetWriteStrCoreSpec] at hpost
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, fmtWriterStrSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨st', hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_right true (Entails.sepExists_right st' ?_))) hpost.2
    rw [pure_sepConj_of_true ⟨hpost.1.1, rfl, hpost.1.2⟩]; exact Entails.refl _
  · exact Or.inr hrest

/-- Budgeted `<String as fmt::Write>::write_str` (`allocBlocks[7]`) meets `fmtWriteStrCallSpec`
    (for `core::fmt::write` literal pieces) over `fmtInnerBudgetW A st0 va R t0 out`. -/
theorem budgetWriteStr_fmtWriteStrCall_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true) (hk7 : keep 7 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl) {P : Program}
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop)
    (t0 : State) (stackBytes : Nat) (out ptr : BitVec 64) (sbs : List (BitVec 8))
    (hext7 : LibBlockNoExtern allocMultiLib mpl P 7)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve mpl "memcpy") (budgetMemcpySpec true))
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocStringWriteStrSym)
      (allocMultiLib.withCodeLoadedWhere keep mpl
        (fmtWriteStrCallSpec (fmtInnerBudgetW A st0 va R t0 out) (fmtInnerBudgetStep ArgStep)
          (fmtInnerBudgetPanic t0 ArgPanic) (fmtInnerBudgetOom A st0 ArgOom)
          stackBytes out ptr sbs)) := by
  have hcore := budgetWriteStr_core_ok A hk1 hk2 hk7 hpl st0 va R t0 stackBytes out true ptr sbs
    hext7 hext1 hext2 hstk hpanic hmemcpy hshim halloc hrealloc
  apply subroutine_ok_outcome_intro
  intro st R₀ s0 hpc hrun hpre hsp0
  refine hcore.mono_outcome st R₀ s0 hpc hrun hpre hsp0 fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [MultiPlacedLib.withCodeLoadedWhere, budgetWriteStrCoreSpec, fmtSrcBytes, ↓reduceIte] at hpost
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, fmtWriteStrCallSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨st', hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hdrop : sf.mem ⊨ (ptr ↦ᵣ sbs) ∗
        ((fmtInnerBudgetW A st0 va R t0 out st' sf ∗ stackFrameAt s0.sp stackBytes) ∗ R₀) :=
      Satisfies.mono (by sep_entail) hpost.2
    refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_right true (Entails.sepExists_right st' ?_)))
      (Satisfies.drop_left hdrop)
    rw [pure_sepConj_of_true ⟨hpost.1.1, rfl, hpost.1.2⟩]; exact Entails.refl _
  · exact Or.inr hrest


end WriterHelpers

end VerifiedLibraries.RustStd
