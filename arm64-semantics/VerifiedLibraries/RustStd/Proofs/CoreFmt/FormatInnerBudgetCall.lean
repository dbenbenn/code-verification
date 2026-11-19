/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FormatInnerBudgetStage
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.StringWriterBudget

/-!
# Budgeted `format_inner`: `core::fmt::write` Call Stage

Stage lemmas for `allocMultiLib` block `3` against `allocFormatInnerBudgetSpec`, covering the
`core::fmt::write` call at `+0x110` (`FormatInnerBudgetSafe` refutes error, panic, and OOM
outcomes) and the `+0x128` return epilogue.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)
open FormatInnerBudget

section StageProofs
set_option maxRecDepth 200000
variable [FormatInnerPlacement]
arm64_proof_prelude

/-- Post-`core::fmt::write` epilogue from `+0x128` for `ok = true`: copies the 24-byte `String`
    from `sp + 8` to `x19 = ret`, restores callee-saved registers and `sp`, and returns. -/
theorem formatInnerBudget_after_fmtWrite
    {P : Program} (A : RustAllocBudget) (E : List AllocEvent → Prop) (va : StringWriteAddrs)
    (R_client : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {b0 : A.σ}
    {cs : List FmtCall} {st₀ st' : FmtBuf}
    {F_frame : SepProp} {s0 sf4 : State}
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hstart : FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs) st₀)
    (hrun_fmt : FmtRun (fmtInnerBudgetStep ArgStep) cs st₀ true st')
    (hE : E st'.evs)
    (hpc4 : sf4.pc = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvNtCs2kXltWtc1W_4core3fmt5write" + 4#64))
    (hrun4 : sf4.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp4 : sf4.sp = s0.sp - 96#64)
    (hcl4 : allocMultiLib.CodeLoaded fmtInnerMpl sf4.mem)
    (hw0 : sf4.readReg32 .x0 = 0#32)
    (hx19_4 : sf4.readReg64 .x19 = ret)
    (hhg_4 : FmtInnerHighGprs s0 sf4)
    (hvregs_4 : calleeSavedVRegs sf4 = calleeSavedVRegs s0)
    (hframe_4 : IoCallFrame s0 sf4 ∧ sf4.fs = s0.fs ∧ sf4.trace = s0.trace)
    (r0 r1 r2 v0 v7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sf4
      (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
        fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗
        A.pool (A.stepEvents st'.evs b0) sf4 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 v0 v7)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
            stackBytes).post (ret, argsRo, tpl, args, b0) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
            stackBytes).onPanic (ret, argsRo, tpl, args, b0) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
        stackBytes).onOom (ret, argsRo, tpl, args, b0) s0 sf) := by
  apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl4
    (mid := s0.readReg64 .lr)
  intro s5' hcpu5
  change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
  have hpc5' : s5'.pc = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvNtCs2kXltWtc1W_4core3fmt5write" + 4#64) :=
    hcpu5.pc_eq.trans hpc4
  have hrun5' : s5'.status = .Running := hcpu5.status_eq.trans hrun4
  have hsp5_in : s5'.sp = s0.sp - 96#64 := hcpu5.sp_eq.trans hsp4
  have hsp5' : s5'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp5_in]; exact s0.spAligned_sub 96#64 hsp0
  have hw0_5' : (s5'.readReg64 (.gpr 0#5)).setWidth 32 = 0#32 := by
    simp only [State.readReg32] at hw0
    rw [hcpu5.readReg64 .x0]; exact hw0
  have hx19_5' : s5'.readReg64 (.gpr 19#5) = ret := (hcpu5.readReg64 .x19).trans hx19_4
  wp_conv_pre =>
    dsimp only [fmtInnerSavedSlots]
    rw [vecHeader_def (s0.sp - 96#64 + 8#64), vecHeader_def ret, ← hsp5_in]
  wp_sym_steps
  wp_conv_pre =>
    rw [hsp5_in, ← vecHeader_def (s0.sp - 96#64 + 8#64), ← vecHeader_def ret]
  apply SepWP.done
    (by simp [wp_norm, arm64_norm])
    (by simpa [wp_norm, arm64_norm] using hrun5')
  intro sf hcpu_f _hcl_f hpseg_f
  obtain ⟨hframe_4f, _⟩ := ioCallFrame_of_pureSeg_fmt hcpu5 hcpu_f hpseg_f rfl rfl
  have hframe_0f := ioCallFrame_trans hframe_4 hframe_4f
  have hpcf : sf.pc = s0.readReg64 .lr := by
    rw [hcpu_f.pc_eq]; simp [wp_norm, arm64_norm]
  have hrunf : sf.status = .Running :=
    hcpu_f.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun5')
  have hspf : sf.sp = s0.sp := by
    rw [hcpu_f.sp_eq]; simp [wp_norm, arm64_norm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs, hcpu_f.calleeSavedVRegs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [wp_norm, arm64_norm] using (hcpu5.readReg64 .x24).trans hhg_4.x24
    · rw [hcpu_f.readReg64]; simpa [wp_norm, arm64_norm] using (hcpu5.readReg64 .x25).trans hhg_4.x25
    · rw [hcpu_f.readReg64]; simpa [wp_norm, arm64_norm] using (hcpu5.readReg64 .x26).trans hhg_4.x26
    · rw [hcpu_f.readReg64]; simpa [wp_norm, arm64_norm] using (hcpu5.readReg64 .x27).trans hhg_4.x27
    · rw [hcpu_f.readReg64]; simpa [wp_norm, arm64_norm] using (hcpu5.readReg64 .x28).trans hhg_4.x28
    · rw [hcpu_f.readReg64]; simp [wp_norm, arm64_norm]
    · simpa [wp_norm, arm64_norm] using hcpu5.calleeSavedVRegs.trans hvregs_4
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, hcsf⟩
  intro hmf
  have hpool_eq : A.pool (A.stepEvents st'.evs b0) sf = A.pool (A.stepEvents st'.evs b0) sf4 :=
    A.pool_of_pureSeg _ hpseg_f hframe_4f.1.1 hframe_4f.1.2.1
  dsimp only [allocFormatInnerBudgetSpec]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨st', ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hframe_0f.1, hframe_0f.2.1, hframe_0f.2.2, hE, cs, st₀, hdec, hstart, hrun_fmt⟩, ?_⟩
  rw [hpool_eq]
  have hstk_back :
      vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
      (((s0.sp - 96#64) ↦₆₄ v0) ∗
        ((s0.sp - 96#64 + 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 96#64 + 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 96#64 + 48#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 96#64 + 56#64) ↦₆₄ v7) ∗
        ((s0.sp - 96#64 + 64#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 96#64 + 72#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 96#64 + 80#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 96#64 + 88#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
      stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ⊢
      stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) := by
    have hsplit : formatInnerFrame + 0x70 + stackBytes = 96 + (0x70 + stackBytes) := by
      dsimp only [formatInnerFrame]; omega
    rw [hsplit, stackFrameAt_split s0.sp 96 (0x70 + stackBytes)
      (by dsimp only [formatInnerFrame] at hstk_fit; omega), ← sepConj_assoc]
    refine sepConj_mono_left ?_
    dsimp only [vecHeader]
    have h16 : s0.sp - 96#64 + 8#64 + 8#64 = s0.sp - 96#64 + 16#64 := by bv_arith
    have h24 : s0.sp - 96#64 + 8#64 + 16#64 = s0.sp - 96#64 + 24#64 := by bv_arith
    rw [h16, h24]
    exact Entails.trans (by sep_entail)
      (pts12_entails_stackFrameAt96 s0.sp v0 st'.cap st'.ptr
        (BitVec.ofNat 64 st'.bytes.length)
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
        (s0.readReg64 (.gpr 23#5)) v7
        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
  have hmf_reord : sf.mem ⊨
      (vecHeader ret st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
        fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗
        A.pool (A.stepEvents st'.evs b0) sf4 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          (((s0.sp - 96#64) ↦₆₄ v0) ∗
            ((s0.sp - 96#64 + 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 96#64 + 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 96#64 + 48#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 96#64 + 56#64) ↦₆₄ v7) ∗
            ((s0.sp - 96#64 + 64#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 96#64 + 72#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 96#64 + 80#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 96#64 + 88#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))) ∗ F_frame := by
    revert hmf; intro hmf; sep_frame
  refine Satisfies.mono (sepConj_mono_left ?_) hmf_reord
  exact sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
    sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right hstk_back

/-- Continuation from `+0x110`: invokes `core::fmt::write`, refutes the error, panic, and OOM
    outcomes via `FormatInnerBudgetSafe`, and finishes via `formatInnerBudget_after_fmtWrite`. -/
theorem formatInnerBudget_from_110
    {P : Program} (A : RustAllocBudget) (E : List AllocEvent → Prop) (va : StringWriteAddrs)
    (R_client : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {b0 : A.σ}
    {cs : List FmtCall} {st₀ : FmtBuf}
    {F_frame : SepProp} {s0 sm3 : State}
    (hfmtWrite : ∀ out : BitVec 64,
      subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym)
        (coreFmtWriteSpec P (fmtInnerBudgetW A b0 va R_client s0 out)
          (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanicInv s0 ArgPanic)
          (fmtInnerBudgetOom A b0 ArgOom) stackBytes))
    (hwriteStr : ∀ (out ptr : BitVec 64) (bs : List (BitVec 8)),
      subroutine_ok P va.writeStr
        (fmtWriteStrCallSpec (fmtInnerBudgetW A b0 va R_client s0 out)
          (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanic s0 ArgPanic)
          (fmtInnerBudgetOom A b0 ArgOom) stackBytes out ptr bs))
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hfit : FitsEnv A b0 E)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hsafe : FormatInnerBudgetSafe A b0 E ArgStep ArgPanic ArgOom (s0.readReg64 .x1) cs)
    (hargsOk : FmtInnerBudgetArgsOk P A b0 va R_client ArgStep ArgPanic ArgOom stackBytes s0 cs)
    (hstart : FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs) st₀)
    (hpc3 : sm3.pc = allocPl03.base + 272#64)
    (hrun3 : sm3.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp3 : sm3.sp = s0.sp - 96#64)
    (hcl3 : allocMultiLib.CodeLoaded fmtInnerMpl sm3.mem)
    (hx19_3 : sm3.readReg64 .x19 = ret)
    (hx20_3 : sm3.readReg64 .x20 = s0.readReg64 .x1)
    (hx21_3 : sm3.readReg64 .x21 = s0.readReg64 .x0)
    (hhg_3 : FmtInnerHighGprs s0 sm3)
    (hvregs_3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (hframe_3 : IoCallFrame s0 sm3 ∧ sm3.fs = s0.fs ∧ sm3.trace = s0.trace)
    (r0 r1 r2 v0 v7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sm3
      (vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
        fmtBufVecAt A st₀.cap st₀.ptr st₀.bytes ∗
        A.pool (A.stepEvents st₀.evs b0) sm3 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 v0 v7)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
            stackBytes).post (ret, argsRo, tpl, args, b0) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
            stackBytes).onPanic (ret, argsRo, tpl, args, b0) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom
        stackBytes).onOom (ret, argsRo, tpl, args, b0) s0 sf) := by
  let out : BitVec 64 := s0.sp - 96#64 + 8#64
  apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl3
    (mid := allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym)
  intro s3' hcpu3
  change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
  have hpc3' : s3'.pc = allocPl03.base + 272#64 := hcpu3.pc_eq.trans hpc3
  have hrun3' : s3'.status = .Running := hcpu3.status_eq.trans hrun3
  have hsp3_in : s3'.sp = s0.sp - 96#64 := hcpu3.sp_eq.trans hsp3
  have hsp3' : s3'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp3_in]; exact s0.spAligned_sub 96#64 hsp0
  have hx19_3' : s3'.readReg64 .x19 = ret := (hcpu3.readReg64 .x19).trans hx19_3
  have hx20_3' : s3'.readReg64 .x20 = s0.readReg64 .x1 := (hcpu3.readReg64 .x20).trans hx20_3
  have hx21_3' : s3'.readReg64 .x21 = s0.readReg64 .x0 := (hcpu3.readReg64 .x21).trans hx21_3
  wp_sym_steps
  apply SepWP.done
    (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
        exact bl_target_eq _ _ _)
    (by simpa [wp_norm, arm64_norm] using hrun3')
  intro sm4 hcpu_m4 hcl4 hpseg_4
  obtain ⟨hframe_34, _⟩ :=
    ioCallFrame_of_pureSeg_fmt hcpu3 hcpu_m4 hpseg_4 (by simp [arm64_norm]) (by simp [arm64_norm])
  have hframe_04 := ioCallFrame_trans hframe_3 hframe_34
  have hpc4 : sm4.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym := by
    rw [hcpu_m4.pc_eq]
    dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
    exact bl_target_eq _ _ _
  have hrun4 : sm4.status = .Running :=
    hcpu_m4.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun3')
  have hsp4_eq : sm4.sp = s0.sp - 96#64 := by
    rw [hcpu_m4.sp_eq]; simp [wp_norm, arm64_norm, hsp3_in]
  have hsp4 : sm4.spAligned = true := by
    simp only [State.spAligned]; rw [hsp4_eq]; exact s0.spAligned_sub 96#64 hsp0
  have hlr4 : sm4.readReg64 .lr = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvNtCs2kXltWtc1W_4core3fmt5write" + 4#64) := by
    rw [hcpu_m4.readReg64 .lr]; simp [wp_norm, arm64_norm]
  have hx0_m4 : sm4.readReg64 .x0 = out := by
    rw [hcpu_m4.readReg64 .x0]
    simp only [wp_norm, arm64_norm]
    dsimp only [out]; bv_arith
  have hx1_m4 : sm4.readReg64 .x1 = va.vtable := by
    rw [hcpu_m4.readReg64 .x1, hvt]
    simp only [wp_norm, arm64_norm]
    rfl
  have hx2_m4 : sm4.readReg64 .x2 = s0.readReg64 .x0 := by
    rw [hcpu_m4.readReg64 .x2]; simp only [wp_norm, arm64_norm]
  have hx3_m4 : sm4.readReg64 .x3 = s0.readReg64 .x1 := by
    rw [hcpu_m4.readReg64 .x3]; simp only [wp_norm, arm64_norm]
  have hx19_m4 : sm4.readReg64 .x19 = ret := by
    rw [hcpu_m4.readReg64 .x19]; simp only [wp_norm, arm64_norm]; exact hx19_3'
  have hhg_m4 : FmtInnerHighGprs s0 sm4 :=
    ⟨(hcpu_m4.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x24).trans hhg_3.x24),
     (hcpu_m4.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x25).trans hhg_3.x25),
     (hcpu_m4.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x26).trans hhg_3.x26),
     (hcpu_m4.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x27).trans hhg_3.x27),
     (hcpu_m4.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x28).trans hhg_3.x28)⟩
  have hvregs_m4 : calleeSavedVRegs sm4 = calleeSavedVRegs s0 :=
    hcpu_m4.calleeSavedVRegs.trans (by simpa [wp_norm, arm64_norm] using hcpu3.calleeSavedVRegs.trans hvregs_3)
  have hcb : FmtCallbacks P (fmtInnerBudgetW A b0 va R_client s0 out) (fmtInnerBudgetStep ArgStep)
      (fmtInnerBudgetPanicInv s0 ArgPanic) (fmtInnerBudgetOom A b0 ArgOom) stackBytes out
      va.vtable va.writeStr cs :=
    { transport := fmtInnerBudgetW_transport A b0 va R_client s0 out
      write_str := fun ptr bs _ =>
        fmtWriteStrCall_inv A b0 va R_client s0 _ _ _ stackBytes out ptr bs (hwriteStr out ptr bs)
      fmt_arg := fun idx value fmtFn opts hmem =>
        fmtArgCall_inv A b0 va R_client s0 _ _ _ stackBytes out va.vtable idx value opts
          (hargsOk idx value fmtFn opts hmem out) }
  refine sepWPp_call_alloc_codeLoaded hcl4 (hfmtWrite out)
    (x := (out, va.vtable, va.writeStr, argsRo, tpl, args, st₀))
    (F := vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7)
    hpc4 hrun4 hsp4 hlr4 ?_
    (fun _ _ _ _ h => not_satisfies_false_sepConj (by dsimp only [coreFmtWriteSpec] at h; exact h))
    ?_ ?_ ?_
  · intro R' hm'
    dsimp only [coreFmtWriteSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hstk70 : 0x70 + stackBytes ≤ 2 ^ 64 := by
      dsimp only [formatInnerFrame] at hstk_fit; omega
    refine ⟨⟨hx0_m4, hx1_m4, hstk70, cs, by rwa [hx2_m4, hx3_m4], hcb⟩, ?_⟩
    rw [hx2_m4, hx3_m4, hsp4_eq]
    dsimp only [fmtInnerBudgetW]
    rw [A.pool_of_pureSeg (A.stepEvents st₀.evs b0) hpseg_4 hframe_34.1.1 hframe_34.1.2.1]
    have hvt_dup : stringWriteVtableAt va =
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) := by
      simp only [stringWriteVtableAt, ← sepConj_assoc, pointsTo64RO_dup]
    rw [hvt_dup] at hm'
    have hm_pure : sm4.mem ⊨
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          (⌜IoCallFrame s0 sm4 ∧ sm4.fs = s0.fs ∧ sm4.trace = s0.trace⌝ ∗
            vecHeader out st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
            fmtBufVecAt A st₀.cap st₀.ptr st₀.bytes ∗ A.pool (A.stepEvents st₀.evs b0) sm3 ∗
            stringWriteVtableAt va ∗ R_client) ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes)) ∗
        ((vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7) ∗ R') := by
      rw [pure_sepConj_of_true hframe_04]; dsimp only [out]; revert hm'; intro hm'; sep_frame
    exact hm_pure
  · intro sf_p _hpan hmp
    exfalso
    dsimp only [coreFmtWriteSpec] at hmp
    rw [hx2_m4, hx3_m4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmp
    rcases hmp with ⟨⟨cs', c, st, hdec', hreach, hpan_c⟩, _⟩
    have hcs_eq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec); subst cs'
    exact not_fmtInnerBudgetPanicInv A b0 E ArgStep ArgPanic ArgOom _ cs s0 hfit hsafe
      hstart hreach hpan_c
  · intro sf4 hpc_sf4 hrun_sf4 hsp_sf4 hcs_sf4 hcl_sf4
    dsimp only [coreFmtWriteSpec]; rw [hx2_m4, hx3_m4, hsp4_eq]; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ok => SepWPp.exists_elim fun st' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hw0_sf4, cs', hdec', hrun_fmt'⟩ => ?_
    have hcs_eq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec); subst cs'
    cases ok with
    | false => exact absurd ⟨st₀, st', hstart, hrun_fmt'⟩ hsafe.2.2.2.1
    | true =>
    simp only [↓reduceIte] at hw0_sf4
    dsimp only [fmtInnerBudgetW]
    rw [sepConj_assoc ⌜IoCallFrame s0 sf4 ∧ sf4.fs = s0.fs ∧ sf4.trace = s0.trace⌝,
      pull_pure_after_two]
    refine SepWPp.pure_left fun hframe_sf4 => ?_
    have hvt_rejoin : (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) =
        stringWriteVtableAt va := by
      simp only [stringWriteVtableAt, ← sepConj_assoc, pointsTo64RO_dup]
    have hmerge :
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          ((vecHeader out st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
            fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗ A.pool (A.stepEvents st'.evs b0) sf4 ∗
            stringWriteVtableAt va ∗ R_client) ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))) ∗
        (vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7) =
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗ A.pool (A.stepEvents st'.evs b0) sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          R_client ∗ stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7) := by
      dsimp only [out]; apply Entails.antisymm <;> sep_entail
    have hreord :
        stringWriteVtableAt va ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗ A.pool (A.stepEvents st'.evs b0) sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          R_client ∗ stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7) =
        vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          fmtBufVecAt A st'.cap st'.ptr st'.bytes ∗ A.pool (A.stepEvents st'.evs b0) sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗ R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 v0 v7 := by
      apply Entails.antisymm <;> sep_entail
    rw [hmerge, hvt_rejoin, hreord]
    exact formatInnerBudget_after_fmtWrite A E va R_client ArgStep ArgPanic ArgOom stackBytes
      hext_blk hstk_fit hdec hstart hrun_fmt' (hsafe.2.2.1 st₀ st' hstart hrun_fmt')
      hpc_sf4 hrun_sf4 hsp0 (hsp_sf4.trans hsp4_eq) hcl_sf4 hw0_sf4
      (hcs_sf4.readReg64_x19.trans hx19_m4) (hhg_m4.of_cs hcs_sf4)
      (hcs_sf4.vregs.trans hvregs_m4) hframe_sf4 r0 r1 r2 v0 v7
  · intro sf_o R' _hoom hmo
    exfalso
    dsimp only [coreFmtWriteSpec] at hmo
    rw [satisfies_pure_sepConj] at hmo
    rcases hmo.1 with ⟨cs', c, st, hdec', hreach, hoom_c⟩
    rw [hx2_m4, hx3_m4] at hdec'
    have hcs_eq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec); subst cs'
    exact not_fmtInnerBudgetOom A b0 E ArgStep ArgPanic ArgOom _ cs hfit hsafe hstart hreach hoom_c

end StageProofs

end VerifiedLibraries.RustStd
