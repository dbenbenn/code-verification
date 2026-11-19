/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FormatInnerBudgetAlloc
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerPrescan

/-!
# Budgeted `alloc::fmt::format::format_inner` Entry Proof

Proves `allocFormatInnerBudget_ok`: block `3` of `allocMultiLib` satisfies
`allocFormatInnerBudgetSpec` under `allocMultiLib.withCodeLoaded mpl`, covering
`Arguments::from_str` (odd `x1`), the empty template, and the template pre-scan.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)
open FormatInnerBudget

/-! ## Entry Stack, Sequencing, and Branch Helpers -/

section Helpers
arm64_proof_prelude

private theorem fmtEntryStack_split_b (sp : BitVec 64) (stackBytes : Nat)
    (hfit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp (formatInnerFrame + 0x70 + stackBytes) =
      (cells (sp - 96#64) 12 ∗ stackFrameAt (sp - 96#64) (0x70 + stackBytes)) := by
  have hsplit : formatInnerFrame + 0x70 + stackBytes = 96 + (0x70 + stackBytes) := by
    dsimp only [formatInnerFrame]; omega
  rw [hsplit, stackFrameAt_split sp 96 (0x70 + stackBytes) (by dsimp only [formatInnerFrame] at hfit; omega),
    ← stackAt_eq_stackFrameAt sp 96 (by decide),
    show (96 : Nat) = 8 * 12 from rfl,
    stackAt_eq_cells sp 12 (by decide)]

private theorem sepWP_seq_b {prog : Program} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {mid_post post : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P mid_post)
    (h2 : ∀ sm Pm, sm.pc = mid_pc → sm.status = .Running → mid_post sm Pm →
      SepWP prog target_pc sm Pm post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h1 ⊢
  intro R hm hL
  obtain ⟨sm, hs1, ⟨hpc_m, hrun_m, Pm, hmm, hmp⟩ | ⟨ho, hmo⟩⟩ := h1 R hm hL
  · have h2' := h2 sm Pm hpc_m hrun_m hmp
    unfold SepWP at h2'
    obtain ⟨sf, hs2, hout2⟩ := h2' R hmm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout2⟩
  · exact ⟨sm, hs1, Or.inr ⟨ho, hmo⟩⟩

private theorem sepWP_frame_left_b {prog : Program} {target_pc : BitVec 64}
    {s : State} {F P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P (fun sf Pf => post sf (F ∗ Pf))) :
    SepWP prog target_pc s (F ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  have hm' : s.mem ⊨ P ∗ (F ∗ R) := by revert hm; intro hm; sep_frame
  refine reaches_pc_mono (h (F ∗ R) hm') ?_
    (fun _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro sf _ _ ⟨Pf, hmf, hp⟩
  have hmf' : sf.mem ⊨ (F ∗ Pf) ∗ R := by revert hmf; intro hmf; sep_frame
  exact ⟨F ∗ Pf, hmf', hp⟩

private theorem lsr1_eq_ofNat_toNat_b (x : BitVec 64) :
    x >>> 1 = BitVec.ofNat 64 (x >>> 1).toNat ∧ (x >>> 1).toNat < 2 ^ 63 := by
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  · rw [BitVec.toNat_ushiftRight]
    have := x.isLt
    omega

private theorem lsl1_ofNat_eq_b {n : Nat} :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 ((2 * n) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : ((n % 2 ^ 64) <<< 1) % 2 ^ 64 = (2 * n) % 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    omega
  simpa using this

private theorem ofNat_getLsbD_63_false_b {cap0 : Nat} (hlt : cap0 < 2 ^ 63) :
    (BitVec.ofNat 64 cap0).getLsbD 63 = false := by
  have hdiv : cap0 >>> 63 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [BitVec.getLsbD_ofNat]
  simp [Nat.testBit, hdiv]

private theorem ule16_ofNat_false_b {lit : Nat} (hlt16 : lit < 16) :
    (16#64).ule (BitVec.ofNat 64 lit) = false := by
  simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lit < 2 ^ 64)]
  omega

private theorem swp_and_ule16_zero_b {lit : Nat} {swp : Bool} (hlit_lt : lit < 2 ^ 64)
    (hnot : ¬ (swp = true ∧ lit < 16)) :
    ((if swp then 1#64 else 0#64) &&&
      if (16#64).ule (BitVec.ofNat 64 lit) = true then 0#64 else 1#64) = 0#64 := by
  cases swp with
  | false => simp
  | true =>
    simp only [true_and, Nat.not_lt] at hnot
    have hule : (16#64).ule (BitVec.ofNat 64 lit) = true := by
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlit_lt]
      omega
    rw [hule]
    simp

private theorem cbz_byte_false_b {n : BitVec 8} (hn : n ≠ 0#8) :
    (BitVec.setWidth 32 (n.zeroExtend 64) == 0#32) = false ∧
    (n.zeroExtend 32 == 0#32) = false := by
  revert hn; bv_robdd

end Helpers

/-! ## Capacity Check After the Pre-Scan (`+0x0bc`) -/

section AfterPrescan
set_option maxRecDepth 200000
variable [FormatInnerPlacement]
arm64_proof_prelude

/-- Capacity check after the template pre-scan (`+0x0bc..+0x0e0`): `cap0 = 0` (placeholder-first,
    `lit < 16`) skips the allocation and enters `formatInnerBudget_from_110`; otherwise
    `cap0 = 2 * lit < 2^63` (by `FormatInnerBudgetSafe`) enters
    `formatInnerBudget_with_capacity_0e4`. -/
theorem formatInnerBudget_after_prescan
    {P : Program} (A : RustAllocBudget) (E : List AllocEvent → Prop) (va : StringWriteAddrs)
    (R_client : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    (hshim : subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerShimSym)
      budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerAllocSym)
      (rustBudgetAllocSpec A))
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {b0 : A.σ}
    {cs : List FmtCall}
    {F_frame : SepProp} {s0 sm_bc : State}
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
    (hstk_min : stringWriterStack ≤ stackBytes)
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hfit : FitsEnv A b0 E)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hsafe : FormatInnerBudgetSafe A b0 E ArgStep ArgPanic ArgOom (s0.readReg64 .x1) cs)
    (hargsOk : FmtInnerBudgetArgsOk P A b0 va R_client ArgStep ArgPanic ArgOom stackBytes s0 cs)
    (hx1_even : (s0.readReg64 .x1).getLsbD 0 = false)
    (hlit_lt : fmtLiteralLen cs < 2 ^ 64)
    (hpc_bc : sm_bc.pc = allocPl03.base + 188#64)
    (hrun_bc : sm_bc.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_bc : sm_bc.sp = s0.sp - 96#64)
    (hcl_bc : allocMultiLib.CodeLoaded fmtInnerMpl sm_bc.mem)
    (hx8_bc : sm_bc.readReg64 .x8 = BitVec.ofNat 64 (fmtLiteralLen cs))
    (hx9_bc : sm_bc.readReg64 .x9 = if fmtStartsWithPlaceholder cs then 1#64 else 0#64)
    (hx19_bc : sm_bc.readReg64 .x19 = ret)
    (hx20_bc : sm_bc.readReg64 .x20 = s0.readReg64 .x1)
    (hx21_bc : sm_bc.readReg64 .x21 = s0.readReg64 .x0)
    (hhg_bc : FmtInnerHighGprs s0 sm_bc)
    (hvregs_bc : calleeSavedVRegs sm_bc = calleeSavedVRegs s0)
    (hframe_bc : IoCallFrame s0 sm_bc ∧ sm_bc.fs = s0.fs ∧ sm_bc.trace = s0.trace)
    (r0 r1 r2 v0 v1 v2 v3 v7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sm_bc
      (vecHeader (s0.sp - 96#64 + 8#64) v1 v2 v3 ∗
        A.pool b0 sm_bc ∗
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
  have hcap_even : ∀ cs', fmtEstimatedCapacity (s0.readReg64 .x1) cs' =
      if fmtStartsWithPlaceholder cs' && decide (fmtLiteralLen cs' < 16) then 0
      else (2 * fmtLiteralLen cs') % 2 ^ 64 := by
    intro cs'
    dsimp only [fmtEstimatedCapacity]
    rw [hx1_even]
    rfl
  by_cases hsmall : fmtStartsWithPlaceholder cs = true ∧ fmtLiteralLen cs < 16
  ·
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl_bc
      (mid := allocPl03.base + 272#64)
    intro sbc'' hcpu_in
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc_in : sbc''.pc = allocPl03.base + 188#64 := hcpu_in.pc_eq.trans hpc_bc
    have hrun_in : sbc''.status = .Running := hcpu_in.status_eq.trans hrun_bc
    have hsp_in : sbc''.sp = s0.sp - 96#64 := hcpu_in.sp_eq.trans hsp_bc
    have hsp_al : sbc''.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx8_in : sbc''.readReg64 .x8 = BitVec.ofNat 64 (fmtLiteralLen cs) :=
      (hcpu_in.readReg64 .x8).trans hx8_bc
    have hx9_in : sbc''.readReg64 .x9 = 1#64 := by
      rw [hcpu_in.readReg64 .x9, hx9_bc, hsmall.1]
      simp
    have hule_false := ule16_ofNat_false_b hsmall.2
    have hsp16 : sbc''.sp + 8#64 + 8#64 = sbc''.sp + 16#64 := by bv_arith
    have hsp24 : sbc''.sp + 8#64 + 16#64 = sbc''.sp + 24#64 := by bv_arith
    wp_conv_pre =>
      rw [← hsp_in, vecHeader_def (sbc''.sp + 8#64), hsp16, hsp24]
    wp_sym_steps
    wp_conv_pre =>
      rw [← hsp24, ← hsp16, ← vecHeader_def (sbc''.sp + 8#64), hsp_in]
    apply SepWP.done
      (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm] using hrun_in)
    intro sm3 hcpu_m3 hcl3 hpseg_3
    obtain ⟨hframe_bc3, _⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu_in hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
      rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
    have hrun3 : sm3.status = .Running :=
      hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun_in)
    have hsp3 : sm3.sp = s0.sp - 96#64 := by
      rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hsp_in]
    let st₀ : FmtBuf := ⟨[], 0#64, 1#64, []⟩
    have hstart : FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs) st₀ := by
      rw [hcap_even]
      simp [FmtBufStart, hsmall.1, hsmall.2, st₀]
    have hpre_eq :
        vecHeader (s0.sp - 96#64 + 8#64) 0#64 1#64 0#64 ∗
          A.pool b0 sm_bc ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 v0 v7 =
        vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
          fmtBufVecAt A st₀.cap st₀.ptr st₀.bytes ∗
          A.pool (A.stepEvents st₀.evs b0) sm3 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 v0 v7 := by
      dsimp only [st₀]
      rw [fmtBufVecAt_zero_eq_emp A (by decide), RustAllocBudget.stepEvents_nil,
        A.pool_of_pureSeg _ hpseg_3 hframe_bc3.1.1 hframe_bc3.1.2.1]
      simp only [List.length_nil, emp_sepConj]
    rw [hpre_eq]
    exact formatInnerBudget_from_110 A E va R_client ArgStep ArgPanic ArgOom stackBytes
      hvt hext_blk hfmtWrite hwriteStr hstk_fit hfit hdec hsafe hargsOk hstart
      hpc3 hrun3 hsp0 hsp3 hcl3
      ((hcpu_m3.readReg64 .x19).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x19).trans hx19_bc))
      ((hcpu_m3.readReg64 .x20).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x20).trans hx20_bc))
      ((hcpu_m3.readReg64 .x21).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x21).trans hx21_bc))
      ⟨(hcpu_m3.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x24).trans hhg_bc.x24),
       (hcpu_m3.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x25).trans hhg_bc.x25),
       (hcpu_m3.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x26).trans hhg_bc.x26),
       (hcpu_m3.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x27).trans hhg_bc.x27),
       (hcpu_m3.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x28).trans hhg_bc.x28)⟩
      (hcpu_m3.calleeSavedVRegs.trans (by simpa [wp_norm, arm64_norm] using hcpu_in.calleeSavedVRegs.trans hvregs_bc))
      (ioCallFrame_trans hframe_bc hframe_bc3)
      r0 r1 r2 v0 v7
  ·
    have hcap_eq : fmtEstimatedCapacity (s0.readReg64 .x1) cs = (2 * fmtLiteralLen cs) % 2 ^ 64 := by
      have hcond : (fmtStartsWithPlaceholder cs && decide (fmtLiteralLen cs < 16)) = false := by
        cases h1 : fmtStartsWithPlaceholder cs <;> simp_all
      rw [hcap_even, hcond]
      rfl
    let cap0 := (2 * fmtLiteralLen cs) % 2 ^ 64
    have hcap_lt63 : cap0 < 2 ^ 63 := by
      have h60 := hsafe.1
      show (2 * fmtLiteralLen cs) % 2 ^ 64 < 2 ^ 63
      omega
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl_bc
      (mid := allocPl03.base + 228#64)
    intro sbc'' hcpu_in
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc_in : sbc''.pc = allocPl03.base + 188#64 := hcpu_in.pc_eq.trans hpc_bc
    have hrun_in : sbc''.status = .Running := hcpu_in.status_eq.trans hrun_bc
    have hsp_in : sbc''.sp = s0.sp - 96#64 := hcpu_in.sp_eq.trans hsp_bc
    have hsp_al : sbc''.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx8_in : sbc''.readReg64 .x8 = BitVec.ofNat 64 (fmtLiteralLen cs) :=
      (hcpu_in.readReg64 .x8).trans hx8_bc
    have hx9_in : sbc''.readReg64 .x9 = if fmtStartsWithPlaceholder cs then 1#64 else 0#64 :=
      (hcpu_in.readReg64 .x9).trans hx9_bc
    have hw9_zero := swp_and_ule16_zero_b hlit_lt hsmall
    have hlsl : (BitVec.ofNat 64 (fmtLiteralLen cs)) <<< 1 = BitVec.ofNat 64 cap0 :=
      lsl1_ofNat_eq_b
    have hbit63 := ofNat_getLsbD_63_false_b hcap_lt63
    wp_sym_steps
    apply SepWP.done
      (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm] using hrun_in)
    intro sm0 hcpu_m0 hcl_m0 hpseg_0
    obtain ⟨hframe_bc0, _⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu_in hcpu_m0 hpseg_0 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc_m0 : sm0.pc = allocPl03.base + 228#64 := by
      rw [hcpu_m0.pc_eq]; simp [wp_norm, arm64_norm]
    have hrun_m0 : sm0.status = .Running :=
      hcpu_m0.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun_in)
    have hsp_m0 : sm0.sp = s0.sp - 96#64 := by
      rw [hcpu_m0.sp_eq]; simp [wp_norm, arm64_norm, hsp_in]
    have hx22_m0 : sm0.readReg64 .x22 = BitVec.ofNat 64 (fmtEstimatedCapacity (s0.readReg64 .x1) cs) := by
      rw [hcpu_m0.readReg64 .x22, hcap_eq]
      dsimp only [cap0]
      simp [wp_norm, arm64_norm]
    rw [← A.pool_of_pureSeg b0 hpseg_0 hframe_bc0.1.1 hframe_bc0.1.2.1]
    exact formatInnerBudget_with_capacity_0e4 A E va R_client ArgStep ArgPanic ArgOom stackBytes
      hvt hext_blk hshim halloc hfmtWrite hwriteStr
      hstk_min hstk_fit hfit hdec hsafe hargsOk (hcap_eq ▸ hcap_lt63)
      hpc_m0 hrun_m0 hsp0 hsp_m0 hcl_m0
      ((hcpu_m0.readReg64 .x19).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x19).trans hx19_bc))
      ((hcpu_m0.readReg64 .x20).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x20).trans hx20_bc))
      ((hcpu_m0.readReg64 .x21).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x21).trans hx21_bc))
      hx22_m0
      ⟨(hcpu_m0.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x24).trans hhg_bc.x24),
       (hcpu_m0.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x25).trans hhg_bc.x25),
       (hcpu_m0.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x26).trans hhg_bc.x26),
       (hcpu_m0.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x27).trans hhg_bc.x27),
       (hcpu_m0.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu_in.readReg64 .x28).trans hhg_bc.x28)⟩
      (hcpu_m0.calleeSavedVRegs.trans (by simpa [wp_norm, arm64_norm] using hcpu_in.calleeSavedVRegs.trans hvregs_bc))
      (ioCallFrame_trans hframe_bc hframe_bc0)
      r0 r1 r2 v0 v1 v2 v3 v7

end AfterPrescan

/-! ## Entry Proof (`allocFormatInnerBudget_ok`) -/

section MainProof
set_option maxRecDepth 200000
arm64_proof_prelude

/-- Budgeted `alloc::fmt::format::format_inner` (`allocMultiLib` block `3`) meets
    `allocFormatInnerBudgetSpec` under `allocMultiLib.withCodeLoaded mpl`, with the callee
    contracts (`budgetAllocShimSpec`, `rustBudgetAllocSpec`, `core::fmt::write` at the
    strengthened `fmtInnerBudgetPanicInv` protocol, and the vtable `write_str`) as hypotheses. -/
theorem allocFormatInnerBudget_ok
    (P : Program) (A : RustAllocBudget) (E : List AllocEvent → Prop) (va : StringWriteAddrs)
    (R_client : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (mpl : Obj.MultiPlacement) (hpl : allocMultiLib.Placeable mpl)
    (hvt : va.vtable = allocMultiLib.resolve mpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern mpl P 3)
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl fmtInnerShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl fmtInnerAllocSym)
      (rustBudgetAllocSpec A))
    (hfmtWrite : ∀ (st0 : A.σ) (t0 : State) (out : BitVec 64),
      subroutine_ok P (allocMultiLib.resolve mpl fmtInnerCoreFmtWriteRawSym)
        (coreFmtWriteSpec P (fmtInnerBudgetW A st0 va R_client t0 out)
          (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanicInv t0 ArgPanic)
          (fmtInnerBudgetOom A st0 ArgOom) stackBytes))
    (hwriteStr : stringWriterStack ≤ stackBytes → stackBytes ≤ 2 ^ 64 →
      ∀ (st0 : A.σ) (t0 : State) (out ptr : BitVec 64) (bs : List (BitVec 8)),
      subroutine_ok P va.writeStr
        (fmtWriteStrCallSpec (fmtInnerBudgetW A st0 va R_client t0 out)
          (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanic t0 ArgPanic)
          (fmtInnerBudgetOom A st0 ArgOom) stackBytes out ptr bs)) :
    subroutine_ok P (allocMultiLib.fnAddr mpl allocFormatInnerSym)
      (allocMultiLib.withCodeLoaded mpl
        (allocFormatInnerBudgetSpec P A E va R_client ArgStep ArgPanic ArgOom stackBytes)) := by
  letI : FormatInnerPlacement := ⟨mpl, hpl⟩
  have hfn : allocMultiLib.fnAddr mpl allocFormatInnerSym = allocPl03.base := by
    simp [Obj.MultiPlacedLib.fnAddr, lookupBlockSym_formatInner, allocPl03,
      Obj.MultiPlacedLib.blockPlacement, fmtInnerMpl]
    rfl
  rw [hfn]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨ret, argsRo, tpl, args, b0⟩ F_frame s0 hpc hrun hpre hsp0
  dsimp only [Obj.MultiPlacedLib.withCodeLoaded, allocFormatInnerBudgetSpec] at hpre
  dsimp only [Obj.MultiPlacedLib.withCodeLoaded]
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hstk_min, hstk_fit, hfit, cs, hdec, hsafe, hargsOk⟩, hpre⟩
  have hfw := hfmtWrite b0 s0
  have hws := hwriteStr hstk_min (by omega) b0 s0
  have htpl_lt : tpl.length < 2 ^ 64 := by
    have hpre_ro := hpre
    dsimp only [fmtArgumentsAt] at hpre_ro
    have hro : s0.mem ⊨ ((s0.readReg64 .x0) ↦ᵣ tpl) ∗ memRegion ret 24 ∗
        ((if (s0.readReg64 .x1).getLsbD 0 then emp
          else fmtArgEntriesAt argsRo (s0.readReg64 .x1) args) ∗
         A.pool b0 s0 ∗ stringWriteVtableAt va ∗ R_client ∗
         stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) ∗ F_frame) := by
      revert hpre_ro; intro hpre_ro; sep_frame
    exact pointsToBytesRO_length_lt_of_memRegion24 hro
  refine ⟨_, hpre, ?_⟩
  conv =>
    arg 4
    rw [memRegion24_eq_vecHeader ret,
      fmtEntryStack_split_b s0.sp stackBytes hstk_fit, cells12_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun st0 => SepWPp.exists_elim fun st1 =>
    SepWPp.exists_elim fun st2 => SepWPp.exists_elim fun st3 =>
    SepWPp.exists_elim fun st4 => SepWPp.exists_elim fun st5 =>
    SepWPp.exists_elim fun st6 => SepWPp.exists_elim fun st7 =>
    SepWPp.exists_elim fun st8 => SepWPp.exists_elim fun st9 =>
    SepWPp.exists_elim fun st10 => SepWPp.exists_elim fun st11 =>
    SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => ?_
  by_cases hx1_odd : (s0.readReg64 .x1).getLsbD 0 = true
  ·
    have hdec_odd := hdec
    dsimp only [decodeFmtArguments] at hdec_odd
    rw [hx1_odd] at hdec_odd
    simp only [↓reduceIte] at hdec_odd
    split at hdec_odd
    · rename_i hlen_eq
      injection hdec_odd with hdec_odd
      subst hdec_odd
      obtain ⟨hlsr_bv, hlsr_lt⟩ := lsr1_eq_ofNat_toNat_b (s0.readReg64 .x1)
      have hcap_odd :
          fmtEstimatedCapacity (s0.readReg64 .x1) [.writeStr (s0.readReg64 .x0) tpl] =
            ((s0.readReg64 .x1) >>> 1).toNat := by
        dsimp only [fmtEstimatedCapacity]
        rw [hx1_odd]
        simp [fmtLiteralLen, hlen_eq]
      apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl0
        (mid := allocPl03.base + 228#64)
      intro s0' hcpu0
      change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
      have hpc0' : s0'.pc = allocPl03.base := hcpu0.pc_eq.trans hpc
      have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
      have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp0
      have hx8' : s0'.readReg64 .x8 = ret := (hcpu0.readReg64 .x8).trans hx8
      have hx1_lsb : (s0'.readReg64 (.gpr 1#5)).getLsbD 0 = true := by
        rw [show s0'.readReg64 (.gpr 1#5) = s0.readReg64 .x1 from hcpu0.readReg64 .x1]
        exact hx1_odd
      wp_conv_pre => rw [← hcpu0.sp_eq]
      clear hpc
      wp_sym_steps
      wp_conv_pre => rw [hcpu0.sp_eq]
      apply SepWP.done
        (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hrun0')
      intro sm0 hcpu_m0 hcl_m0 hpseg_0
      obtain ⟨hframe_0, _⟩ :=
        ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m0 hpseg_0 (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpc_m0 : sm0.pc = allocPl03.base + 228#64 := by
        rw [hcpu_m0.pc_eq]; simp [wp_norm, arm64_norm]
      have hrun_m0 : sm0.status = .Running :=
        hcpu_m0.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun0')
      have hsp_m0 : sm0.sp = s0.sp - 96#64 := by
        rw [hcpu_m0.sp_eq]; simp [wp_norm, arm64_norm, hcpu0.sp_eq]
      have hx22_m0 : sm0.readReg64 .x22 =
          BitVec.ofNat 64 (fmtEstimatedCapacity (s0.readReg64 .x1) [.writeStr (s0.readReg64 .x0) tpl]) := by
        rw [hcpu_m0.readReg64 .x22, hcap_odd, ← hlsr_bv]
        simp [wp_norm, arm64_norm, hcpu0.readReg64]
      have hpre_eq :
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
            vecHeader ret r0 r1 r2 ∗
            A.pool b0 s0 ∗
            stringWriteVtableAt va ∗
            R_client ∗
            ((((s0.sp - 96#64) ↦₆₄ st0) ∗
              ((s0.sp - 96#64 + 8#64) ↦₆₄ st1) ∗
              ((s0.sp - 96#64 + 16#64) ↦₆₄ st2) ∗
              ((s0.sp - 96#64 + 24#64) ↦₆₄ st3) ∗
              ((s0.sp - 96#64 + 32#64) ↦₆₄ s0'.readReg64 (.gpr 29#5)) ∗
              ((s0.sp - 96#64 + 40#64) ↦₆₄ s0'.readReg64 (.gpr 30#5)) ∗
              ((s0.sp - 96#64 + 48#64) ↦₆₄ s0'.readReg64 (.gpr 23#5)) ∗
              ((s0.sp - 96#64 + 56#64) ↦₆₄ st7) ∗
              ((s0.sp - 96#64 + 64#64) ↦₆₄ s0'.readReg64 (.gpr 22#5)) ∗
              ((s0.sp - 96#64 + 72#64) ↦₆₄ s0'.readReg64 (.gpr 21#5)) ∗
              ((s0.sp - 96#64 + 80#64) ↦₆₄ s0'.readReg64 (.gpr 20#5)) ∗
              ((s0.sp - 96#64 + 88#64) ↦₆₄ s0'.readReg64 (.gpr 19#5))) ∗
             stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes)) =
          vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
            A.pool b0 sm0 ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
            stringWriteVtableAt va ∗
            R_client ∗
            stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
            vecHeader ret r0 r1 r2 ∗
            fmtInnerSavedSlots s0 st0 st7 := by
        dsimp only [vecHeader, fmtInnerSavedSlots]
        have h16 : s0.sp - 96#64 + 8#64 + 8#64 = s0.sp - 96#64 + 16#64 := by bv_arith
        have h24 : s0.sp - 96#64 + 8#64 + 16#64 = s0.sp - 96#64 + 24#64 := by bv_arith
        rw [h16, h24, A.pool_of_pureSeg _ hpseg_0 hframe_0.1.1 hframe_0.1.2.1]
        simp only [hcpu0.readReg64]
        apply Entails.antisymm <;> sep_entail
      rw [hpre_eq]
      exact formatInnerBudget_with_capacity_0e4 A E va R_client ArgStep ArgPanic ArgOom stackBytes
        hvt hext_blk hshim halloc hfw hws
        hstk_min hstk_fit hfit hdec hsafe hargsOk (hcap_odd ▸ hlsr_lt)
        hpc_m0 hrun_m0 hsp0 hsp_m0 hcl_m0
        ((hcpu_m0.readReg64 .x19).trans (by simp [wp_norm, arm64_norm]))
        ((hcpu_m0.readReg64 .x20).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]))
        ((hcpu_m0.readReg64 .x21).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]))
        hx22_m0
        ⟨(hcpu_m0.readReg64 .x24).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
         (hcpu_m0.readReg64 .x25).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
         (hcpu_m0.readReg64 .x26).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
         (hcpu_m0.readReg64 .x27).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
         (hcpu_m0.readReg64 .x28).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64])⟩
        (hcpu_m0.calleeSavedVRegs.trans (by simp [wp_norm, arm64_norm, hcpu0.calleeSavedVRegs]))
        hframe_0 r0 r1 r2 st0 st1 st2 st3 st7
    · cases hdec_odd
  ·
    have hx1_even : (s0.readReg64 .x1).getLsbD 0 = false := Bool.eq_false_iff.mpr hx1_odd
    have hcap_even : ∀ cs', fmtEstimatedCapacity (s0.readReg64 .x1) cs' =
        if fmtStartsWithPlaceholder cs' && decide (fmtLiteralLen cs' < 16) then 0
        else (2 * fmtLiteralLen cs') % 2 ^ 64 := by
      intro cs'
      dsimp only [fmtEstimatedCapacity]
      rw [hx1_even]
      rfl
    have hdec_tpl : decodeFmtTemplate (s0.readReg64 .x0) args tpl.length 0 0 tpl = some cs := by
      have h := hdec
      dsimp only [decodeFmtArguments] at h
      rw [hx1_even] at h
      simpa using h
    obtain ⟨htpl_ne, hlit_lt_tpl⟩ := decodeFmtTemplate_nonempty_and_litLen_lt hdec_tpl
    have hlit_lt : fmtLiteralLen cs < 2 ^ 64 := Nat.lt_trans hlit_lt_tpl htpl_lt
    rcases tpl with _ | ⟨n, rest⟩
    · exact False.elim (htpl_ne rfl)
    · by_cases hn0 : n = 0#8
      ·
        subst hn0
        have hdec0 := hdec_tpl
        simp only [List.length_cons, decodeFmtTemplate, ↓reduceIte] at hdec0
        by_cases hr0 : rest = []
        · subst hr0
          simp only [↓reduceIte, Option.some.injEq] at hdec0
          subst hdec0
          apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl0
            (mid := allocPl03.base + 272#64)
          intro s0' hcpu0
          change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
          have hpc0' : s0'.pc = allocPl03.base := hcpu0.pc_eq.trans hpc
          have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
          have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp0
          have hx8' : s0'.readReg64 .x8 = ret := (hcpu0.readReg64 .x8).trans hx8
          have hx1_lsb : (s0'.readReg64 (.gpr 1#5)).getLsbD 0 = false := by
            rw [show s0'.readReg64 (.gpr 1#5) = s0.readReg64 .x1 from hcpu0.readReg64 .x1]
            exact hx1_even
          wp_conv_pre =>
            dsimp only [fmtArgumentsAt]
            rw [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
              ← hcpu0.readReg64 .x0, ← hcpu0.sp_eq]
          clear hpc
          wp_sym_steps
          wp_conv_pre =>
            rw [hcpu0.sp_eq, hcpu0.readReg64 .x0]
          apply SepWP.done
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using hrun0')
          intro sm3 hcpu_m3 hcl3 hpseg_3
          obtain ⟨hframe_3, _⟩ :=
            ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
            rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
          have hrun3 : sm3.status = .Running :=
            hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun0')
          have hsp3 : sm3.sp = s0.sp - 96#64 := by
            rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hcpu0.sp_eq]
          let st₀ : FmtBuf := ⟨[], 0#64, 1#64, []⟩
          have hstart : FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) []) st₀ := by
            rw [hcap_even]
            simp [FmtBufStart, fmtStartsWithPlaceholder, fmtLiteralLen, st₀]
          have hpre_eq :
              (((s0.readReg64 .x0 ↦₈ᵣ 0#8) ∗
                  if (s0.readReg64 .x1).getLsbD 0 = true then emp
                  else fmtArgEntriesAt argsRo (s0.readReg64 .x1) args) ∗
                vecHeader ret r0 r1 r2 ∗
                A.pool b0 s0 ∗
                stringWriteVtableAt va ∗
                R_client ∗
                ((((s0.sp - 96#64) ↦₆₄ st0) ∗
                  ((s0.sp - 96#64 + 8#64) ↦₆₄ 0#64) ∗
                  ((s0.sp - 96#64 + 16#64) ↦₆₄ 1#64) ∗
                  ((s0.sp - 96#64 + 24#64) ↦₆₄ 0#64) ∗
                  ((s0.sp - 96#64 + 32#64) ↦₆₄ s0'.readReg64 (.gpr 29#5)) ∗
                  ((s0.sp - 96#64 + 40#64) ↦₆₄ s0'.readReg64 (.gpr 30#5)) ∗
                  ((s0.sp - 96#64 + 48#64) ↦₆₄ s0'.readReg64 (.gpr 23#5)) ∗
                  ((s0.sp - 96#64 + 56#64) ↦₆₄ st7) ∗
                  ((s0.sp - 96#64 + 64#64) ↦₆₄ s0'.readReg64 (.gpr 22#5)) ∗
                  ((s0.sp - 96#64 + 72#64) ↦₆₄ s0'.readReg64 (.gpr 21#5)) ∗
                  ((s0.sp - 96#64 + 80#64) ↦₆₄ s0'.readReg64 (.gpr 20#5)) ∗
                  ((s0.sp - 96#64 + 88#64) ↦₆₄ s0'.readReg64 (.gpr 19#5))) ∗
                 stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))) =
              vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
                fmtBufVecAt A st₀.cap st₀.ptr st₀.bytes ∗
                A.pool (A.stepEvents st₀.evs b0) sm3 ∗
                fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) [0#8] args ∗
                stringWriteVtableAt va ∗
                R_client ∗
                stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
                vecHeader ret r0 r1 r2 ∗
                fmtInnerSavedSlots s0 st0 st7 := by
            dsimp only [st₀, vecHeader, fmtInnerSavedSlots, fmtArgumentsAt]
            have h16 : s0.sp - 96#64 + 8#64 + 8#64 = s0.sp - 96#64 + 16#64 := by bv_arith
            have h24 : s0.sp - 96#64 + 8#64 + 16#64 = s0.sp - 96#64 + 24#64 := by bv_arith
            rw [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
              h16, h24, fmtBufVecAt_zero_eq_emp A (by decide), RustAllocBudget.stepEvents_nil,
              A.pool_of_pureSeg _ hpseg_3 hframe_3.1.1 hframe_3.1.2.1]
            simp only [hcpu0.readReg64, List.length_nil, emp_sepConj]
            apply Entails.antisymm <;> sep_entail
          rw [hpre_eq]
          exact formatInnerBudget_from_110 A E va R_client ArgStep ArgPanic ArgOom stackBytes
            hvt hext_blk hfw hws hstk_fit hfit hdec hsafe hargsOk hstart
            hpc3 hrun3 hsp0 hsp3 hcl3
            ((hcpu_m3.readReg64 .x19).trans (by simp [wp_norm, arm64_norm]))
            ((hcpu_m3.readReg64 .x20).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]))
            ((hcpu_m3.readReg64 .x21).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]))
            ⟨(hcpu_m3.readReg64 .x24).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
             (hcpu_m3.readReg64 .x25).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
             (hcpu_m3.readReg64 .x26).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
             (hcpu_m3.readReg64 .x27).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64]),
             (hcpu_m3.readReg64 .x28).trans (by simp [wp_norm, arm64_norm, hcpu0.readReg64])⟩
            (hcpu_m3.calleeSavedVRegs.trans (by simp [wp_norm, arm64_norm, hcpu0.calleeSavedVRegs]))
            hframe_3 r0 r1 r2 st0 st7
        · simp [hr0] at hdec0
      ·
        obtain ⟨hcbz1, hcbz2⟩ := cbz_byte_false_b hn0
        apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl0
          (mid := allocPl03.base + 188#64)
        intro s0' hcpu0
        change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
        have hpc0' : s0'.pc = allocPl03.base := hcpu0.pc_eq.trans hpc
        have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
        have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp0
        have hx8' : s0'.readReg64 .x8 = ret := (hcpu0.readReg64 .x8).trans hx8
        have hx1_lsb : (s0'.readReg64 (.gpr 1#5)).getLsbD 0 = false := by
          rw [show s0'.readReg64 (.gpr 1#5) = s0.readReg64 .x1 from hcpu0.readReg64 .x1]
          exact hx1_even
        let FramePre : SepProp :=
          (if (s0.readReg64 .x1).getLsbD 0 = true then emp
           else fmtArgEntriesAt argsRo (s0.readReg64 .x1) args) ∗
          vecHeader ret r0 r1 r2 ∗
          A.pool b0 s0 ∗
          stringWriteVtableAt va ∗
          R_client ∗
          ((((s0.sp - 96#64) ↦₆₄ st0) ∗
            ((s0.sp - 96#64 + 8#64) ↦₆₄ st1) ∗
            ((s0.sp - 96#64 + 16#64) ↦₆₄ st2) ∗
            ((s0.sp - 96#64 + 24#64) ↦₆₄ st3) ∗
            ((s0.sp - 96#64 + 32#64) ↦₆₄ s0'.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 96#64 + 40#64) ↦₆₄ s0'.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 96#64 + 48#64) ↦₆₄ s0'.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 96#64 + 56#64) ↦₆₄ st7) ∗
            ((s0.sp - 96#64 + 64#64) ↦₆₄ s0'.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 96#64 + 72#64) ↦₆₄ s0'.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 96#64 + 80#64) ↦₆₄ s0'.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 96#64 + 88#64) ↦₆₄ s0'.readReg64 (.gpr 19#5))) ∗
           stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))
        apply sepWP_seq_b (mid_pc := allocPl03.base + 84#64)
          (mid_post := fun s54 P54 =>
            P54 = (FramePre ∗ ((s0.readReg64 .x0) ↦ᵣ (n :: rest))) ∧
            s54.spAligned = true ∧
            s54.sp = s0.sp - 96#64 ∧
            s54.tpidrEl0 = s0'.tpidrEl0 ∧
            s54.sigActions = s0'.sigActions ∧
            s54.readReg64 .x8 = 0#64 ∧
            s54.readReg64 .x9 = 0#64 ∧
            s54.readReg64 .x10 = n.zeroExtend 64 ∧
            s54.readReg64 .x11 = s0.readReg64 .x0 ∧
            s54.readReg64 .x19 = ret ∧
            s54.readReg64 .x20 = s0.readReg64 .x1 ∧
            s54.readReg64 .x21 = s0.readReg64 .x0 ∧
            FmtInnerHighGprs s0 s54 ∧
            calleeSavedVRegs s54 = calleeSavedVRegs s0)
        · wp_conv_pre =>
            dsimp only [fmtArgumentsAt]
            rw [pointsToBytesRO_cons, ← hcpu0.readReg64 .x0, ← hcpu0.sp_eq]
          clear hpc
          wp_sym_steps
          apply SepWP.done
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using hrun0')
          refine ⟨?_,
            by simpa [State.spAligned, wp_norm, arm64_norm, hcpu0.sp_eq] using
              s0.spAligned_sub 96#64 hsp0,
            by simp [wp_norm, arm64_norm, hcpu0.sp_eq],
            by simp [arm64_norm],
            by simp [arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm, hcpu0.readReg64],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm, hcpu0.readReg64],
            by simp [wp_norm, arm64_norm, hcpu0.readReg64],
            ⟨by simp [wp_norm, arm64_norm, hcpu0.readReg64],
             by simp [wp_norm, arm64_norm, hcpu0.readReg64],
             by simp [wp_norm, arm64_norm, hcpu0.readReg64],
             by simp [wp_norm, arm64_norm, hcpu0.readReg64],
             by simp [wp_norm, arm64_norm, hcpu0.readReg64]⟩,
            by simp [wp_norm, arm64_norm, hcpu0.calleeSavedVRegs]⟩
          rw [hcpu0.sp_eq, hcpu0.readReg64 .x0, ← pointsToBytesRO_cons]
          dsimp only [FramePre]
          apply Entails.antisymm <;> sep_entail
        · rintro s54 _ hpc54 hrun54 ⟨rfl, hsp54, hsp54_eq, htp54, hsig54,
            hx8_54, hx9_54, hx10_54, hx11_54, hx19_54, hx20_54, hx21_54, hhg_54, hvregs_54⟩
          apply sepWP_frame_left_b
          refine SepWP.mono
            (formatInner_prescan_from_054 hpc54 hrun54 hsp54 hx8_54 hx9_54 hx10_54 hx11_54
              hn0 (by simpa [List.length_cons] using hdec_tpl) hlit_lt) ?_
          rintro sbc' _ hpc_bc' hrun_bc' ⟨rfl, _hsp_bc', hkeep_bc, hx8_bc', hx9_bc'⟩
          intro sm_bc hcpu_bc hcl_bc hpseg_bc
          obtain ⟨hframe_bc, _⟩ :=
            ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_bc hpseg_bc
              (hkeep_bc.tpidr.trans htp54) (hkeep_bc.sigActions.trans hsig54)
          have hpc_bc : sm_bc.pc = allocPl03.base + 188#64 := hcpu_bc.pc_eq.trans hpc_bc'
          have hrun_bc : sm_bc.status = .Running := hcpu_bc.status_eq.trans hrun_bc'
          have hsp_bc : sm_bc.sp = s0.sp - 96#64 :=
            hcpu_bc.sp_eq.trans (hkeep_bc.sp.trans hsp54_eq)
          have hx8_bc : sm_bc.readReg64 .x8 = BitVec.ofNat 64 (fmtLiteralLen cs) :=
            (hcpu_bc.readReg64 .x8).trans hx8_bc'
          have hx9_bc : sm_bc.readReg64 .x9 = if fmtStartsWithPlaceholder cs then 1#64 else 0#64 :=
            (hcpu_bc.readReg64 .x9).trans hx9_bc'
          have hx19_bc : sm_bc.readReg64 .x19 = ret :=
            (hcpu_bc.readReg64 .x19).trans (hkeep_bc.x19.trans hx19_54)
          have hx20_bc : sm_bc.readReg64 .x20 = s0.readReg64 .x1 :=
            (hcpu_bc.readReg64 .x20).trans (hkeep_bc.x20.trans hx20_54)
          have hx21_bc : sm_bc.readReg64 .x21 = s0.readReg64 .x0 :=
            (hcpu_bc.readReg64 .x21).trans (hkeep_bc.x21.trans hx21_54)
          have hhg_bc : FmtInnerHighGprs s0 sm_bc :=
            ⟨(hcpu_bc.readReg64 .x24).trans (hkeep_bc.x24.trans hhg_54.x24),
             (hcpu_bc.readReg64 .x25).trans (hkeep_bc.x25.trans hhg_54.x25),
             (hcpu_bc.readReg64 .x26).trans (hkeep_bc.x26.trans hhg_54.x26),
             (hcpu_bc.readReg64 .x27).trans (hkeep_bc.x27.trans hhg_54.x27),
             (hcpu_bc.readReg64 .x28).trans (hkeep_bc.x28.trans hhg_54.x28)⟩
          have hvregs_bc : calleeSavedVRegs sm_bc = calleeSavedVRegs s0 :=
            hcpu_bc.calleeSavedVRegs.trans (hkeep_bc.vregs.trans hvregs_54)
          have hpre_bc :
              FramePre ∗ ((s0.readReg64 .x0) ↦ᵣ (n :: rest)) =
              vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
                A.pool b0 sm_bc ∗
                fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) (n :: rest) args ∗
                stringWriteVtableAt va ∗
                R_client ∗
                stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
                vecHeader ret r0 r1 r2 ∗
                fmtInnerSavedSlots s0 st0 st7 := by
            dsimp only [FramePre, vecHeader, fmtInnerSavedSlots, fmtArgumentsAt]
            have h16 : s0.sp - 96#64 + 8#64 + 8#64 = s0.sp - 96#64 + 16#64 := by bv_arith
            have h24 : s0.sp - 96#64 + 8#64 + 16#64 = s0.sp - 96#64 + 24#64 := by bv_arith
            rw [h16, h24, A.pool_of_pureSeg _ hpseg_bc hframe_bc.1.1 hframe_bc.1.2.1]
            simp only [hcpu0.readReg64]
            apply Entails.antisymm <;> sep_entail
          rw [hpre_bc]
          exact formatInnerBudget_after_prescan A E va R_client ArgStep ArgPanic ArgOom stackBytes
            hvt hext_blk hshim halloc hfw hws hstk_min hstk_fit hfit hdec hsafe hargsOk
            hx1_even hlit_lt hpc_bc hrun_bc hsp0 hsp_bc hcl_bc hx8_bc hx9_bc hx19_bc hx20_bc
            hx21_bc hhg_bc hvregs_bc hframe_bc r0 r1 r2 st0 st1 st2 st3 st7

end MainProof

end VerifiedLibraries.RustStd
