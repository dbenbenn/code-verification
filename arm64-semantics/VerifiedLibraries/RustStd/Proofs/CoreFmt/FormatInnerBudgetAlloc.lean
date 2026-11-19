/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FormatInnerBudgetCall
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FinishGrowBudget

/-!
# Budgeted `format_inner`: `String::with_capacity` Stage

Stage lemmas for the `String::with_capacity` prefix of `alloc::fmt::format::format_inner`
(`allocMultiLib` block 3) against `allocFormatInnerBudgetSpec`: `formatInnerBudget_with_capacity_0e4`
and `formatInnerBudget_after_alloc_0fc`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)
open FormatInnerBudget

namespace FormatInnerBudget

theorem pull_pure_third (A1 A2 : SepProp) (P : Prop) (F : SepProp) :
    (A1 ∗ A2 ∗ ⌜P⌝) ∗ F = ⌜P⌝ ∗ ((A1 ∗ A2) ∗ F) := by
  rw [sepConj_comm A2 ⌜P⌝, ← sepConj_assoc A1 ⌜P⌝ A2, sepConj_comm A1 ⌜P⌝,
    sepConj_assoc ⌜P⌝ A1 A2, sepConj_assoc ⌜P⌝ _ F]

theorem fmtBufStart_pos {cap0 : Nat} (h : cap0 ≠ 0) (p : BitVec 64) :
    FmtBufStart cap0 ⟨[], BitVec.ofNat 64 cap0, p, rustAllocEvents cap0 1⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [h, ↓reduceIte]

end FormatInnerBudget

section StageProofs
set_option maxRecDepth 200000
variable [FormatInnerPlacement]
arm64_proof_prelude

theorem formatInnerBudget_after_alloc_0fc
    {P : Program} (A : RustAllocBudget) (E : List AllocEvent → Prop) (va : StringWriteAddrs)
    (R_client : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {b0 : A.σ}
    {cs : List FmtCall}
    {F_frame : SepProp} {s0 sf2 : State}
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
    (hcap0 : fmtEstimatedCapacity (s0.readReg64 .x1) cs ≠ 0)
    (hcap_lt63 : fmtEstimatedCapacity (s0.readReg64 .x1) cs < 2 ^ 63)
    (hp_ne : sf2.readReg64 .x0 ≠ 0#64)
    (hpc_sf2 : sf2.pc = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64))
    (hrun_sf2 : sf2.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_sf2 : sf2.sp = s0.sp - 96#64)
    (hcl_sf2 : allocMultiLib.CodeLoaded fmtInnerMpl sf2.mem)
    (hx19_sf2 : sf2.readReg64 .x19 = ret)
    (hx20_sf2 : sf2.readReg64 .x20 = s0.readReg64 .x1)
    (hx21_sf2 : sf2.readReg64 .x21 = s0.readReg64 .x0)
    (hx22_sf2 : sf2.readReg64 .x22 = BitVec.ofNat 64 (fmtEstimatedCapacity (s0.readReg64 .x1) cs))
    (hhg_sf2 : FmtInnerHighGprs s0 sf2)
    (hvregs_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hframe_sf2 : IoCallFrame s0 sf2 ∧ sf2.fs = s0.fs ∧ sf2.trace = s0.trace)
    (r0 r1 r2 v0 v1 v2 v3 v7 : BitVec 64) :
    let cap0 := fmtEstimatedCapacity (s0.readReg64 .x1) cs
    SepWPp P (s0.readReg64 .lr) sf2
      ((A.pool (A.stepEvents (rustAllocEvents cap0 1) b0) sf2 ∗
          Rust.hookFrame (s0.sp - 96#64) ∗
          A.live (sf2.readReg64 .x0) cap0 1 ∗
          memRegion (sf2.readReg64 .x0) cap0) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) v1 v2 v3 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 v0 v7))
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
  intro cap0
  have hcap_pos : 0 < cap0 := Nat.pos_of_ne_zero hcap0
  have hstk70 : 0x70 + stackBytes ≤ 2 ^ 64 := by
    dsimp only [formatInnerFrame] at hstk_fit; omega
  let p := sf2.readReg64 .x0
  apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl_sf2
    (mid := allocPl03.base + 272#64)
  intro s3' hcpu3
  change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
  have hpc3' : s3'.pc = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) :=
    hcpu3.pc_eq.trans hpc_sf2
  have hrun3' : s3'.status = .Running := hcpu3.status_eq.trans hrun_sf2
  have hsp3_in : s3'.sp = s0.sp - 96#64 := hcpu3.sp_eq.trans hsp_sf2
  have hsp3' : s3'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp3_in]; exact s0.spAligned_sub 96#64 hsp0
  have hx0_3' : s3'.readReg64 .x0 = p := hcpu3.readReg64 .x0
  have hp_ne_zero : p ≠ 0#64 := hp_ne
  have hx19_3' : s3'.readReg64 .x19 = ret := (hcpu3.readReg64 .x19).trans hx19_sf2
  have hx20_3' : s3'.readReg64 .x20 = s0.readReg64 .x1 := (hcpu3.readReg64 .x20).trans hx20_sf2
  have hx21_3' : s3'.readReg64 .x21 = s0.readReg64 .x0 := (hcpu3.readReg64 .x21).trans hx21_sf2
  have hx22_3' : s3'.readReg64 .x22 = BitVec.ofNat 64 cap0 := (hcpu3.readReg64 .x22).trans hx22_sf2
  wp_conv_pre =>
    rw [vecHeader_def (s0.sp - 96#64 + 8#64), ← hsp3_in]
  wp_sym_steps
  wp_conv_pre =>
    rw [hsp3_in, ← vecHeader_def (s0.sp - 96#64 + 8#64)]
  apply SepWP.done
    (by simp [wp_norm, arm64_norm])
    (by simpa [wp_norm, arm64_norm] using hrun3')
  intro sm3 hcpu_m3 hcl3 hpseg_3
  obtain ⟨hframe_23, _⟩ :=
    ioCallFrame_of_pureSeg_fmt hcpu3 hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
    rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
  have hrun3 : sm3.status = .Running :=
    hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun3')
  have hsp3 : sm3.sp = s0.sp - 96#64 := by
    rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hsp3_in]
  let st₀ : FmtBuf := ⟨[], BitVec.ofNat 64 cap0, p, rustAllocEvents cap0 1⟩
  have hstart : FmtBufStart cap0 st₀ := fmtBufStart_pos hcap0 p
  have hpre_eq :
      ((A.pool (A.stepEvents (rustAllocEvents cap0 1) b0) sf2 ∗
          Rust.hookFrame (s0.sp - 96#64) ∗
          A.live p cap0 1 ∗
          memRegion p cap0) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) (BitVec.ofNat 64 cap0) p 0#64 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 v0 v7)) =
      vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
        fmtBufVecAt A st₀.cap st₀.ptr st₀.bytes ∗
        A.pool (A.stepEvents st₀.evs b0) sm3 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 v0 v7 := by
    dsimp only [st₀, p]
    rw [fmtBufVecAt_empty_alloc A hcap_pos hcap_lt63 hp_ne,
      A.pool_of_pureSeg _ hpseg_3 hframe_23.1.1 hframe_23.1.2.1,
      fmtCalleeStack_eq_hook (s0.sp - 96#64) stackBytes hstk_min hstk70]
    simp only [List.length_nil]
    apply Entails.antisymm <;> sep_entail
  rw [hpre_eq]
  exact formatInnerBudget_from_110 A E va R_client ArgStep ArgPanic ArgOom stackBytes
    hvt hext_blk hfmtWrite hwriteStr hstk_fit hfit hdec hsafe hargsOk hstart
    hpc3 hrun3 hsp0 hsp3 hcl3
    ((hcpu_m3.readReg64 .x19).trans (by simpa [wp_norm, arm64_norm] using hx19_3'))
    ((hcpu_m3.readReg64 .x20).trans (by simpa [wp_norm, arm64_norm] using hx20_3'))
    ((hcpu_m3.readReg64 .x21).trans (by simpa [wp_norm, arm64_norm] using hx21_3'))
    ⟨(hcpu_m3.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x24).trans hhg_sf2.x24),
     (hcpu_m3.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x25).trans hhg_sf2.x25),
     (hcpu_m3.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x26).trans hhg_sf2.x26),
     (hcpu_m3.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x27).trans hhg_sf2.x27),
     (hcpu_m3.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu3.readReg64 .x28).trans hhg_sf2.x28)⟩
    (hcpu_m3.calleeSavedVRegs.trans
      (by simpa [wp_norm, arm64_norm] using hcpu3.calleeSavedVRegs.trans hvregs_sf2))
    (ioCallFrame_trans hframe_sf2 hframe_23)
    r0 r1 r2 v0 v7

/-- Continuation from `+0x0e4` (`String::with_capacity(cap0)` with `cap0 < 2 ^ 63`). -/
theorem formatInnerBudget_with_capacity_0e4
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
    {F_frame : SepProp} {s0 sm0 : State}
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
    (hcap_lt63 : fmtEstimatedCapacity (s0.readReg64 .x1) cs < 2 ^ 63)
    (hpc0 : sm0.pc = allocPl03.base + 228#64)
    (hrun0 : sm0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_m0 : sm0.sp = s0.sp - 96#64)
    (hcl0 : allocMultiLib.CodeLoaded fmtInnerMpl sm0.mem)
    (hx19_0 : sm0.readReg64 .x19 = ret)
    (hx20_0 : sm0.readReg64 .x20 = s0.readReg64 .x1)
    (hx21_0 : sm0.readReg64 .x21 = s0.readReg64 .x0)
    (hx22_0 : sm0.readReg64 .x22 = BitVec.ofNat 64 (fmtEstimatedCapacity (s0.readReg64 .x1) cs))
    (hhg_0 : FmtInnerHighGprs s0 sm0)
    (hvregs_0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0)
    (hframe_0 : IoCallFrame s0 sm0 ∧ sm0.fs = s0.fs ∧ sm0.trace = s0.trace)
    (r0 r1 r2 v0 v1 v2 v3 v7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHeader (s0.sp - 96#64 + 8#64) v1 v2 v3 ∗
        A.pool b0 sm0 ∗
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
  let cap0 := fmtEstimatedCapacity (s0.readReg64 .x1) cs
  by_cases hcap0 : cap0 = 0
  · apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl0
      (mid := allocPl03.base + 272#64)
    intro s0' hcpu0
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc0' : s0'.pc = allocPl03.base + 228#64 := hcpu0.pc_eq.trans hpc0
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun0
    have hsp0_in : s0'.sp = s0.sp - 96#64 := hcpu0.sp_eq.trans hsp_m0
    have hsp0' : s0'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp0_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx22_0' : s0'.readReg64 .x22 = 0#64 := by
      rw [hcpu0.readReg64 .x22, hx22_0]; simp [cap0, hcap0]
    wp_conv_pre =>
      rw [vecHeader_def (s0.sp - 96#64 + 8#64), ← hsp0_in]
    wp_sym_steps
    wp_conv_pre =>
      rw [hsp0_in, ← vecHeader_def (s0.sp - 96#64 + 8#64)]
    apply SepWP.done
      (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm] using hrun0')
    intro sm3 hcpu_m3 hcl3 hpseg_3
    obtain ⟨hframe_03, _⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
      rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
    have hrun3 : sm3.status = .Running :=
      hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun0')
    have hsp3 : sm3.sp = s0.sp - 96#64 := by
      rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hsp0_in]
    let st₀ : FmtBuf := ⟨[], 0#64, 1#64, []⟩
    have hstart : FmtBufStart cap0 st₀ := by
      simp [FmtBufStart, st₀, hcap0]
    have hpre_eq :
        vecHeader (s0.sp - 96#64 + 8#64) 0#64 1#64 0#64 ∗
          A.pool b0 sm0 ∗
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
        A.pool_of_pureSeg _ hpseg_3 hframe_03.1.1 hframe_03.1.2.1]
      simp only [List.length_nil, emp_sepConj]
    rw [hpre_eq]
    exact formatInnerBudget_from_110 A E va R_client ArgStep ArgPanic ArgOom stackBytes
      hvt hext_blk hfmtWrite hwriteStr hstk_fit hfit hdec hsafe hargsOk hstart
      hpc3 hrun3 hsp0 hsp3 hcl3
      ((hcpu_m3.readReg64 .x19).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x19).trans hx19_0))
      ((hcpu_m3.readReg64 .x20).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x20).trans hx20_0))
      ((hcpu_m3.readReg64 .x21).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x21).trans hx21_0))
      ⟨(hcpu_m3.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x24).trans hhg_0.x24),
       (hcpu_m3.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x25).trans hhg_0.x25),
       (hcpu_m3.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x26).trans hhg_0.x26),
       (hcpu_m3.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x27).trans hhg_0.x27),
       (hcpu_m3.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x28).trans hhg_0.x28)⟩
      (hcpu_m3.calleeSavedVRegs.trans (by simpa [wp_norm, arm64_norm] using hcpu0.calleeSavedVRegs.trans hvregs_0))
      (ioCallFrame_trans hframe_0 hframe_03)
      r0 r1 r2 v0 v7
  · have hcap_pos : 0 < cap0 := Nat.pos_of_ne_zero hcap0
    have hstk70 : 0x70 + stackBytes ≤ 2 ^ 64 := by
      dsimp only [formatInnerFrame] at hstk_fit; omega
    have hfits : A.FitsEvents b0 (rustAllocEvents cap0 1) :=
      A.fitsEvents_of_prefix_env hfit (hsafe.2.1 _ (fmtBufStart_pos hcap0 0#64))
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl0
      (mid := allocMultiLib.resolve fmtInnerMpl fmtInnerShimSym)
    intro s0' hcpu0
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc0' : s0'.pc = allocPl03.base + 228#64 := hcpu0.pc_eq.trans hpc0
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun0
    have hsp0_in : s0'.sp = s0.sp - 96#64 := hcpu0.sp_eq.trans hsp_m0
    have hsp0' : s0'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp0_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx22_0' : s0'.readReg64 .x22 = BitVec.ofNat 64 cap0 :=
      (hcpu0.readReg64 .x22).trans hx22_0
    wp_sym_steps
    apply SepWP.done
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun0')
    intro sm1 hcpu_m1 hcl1 hpseg_1
    obtain ⟨hframe_01, _⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m1 hpseg_1 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool1 : A.pool b0 sm1 = A.pool b0 sm0 :=
      A.pool_of_pureSeg _ hpseg_1 hframe_01.1.1 hframe_01.1.2.1
    have hframe_s1 := ioCallFrame_trans hframe_0 hframe_01
    have hpc1 : sm1.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerShimSym := by
      rw [hcpu_m1.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq _ _ _
    have hrun1 : sm1.status = .Running :=
      hcpu_m1.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun0')
    have hsp1_eq : sm1.sp = s0.sp - 96#64 := by
      rw [hcpu_m1.sp_eq]; simp [wp_norm, arm64_norm, hsp0_in]
    have hsp1 : sm1.spAligned = true := by
      simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 96#64 hsp0
    have hlr1 : sm1.readReg64 .lr = allocPl03.base +
        (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) := by
      rw [hcpu_m1.readReg64 .lr]; simp [wp_norm, arm64_norm]
    have hx19_m1 : sm1.readReg64 .x19 = ret :=
      (hcpu_m1.readReg64 .x19).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x19).trans hx19_0)
    have hx20_m1 : sm1.readReg64 .x20 = s0.readReg64 .x1 :=
      (hcpu_m1.readReg64 .x20).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x20).trans hx20_0)
    have hx21_m1 : sm1.readReg64 .x21 = s0.readReg64 .x0 :=
      (hcpu_m1.readReg64 .x21).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x21).trans hx21_0)
    have hx22_m1 : sm1.readReg64 .x22 = BitVec.ofNat 64 cap0 :=
      (hcpu_m1.readReg64 .x22).trans (by simpa [wp_norm, arm64_norm] using hx22_0')
    have hhg_m1 : FmtInnerHighGprs s0 sm1 :=
      ⟨(hcpu_m1.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x24).trans hhg_0.x24),
       (hcpu_m1.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x25).trans hhg_0.x25),
       (hcpu_m1.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x26).trans hhg_0.x26),
       (hcpu_m1.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x27).trans hhg_0.x27),
       (hcpu_m1.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu0.readReg64 .x28).trans hhg_0.x28)⟩
    have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
      hcpu_m1.calleeSavedVRegs.trans (by simpa [wp_norm, arm64_norm] using hcpu0.calleeSavedVRegs.trans hvregs_0)
    rw [fmtCalleeStack_eq_hook (s0.sp - 96#64) stackBytes hstk_min hstk70]
    refine sepWPp_call_alloc_codeLoaded hcl1 hshim (x := ())
      (F := vecHeader (s0.sp - 96#64 + 8#64) v1 v2 v3 ∗
        A.pool b0 sm0 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 v0 v7)
      hpc1 hrun1 hsp1 hlr1
      (fun R' hm' => by
        dsimp only [budgetAllocShimSpec]
        rw [hsp1_eq]
        revert hm'; intro hm'; sep_frame)
      (fun _ _ _ _ h => not_satisfies_false_sepConj (by dsimp only [budgetAllocShimSpec] at h; exact h))
      (fun _ _ h => False.elim (not_satisfies_false_sepConj (by
        dsimp only [budgetAllocShimSpec] at h
        rw [sepConj_assoc] at h
        exact h)))
      ?_
      (fun _ _ _ h => False.elim (not_satisfies_false_sepConj (by dsimp only [budgetAllocShimSpec] at h; exact h)))
    intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hcl_sf1
    dsimp only [budgetAllocShimSpec]
    rw [hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hacp1, hvm1⟩ => ?_
    have hframe_sf1 := ioCallFrame_trans hframe_s1 (ioCallFrame_of_allocCallPreserved hacp1)
    have hpool_sf1 : A.pool b0 sf1 = A.pool b0 sm0 :=
      (A.pool_transport b0 sm1 sf1 hvm1).trans hpool1
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl_sf1
      (mid := allocMultiLib.resolve fmtInnerMpl fmtInnerAllocSym)
    intro s2' hcpu2
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc2' : s2'.pc = allocPl03.base +
        (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) :=
      hcpu2.pc_eq.trans hpc_sf1
    have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
    have hsp2_in : s2'.sp = s0.sp - 96#64 := (hcpu2.sp_eq.trans hsp_sf1).trans hsp1_eq
    have hsp2' : s2'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx19_2' : s2'.readReg64 .x19 = ret :=
      (hcpu2.readReg64 .x19).trans (hcs_sf1.readReg64_x19.trans hx19_m1)
    have hx20_2' : s2'.readReg64 .x20 = s0.readReg64 .x1 :=
      (hcpu2.readReg64 .x20).trans (hcs_sf1.readReg64_x20.trans hx20_m1)
    have hx21_2' : s2'.readReg64 .x21 = s0.readReg64 .x0 :=
      (hcpu2.readReg64 .x21).trans (hcs_sf1.readReg64_x21.trans hx21_m1)
    have hx22_2' : s2'.readReg64 .x22 = BitVec.ofNat 64 cap0 :=
      (hcpu2.readReg64 .x22).trans (hcs_sf1.readReg64_x22.trans hx22_m1)
    wp_sym_steps
    apply SepWP.done
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun2')
    intro sm2 hcpu_m2 hcl2 hpseg_2
    obtain ⟨hframe_12, _⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu2 hcpu_m2 hpseg_2 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool2 : A.pool b0 sm2 = A.pool b0 sm0 :=
      (A.pool_of_pureSeg _ hpseg_2 hframe_12.1.1 hframe_12.1.2.1).trans hpool_sf1
    have hframe_s2 := ioCallFrame_trans hframe_sf1 hframe_12
    have hpc2 : sm2.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerAllocSym := by
      rw [hcpu_m2.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq _ _ _
    have hrun2 : sm2.status = .Running :=
      hcpu_m2.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun2')
    have hsp2_eq : sm2.sp = s0.sp - 96#64 := by
      rw [hcpu_m2.sp_eq]; simp [wp_norm, arm64_norm, hsp2_in]
    have hsp2 : sm2.spAligned = true := by
      simp only [State.spAligned]; rw [hsp2_eq]; exact s0.spAligned_sub 96#64 hsp0
    have hlr2 : sm2.readReg64 .lr = allocPl03.base +
        (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) := by
      rw [hcpu_m2.readReg64 .lr]; simp [wp_norm, arm64_norm]
    have hx0_m2 : (sm2.readReg64 .x0).toNat = cap0 := by
      rw [hcpu_m2.readReg64 .x0]
      simp only [wp_norm, arm64_norm]
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hx1_m2 : (sm2.readReg64 .x1).toNat = 1 := by
      rw [hcpu_m2.readReg64 .x1]; simp [wp_norm, arm64_norm]
    have hx19_m2 : sm2.readReg64 .x19 = ret := by
      rw [hcpu_m2.readReg64 .x19]; simp only [wp_norm, arm64_norm]; exact hx19_2'
    have hx20_m2 : sm2.readReg64 .x20 = s0.readReg64 .x1 := by
      rw [hcpu_m2.readReg64 .x20]; simp only [wp_norm, arm64_norm]; exact hx20_2'
    have hx21_m2 : sm2.readReg64 .x21 = s0.readReg64 .x0 := by
      rw [hcpu_m2.readReg64 .x21]; simp only [wp_norm, arm64_norm]; exact hx21_2'
    have hx22_m2 : sm2.readReg64 .x22 = BitVec.ofNat 64 cap0 := by
      rw [hcpu_m2.readReg64 .x22]; simp only [wp_norm, arm64_norm]; exact hx22_2'
    have hhg_sf1 := hhg_m1.of_cs hcs_sf1
    have hhg_m2 : FmtInnerHighGprs s0 sm2 :=
      ⟨(hcpu_m2.readReg64 .x24).trans (by simpa [wp_norm, arm64_norm] using (hcpu2.readReg64 .x24).trans hhg_sf1.x24),
       (hcpu_m2.readReg64 .x25).trans (by simpa [wp_norm, arm64_norm] using (hcpu2.readReg64 .x25).trans hhg_sf1.x25),
       (hcpu_m2.readReg64 .x26).trans (by simpa [wp_norm, arm64_norm] using (hcpu2.readReg64 .x26).trans hhg_sf1.x26),
       (hcpu_m2.readReg64 .x27).trans (by simpa [wp_norm, arm64_norm] using (hcpu2.readReg64 .x27).trans hhg_sf1.x27),
       (hcpu_m2.readReg64 .x28).trans (by simpa [wp_norm, arm64_norm] using (hcpu2.readReg64 .x28).trans hhg_sf1.x28)⟩
    have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 :=
      hcpu_m2.calleeSavedVRegs.trans
        (by simpa [wp_norm, arm64_norm] using hcpu2.calleeSavedVRegs.trans (hcs_sf1.vregs.trans hvregs_m1))
    refine sepWPp_call_alloc_codeLoaded hcl2 halloc (x := (cap0, 1, b0))
      (F := vecHeader (s0.sp - 96#64 + 8#64) v1 v2 v3 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 v0 v7)
      hpc2 hrun2 hsp2 hlr2 ?_
      (fun _ _ _ _ h => not_satisfies_false_sepConj (by dsimp only [rustBudgetAllocSpec] at h; exact h))
      (fun _ _ h => False.elim (not_satisfies_false_sepConj (by
        dsimp only [rustBudgetAllocSpec] at h
        rw [sepConj_assoc] at h
        exact h)))
      ?_ ?_
    · intro R' hm'
      dsimp only [rustBudgetAllocSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_m2, hx1_m2, rustLayoutOk_one hcap_pos hcap_lt63⟩, ?_⟩
      rw [hsp2_eq, hpool2]
      revert hm'; intro hm'; sep_frame
    · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2 hcl_sf2
      dsimp only [rustBudgetAllocSpec]
      rw [hsp2_eq, sepConj_assoc]
      refine SepWPp.pure_left fun hacp2 => ?_
      by_cases hp0 : sf2.readReg64 .x0 = 0#64
      · have hp0' : sf2.readReg64 .x0 = 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [pull_pure_third]
        exact SepWPp.pure_left fun hnull =>
          absurd hnull (A.fits_not_nullAllowed_alloc (by decide) hfits)
      · have hp0' : ¬ sf2.readReg64 .x0 = 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [pull_pure_after_two]
        refine SepWPp.pure_left fun _ => ?_
        exact formatInnerBudget_after_alloc_0fc A E va R_client ArgStep ArgPanic ArgOom stackBytes
          hvt hext_blk hfmtWrite hwriteStr hstk_min hstk_fit hfit hdec hsafe hargsOk hcap0 hcap_lt63
          hp0 hpc_sf2 hrun_sf2 hsp0 (hsp_sf2.trans hsp2_eq) hcl_sf2
          (hcs_sf2.readReg64_x19.trans hx19_m2)
          (hcs_sf2.readReg64_x20.trans hx20_m2)
          (hcs_sf2.readReg64_x21.trans hx21_m2)
          (hcs_sf2.readReg64_x22.trans hx22_m2)
          (hhg_m2.of_cs hcs_sf2)
          (hcs_sf2.vregs.trans hvregs_m2)
          (ioCallFrame_trans hframe_s2 (ioCallFrame_of_allocCallPreserved hacp2))
          r0 r1 r2 v0 v1 v2 v3 v7
    · intro sf_o R' _hoom hmo
      exfalso
      dsimp only [rustBudgetAllocSpec] at hmo
      rw [satisfies_pure_sepConj] at hmo
      exact hmo.1.1 hfits

end StageProofs

end VerifiedLibraries.RustStd
