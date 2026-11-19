/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerLemmas
public import VerifiedLibraries.RustStd.Proofs.FinishGrow

/-!
# `alloc::fmt::format::format_inner` Stage Lemmas

Stack-frame and state-preservation helpers (`fmtInnerSavedSlots`, `FmtInnerHighGprs`,
`ioCallFrame_of_pureSeg_fmt`) and stage lemmas (`formatInner_from_110`,
`formatInner_with_capacity_0e4`) for `allocMultiLib` block `3`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib

/-! ## Frame, Stack, Buffer, and State-Preservation Helpers -/

section Helpers
arm64_proof_prelude

private def errnoCell (tp : BitVec 64) : SepProp := StdErrnoCell tp

private theorem errnoCell_eq (tp : BitVec 64) : StdErrnoCell tp = errnoCell tp := rfl

private theorem fmtInnerW_transport_local {oom : State → State → Prop}
    (A : RustStdAlloc oom) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (out : BitVec 64) (st : FmtStr) (s s' : State) (hfr : FmtWriteFrame s s') :
    fmtInnerW A va R t0 out st s ⊢ fmtInnerW A va R t0 out st s' := by
  rcases hfr with ⟨htr, hfs, hsig, htp, hbrk, hbrks, _, hora, _, hsym, _⟩
  have hpool : A.pool st.lb st.lk s = A.pool st.lb st.lk s' :=
    (A.pool_transport st.lb st.lk s s' ⟨hbrks, hbrk, htp⟩).symm
  dsimp only [fmtInnerW, IoCallFrame]
  rw [hsig, htp, hbrks, hora, hsym, hfs, htr, hpool]
  exact Entails.refl _

/-- Saved-register and padding slots in `format_inner`'s `0x60`-byte stack frame
    at `sp1 := s0.sp - 96#64` (excluding `vecHeader (sp1 + 8#64)` at `[sp1 + 8 .. sp1 + 24]`). -/
def fmtInnerSavedSlots (s0 : State) (st0 st7 : BitVec 64) : SepProp :=
  let sp1 := s0.sp - 96#64
  (sp1 ↦₆₄ st0) ∗
  ((sp1 + 32#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp1 + 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp1 + 48#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp1 + 56#64) ↦₆₄ st7) ∗
  ((sp1 + 64#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp1 + 72#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp1 + 80#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp1 + 88#64) ↦₆₄ s0.readReg64 .x19)

/-- Callee-saved GPRs `x24..x28` untouched by `format_inner`. -/
structure FmtInnerHighGprs (s0 s : State) : Prop where
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28

theorem FmtInnerHighGprs.refl (s : State) : FmtInnerHighGprs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem FmtInnerHighGprs.of_cs {s0 s1 s2 : State}
    (h01 : FmtInnerHighGprs s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    FmtInnerHighGprs s0 s2 :=
  ⟨hcs.readReg64_x24.trans h01.x24,
   hcs.readReg64_x25.trans h01.x25,
   hcs.readReg64_x26.trans h01.x26,
   hcs.readReg64_x27.trans h01.x27,
   hcs.readReg64_x28.trans h01.x28⟩

private theorem cells12_eq (a : BitVec 64) :
    cells a 12 =
      ∃∗ st0 : BitVec 64, ∃∗ st1 : BitVec 64, ∃∗ st2 : BitVec 64, ∃∗ st3 : BitVec 64,
      ∃∗ st4 : BitVec 64, ∃∗ st5 : BitVec 64, ∃∗ st6 : BitVec 64, ∃∗ st7 : BitVec 64,
      ∃∗ st8 : BitVec 64, ∃∗ st9 : BitVec 64, ∃∗ st10 : BitVec 64, ∃∗ st11 : BitVec 64,
        (a ↦₆₄ st0) ∗ ((a + 8#64) ↦₆₄ st1) ∗ ((a + 16#64) ↦₆₄ st2) ∗
        ((a + 24#64) ↦₆₄ st3) ∗ ((a + 32#64) ↦₆₄ st4) ∗ ((a + 40#64) ↦₆₄ st5) ∗
        ((a + 48#64) ↦₆₄ st6) ∗ ((a + 56#64) ↦₆₄ st7) ∗ ((a + 64#64) ↦₆₄ st8) ∗
        ((a + 72#64) ↦₆₄ st9) ∗ ((a + 80#64) ↦₆₄ st10) ∗ ((a + 88#64) ↦₆₄ st11) := by
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right]
  simp only [bv_lin_norm]

private theorem stackFrameAt96_eq_cells12 (sp : BitVec 64) :
    stackFrameAt sp 96 = cells (sp - 96#64) 12 := by
  rw [← stackAt_eq_stackFrameAt sp 96 (by decide),
    show (96 : Nat) = 8 * 12 from rfl,
    stackAt_eq_cells sp 12 (by decide)]

private theorem pts12_entails_stackFrameAt96 (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    let a := sp - 96#64
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
    ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗
    ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗
    ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ⊢
      stackFrameAt sp 96 := by
  dsimp only
  rw [stackFrameAt96_eq_cells12 sp, cells12_eq]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _

private theorem fmtCalleeStack_eq_hook (sp1 : BitVec 64) (stackBytes : Nat)
    (hmin : stringWriterStack ≤ stackBytes)
    (hfit : 0x70 + stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp1 (0x70 + stackBytes) =
      (Rust.hookFrame sp1 ∗ stackFrameAt (sp1 - 4096#64) (0x70 + stackBytes - 4096)) := by
  have hge : 4096 ≤ 0x70 + stackBytes := by dsimp only [stringWriterStack] at hmin; omega
  have heq : 0x70 + stackBytes = 4096 + (0x70 + stackBytes - 4096) := by omega
  conv => lhs; rw [heq]
  rw [stackFrameAt_split sp1 4096 (0x70 + stackBytes - 4096) (by omega),
    ← stackAt_eq_stackFrameAt sp1 4096 (by decide)]

private theorem vecHeader_def (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) :=
  rfl

private theorem ioVecBuf_empty_zero {oom : State → State → Prop} (A : RustStdAlloc oom) :
    ioVecBuf A 0#64 1#64 [] = emp := by
  unfold ioVecBuf
  have hp : (([] : List (BitVec 8)).length ≤ (0#64).toNat ∧
      (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨by decide, by decide, by decide⟩⟩
  simp only [hp, ↓reduceIte, pure_true, emp_sepConj]

private theorem ioVecBuf_empty_alloc {oom : State → State → Prop} (A : RustStdAlloc oom)
    {cap0 : Nat} {p : BitVec 64}
    (hpos : 0 < cap0) (hlt : cap0 < 2 ^ 63) (hp0 : p ≠ 0#64) :
    ioVecBuf A (BitVec.ofNat 64 cap0) p [] =
      (A.live p cap0 1 ∗ memRegion p cap0) := by
  unfold ioVecBuf
  have hcap_tn : (BitVec.ofNat 64 cap0).toNat = cap0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 cap0 ≠ 0#64 := by bv_omega
  simp only [hcap_ne, ↓reduceIte, hcap_tn, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, pointsToBytes_nil, emp_sepConj]
  rw [pure_sepConj_of_true ⟨Nat.zero_le _, hlt, hp0⟩]

private theorem rustLayoutOk_one_local {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega, by decide⟩

private theorem bl_target_eq_local (base off target : BitVec 64) :
    base + off + (target - base - off) = target := by
  bv_arith

theorem ioCallFrame_of_pureSeg_fmt {s0 s0' s1 s1' : State}
    (hcpu0 : SameCpuState s0' s0) (hcpu1 : SameCpuState s1 s1')
    (hpseg : PureSegPreserved s0 s1)
    (htp : s1'.tpidrEl0 = s0'.tpidrEl0)
    (hsig : s1'.sigActions = s0'.sigActions) :
    (IoCallFrame s0 s1 ∧ s1.fs = s0.fs ∧ s1.trace = s0.trace) ∧ PoolPreserved s0 s1 := by
  have htp01 : s1.tpidrEl0 = s0.tpidrEl0 :=
    hcpu1.tpidrEl0_eq.trans (htp.trans hcpu0.tpidrEl0_eq)
  have hsig01 : s1.sigActions = s0.sigActions :=
    hcpu1.sigActions_eq.trans (hsig.trans hcpu0.sigActions_eq)
  exact ⟨⟨⟨hsig01, htp01, hpseg.1.2.2.2.1, hpseg.2.1, hpseg.2.2⟩,
          hpseg.1.2.2.2.2.2.2, hpseg.1.1⟩,
         ⟨hpseg.1.2.2.2.1, hpseg.1.2.2.1, htp01⟩⟩

private theorem ioCallFrame_trans {s0 s1 s2 : State}
    (h01 : IoCallFrame s0 s1 ∧ s1.fs = s0.fs ∧ s1.trace = s0.trace)
    (h12 : IoCallFrame s1 s2 ∧ s2.fs = s1.fs ∧ s2.trace = s1.trace) :
    IoCallFrame s0 s2 ∧ s2.fs = s0.fs ∧ s2.trace = s0.trace :=
  ⟨⟨h12.1.1.trans h01.1.1, h12.1.2.1.trans h01.1.2.1, h12.1.2.2.1.trans h01.1.2.2.1,
    h12.1.2.2.2.1.trans h01.1.2.2.2.1, h12.1.2.2.2.2.trans h01.1.2.2.2.2⟩,
   h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

private theorem ioCallFrame_of_allocCallPreserved {s0 s1 : State}
    (h : AllocCallPreserved s0 s1) :
    IoCallFrame s0 s1 ∧ s1.fs = s0.fs ∧ s1.trace = s0.trace :=
  ⟨⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, h.1, h.2.1⟩

private theorem poolPreserved_trans_local {s0 s1 s2 : State}
    (h01 : PoolPreserved s0 s1) (h12 : PoolPreserved s1 s2) : PoolPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

private theorem pull_pure_after_two_local (A1 A2 : SepProp) (P : Prop) (Rest F : SepProp) :
    (A1 ∗ A2 ∗ (⌜P⌝ ∗ Rest)) ∗ F = ⌜P⌝ ∗ ((A1 ∗ A2 ∗ Rest) ∗ F) := by
  rw [← sepConj_assoc A2 ⌜P⌝ Rest, sepConj_comm A2 ⌜P⌝, sepConj_assoc ⌜P⌝ A2 Rest,
    ← sepConj_assoc A1 ⌜P⌝ (A2 ∗ Rest), sepConj_comm A1 ⌜P⌝,
    sepConj_assoc ⌜P⌝ A1 (A2 ∗ Rest), sepConj_assoc ⌜P⌝ _ F]

end Helpers

/-! ## Block-3 Stage Lemmas (`+0x128`, `+0x110`, `+0x0e4`) -/

section StageProofs
set_option maxRecDepth 200000
variable [FormatInnerPlacement]
arm64_proof_prelude

private theorem formatInner_after_fmtWrite {oom : State → State → Prop}
    {P : Program} (A : RustStdAlloc oom) (va : StringWriteAddrs) (R_client : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    (hpanic_unwrap : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym) =
      some Rust.panicked)
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {lb lk : Nat}
    {cs : List FmtCall} {st₀ st' : FmtStr} {ok : Bool}
    {F_frame : SepProp} {s0 sf4 : State}
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hstart : FmtInnerStart A (fmtEstimatedCapacity (s0.readReg64 .x1) cs) lb lk st₀)
    (hrun_fmt : FmtRun (fmtInnerStep A ArgStep) cs st₀ ok st')
    (hpc4 : sf4.pc = allocPl03.base +
      (reloc_call_off% allocLib03.text.relocs "_RNvNtCs2kXltWtc1W_4core3fmt5write" + 4#64))
    (hrun4 : sf4.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp4 : sf4.sp = s0.sp - 96#64)
    (hcl4 : allocMultiLib.CodeLoaded fmtInnerMpl sf4.mem)
    (hw0 : sf4.readReg32 .x0 = if ok then 0#32 else 1#32)
    (hx19_4 : sf4.readReg64 .x19 = ret)
    (hhg_4 : FmtInnerHighGprs s0 sf4)
    (hvregs_4 : calleeSavedVRegs sf4 = calleeSavedVRegs s0)
    (hframe_4 : IoCallFrame s0 sf4 ∧ sf4.fs = s0.fs ∧ sf4.trace = s0.trace)
    (r0 r1 r2 st0 st7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sf4
      (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
        ioVecBuf A st'.cap st'.ptr st'.bytes ∗
        A.pool st'.lb st'.lk sf4 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        errnoCell s0.tpidrEl0 ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 st0 st7)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).post
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onPanic
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onOom
        (ret, argsRo, tpl, args, lb, lk) s0 sf) := by
  cases ok with
  | true =>
    simp only [↓reduceIte] at hw0
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
    obtain ⟨hframe_4f, hpool_4f⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu5 hcpu_f hpseg_f rfl rfl
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
    have hpool_eq : A.pool st'.lb st'.lk sf = A.pool st'.lb st'.lk sf4 :=
      A.pool_transport st'.lb st'.lk sf4 sf hpool_4f
    dsimp only [allocFormatInnerSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨st', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hframe_0f.1, hframe_0f.2.1, hframe_0f.2.2, cs, st₀, hdec, hstart, hrun_fmt⟩, ?_⟩
    rw [hpool_eq, errnoCell_eq]
    have hstk_back :
        vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
        (((s0.sp - 96#64) ↦₆₄ st0) ∗
          ((s0.sp - 96#64 + 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 96#64 + 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 96#64 + 48#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
          ((s0.sp - 96#64 + 56#64) ↦₆₄ st7) ∗
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
        (pts12_entails_stackFrameAt96 s0.sp st0 st'.cap st'.ptr
          (BitVec.ofNat 64 st'.bytes.length)
          (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
          (s0.readReg64 (.gpr 23#5)) st7
          (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
          (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
    have hmf_reord : sf.mem ⊨
        (vecHeader ret st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          ioVecBuf A st'.cap st'.ptr st'.bytes ∗
          A.pool st'.lb st'.lk sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          errnoCell s0.tpidrEl0 ∗
          stringWriteVtableAt va ∗
          R_client ∗
          (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
            (((s0.sp - 96#64) ↦₆₄ st0) ∗
              ((s0.sp - 96#64 + 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
              ((s0.sp - 96#64 + 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
              ((s0.sp - 96#64 + 48#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
              ((s0.sp - 96#64 + 56#64) ↦₆₄ st7) ∗
              ((s0.sp - 96#64 + 64#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
              ((s0.sp - 96#64 + 72#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
              ((s0.sp - 96#64 + 80#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
              ((s0.sp - 96#64 + 88#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
            stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))) ∗ F_frame := by
      revert hmf; intro hmf; sep_frame
    refine Satisfies.mono (sepConj_mono_left ?_) hmf_reord
    exact sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
      sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
      sepConj_mono_right hstk_back
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hw0
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl4
      (mid := allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym)
    intro s5' hcpu5
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc5' : s5'.pc = allocPl03.base +
        (reloc_call_off% allocLib03.text.relocs "_RNvNtCs2kXltWtc1W_4core3fmt5write" + 4#64) :=
      hcpu5.pc_eq.trans hpc4
    have hrun5' : s5'.status = .Running := hcpu5.status_eq.trans hrun4
    have hsp5_in : s5'.sp = s0.sp - 96#64 := hcpu5.sp_eq.trans hsp4
    have hsp5' : s5'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp5_in]; exact s0.spAligned_sub 96#64 hsp0
    have hw0_5' : (s5'.readReg64 (.gpr 0#5)).setWidth 32 = 1#32 := by
      simp only [State.readReg32] at hw0
      rw [hcpu5.readReg64 .x0]; exact hw0
    wp_sym_steps
    apply SepWP.done
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq_local _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun5')
    intro sm_pan hcpu_pan _hcl_pan hpseg_pan
    have hpc_pan : sm_pan.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym := by
      rw [hcpu_pan.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq_local _ _ _
    have hrun_pan : sm_pan.status = .Running :=
      hcpu_pan.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun5')
    refine SepWPp.panic hrun_pan (hpc_pan ▸ hpanic_unwrap) ?_
    intro hmp
    dsimp only [allocFormatInnerSpec]
    rw [satisfies_pure_sepConj]
    have hfs_pan : (Rust.panicked sm_pan).fs = s0.fs :=
      hpseg_pan.1.2.2.2.2.2.2.trans hframe_4.2.1
    have htr_pan : (Rust.panicked sm_pan).trace = s0.trace :=
      hpseg_pan.1.1.trans hframe_4.2.2
    exact ⟨⟨hfs_pan, htr_pan, cs, hdec, Or.inr (Or.inr ⟨st₀, st', hstart, hrun_fmt⟩)⟩,
           Satisfies.drop_left hmp⟩

/-- Continuation from `+0x110` (`272#64`): loads `va.vtable` (`adrp+add .Lanon.34`), prepares
    `(out, va.vtable, x0, x1)`, invokes `core::fmt::write`, and finishes via
    `formatInner_after_fmtWrite`. -/
theorem formatInner_from_110 {oom : State → State → Prop}
    {P : Program} (A : RustStdAlloc oom) (va : StringWriteAddrs) (R_client : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    (hpanic_unwrap : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym) =
      some Rust.panicked)
    (hfmtWrite : ∀ (t0 : State) (out : BitVec 64),
      subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym)
        (coreFmtWriteSpec P (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes))
    (hwriteStr : ∀ (t0 : State) (out ptr : BitVec 64) (bs : List (BitVec 8)),
      subroutine_ok P va.writeStr
        (fmtWriteStrCallSpec (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes out ptr bs))
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {lb lk : Nat}
    {cs : List FmtCall} {st₀ : FmtStr}
    {F_frame : SepProp} {s0 sm3 : State}
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hargsOk : FmtInnerArgsOk P A va R_client ArgStep ArgPanic stackBytes s0 cs)
    (hstart : FmtInnerStart A (fmtEstimatedCapacity (s0.readReg64 .x1) cs) lb lk st₀)
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
    (r0 r1 r2 st0 st7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sm3
      (vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
        ioVecBuf A st₀.cap st₀.ptr st₀.bytes ∗
        A.pool st₀.lb st₀.lk sm3 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        StdErrnoCell s0.tpidrEl0 ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 st0 st7)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).post
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onPanic
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onOom
        (ret, argsRo, tpl, args, lb, lk) s0 sf) := by
  rw [errnoCell_eq]
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
    (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq_local _ _ _)
    (by simpa [wp_norm, arm64_norm] using hrun3')
  intro sm4 hcpu_m4 hcl4 hpseg_4
  obtain ⟨hframe_34, hpool_34⟩ :=
    ioCallFrame_of_pureSeg_fmt hcpu3 hcpu_m4 hpseg_4 (by simp [arm64_norm]) (by simp [arm64_norm])
  have hframe_04 := ioCallFrame_trans hframe_3 hframe_34
  have hpc4 : sm4.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym := by
    rw [hcpu_m4.pc_eq]
    dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
    exact bl_target_eq_local _ _ _
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
  have hcb : FmtCallbacks P (fmtInnerW A va R_client s0 out) (fmtInnerStep A ArgStep)
      (fmtInnerPanic ArgPanic s0) (fmtInnerOom oom s0) stackBytes out va.vtable va.writeStr cs :=
    { transport := fmtInnerW_transport_local A va R_client s0 out
      write_str := fun ptr bs _ => hwriteStr s0 out ptr bs
      fmt_arg := fun idx value fmtFn opts hmem => hargsOk idx value fmtFn opts hmem out }
  refine sepWPp_call_alloc_codeLoaded hcl4 (hfmtWrite s0 out)
    (x := (out, va.vtable, va.writeStr, argsRo, tpl, args, st₀))
    (F := vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7)
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
    dsimp only [fmtInnerW]
    rw [A.pool_transport st₀.lb st₀.lk sm3 sm4 hpool_34, errnoCell_eq]
    have hvt_dup : stringWriteVtableAt va =
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) := by
      simp only [stringWriteVtableAt, ← sepConj_assoc, pointsTo64RO_dup]
    rw [hvt_dup] at hm'
    have hm_pure : sm4.mem ⊨
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          (⌜IoCallFrame s0 sm4 ∧ sm4.fs = s0.fs ∧ sm4.trace = s0.trace⌝ ∗
            vecHeader out st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
            ioVecBuf A st₀.cap st₀.ptr st₀.bytes ∗ A.pool st₀.lb st₀.lk sm3 ∗
            errnoCell s0.tpidrEl0 ∗ stringWriteVtableAt va ∗ R_client) ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes)) ∗
        ((vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7) ∗ R') := by
      rw [pure_sepConj_of_true hframe_04]; dsimp only [out]; revert hm'; intro hm'; sep_frame
    exact hm_pure
  · intro sf_p _hpan hmp
    dsimp only [coreFmtWriteSpec] at hmp
    rw [hx2_m4, hx3_m4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmp
    rcases hmp with ⟨⟨cs', c, st, hdec', hreach, hpan_c⟩, hmp_rest⟩
    have hcs_eq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec); subst cs'
    dsimp only [allocFormatInnerSpec]; rw [satisfies_pure_sepConj]; rw [← sepConj_assoc] at hmp_rest
    exact ⟨⟨hpan_c.1, hpan_c.2.1, cs, hdec, Or.inr (Or.inl ⟨st₀, c, st, hstart, hreach, hpan_c.2.2⟩)⟩,
           Satisfies.drop_left hmp_rest⟩
  · intro sf4 hpc_sf4 hrun_sf4 hsp_sf4 hcs_sf4 hcl_sf4
    dsimp only [coreFmtWriteSpec]; rw [hx2_m4, hx3_m4, hsp4_eq]; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ok => SepWPp.exists_elim fun st' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hw0_sf4, cs', hdec', hrun_fmt'⟩ => ?_
    have hcs_eq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec); subst cs'
    dsimp only [fmtInnerW]
    rw [errnoCell_eq, sepConj_assoc ⌜IoCallFrame s0 sf4 ∧ sf4.fs = s0.fs ∧ sf4.trace = s0.trace⌝,
      pull_pure_after_two_local]
    refine SepWPp.pure_left fun hframe_sf4 => ?_
    have hvt_rejoin : (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) =
        stringWriteVtableAt va := by
      simp only [stringWriteVtableAt, ← sepConj_assoc, pointsTo64RO_dup]
    have hmerge :
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          ((vecHeader out st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
            ioVecBuf A st'.cap st'.ptr st'.bytes ∗ A.pool st'.lb st'.lk sf4 ∗
            errnoCell s0.tpidrEl0 ∗ stringWriteVtableAt va ∗ R_client) ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes))) ∗
        (vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7) =
        (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          ioVecBuf A st'.cap st'.ptr st'.bytes ∗ A.pool st'.lb st'.lk sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          errnoCell s0.tpidrEl0 ∗ R_client ∗ stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7) := by
      dsimp only [out]; apply Entails.antisymm <;> sep_entail
    have hreord :
        stringWriteVtableAt va ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          ioVecBuf A st'.cap st'.ptr st'.bytes ∗ A.pool st'.lb st'.lk sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          errnoCell s0.tpidrEl0 ∗ R_client ∗ stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7) =
        vecHeader (s0.sp - 96#64 + 8#64) st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          ioVecBuf A st'.cap st'.ptr st'.bytes ∗ A.pool st'.lb st'.lk sf4 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          errnoCell s0.tpidrEl0 ∗ stringWriteVtableAt va ∗ R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗ fmtInnerSavedSlots s0 st0 st7 := by
      apply Entails.antisymm <;> sep_entail
    rw [hmerge, hvt_rejoin, hreord]
    exact formatInner_after_fmtWrite A va R_client ArgStep ArgPanic stackBytes
      hext_blk hpanic_unwrap hstk_fit hdec hstart hrun_fmt'
      hpc_sf4 hrun_sf4 hsp0 (hsp_sf4.trans hsp4_eq) hcl_sf4 hw0_sf4
      (hcs_sf4.readReg64_x19.trans hx19_m4) (hhg_m4.of_cs hcs_sf4)
      (hcs_sf4.vregs.trans hvregs_m4) hframe_sf4 r0 r1 r2 st0 st7
  · intro sf_o R' _hoom hmo
    dsimp only [coreFmtWriteSpec] at hmo
    dsimp only [allocFormatInnerSpec]
    have hmo' := Satisfies.drop_mid hmo
    rw [satisfies_pure_sepConj] at hmo' ⊢
    rcases hmo'.1 with ⟨_, _, _, _, _, hoom_o⟩
    exact ⟨hoom_o, hmo'.2⟩

private theorem formatInner_after_alloc_0fc {oom : State → State → Prop}
    {P : Program} (A : RustStdAlloc oom) (va : StringWriteAddrs) (R_client : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    (hpanic_oom : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerHandleErrorSym) =
      some Rust.panicked)
    (hpanic_unwrap : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym) =
      some Rust.panicked)
    (hfmtWrite : ∀ (t0 : State) (out : BitVec 64),
      subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym)
        (coreFmtWriteSpec P (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes))
    (hwriteStr : ∀ (t0 : State) (out ptr : BitVec 64) (bs : List (BitVec 8)),
      subroutine_ok P va.writeStr
        (fmtWriteStrCallSpec (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes out ptr bs))
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {lb lk : Nat}
    {cs : List FmtCall}
    {F_frame : SepProp} {s0 sf2 : State}
    (hstk_min : stringWriterStack ≤ stackBytes)
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hargsOk : FmtInnerArgsOk P A va R_client ArgStep ArgPanic stackBytes s0 cs)
    (hcap0 : fmtEstimatedCapacity (s0.readReg64 .x1) cs ≠ 0)
    (hcap_lt63 : fmtEstimatedCapacity (s0.readReg64 .x1) cs < 2 ^ 63)
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
    (r0 r1 r2 st0 st1 st2 st3 st7 : BitVec 64) :
    let cap0 := fmtEstimatedCapacity (s0.readReg64 .x1) cs
    SepWPp P (s0.readReg64 .lr) sf2
      ((errnoCell s0.tpidrEl0 ∗
          Rust.hookFrame (s0.sp - 96#64) ∗
          if sf2.readReg64 .x0 = 0 then
            ⌜NullAllowed cap0 1⌝ ∗ A.pool lb lk sf2
          else
            ⌜(sf2.readReg64 .x0).toNat % 1 = 0⌝ ∗
              A.pool (lb + A.cost cap0 1) (lk + 1) sf2 ∗
              A.live (sf2.readReg64 .x0) cap0 1 ∗
              memRegion (sf2.readReg64 .x0) cap0) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 st0 st7))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).post
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onPanic
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onOom
        (ret, argsRo, tpl, args, lb, lk) s0 sf) := by
  intro cap0
  have hcap_pos : 0 < cap0 := Nat.pos_of_ne_zero hcap0
  have hstk70 : 0x70 + stackBytes ≤ 2 ^ 64 := by
    dsimp only [formatInnerFrame] at hstk_fit; omega
  by_cases hp0 : sf2.readReg64 .x0 = 0#64
  · have hp0' : sf2.readReg64 .x0 = 0 := hp0
    conv =>
      arg 4
      simp only [hp0', ↓reduceIte]
      rw [pull_pure_after_two_local]
    refine SepWPp.pure_left fun hnull => ?_
    apply sepWPp_seg_alloc_block_pure 3 (by decide) hext_blk allocBlockNoSvc0_03 hcl_sf2
      (mid := allocMultiLib.resolve fmtInnerMpl fmtInnerHandleErrorSym)
    intro s3' hcpu3
    change SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) _ _ _ _
    have hpc3' : s3'.pc = allocPl03.base +
        (reloc_call_off% allocLib03.text.relocs "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) :=
      hcpu3.pc_eq.trans hpc_sf2
    have hrun3' : s3'.status = .Running := hcpu3.status_eq.trans hrun_sf2
    have hsp3_in : s3'.sp = s0.sp - 96#64 := hcpu3.sp_eq.trans hsp_sf2
    have hsp3' : s3'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp3_in]; exact s0.spAligned_sub 96#64 hsp0
    have hx0_3' : s3'.readReg64 .x0 = 0#64 := (hcpu3.readReg64 .x0).trans hp0
    wp_sym_steps
    apply SepWP.done
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq_local _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun3')
    intro sm_pan hcpu_pan _hcl_pan hpseg_pan
    have hpc_pan : sm_pan.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerHandleErrorSym := by
      rw [hcpu_pan.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq_local _ _ _
    have hrun_pan : sm_pan.status = .Running :=
      hcpu_pan.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun3')
    refine SepWPp.panic hrun_pan (hpc_pan ▸ hpanic_oom) ?_
    intro hmp
    dsimp only [allocFormatInnerSpec]
    rw [satisfies_pure_sepConj]
    have hfs_pan : (Rust.panicked sm_pan).fs = s0.fs :=
      hpseg_pan.1.2.2.2.2.2.2.trans hframe_sf2.2.1
    have htr_pan : (Rust.panicked sm_pan).trace = s0.trace :=
      hpseg_pan.1.1.trans hframe_sf2.2.2
    exact ⟨⟨hfs_pan, htr_pan, cs, hdec, Or.inl hnull⟩, Satisfies.drop_left hmp⟩
  · let p := sf2.readReg64 .x0
    have hp_ne0 : sf2.readReg64 .x0 ≠ 0 := hp0
    conv =>
      arg 4
      simp only [hp_ne0, ↓reduceIte]
      rw [pull_pure_after_two_local]
    refine SepWPp.pure_left fun _halign => ?_
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
    have hp_ne_zero : p ≠ 0#64 := hp0
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
    obtain ⟨hframe_23, hpool_23⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu3 hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
      rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
    have hrun3 : sm3.status = .Running :=
      hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun3')
    have hsp3 : sm3.sp = s0.sp - 96#64 := by
      rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hsp3_in]
    let st₀ : FmtStr := ⟨[], BitVec.ofNat 64 cap0, p, lb + A.cost cap0 1, lk + 1⟩
    have hstart : FmtInnerStart A cap0 lb lk st₀ := by
      dsimp only [FmtInnerStart, st₀, cap0]
      simp [hcap0]
    have hpre_eq :
        ((errnoCell s0.tpidrEl0 ∗
          Rust.hookFrame (s0.sp - 96#64) ∗
          A.pool (lb + A.cost cap0 1) (lk + 1) sf2 ∗
          A.live p cap0 1 ∗
          memRegion p cap0) ∗
        (vecHeader (s0.sp - 96#64 + 8#64) (BitVec.ofNat 64 cap0) p 0#64 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 st0 st7)) =
        vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
          ioVecBuf A st₀.cap st₀.ptr st₀.bytes ∗
          A.pool st₀.lb st₀.lk sm3 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          StdErrnoCell s0.tpidrEl0 ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 st0 st7 := by
      dsimp only [st₀, p]
      rw [ioVecBuf_empty_alloc A hcap_pos hcap_lt63 hp0,
        ← A.pool_transport (lb + A.cost cap0 1) (lk + 1) sf2 sm3 hpool_23,
        fmtCalleeStack_eq_hook (s0.sp - 96#64) stackBytes hstk_min hstk70,
        ← errnoCell_eq]
      simp only [List.length_nil]
      apply Entails.antisymm <;> sep_entail
    rw [hpre_eq]
    exact formatInner_from_110 A va R_client ArgStep ArgPanic stackBytes
      hvt hext_blk hpanic_unwrap hfmtWrite hwriteStr
      hstk_fit hdec hargsOk hstart
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
      r0 r1 r2 st0 st7

/-- Continuation from `+0x0e4` (`228#64`, `String::with_capacity(cap0)` with `cap0 < 2 ^ 63`):
    - `cap0 = 0`: skips allocation (`cbz x22, 0x104`), writes `{0, 1, 0}` at `sp + 8`, and enters
      `formatInner_from_110`;
    - `0 < cap0 < 2 ^ 63`: calls `shim` and `__rust_alloc(cap0, 1)`, panics at `handle_error` on
      null (`NullAllowed cap0 1`), or writes `{cap0, p, 0}` at `sp + 8` and enters
      `formatInner_from_110`. -/
theorem formatInner_with_capacity_0e4 {oom : State → State → Prop}
    {P : Program} (A : RustStdAlloc oom) (va : StringWriteAddrs) (R_client : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat)
    (hvt : va.vtable = allocMultiLib.resolve fmtInnerMpl stringWriteVtableSym)
    (hext_blk : FmtAllocBlockNoExtern fmtInnerMpl P 3)
    (hpanic_oom : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerHandleErrorSym) =
      some Rust.panicked)
    (hpanic_unwrap : P.externAt? (allocMultiLib.resolve fmtInnerMpl fmtInnerUnwrapFailedSym) =
      some Rust.panicked)
    (hshim : subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerShimSym)
      VerifiedLibraries.RustStd.Io.rustAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerAllocSym)
      (rustStdAllocSpec A))
    (hfmtWrite : ∀ (t0 : State) (out : BitVec 64),
      subroutine_ok P (allocMultiLib.resolve fmtInnerMpl fmtInnerCoreFmtWriteRawSym)
        (coreFmtWriteSpec P (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes))
    (hwriteStr : ∀ (t0 : State) (out ptr : BitVec 64) (bs : List (BitVec 8)),
      subroutine_ok P va.writeStr
        (fmtWriteStrCallSpec (fmtInnerW A va R_client t0 out) (fmtInnerStep A ArgStep)
          (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes out ptr bs))
    {ret : BitVec 64} {argsRo : Bool} {tpl : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {lb lk : Nat}
    {cs : List FmtCall}
    {F_frame : SepProp} {s0 sm0 : State}
    (hstk_min : stringWriterStack ≤ stackBytes)
    (hstk_fit : formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64)
    (hcan : ∀ lb' lk' n al, A.CanAlloc lb' lk' n al)
    (hdec : decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs)
    (hargsOk : FmtInnerArgsOk P A va R_client ArgStep ArgPanic stackBytes s0 cs)
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
    (r0 r1 r2 st0 st1 st2 st3 st7 : BitVec 64) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
        A.pool lb lk sm0 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        StdErrnoCell s0.tpidrEl0 ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 st0 st7)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).post
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ F_frame) →
          (sf.mem ⊨ (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onPanic
            (ret, argsRo, tpl, args, lb, lk) s0 sf ∗ F_frame))
      (fun sf => (allocFormatInnerSpec P A va R_client ArgStep ArgPanic stackBytes).onOom
        (ret, argsRo, tpl, args, lb, lk) s0 sf) := by
  rw [errnoCell_eq]
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
    obtain ⟨hframe_03, hpool_03⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m3 hpseg_3 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc3 : sm3.pc = allocPl03.base + 272#64 := by
      rw [hcpu_m3.pc_eq]; simp [wp_norm, arm64_norm]
    have hrun3 : sm3.status = .Running :=
      hcpu_m3.status_eq.trans (by simpa [wp_norm, arm64_norm] using hrun0')
    have hsp3 : sm3.sp = s0.sp - 96#64 := by
      rw [hcpu_m3.sp_eq]; simp [wp_norm, arm64_norm, hsp0_in]
    let st₀ : FmtStr := ⟨[], 0#64, 1#64, lb, lk⟩
    have hstart : FmtInnerStart A cap0 lb lk st₀ := by
      simp [FmtInnerStart, st₀, hcap0]
    have hpre_eq :
        vecHeader (s0.sp - 96#64 + 8#64) 0#64 1#64 0#64 ∗
          A.pool lb lk sm0 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          errnoCell s0.tpidrEl0 ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 st0 st7 =
        vecHeader (s0.sp - 96#64 + 8#64) st₀.cap st₀.ptr (BitVec.ofNat 64 st₀.bytes.length) ∗
          ioVecBuf A st₀.cap st₀.ptr st₀.bytes ∗
          A.pool st₀.lb st₀.lk sm3 ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          StdErrnoCell s0.tpidrEl0 ∗
          stringWriteVtableAt va ∗
          R_client ∗
          stackFrameAt (s0.sp - 96#64) (0x70 + stackBytes) ∗
          vecHeader ret r0 r1 r2 ∗
          fmtInnerSavedSlots s0 st0 st7 := by
      dsimp only [st₀]
      rw [ioVecBuf_empty_zero, ← A.pool_transport lb lk sm0 sm3 hpool_03, ← errnoCell_eq]
      simp only [List.length_nil, emp_sepConj]
    rw [hpre_eq]
    exact formatInner_from_110 A va R_client ArgStep ArgPanic stackBytes
      hvt hext_blk hpanic_unwrap hfmtWrite hwriteStr
      hstk_fit hdec hargsOk hstart
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
      r0 r1 r2 st0 st7
  · have hcap_pos : 0 < cap0 := Nat.pos_of_ne_zero hcap0
    have hcap_ne : BitVec.ofNat 64 cap0 ≠ 0#64 := by bv_omega
    have hstk70 : 0x70 + stackBytes ≤ 2 ^ 64 := by
      dsimp only [formatInnerFrame] at hstk_fit; omega
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
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq_local _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun0')
    intro sm1 hcpu_m1 hcl1 hpseg_1
    obtain ⟨hframe_01, hpool_01⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu0 hcpu_m1 hpseg_1 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hframe_s1 := ioCallFrame_trans hframe_0 hframe_01
    have hpc1 : sm1.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerShimSym := by
      rw [hcpu_m1.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq_local _ _ _
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
      (F := vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
        A.pool lb lk sm0 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        errnoCell s0.tpidrEl0 ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 st0 st7)
      hpc1 hrun1 hsp1 hlr1
      (fun R' hm' => by
        dsimp only [VerifiedLibraries.RustStd.Io.rustAllocShimSpec]
        rw [hsp1_eq]
        revert hm'; intro hm'; sep_frame)
      (fun _ _ _ _ h => not_satisfies_false_sepConj (by dsimp only [VerifiedLibraries.RustStd.Io.rustAllocShimSpec] at h; exact h))
      (fun _ _ h => False.elim (not_satisfies_false_sepConj (by
        dsimp only [VerifiedLibraries.RustStd.Io.rustAllocShimSpec] at h
        rw [sepConj_assoc] at h
        exact h)))
      ?_
      (fun _ _ _ h => False.elim (not_satisfies_false_sepConj (by dsimp only [VerifiedLibraries.RustStd.Io.rustAllocShimSpec] at h; exact h)))
    intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hcl_sf1
    dsimp only [VerifiedLibraries.RustStd.Io.rustAllocShimSpec]
    rw [hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hacp1, hbrk1⟩ => ?_
    have hframe_sf1 := ioCallFrame_trans hframe_s1 (ioCallFrame_of_allocCallPreserved hacp1)
    have hpool_0_sf1 : PoolPreserved sm0 sf1 :=
      poolPreserved_trans_local hpool_01 ⟨hacp1.2.2.2.2.1, hbrk1, hacp1.2.2.2.1⟩
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
      (by dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]; exact bl_target_eq_local _ _ _)
      (by simpa [wp_norm, arm64_norm] using hrun2')
    intro sm2 hcpu_m2 hcl2 hpseg_2
    obtain ⟨hframe_12, hpool_12⟩ :=
      ioCallFrame_of_pureSeg_fmt hcpu2 hcpu_m2 hpseg_2 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hframe_s2 := ioCallFrame_trans hframe_sf1 hframe_12
    have hpool_0_m2 := poolPreserved_trans_local hpool_0_sf1 hpool_12
    have hpc2 : sm2.pc = allocMultiLib.resolve fmtInnerMpl fmtInnerAllocSym := by
      rw [hcpu_m2.pc_eq]
      dsimp only [State.setMem, State.setPC, State.writeReg64, State.writeReg]
      exact bl_target_eq_local _ _ _
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
    refine sepWPp_call_alloc_codeLoaded hcl2 halloc (x := (cap0, 1, lb, lk))
      (F := vecHeader (s0.sp - 96#64 + 8#64) st1 st2 st3 ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗
        R_client ∗
        stackFrameAt (s0.sp - 96#64 - 4096#64) (0x70 + stackBytes - 4096) ∗
        vecHeader ret r0 r1 r2 ∗
        fmtInnerSavedSlots s0 st0 st7)
      hpc2 hrun2 hsp2 hlr2 ?_
      (fun _ _ _ _ h => not_satisfies_false_sepConj (by dsimp only [rustStdAllocSpec] at h; exact h))
      (fun _ _ h => False.elim (not_satisfies_false_sepConj (by
        dsimp only [rustStdAllocSpec] at h
        rw [sepConj_assoc] at h
        exact h)))
      ?_ ?_
    · intro R' hm'
      dsimp only [rustStdAllocSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_m2, hx1_m2, rustLayoutOk_one_local hcap_pos hcap_lt63, hcan lb lk cap0 1⟩, ?_⟩
      rw [hsp2_eq, A.pool_transport lb lk sm0 sm2 hpool_0_m2, hframe_s2.1.2.1, errnoCell_eq]
      revert hm'; intro hm'; sep_frame
    · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2 hcl_sf2
      dsimp only [rustStdAllocSpec]
      rw [hsp2_eq, hframe_s2.1.2.1, errnoCell_eq, sepConj_assoc]
      refine SepWPp.pure_left fun hacp2 => ?_
      exact formatInner_after_alloc_0fc A va R_client ArgStep ArgPanic stackBytes
        hvt hext_blk hpanic_oom hpanic_unwrap hfmtWrite hwriteStr
        hstk_min hstk_fit hdec hargsOk hcap0 hcap_lt63
        hpc_sf2 hrun_sf2 hsp0 (hsp_sf2.trans hsp2_eq) hcl_sf2
        (hcs_sf2.readReg64_x19.trans hx19_m2)
        (hcs_sf2.readReg64_x20.trans hx20_m2)
        (hcs_sf2.readReg64_x21.trans hx21_m2)
        (hcs_sf2.readReg64_x22.trans hx22_m2)
        (hhg_m2.of_cs hcs_sf2)
        (hcs_sf2.vregs.trans hvregs_m2)
        (ioCallFrame_trans hframe_s2 (ioCallFrame_of_allocCallPreserved hacp2))
        r0 r1 r2 st0 st1 st2 st3 st7
    · intro sf_o R' _hoom hmo
      dsimp only [rustStdAllocSpec] at hmo
      dsimp only [allocFormatInnerSpec]
      have hmo' := Satisfies.drop_mid hmo
      rw [satisfies_pure_sepConj] at hmo' ⊢
      exact ⟨⟨sm2, ⟨hframe_s2.2.2, hframe_s2.1.1⟩, hframe_s2.2.1, hmo'.1⟩, hmo'.2⟩

end StageProofs

end VerifiedLibraries.RustStd
