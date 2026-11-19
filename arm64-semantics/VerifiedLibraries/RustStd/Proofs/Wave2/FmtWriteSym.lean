/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Generated.CorePlacedObj
public import VerifiedLibraries.RustStd.Proofs.ExecSegSym
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement and Segment Infrastructure for `core::fmt::write`

Provides `WordTree` fetch generation for `core::fmt::write` (`coreMultiLib` block `0`), the
block-local pure-segment lifter `sepWPp_seg_coreFmt_pure`, and `0x70`-byte stack-frame folding
helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-- Placement typeclass for `core::fmt::write` (`coreMultiLib` block `0`). -/
class CoreFmtWritePl where
  mpl : MultiPlacement
  placeable : coreMultiLib.Placeable mpl

abbrev coreFmtMpl [CoreFmtWritePl] : MultiPlacement := CoreFmtWritePl.mpl

def cwLib0 : PlacedLib := coreMultiLib.blockLib 0
def cwPl0 [CoreFmtWritePl] : Placement := coreMultiLib.blockPlacement CoreFmtWritePl.mpl 0
theorem cwPlaceable0 [CoreFmtWritePl] : cwLib0.Placeable cwPl0 :=
  coreMultiLib.placeable_blockLib (by decide) CoreFmtWritePl.placeable
def cwPC0 [CoreFmtWritePl] : Program := cwLib0.program cwPl0

def cwProg0 : Program := { code := cwLib0.text.code, symbols := cwLib0.text.symbols }
def cwTree0 : WordTree := word_tree_of% cwProg0
theorem cw0_code_eq : cwLib0.text.code = cwTree0.toBytes := by rfl_kernel
theorem cw0_tree_size : cwTree0.checkSize? = some 109 := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cwPC0 cwLib0 cwTree0 cw0_code_eq cw0_tree_size
  via_placement cwPl0 cwPlaceable0 [0x0 → 0x1b0]
end

def cwIsGprOrBranch : Instr → Bool
  | .addSubImm .. | .addSubShift .. | .addSubExt .. | .logicalImm .. | .logicalShift ..
  | .moveWide .. | .bitfield .. | .condCompareImm .. | .condCompareReg .. | .condSelect ..
  | .b .. | .bl .. | .bCond .. | .cbz .. | .tbz .. | .br .. | .blr .. | .ret ..
  | .ldr .. | .str .. | .ldp .. | .stp .. => true
  | _ => false

theorem cwNoSvc0_0 : checkBlockNoSvc0 (coreMultiLib.blockLib 0).text = true := by
  rfl_kernel

theorem cwNoMsr_0 : cwProg0.allInstrs (fun i => !i.isMsrTpidrEl0) = true := by
  rfl_kernel

theorem cwGpr_0 : cwProg0.allInstrs cwIsGprOrBranch = true := by
  rfl_kernel

private theorem execInst_oracle_of_gpr {inst : Instr} (h : cwIsGprOrBranch inst = true) (s : State) :
    (execInst inst s).oracle = s.oracle := by
  cases inst
  case addSubImm | addSubShift | addSubExt | logicalImm | logicalShift | moveWide | bitfield
     | condCompareImm | condCompareReg | condSelect
     | b | bl | bCond | cbz | tbz | br | blr | ret
     | ldr | str | ldp | stp =>
    dsimp only [execInst, execInstWithSvc, execLdr, execStr, execLdp, execStp,
      execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift,
      execMoveWide, execBitfield, execCondCompare, execCondSelect]
    (repeat' split) <;>
      simp [State.oracle_advancePC, State.oracle_setPC, State.oracle_setMem,
        State.oracle_setPState, State.oracle_setStatus, State.oracle_writeReg64,
        State.oracle_writeReg]
  all_goals simp [cwIsGprOrBranch] at h

theorem fnAddr_coreFmtWrite {mpl : MultiPlacement} (hpl : coreMultiLib.Placeable mpl) :
    coreMultiLib.fnAddr mpl "core::fmt::write" = mpl.base 0 :=
  fnAddr_eq_base hpl 0 "core::fmt::write" (by decide) (by decide)

private theorem strip_codeLoaded_cw {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_cw (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_cw {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_cw {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    (hall_msr : R_j.allInstrs (fun i => !i.isMsrTpidrEl0) = true)
    (hall_gpr : R_j.allInstrs cwIsGprOrBranch = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧
        sf.sigActions = s1.sigActions ∧ sf.tpidrEl0 = s1.tpidrEl0 ∧ sf.oracle = s1.oracle := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl, rfl, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_cw hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_cw hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_cw R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hgpr : cwIsGprOrBranch inst = true :=
        Program.fetchMem_of_allInstrs hall_gpr hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              simpa using (ProofLib.strip_perm_x_imp hx0).2
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hsig1 : (execInst inst s1).sigActions = s1.sigActions :=
        (execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1).1
      have htp1 : (execInst inst s1).tpidrEl0 = s1.tpidrEl0 :=
        execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
      have horc1 : (execInst inst s1).oracle = s1.oracle :=
        execInst_oracle_of_gpr hgpr s1
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, hsig_rest, htp_rest, horc_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest,
        hsig_rest.trans hsig1, htp_rest.trans htp1, horc_rest.trans horc1⟩

/-- Lift a pure `SepWP` segment on `cwPC0.rebase cwPl0.base (fun _ => none)` directly into
    `SepWPp P ret s Pre Q Qp oom` for any `P : Program` that has no hooks inside the 436-byte body
    of `core::fmt::write` (`coreMultiLib.blocks[0]`). -/
theorem sepWPp_seg_coreFmt_pure [CoreFmtWritePl] {P : Program}
    (hext_blk : ∀ off : Nat, off < 436 →
      P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (cwPC0.rebase cwPl0.base (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, SameCpuState sm sm' → coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
          ProofLib.NonSyscallPreserved s sm → sm.sigActions = s.sigActions →
          sm.tpidrEl0 = s.tpidrEl0 → sm.oracle = s.oracle → sm.symtab = s.symtab →
          SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom := by
  let R_0 : Program := cwPC0.rebase cwPl0.base (fun _ => none)
  let keep := ProofLib.progKeep R_0
  have hR_eq : R_0 = (coreMultiLib.blockProgram coreFmtMpl 0).rebase (coreFmtMpl.base 0) (fun _ => none) := rfl
  have hL_R : R_0.CodeLoaded s.mem := by
    rw [hR_eq]; exact (hcl 0 (by decide)).of_base_code rfl rfl
  have hext_R : ∀ pc, R_0.externAt? pc = none := by
    intro pc; rw [hR_eq]; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_0.allInstrs (fun i => !i.isSvc0) = true := by
    rw [hR_eq]
    exact blockProgram_rebase_allInstrs_not_isSvc0 coreMultiLib coreFmtMpl 0 cwNoSvc0_0
  have hcode_R : R_0.code = cwProg0.code := by
    have hpw : ∀ off, cwLib0.text.patchedWord cwPl0 off =
        cwLib0.text.patchedWord { base := 0#64, ρ := fun _ => 0#64 } off := by
      intro off
      have hr : cwLib0.text.relocAt? off = none := by
        have hnil : cwLib0.text.relocs = [] := by rfl_kernel
        simp [Obj.CodeBlock.relocAt?, hnil]
      simp [Obj.CodeBlock.patchedWord, hr]
    change cwLib0.text.patched cwPl0 = cwProg0.code
    calc cwLib0.text.patched cwPl0
        = cwLib0.text.patched { base := 0#64, ρ := fun _ => 0#64 } := by
          simp [Obj.CodeBlock.patched, hpw]
      _ = cwProg0.code := by rfl_kernel
  have hall_msr : R_0.allInstrs (fun i => !i.isMsrTpidrEl0) = true := by
    have h0 := cwNoMsr_0
    unfold Program.allInstrs Program.allWords at h0 ⊢
    rwa [hcode_R]
  have hall_gpr : R_0.allInstrs cwIsGprOrBranch = true := by
    have h0 := cwGpr_0
    unfold Program.allInstrs Program.allWords at h0 ⊢
    rwa [hcode_R]
  have hlen_R : R_0.code.length = 436 := by
    have hc : R_0.code = cwLib0.text.patched cwPl0 := rfl
    rw [hc, Obj.CodeBlock.length_patched, length_text_of_tree cw0_code_eq cw0_tree_size]
  have hext_R_blk : ∀ off : Nat, off < R_0.code.length →
      P.externAt? (R_0.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]
    exact hext_blk
  intro R hm hL_P
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuState (ProofLib.stripS keep s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_cw hL_R)
  rcases hout' with ⟨_hpc_m', hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp, hsig, htp, horc⟩ :=
      steps_rebase_lift_cw hext_R_blk hext_R hall hall_msr hall_gpr hsteps' hrun_m' s rfl hL_R
    have hcl_m : coreMultiLib.CodeLoaded coreFmtMpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont :=
      hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hnsp hsig htp horc hsteps_P.symtab_eq
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm (hsteps_P.codeLoaded hL_P)
    exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

theorem sepWPp_seq_coreFmt_cl [CoreFmtWritePl] {P : Program}
    {mid_pc ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (h1 : SepWPp P mid_pc s Pre
      (fun sm Pm => coreMultiLib.CodeLoaded coreFmtMpl sm.mem → SepWPp P ret sm Pm Q Qp oom)
      Qp oom) :
    SepWPp P ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨_hpcm, _hrunm, Pm, hmm, hcont⟩ | hpan | hoom
  · have hcl_m : coreMultiLib.CodeLoaded coreFmtMpl sm.mem :=
      fun k hk => hsteps1.codeLoaded (hcl k hk)
    obtain ⟨sf, hsteps2, hout2⟩ := hcont hcl_m R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inr hoom)⟩

/-- `SepWPp` subroutine call rule threading `coreMultiLib.CodeLoaded coreFmtMpl` across the
callback. -/
theorem call_wpp_coreFmt [CoreFmtWritePl] {α : Type} {P : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α}
    {x : α} {s : State} {Pre F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok P entry spec)
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      coreMultiLib.CodeLoaded coreFmtMpl sf.mem →
      SepWPp P ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R')) :
    SepWPp P ret s Pre Q Qp oom := by
  refine sepWPp_seq_coreFmt_cl (mid_pc := ret_pc) hcl ?_
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic ?_ hoom
  intro sf hpcf hrunf hspf hcsf
  exact SepWPp.done hpcf hrunf (fun hcl_sf => hnext sf hpcf hrunf hspf hcsf hcl_sf)

/-- Callee-saved GPRs spilled on `core::fmt::write`'s `0x70`-byte frame (`x19..x26`, `fp`, `lr`). -/
def cwSavedSlots (sp0 : BitVec 64) (s0 : State) (ret_pc : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem memRegion24_eq_exists_triple64 (f : BitVec 64) :
    memRegion f 24 =
      ∃∗ w0, ∃∗ w1, ∃∗ w2,
        ((f ↦₆₄ w0) ∗ ((f + 8#64) ↦₆₄ w1) ∗ ((f + 16#64) ↦₆₄ w2)) := by
  have h := memRegion_cells f 3 (by decide)
  simp only [Nat.reduceMul, ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at h
  have hf2 : f + 8#64 + 8#64 = f + 16#64 := by bv_omega
  rw [hf2] at h
  exact h

theorem triple64_entails_memRegion24 (f w0 w1 w2 : BitVec 64) :
    ((f ↦₆₄ w0) ∗ ((f + 8#64) ↦₆₄ w1) ∗ ((f + 16#64) ↦₆₄ w2)) ⊢ memRegion f 24 := by
  rw [memRegion24_eq_exists_triple64 f]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

theorem cwFrame_fold (sp0 pad : BitVec 64) (s0 : State) (ret_pc : BitVec 64) :
    (((sp0 - 112#64) ↦₆₄ pad) ∗ memRegion (sp0 - 104#64) 24 ∗ cwSavedSlots sp0 s0 ret_pc) ⊢
      stackFrameAt sp0 0x70 := by
  rw [memRegion24_eq_exists_triple64 (sp0 - 104#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  have ha1 : sp0 - 104#64 + 8#64 = sp0 - 96#64 := by bv_omega
  have ha2 : sp0 - 104#64 + 16#64 = sp0 - 88#64 := by bv_omega
  rw [ha1, ha2]
  dsimp only [cwSavedSlots]
  simp only [sepConj_assoc]
  rw [← stackAt_eq_stackFrameAt sp0 0x70, stackAt_eq_cells sp0 14]
  simp only [Nat.reduceMul]
  iterate 13 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
  rw [ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right _ (Entails.refl _)

end VerifiedLibraries.RustStd
