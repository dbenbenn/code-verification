/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Placed.Multi
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess

/-!
# Intermediate Contracts and Program-Lifting Combinators for `libcrux_sha2::hacl` and `libcrux_hmac`

1. `HaclInProg P mpl`: placement-generic containment of `libcruxHmacLib` inside any ambient
   `P : Program` (independent of external hooks or other code outside the 7 blocks).
2. `withHaclPreserved`, `subroutine_ok_of_pure_block`, `sepWP_block_seg`, `sepWPp_block_seg`,
   `sepWP_block_bl`, `sepWPp_block_bl`, and `sepWPp_block_bl_panic`: lift straight-line/loop
   `SepWP (libcruxHmacLib.blockProgram mpl i)` segments and `BL` calls into `SepWP P` /
   `SepWPp P`, threading `ProcessFieldsPreserved` (`VmPreserved` + `KeepsFrozen`) and
   `libcruxHmacLib.CodeLoaded mpl`.
3. Intermediate subroutine contracts (`sha256InitRawSpec`, `sha256UpdateRawSpec`,
   `sha256UpdateNblocksSpec`, `sha256UpdateLastSpec`, `sha256FinishRawSpec`, `hash256Spec`) and
   the `HaclSubroutines P mpl` bundle.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV sha256With toBEBytes chunks64)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (strip_codeLoaded_prog steps_lift_placed_process)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib hacl_blockProgram_noSvc hacl_blockProgram_noMsrTpidrEl0)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure (haclUpdateLastState)

/-! ## 1. Ambient Program Containment & Patched Block Lengths -/

/-- Containment of `libcruxHmacLib` at `mpl` inside an arbitrary ambient `P : Program`: `mpl` is
`Placeable`, `P.svc = Syscall.standard`, and none of `P`'s extern hooks lie inside the 7 blocks of
`libcruxHmacLib`. -/
structure HaclInProg (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  placeable : libcruxHmacLib.Placeable mpl
  svc_eq    : P.svc = Syscall.standard
  noHooks   : ∀ i : Nat, (hi : i < libcruxHmacLib.blocks.length) → ∀ off : Nat,
    off < (libcruxHmacLib.blocks[i]).code.length →
    P.externAt? (mpl.base i + BitVec.ofNat 64 off) = none

theorem haclBlockProgram_code_length {mpl : Obj.MultiPlacement}
    (hpl : libcruxHmacLib.Placeable mpl) {i : Nat} (hi : i < 7) :
    (libcruxHmacLib.blockProgram mpl i).code.length = (libcruxHmacLib.blocks[i]'hi).code.length := by
  have hi' : i < libcruxHmacLib.blocks.length := hi
  have hblk := libcruxHmacLib.placeable_blockLib hi' hpl
  have hc : (libcruxHmacLib.blockProgram mpl i).code =
      (libcruxHmacLib.blockLib i).text.patched (libcruxHmacLib.blockPlacement mpl i) := rfl
  rw [hc, Obj.CodeBlock.length_patched_of_aligned (libcruxHmacLib.blockPlacement mpl i)
      hblk.text.len_aligned, libcruxHmacLib.blockLib_text hi']
  rfl

theorem codeLoaded_of_steps {P : Program} {mpl : Obj.MultiPlacement} {s1 s2 : State}
    (hcl : libcruxHmacLib.CodeLoaded mpl s1.mem) (hsteps : Steps P s1 s2) :
    libcruxHmacLib.CodeLoaded mpl s2.mem :=
  hcl.of_keepsFrozen hsteps.keepsFrozen

theorem execInst_bl_eq (imm : BitVec 64) (s : State) :
    execInst (.bl imm) s = (s.writeReg64 Reg.lr (s.pc + 4#64)).setPC (s.pc + imm) :=
  rfl

/-! ## 2. `withHaclPreserved` & Whole-Subroutine Pure-Block Lifting -/

/-- Adjoin `⌜libcruxHmacLib.CodeLoaded mpl s0.mem⌝` to `spec.pre` and
`⌜ProcessFieldsPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded mpl sf.mem⌝` to `spec.post`. -/
@[expose] def withHaclPreserved {α : Type} (mpl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => ⌜libcruxHmacLib.CodeLoaded mpl s0.mem⌝ ∗ spec.pre x s0
    post := fun x s0 sf =>
      ⌜ProcessFieldsPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded mpl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Lift a hook-free pure block `subroutine_ok (libcruxHmacLib.blockProgram mpl i) (mpl.base i) spec`
(with `onPanic = onExit = onOom = ⌜False⌝` and `setMem`-invariant `pre`/`post`) to any ambient
`P : Program` satisfying `HaclInProg P mpl`. -/
theorem subroutine_ok_of_pure_block {α : Type} {P : Program} {mpl : Obj.MultiPlacement}
    {i : Nat} (hi : i < 7) (hP : HaclInProg P mpl) {spec : Spec α}
    (hpre_mem : ∀ x (s : State) (m : Memory), spec.pre x (s.setMem m) = spec.pre x s)
    (hpost_mem : ∀ x (s1 s2 : State) (m1 m2 : Memory),
      spec.post x (s1.setMem m1) (s2.setMem m2) = spec.post x s1 s2)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hexit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝)
    (hsub : subroutine_ok (libcruxHmacLib.blockProgram mpl i) (mpl.base i) spec) :
    subroutine_ok P (mpl.base i) (withHaclPreserved mpl spec) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _
  dsimp only [withHaclPreserved] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre_raw⟩ := hpre
  let R₀ := libcruxHmacLib.blockProgram mpl i
  have hL0 : R₀.CodeLoaded s0.mem := hcl i hi
  let kp₀ := progKeep R₀
  let s0' := stripS kp₀ s0
  obtain ⟨R_view, hpre_view, hunstrip⟩ := strip_frame kp₀ hpre_raw
  have hpre' : s0'.mem ⊨ spec.pre x s0' ∗ R_view := by
    dsimp [s0', stripS]; rw [hpre_mem, State.mem_setMem]; exact hpre_view
  obtain ⟨sf', hsteps', hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hsub x R_view s0'
      (by cases s0; exact hpc) (by cases s0; exact hrun) hpre' (by cases s0; exact hsp))
    (by change R₀.CodeLoaded (stripExecOutside kp₀ s0.mem); exact strip_codeLoaded_prog hL0)
  have hlen_R : R₀.code.length = (libcruxHmacLib.blocks[i]'hi).code.length :=
    haclBlockProgram_code_length hP.placeable hi
  have hext_blk : ∀ off : Nat, off < R₀.code.length →
      P.externAt? (R₀.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]; exact hP.noHooks i hi
  have hext_R : ∀ pc, R₀.externAt? pc = none :=
    fun pc => Obj.MultiPlacedLib.externAt?_blockProgram_none libcruxHmacLib mpl i pc
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hstepsP, hsf_eq, hpf⟩ :=
      steps_lift_placed_process hext_blk hext_R (hacl_blockProgram_noSvc mpl hi)
        (hacl_blockProgram_noMsrTpidrEl0 mpl hi) hsteps' hret'.2.2 s0 rfl hL0
    refine ⟨sf, hstepsP, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      exact ⟨by rw [hsf_eq] at hr_pc; cases sf; cases s0; exact hr_pc,
             by rw [hsf_eq] at hr_sp; cases sf; cases s0; exact hr_sp,
             by rw [hsf_eq] at hr_st; cases sf; exact hr_st⟩
    · rw [hsf_eq] at hcc'
      exact ⟨by cases sf; cases s0; exact hcc'.1, by cases s0; cases sf; exact hcc'.2⟩
    · rw [hsf_eq] at hpost'
      dsimp [s0', stripS] at hpost'
      rw [hpost_mem, State.mem_setMem] at hpost'
      have hpost'' := hunstrip hpf.2.2.2.2.2.2.2 hpost'
      dsimp only [withHaclPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpf, codeLoaded_of_steps hcl hstepsP⟩, hpost''⟩
  · rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [hexit] at he; exact False.elim (not_satisfies_false_sepConj he)
  · rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-! ## 3. Pure-Segment & Single-Instruction `BL` Combinators for `SepWP P` and `SepWPp P` -/

/-- Lift a straight-line or loop `SepWP (libcruxHmacLib.blockProgram mpl i) mid` segment into
`SepWP P target`, preserving an arbitrary `Frame : SepProp` (such as `A.pool lim st s`) and
handing `ProcessFieldsPreserved s sm` + `libcruxHmacLib.CodeLoaded mpl sm.mem` to the continuation. -/
theorem sepWP_block_seg {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {mid target : BitVec 64} {s : State}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem)
    {Pre Frame : SepProp} {Post : State → SepProp} {PurePost : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hPost_mem : ∀ (sm : State) (m : Memory), Post (sm.setMem m) = Post sm)
    (hPure_mem : ∀ (sm : State) (m : Memory), PurePost (sm.setMem m) ↔ PurePost sm)
    (hseg : ∀ m : Memory,
      SepWP (libcruxHmacLib.blockProgram mpl i) mid (s.setMem m) Pre
        (fun sm' Pm' => PurePost sm' ∧ (Pm' ⊢ Post sm')) (fun _ => ⌜False⌝))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      ProcessFieldsPreserved s sm → libcruxHmacLib.CodeLoaded mpl sm.mem → PurePost sm →
      SepWP P target sm (Post sm ∗ Frame) post oom) :
    SepWP P target s (Pre ∗ Frame) post oom := by
  unfold SepWP reaches_pc
  intro R hm hLP
  let R₀ := libcruxHmacLib.blockProgram mpl i
  have hL0 : R₀.CodeLoaded s.mem := hcl i hi
  let kp₀ := progKeep R₀
  have hm_assoc : s.mem ⊨ Pre ∗ (Frame ∗ R) := by rwa [← sepConj_assoc]
  obtain ⟨R_view, hpre_view, hunstrip⟩ := strip_frame kp₀ hm_assoc
  have hstrip_eq : stripS kp₀ s = s.setMem (stripExecOutside kp₀ s.mem) := by cases s; rfl
  have hseg' := hseg (stripExecOutside kp₀ s.mem)
  obtain ⟨sm', hsteps', hout'⟩ :=
    hseg'.elim (by rw [State.mem_setMem]; exact hpre_view)
      (by rw [State.mem_setMem]; exact strip_codeLoaded_prog hL0)
  rcases hout' with ⟨hpc', hrun', Pm', hmm', hpure', hent'⟩ | ⟨_, hoom'⟩
  · have hlen_R : R₀.code.length = (libcruxHmacLib.blocks[i]'hi).code.length :=
      haclBlockProgram_code_length hP.placeable hi
    have hext_blk : ∀ off : Nat, off < R₀.code.length →
        P.externAt? (R₀.base + BitVec.ofNat 64 off) = none := by
      rw [hlen_R]; exact hP.noHooks i hi
    have hext_R : ∀ pc, R₀.externAt? pc = none :=
      fun pc => Obj.MultiPlacedLib.externAt?_blockProgram_none libcruxHmacLib mpl i pc
    obtain ⟨sm, hstepsP, hsm_eq, hpf⟩ :=
      steps_lift_placed_process hext_blk hext_R (hacl_blockProgram_noSvc mpl hi)
        (hacl_blockProgram_noMsrTpidrEl0 mpl hi) hsteps' hrun' s hstrip_eq.symm hL0
    have hpost_view : sm'.mem ⊨ Post sm' ∗ R_view :=
      Satisfies.of_entails hmm' (sepConj_mono_left hent')
    rw [hsm_eq] at hpost_view hpure' hpc' hrun'
    have hsm_strip : stripS kp₀ sm = sm.setMem (stripExecOutside kp₀ sm.mem) := by
      cases sm; rfl
    rw [hsm_strip, hPost_mem, State.mem_setMem] at hpost_view
    rw [hsm_strip, hPure_mem] at hpure'
    have hsm_mem : sm.mem ⊨ (Post sm ∗ Frame) ∗ R := by
      rw [sepConj_assoc]
      exact hunstrip hpf.2.2.2.2.2.2.2 hpost_view
    have hpc_sm : sm.pc = mid := by cases sm; exact hpc'
    have hrun_sm : sm.status = .Running := by cases sm; exact hrun'
    have hcl_sm := codeLoaded_of_steps hcl hstepsP
    obtain ⟨sf, hsteps2, hout2⟩ :=
      (hcont sm hpc_sm hrun_sm hpf hcl_sm hpure').elim hsm_mem (hstepsP.codeLoaded hLP)
    exact ⟨sf, hstepsP.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom')

/-- `SepWPp` counterpart of `sepWP_block_seg`. -/
theorem sepWPp_block_seg {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {mid ret : BitVec 64} {s : State}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem)
    {Pre Frame : SepProp} {Post : State → SepProp} {PurePost : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hPost_mem : ∀ (sm : State) (m : Memory), Post (sm.setMem m) = Post sm)
    (hPure_mem : ∀ (sm : State) (m : Memory), PurePost (sm.setMem m) ↔ PurePost sm)
    (hseg : ∀ m : Memory,
      SepWP (libcruxHmacLib.blockProgram mpl i) mid (s.setMem m) Pre
        (fun sm' Pm' => PurePost sm' ∧ (Pm' ⊢ Post sm')) (fun _ => ⌜False⌝))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      ProcessFieldsPreserved s sm → libcruxHmacLib.CodeLoaded mpl sm.mem → PurePost sm →
      SepWPp P ret sm (Post sm ∗ Frame) Q Qp oom) :
    SepWPp P ret s (Pre ∗ Frame) Q Qp oom := by
  intro R hm hLP
  have hwp : SepWP P mid s (Pre ∗ Frame)
      (fun sm Pm => sm.pc = mid ∧ sm.status = .Running ∧
        ProcessFieldsPreserved s sm ∧ libcruxHmacLib.CodeLoaded mpl sm.mem ∧
        PurePost sm ∧ Pm = (Post sm ∗ Frame)) (fun _ => ⌜False⌝) :=
    sepWP_block_seg hi hP hcl hPost_mem hPure_mem hseg
      (fun sm hpc hrun hpf hcl' hpure =>
        SepWP.done hpc hrun ⟨hpc, hrun, hpf, hcl', hpure, rfl⟩)
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hmm, hpc, hrun, hpf, hcl', hpure, rfl⟩ | ⟨_, hoom1⟩⟩ :=
    hwp.elim hm hLP
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont sm hpc hrun hpf hcl' hpure R hmm (hsteps1.codeLoaded hLP)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom1)

/-- Fetch agreement at any instruction offset `off` inside block `i` of `libcruxHmacLib`. -/
theorem hacl_fetchMem_eq {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {m : Memory} (hcl : libcruxHmacLib.CodeLoaded mpl m)
    {off : Nat} (hoff : off < (libcruxHmacLib.blocks[i]'hi).code.length)
    {pc : BitVec 64} (hpc : pc = mpl.base i + BitVec.ofNat 64 off)
    {inst : Instr} (hf : (libcruxHmacLib.blockProgram mpl i).fetch pc = some inst) :
    P.fetchMem m pc = some inst := by
  have hfm : (libcruxHmacLib.blockProgram mpl i).fetchMem m pc = some inst :=
    Program.fetchMem_of_fetch (hcl i hi) hf
  unfold Program.fetchMem at hfm ⊢
  rw [Obj.MultiPlacedLib.externAt?_blockProgram_none] at hfm
  rw [hpc, hP.noHooks i hi off hoff]
  rw [← hpc]
  exact hfm

private theorem step_exec_bl {P : Program} {s : State} {imm : BitVec 64}
    (hrun : s.status = .Running) (hfe : P.fetchMem s.mem s.pc = some (.bl imm)) :
    Step P s (execInst (.bl imm) s) := by
  have hs := Step.exec (prog := P) hrun hfe
  rwa [evalInst_eq_execInst_of_not_isSvc0 (by rfl)] at hs

private theorem bl_pc {s : State} {imm calleeAddr : BitVec 64} (htgt : s.pc + imm = calleeAddr) :
    (execInst (.bl imm) s).pc = calleeAddr := by
  rw [execInst_bl_eq, State.pc_setPC, htgt]

private theorem bl_status {s : State} {imm : BitVec 64} (hrun : s.status = .Running) :
    (execInst (.bl imm) s).status = .Running := by
  rw [execInst_bl_eq]; cases s; exact hrun

private theorem bl_spAligned {s : State} {imm : BitVec 64} (hsp : s.spAligned = true) :
    (execInst (.bl imm) s).spAligned = true := by
  rw [execInst_bl_eq]; cases s; exact hsp

private theorem bl_lr (s : State) (imm : BitVec 64) :
    (execInst (.bl imm) s).readReg64 Reg.lr = s.pc + 4#64 := by
  change (s.writeReg64 Reg.lr (s.pc + 4#64)).readReg64 Reg.lr = s.pc + 4#64
  exact State.readReg64_writeReg64_same s Reg.lr (s.pc + 4#64) (by decide) (by decide)

private theorem bl_mem (s : State) (imm : BitVec 64) :
    (execInst (.bl imm) s).mem = s.mem := by
  rw [execInst_bl_eq]; cases s; rfl

private theorem bl_sp (s : State) (imm : BitVec 64) :
    (execInst (.bl imm) s).sp = s.sp := by
  rw [execInst_bl_eq]; cases s; rfl

/-- Step a `BL imm` instruction at offset `off` of block `i` in `SepWP P` and invoke
`SepWP.call_subroutine_frame` on `hcall : subroutine_ok P calleeAddr spec`. -/
theorem sepWP_block_bl {α : Type} {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {off : Nat} (hoff : off < (libcruxHmacLib.blocks[i]'hi).code.length)
    {calleeAddr target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok P calleeAddr spec)
    {x : α} {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = mpl.base i + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    {imm : BitVec 64}
    (hf : (libcruxHmacLib.blockProgram mpl i).fetch s.pc = some (.bl imm))
    (htgt : s.pc + imm = calleeAddr)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ spec.pre x (execInst (.bl imm) s) ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked →
      ¬(sf.mem ⊨ spec.onPanic x (execInst (.bl imm) s) sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code (execInst (.bl imm) s) sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = s.pc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved (execInst (.bl imm) s) sf →
      libcruxHmacLib.CodeLoaded mpl sf.mem →
      SepWP P target_pc sf (spec.post x (execInst (.bl imm) s) sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x (execInst (.bl imm) s) sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  unfold SepWP reaches_pc
  intro R hm hLP
  have hfe := hacl_fetchMem_eq hi hP hcl hoff hpc hf
  have hstep1 := step_exec_bl hrun hfe
  let sc := execInst (.bl imm) s
  obtain ⟨sm, hsteps_call, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hcall x (F ∗ R) sc
      (bl_pc htgt)
      (bl_status hrun)
      (by rw [bl_mem]; exact hpre R hm)
      (bl_spAligned hsp_align))
    (hstep1.codeLoaded hLP)
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostM⟩ | ⟨hpan, hpanM⟩ |
      ⟨code, hex, hexM⟩ | ⟨hoom_st, hoomM⟩
  · rw [← sepConj_assoc] at hpostM
    have hpcm' : sm.pc = s.pc + 4#64 := by rwa [bl_lr s imm] at hpcm
    have hspm' : sm.sp = s.sp := by rwa [bl_sp s imm] at hspm
    have hcl_sm := codeLoaded_of_steps hcl (Steps.step hstep1 hsteps_call)
    obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
      (hnext sm hpcm' hrunm hspm' hcsm hcl_sm).elim hpostM
        (hsteps_call.codeLoaded (hstep1.codeLoaded hLP))
    exact ⟨sf, Steps.step hstep1 (hsteps_call.trans hsteps_rest), hout_rest⟩
  · exact False.elim (h_no_panic (F ∗ R) sm hpan hpanM)
  · exact False.elim (h_no_exit (F ∗ R) code sm hex hexM)
  · exact ⟨sm, Steps.step hstep1 hsteps_call, Or.inr ⟨hoom_st, h_oom R sm hoom_st hoomM⟩⟩

/-- Panic-aware `SepWPp P` counterpart of `sepWP_block_bl`: steps a `BL imm` instruction at offset
`off` of block `i` and calls `subroutine_ok P calleeAddr spec` (allowing normal return, panic, or OOM). -/
theorem sepWPp_block_bl {α : Type} {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {off : Nat} (hoff : off < (libcruxHmacLib.blocks[i]'hi).code.length)
    {calleeAddr ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok P calleeAddr spec)
    {x : α} {s : State} {Pre F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = mpl.base i + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    {imm : BitVec 64}
    (hf : (libcruxHmacLib.blockProgram mpl i).fetch s.pc = some (.bl imm))
    (htgt : s.pc + imm = calleeAddr)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ spec.pre x (execInst (.bl imm) s) ∗ (F ∗ R)))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code (execInst (.bl imm) s) sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = s.pc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved (execInst (.bl imm) s) sf →
      libcruxHmacLib.CodeLoaded mpl sf.mem →
      SepWPp P ret_pc sf (spec.post x (execInst (.bl imm) s) sf ∗ F) Q Qp oom)
    (h_panic : ∀ R' sf, sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x (execInst (.bl imm) s) sf ∗ (F ∗ R')) →
      ∃ Pp, (sf.mem ⊨ Pp ∗ R') ∧ Qp sf Pp)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x (execInst (.bl imm) s) sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R')) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  intro R hm hLP
  have hfe := hacl_fetchMem_eq hi hP hcl hoff hpc hf
  have hstep1 := step_exec_bl hrun hfe
  let sc := execInst (.bl imm) s
  obtain ⟨sm, hsteps_call, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hcall x (F ∗ R) sc
      (bl_pc htgt)
      (bl_status hrun)
      (by rw [bl_mem]; exact hpre R hm)
      (bl_spAligned hsp_align))
    (hstep1.codeLoaded hLP)
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostM⟩ | ⟨hpan, hpanM⟩ |
      ⟨code, hex, hexM⟩ | ⟨hoom_st, hoomM⟩
  · rw [← sepConj_assoc] at hpostM
    have hpcm' : sm.pc = s.pc + 4#64 := by
      rwa [bl_lr s imm] at hpcm
    have hspm' : sm.sp = s.sp := by
      rwa [bl_sp s imm] at hspm
    have hcl_sm := codeLoaded_of_steps hcl (Steps.step hstep1 hsteps_call)
    obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
      hnext sm hpcm' hrunm hspm' hcsm hcl_sm R hpostM
        (hsteps_call.codeLoaded (hstep1.codeLoaded hLP))
    exact ⟨sf, Steps.step hstep1 (hsteps_call.trans hsteps_rest), hout_rest⟩
  · obtain ⟨Pp, hPp, hQp⟩ := h_panic R sm hpan hpanM
    exact ⟨sm, Steps.step hstep1 hsteps_call, Or.inr (Or.inl ⟨hpan, Pp, hPp, hQp⟩)⟩
  · exact False.elim (h_no_exit (F ∗ R) code sm hex hexM)
  · exact ⟨sm, Steps.step hstep1 hsteps_call, Or.inr (Or.inr ⟨hoom_st, h_oom R sm hoom_st hoomM⟩)⟩

/-- Direct `BL` to a `P.externAt? calleeAddr = some Rust.panicked` stub (such as `unwrap_failed`). -/
theorem sepWPp_block_bl_panic {P : Program} {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 7)
    (hP : HaclInProg P mpl) {off : Nat} (hoff : off < (libcruxHmacLib.blocks[i]'hi).code.length)
    {calleeAddr ret_pc : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = mpl.base i + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    {imm : BitVec 64}
    (hf : (libcruxHmacLib.blockProgram mpl i).fetch s.pc = some (.bl imm))
    (htgt : s.pc + imm = calleeAddr)
    (hext : P.externAt? calleeAddr = some Rust.panicked)
    (hqp : Qp (Rust.panicked (execInst (.bl imm) s)) Pre) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  intro R hm _
  have hfe := hacl_fetchMem_eq hi hP hcl hoff hpc hf
  have hstep1 := step_exec_bl hrun hfe
  let sc := execInst (.bl imm) s
  have hext_sc : P.externAt? sc.pc = some Rust.panicked := by
    change P.externAt? (execInst (.bl imm) s).pc = some Rust.panicked
    rwa [bl_pc htgt]
  have hstep2 : Step P sc (Rust.panicked sc) :=
    Step.extern (bl_status hrun) hext_sc (Memory.KeepsFrozen.refl _) rfl
  exact ⟨Rust.panicked sc, Steps.step hstep1 (Steps.step hstep2 (Steps.refl _)),
    Or.inr (Or.inl ⟨rfl, Pre, hm, hqp⟩)⟩

/-! ## 4. Intermediate `libcrux_sha2::hacl` Contracts (Blocks `0..5`) -/

/-- Block 0: `libcrux_sha2::hacl::sha256_init` (`x0 = stA`, `8 ≤ x1.toNat`, `16`-B stack). -/
@[expose] def sha256InitRawSpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (stA, old) s =>
    ⌜s.readReg64 .x0 = stA ∧ 8 ≤ (s.readReg64 .x1).toNat ∧ old.length = 32⌝ ∗
    (stA ↦ₛ old) ∗ stackFrame s 16
  post := fun (stA, _) s0 _ =>
    (stA ↦ₛ shaStateBytes sha256IV) ∗ stackFrame s0 16

/-- Block 1: `libcrux_sha2::hacl::sha256_update` (`x0 = blkA`, `64 ≤ x1.toNat`, `x2 = stA`,
`8 ≤ x3.toNat`, `160`-B stack; updates `st` to `sha256CompressState st (bs.take 64)`). -/
@[expose] def sha256UpdateRawSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × ShaState) where
  pre := fun (blkA, bs, stA, st) s =>
    ⌜s.readReg64 .x0 = blkA ∧ (s.readReg64 .x1).toNat = bs.length ∧ 64 ≤ bs.length ∧
      s.readReg64 .x2 = stA ∧ 8 ≤ (s.readReg64 .x3).toNat⌝ ∗
    (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s 160
  post := fun (blkA, bs, stA, st) s0 _ =>
    (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes (sha256CompressState st (bs.take 64))) ∗
      stackFrame s0 160

/-- Block 2: `libcrux_sha2::hacl::sha256_update_nblocks` (`w0 = len < 2^32`, `x1 = blkA`,
`x2 = bs.length`, `len ≤ bs.length`, `bs.length + 64 < 2^64`, `x3 = stA`, `8 ≤ x4.toNat`,
`224`-B stack = `64` local + `160` `sha256_update`). Covers both `len < 64` (including `len = 0,
bs = []`) and `len ≥ 64`. -/
@[expose] def sha256UpdateNblocksSpec (mpl : Obj.MultiPlacement) :
    Spec (Nat × BitVec 64 × List (BitVec 8) × BitVec 64 × ShaState) where
  pre := fun (len, blkA, bs, stA, st) s =>
    ⌜libcruxHmacLib.CodeLoaded mpl s.mem ∧
      len < 2 ^ 32 ∧ (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 len ∧
      s.readReg64 .x1 = blkA ∧ (s.readReg64 .x2).toNat = bs.length ∧
      len ≤ bs.length ∧ bs.length + 64 < 2 ^ 64 ∧
      s.readReg64 .x3 = stA ∧ 8 ≤ (s.readReg64 .x4).toNat⌝ ∗
    (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s 224
  post := fun (len, blkA, bs, stA, st) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded mpl sf.mem⌝ ∗
    (blkA ↦ₛ bs) ∗
    (stA ↦ₛ shaStateBytes ((chunks64 (bs.take (64 * (len / 64)))).foldl sha256CompressState st)) ∗
    stackFrame s0 224

/-- Block 3: `libcrux_sha2::hacl::sha256_update_last` (`x0 = totlen`, `w1 = remLen ≤ 64`,
`x2 = remA`, `x3 = slice.length` with `remLen ≤ slice.length`, `x4 = stA`, `8 ≤ x5.toNat`,
`352`-B stack = `192` local + `160` `sha256_update`). Note `memcpy` preserves `VmPreserved`
(`LibsignalBinary.Heap.VmPreserved s0 sf` + `KeepsFrozen`). -/
@[expose] def sha256UpdateLastSpec (mpl : Obj.MultiPlacement) :
    Spec (Nat × Nat × BitVec 64 × List (BitVec 8) × BitVec 64 × ShaState) where
  pre := fun (totlen, remLen, remA, slice, stA, st) s =>
    ⌜libcruxHmacLib.CodeLoaded mpl s.mem ∧
      (s.readReg64 .x0).toNat = totlen ∧
      remLen ≤ 64 ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 remLen ∧
      s.readReg64 .x2 = remA ∧ (s.readReg64 .x3).toNat = slice.length ∧ remLen ≤ slice.length ∧
      s.readReg64 .x4 = stA ∧ 8 ≤ (s.readReg64 .x5).toNat⌝ ∗
    (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s 352
  post := fun (totlen, remLen, remA, slice, stA, st) s0 sf =>
    ⌜LibsignalBinary.Heap.VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded mpl sf.mem⌝ ∗
    (remA ↦ₛ slice) ∗
    (stA ↦ₛ shaStateBytes (haclUpdateLastState sha256CompressState totlen (slice.take remLen) st)) ∗
    stackFrame s0 352

/-- Block 4: `libcrux_sha2::hacl::sha256_finish` (`x0 = stA`, `8 ≤ x1.toNat`, `x2 = dstA`,
`x3 = dst.length`, `32 ≤ dst.length`, `16`-B stack). -/
@[expose] def sha256FinishRawSpec : Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8)) where
  pre := fun (stA, st, dstA, dst) s =>
    ⌜s.readReg64 .x0 = stA ∧ 8 ≤ (s.readReg64 .x1).toNat ∧
      s.readReg64 .x2 = dstA ∧ (s.readReg64 .x3).toNat = dst.length ∧ 32 ≤ dst.length⌝ ∗
    (stA ↦ₛ shaStateBytes st) ∗ (dstA ↦ₛ dst) ∗ stackFrame s 16
  post := fun (stA, st, dstA, dst) s0 _ =>
    (stA ↦ₛ shaStateBytes st) ∗
    (dstA ↦ₛ (st.toList.flatMap (toBEBytes 4) ++ dst.drop 32)) ∗
    stackFrame s0 16

/-- Block 5: `libcrux_sha2::hacl::hash_256` (`x0 = dstA`, `x1 = dst.length ≥ 32`,
`x2 = msgA`, `x3 = msg.length < 2^32`, `w4 = msg.length`, `480`-B stack = `128` local + `352`
`sha256_update_last`). Produces `sha256With sha256CompressState msg`. -/
@[expose] def hash256Spec (mpl : Obj.MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (dstA, dst, msgA, msg) s =>
    ⌜libcruxHmacLib.CodeLoaded mpl s.mem ∧
      s.readReg64 .x0 = dstA ∧ (s.readReg64 .x1).toNat = dst.length ∧ 32 ≤ dst.length ∧
      s.readReg64 .x2 = msgA ∧ (s.readReg64 .x3).toNat = msg.length ∧
      msg.length < 2 ^ 32 ∧ (s.readReg64 .x4).setWidth 32 = BitVec.ofNat 32 msg.length⌝ ∗
    (dstA ↦ₛ dst) ∗ (msgA ↦ₛ msg) ∗ stackFrame s 480
  post := fun (dstA, dst, msgA, msg) s0 sf =>
    ⌜LibsignalBinary.Heap.VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded mpl sf.mem⌝ ∗
    (dstA ↦ₛ (sha256With sha256CompressState msg ++ dst.drop 32)) ∗
    (msgA ↦ₛ msg) ∗ stackFrame s0 480

/-- Bundle of verified `libcrux_sha2::hacl` subroutines (`0, 2, 3, 4, 5`) consumed by
`libcrux_hmac::hmac` (Block 6). -/
structure HaclSubroutines (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  init_ok          : subroutine_ok P (mpl.base 0) (withHaclPreserved mpl sha256InitRawSpec)
  updateNblocks_ok : subroutine_ok P (mpl.base 2) (sha256UpdateNblocksSpec mpl)
  updateLast_ok    : subroutine_ok P (mpl.base 3) (sha256UpdateLastSpec mpl)
  finish_ok        : subroutine_ok P (mpl.base 4) (withHaclPreserved mpl sha256FinishRawSpec)
  hash256_ok       : subroutine_ok P (mpl.base 5) (hash256Spec mpl)

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
