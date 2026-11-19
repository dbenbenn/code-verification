/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
public import ProofLib.GenPlacedFetches
public import VerifiedLibraries.RustStd.Proofs.StdoutRaw
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import ProofLib.ProgramReflection
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Prologue, Chunked `write(1, ...)` Loop, and Epilogue for `libsignal_cli_io::write_stdout`

Steps `signalSessionIoMultiLib` block `2` (`cliIoWriteStdoutSym`, `46` instructions = `184` B,
`64`-B stack frame + `32`-B `musl` `write` callee frame = `96` B total):
1. `cliIoWriteStdout_prologue` (`+0x000 .. +0x024`): saves `x19..x24, x29, x30` into the `64`-B
   frame and initializes `x19 = len`, `x20 = buf`, `x23 = 0`, `x24 = 0x7fff_f000`.
2. `cliIoWriteStdout_epilogue` (`+0x084 .. +0x098`): zero-extends `w21 = 0` into `x0 = 0#64`,
   restores `x19..x24, x29, x30` and `sp = s0.sp`, and returns to `s0.readReg64 .lr`.
3. `cliIoWriteStdout_loop` (`+0x024 .. +0x084`): inductive `0x7fff_f000`-chunk `write(1, ...)` loop
   handling both `rem = []` (`w21 = 0`, `b.ls +0x084`) and `0 < rem.length` (`bl write` via
   `muslWriteStdout32Spec`, non-zero `< 2 ^ 63` return, `b.ls +0x024` back-edge).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open Arm64.Obj (MultiPlacedLib MultiPlacement CodeBlock PlacedLib Placement)
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  stdoutBytesAt seqCodeLoadedWhere syscallPreserved_of_seg
)
open VerifiedLibraries.RustStd.Io (muslWriteStdout32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoBlocks_len cliIoWriteSym
  cliIoBlockNoSvc0_02
)

-- Local `@[expose]` block-2 (`signal_session_io::write_stdout`, `184` B / `46` insns) placement & fetches
@[expose] def cliIoLib02 : PlacedLib := signalSessionIoMultiLib.blockLib 2
@[expose] def cliIoPl02 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 2
theorem cliIoPlaceable02 [CliIoPlacement] : cliIoLib02.Placeable cliIoPl02 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
@[expose] def cliIoPC02 [CliIoPlacement] : Program := cliIoLib02.program cliIoPl02

def cliIoProg02 : Program := { code := cliIoLib02.text.code, symbols := cliIoLib02.text.symbols }
def cliIoTree02 : WordTree := word_tree_of% cliIoProg02
theorem cliIo02_code_eq : cliIoLib02.text.code = cliIoTree02.toBytes := by rfl_kernel
theorem cliIo02_tree_size : cliIoTree02.checkSize? = some 46 := by rfl_kernel
def cliIoSymChars02 : List (List Char × Nat) := sym_chars_of% cliIoProg02
theorem cliIo02_symbols_eq : cliIoLib02.text.symbols = toStringSymbols cliIoSymChars02 := by rfl_kernel
theorem cliIo02_symbols_fresh : allFreshCharSymbols cliIoSymChars02 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC02 cliIoLib02 cliIoTree02 cliIo02_code_eq cliIo02_tree_size
  via_placement cliIoPl02 cliIoPlaceable02 [0x0 → 0xb4]
gen_placed_fnOffs cliIoPC02 cliIoLib02 cliIoSymChars02 cliIo02_symbols_eq cliIo02_symbols_fresh
end

/-! ## 1. Block-`2` `CodeLoadedWhere` Pure-Segment Lifter -/

private theorem ws_strip_codeLoaded {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
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

private theorem ws_strip_execOnlyIn (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem ws_steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem ws_steps_rebase_lift_block {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := ws_steps_start_running hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        ws_strip_codeLoaded hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        ws_strip_execOnlyIn R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
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
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

/-- Lift a pure (non-syscall) segment of `signalSessionIoMultiLib` block `2` up to `mid` under
    `CodeLoadedWhere keep cliIoMpl` (`keep 2 = true`) and `CliIoBlockNoExtern cliIoMpl P 2`. -/
theorem sepWP_seg_cliIo_block2_pureWhere [CliIoPlacement] {keep : Nat → Bool}
    (hk2 : keep 2 = true) {P : Program}
    (hext2 : CliIoBlockNoExtern cliIoMpl P 2)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (cliIoPC02.rebase cliIoPl02.base (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' →
            signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl sm.mem →
            ProofLib.NonSyscallPreserved s sm →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_2 : Program := cliIoPC02.rebase cliIoPl02.base (fun _ => none)
  let kp := ProofLib.progKeep R_2
  have h2_lt : 2 < signalSessionIoMultiLib.blocks.length := by rw [cliIoBlocks_len]; decide
  have hR_eq : R_2 =
      (signalSessionIoMultiLib.blockProgram cliIoMpl 2).rebase (cliIoMpl.base 2) (fun _ => none) :=
    rfl
  have hL_R : R_2.CodeLoaded s.mem := (hcl 2 h2_lt hk2).of_base_code rfl rfl
  have hext_R : ∀ pc, R_2.externAt? pc = none := by
    intro pc; rw [hR_eq]; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_2.allInstrs (fun i => !i.isSvc0) = true := by
    rw [hR_eq]
    exact blockProgram_rebase_allInstrs_not_isSvc0 signalSessionIoMultiLib cliIoMpl 2
      cliIoBlockNoSvc0_02
  have hext_R_blk : ∀ off : Nat, off < R_2.code.length →
      P.externAt? (R_2.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    have hlen : R_2.code.length ≤ cliIoLib02.text.code.length := by
      have hc : R_2.code = cliIoLib02.text.patched cliIoPl02 := rfl
      rw [hc, CodeBlock.length_patched]
      exact Nat.mul_div_le _ 4
    exact hext2 off (Nat.lt_of_lt_of_le hoff hlen)
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame kp hm
  have hcpu_in : SameCpuState (ProofLib.stripS kp s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS kp s) hcpu_in) hm_strip
      (ws_strip_codeLoaded hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      ws_steps_rebase_lift_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl sm.mem :=
      hsteps_P.codeLoadedWhere hcl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside kp sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside kp sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hnsp
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-! ## 2. Frame Layout, Arithmetic Helpers, and Relocation Identity -/

/-- Saved callee-saved and return registers in `write_stdout`'s `64`-byte stack frame
    (`s0.sp - 64#64 .. s0.sp`). -/
@[expose] def cliIoWriteStdoutSaved (s0 : State) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp -  8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

/-- Upper GPRs (`x25..x28`) and callee-saved SIMD registers untouched by `write_stdout`. -/
@[expose] def WriteStdoutUpperSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem WriteStdoutUpperSaved.of_calleeSaved {s0 s1 s2 : State}
    (h01 : WriteStdoutUpperSaved s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    WriteStdoutUpperSaved s0 s2 := by
  rw [CalleeSavedPreserved.iff_regs] at hcs
  rcases hcs with ⟨_, _, _, _, _, _, hx25, hx26, hx27, hx28, _, hv⟩
  exact ⟨hx25.trans h01.1, hx26.trans h01.2.1, hx27.trans h01.2.2.1,
    hx28.trans h01.2.2.2.1, hv.trans h01.2.2.2.2⟩

theorem cliIoWriteStdout_write_pc [CliIoPlacement] :
    cliIoPl02.base + 72#64 + (cliIoPl02.ρ cliIoWriteSym - cliIoPl02.base - 72#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoWriteSym := by
  change cliIoPl02.base + 72#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl02.base - 72#64) = _
  bv_lin

private theorem stdoutBytesAt_take_drop_local (ro : Bool) (a : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hn : n ≤ bs.length) :
    stdoutBytesAt ro a bs =
      (stdoutBytesAt ro a (bs.take n) ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 n) (bs.drop n)) := by
  have happ : ∀ xs ys : List (BitVec 8),
      stdoutBytesAt ro a (xs ++ ys) =
        (stdoutBytesAt ro a xs ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 xs.length) ys) := by
    intro xs ys; cases ro
    · exact pointsToBytes_append a xs ys
    · exact pointsToBytesRO_append a xs ys
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [happ, List.length_take_of_le hn]

private theorem traceEvent_ofBytes_append_local (s : OutputStream) (a b : List (BitVec 8)) :
    TraceEvent.ofBytes s (a ++ b) = TraceEvent.ofBytes s a ++ TraceEvent.ofBytes s b := by
  unfold TraceEvent.ofBytes; exact List.map_append

private theorem bv64_sub_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
  rw [BitVec.ofNat_add]; bv_omega

private theorem bv64_csel_want {remLen : Nat} (hrem_lt : remLen < 2 ^ 63) :
    (if (BitVec.ofNat 64 remLen).ult 0x7ffff000#64 then
      BitVec.ofNat 64 remLen
     else 0x7ffff000#64) = BitVec.ofNat 64 (min remLen Arm64.MAX_RW_COUNT) := by
  have hmax : (0x7ffff000#64 : BitVec 64) = BitVec.ofNat 64 Arm64.MAX_RW_COUNT := rfl
  have htoNat : (BitVec.ofNat 64 remLen).toNat = remLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmax_nat : (0x7ffff000#64 : BitVec 64).toNat = Arm64.MAX_RW_COUNT := rfl
  by_cases hlt : remLen < Arm64.MAX_RW_COUNT
  · have hult : (BitVec.ofNat 64 remLen).ult 0x7ffff000#64 = true := by
      simp only [BitVec.ult, htoNat, hmax_nat, decide_eq_true_eq]
      exact hlt
    simp only [hult, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hlt)]
  · have hult : (BitVec.ofNat 64 remLen).ult 0x7ffff000#64 = false := by
      simp only [BitVec.ult, htoNat, hmax_nat, decide_eq_false_iff_not]
      exact hlt
    rw [hult]
    simp only [Bool.false_eq_true, ↓reduceIte,
      Nat.min_eq_right (Nat.le_of_not_lt hlt), hmax]

private theorem bv64_ult_add_false {w r : Nat} (h : w + r < 2 ^ 63) :
    (BitVec.ofNat 64 (w + r)).ult (BitVec.ofNat 64 w) = false := by
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show w + r < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]
  omega

private theorem bv64_ule_add_false {w r : Nat} (hpos : 0 < r) (h : w + r < 2 ^ 63) :
    (BitVec.ofNat 64 (w + r)).ule (BitVec.ofNat 64 w) = false := by
  simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show w + r < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]
  omega

private theorem bv64_ofNat_ne_zero {r : Nat} (hpos : 0 < r) (hlt : r < 2 ^ 63) :
    BitVec.ofNat 64 r ≠ 0#64 := by
  intro h0
  have hn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.zero_mod] at hn
  omega

private theorem bv64_getLsbD_63_false {r : Nat} (hlt : r < 2 ^ 63) :
    (BitVec.ofNat 64 r).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)]
  exact Nat.testBit_lt_two_pow hlt

/-! ## 3. Prologue (`+0x000 .. +0x024`), Epilogue (`+0x084 .. +0x098`), and Loop (`+0x024 .. +0x084`) -/

section
arm64_proof_prelude

/-- Prologue (`+0x000 .. +0x024`) of `libsignal_cli_io::write_stdout`. -/
theorem cliIoWriteStdout_prologue [CliIoPlacement] {keep : Nat → Bool}
    (hk2 : keep 2 = true) {P : Program}
    (hext2 : CliIoBlockNoExtern cliIoMpl P 2)
    {s0 : State} {buf : BitVec 64} {len : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl0 : signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl s0.mem)
    (hpc0 : s0.pc = cliIoPl02.base)
    (hrun0 : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = buf)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 len)
    (hcont : ∀ sm : State,
      signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl sm.mem →
      sm.pc = cliIoPl02.base + 36#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 64#64 →
      sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 len →
      sm.readReg64 (.gpr 20#5) = buf →
      sm.readReg64 (.gpr 23#5) = 0#64 →
      sm.readReg64 (.gpr 24#5) = 0x7ffff000#64 →
      WriteStdoutUpperSaved s0 sm →
      SyscallPreserved s0 sm →
      sm.fs = s0.fs →
      sm.trace = s0.trace →
      SepWP P (s0.readReg64 .lr) sm
        (stackAt (s0.sp - 64#64) 32 ∗ cliIoWriteStdoutSaved s0 ∗ F) post oomProp) :
    SepWP P (s0.readReg64 .lr) s0 (stackAt s0.sp 96 ∗ F) post oomProp := by
  wp_conv_pre =>
    rw [show stackAt s0.sp 96 = stackAt (s0.sp - 64#64) 32 ∗ cells (s0.sp - 64#64) 8 from
      stackAt_split_cells s0.sp 32 8 (by decide)]
  cells_unfold
  simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  apply sepWP_seg_cliIo_block2_pureWhere hk2 hext2 hcl0 (mid := cliIoPl02.base + 36#64)
  intro s' hcpu
  have hpc' : s'.pc = cliIoPl02.base := hcpu.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu.status_eq.trans hrun0
  have hsp_eq' : s'.sp = s0.sp := hcpu.sp_eq
  have hsp' : s'.spAligned = true := hcpu.spAligned.trans hsp0
  have hx0' : s'.readReg64 (.gpr 0#5) = buf := (hcpu.readReg64 .x0).trans hx0
  have hx1' : s'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 len := (hcpu.readReg64 .x1).trans hx1
  wp_conv_pre => simp only [← hsp_eq']
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_m hcl_m hnsp => ?_
  have hpres : SyscallPreserved s0 sm :=
    syscallPreserved_of_seg hcpu hcpu_m hnsp (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc_m : sm.pc = cliIoPl02.base + 36#64 := by rw [hcpu_m.pc_eq]; simp [arm64_norm]
  have hrun_m : sm.status = .Running :=
    hcpu_m.status_eq.trans (by simpa [arm64_norm] using hrun')
  have hsp_m : sm.sp = s0.sp - 64#64 := by
    rw [hcpu_m.sp_eq]; simp [arm64_norm]
  have hx19_m : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 len := by
    rw [hcpu_m.readReg64 (.gpr 19#5)]; simp [arm64_norm]
  have hx20_m : sm.readReg64 (.gpr 20#5) = buf := by
    rw [hcpu_m.readReg64 (.gpr 20#5)]; simp [arm64_norm]
  have hx23_m : sm.readReg64 (.gpr 23#5) = 0#64 := by
    rw [hcpu_m.readReg64 (.gpr 23#5)]; simp [arm64_norm]
  have hx24_m : sm.readReg64 (.gpr 24#5) = 0x7ffff000#64 := by
    rw [hcpu_m.readReg64 (.gpr 24#5)]; simp [arm64_norm]
  have hup_m : WriteStdoutUpperSaved s0 sm := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_m.readReg64 (.gpr 25#5)]; simp [arm64_norm]; exact hcpu.readReg64 (.gpr 25#5)
    · rw [hcpu_m.readReg64 (.gpr 26#5)]; simp [arm64_norm]; exact hcpu.readReg64 (.gpr 26#5)
    · rw [hcpu_m.readReg64 (.gpr 27#5)]; simp [arm64_norm]; exact hcpu.readReg64 (.gpr 27#5)
    · rw [hcpu_m.readReg64 (.gpr 28#5)]; simp [arm64_norm]; exact hcpu.readReg64 (.gpr 28#5)
    · rw [hcpu_m.calleeSavedVRegs]; simp only [arm64_norm]; exact hcpu.calleeSavedVRegs
  have hfs_m : sm.fs = s0.fs := hnsp.2.2.2.2.2.2
  have htr_m : sm.trace = s0.trace := hnsp.1
  refine SepWP.weaken_pre ?_
    (hcont sm hcl_m hpc_m hrun_m hsp_m hx19_m hx20_m hx23_m hx24_m hup_m hpres hfs_m htr_m)
  unfold cliIoWriteStdoutSaved
  simp only [hsp_eq',
    hcpu.readReg64 (.gpr 29#5), hcpu.readReg64 (.gpr 30#5),
    hcpu.readReg64 (.gpr 24#5), hcpu.readReg64 (.gpr 23#5),
    hcpu.readReg64 (.gpr 22#5), hcpu.readReg64 (.gpr 21#5),
    hcpu.readReg64 (.gpr 20#5), hcpu.readReg64 (.gpr 19#5)]
  sep_entail

/-- Epilogue (`+0x084 .. +0x098`) of `libsignal_cli_io::write_stdout` when `w21 = 0#32`. -/
theorem cliIoWriteStdout_epilogue [CliIoPlacement] {keep : Nat → Bool}
    (hk2 : keep 2 = true) {P : Program}
    (hext2 : CliIoBlockNoExtern cliIoMpl P 2)
    {s0 se : State} {F : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hsp0 : s0.spAligned = true)
    (hcl_e : signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl se.mem)
    (hpc_e : se.pc = cliIoPl02.base + 132#64)
    (hrun_e : se.status = .Running)
    (hsp_e : se.sp = s0.sp - 64#64)
    (hw21_e : se.readReg32 (.gpr 21#5) = 0#32)
    (hup_e : WriteStdoutUpperSaved s0 se)
    (hcont : ∀ sf : State, ∀ {Pre_f : SepProp},
      (Pre_f ⊢ stackAt s0.sp 96 ∗ F) →
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      SyscallPreserved se sf →
      sf.fs = se.fs →
      sf.trace = se.trace →
      sf.readReg64 .x0 = 0#64 →
      post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 64#64) 32 ∗ cliIoWriteStdoutSaved s0 ∗ F) post oomProp := by
  apply sepWP_seg_cliIo_block2_pureWhere hk2 hext2 hcl_e (mid := s0.readReg64 .lr)
  intro s' hcpu
  have hpc' : s'.pc = cliIoPl02.base + 132#64 := hcpu.pc_eq.trans hpc_e
  have hrun' : s'.status = .Running := hcpu.status_eq.trans hrun_e
  have hsp_in : s'.sp = s0.sp - 64#64 := hcpu.sp_eq.trans hsp_e
  have hsp' : s'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_in]; exact s0.spAligned_sub 64#64 hsp0
  have hw21' : s'.readReg32 (.gpr 21#5) = 0#32 :=
    (hcpu.readReg32 (.gpr 21#5)).trans hw21_e
  wp_conv_pre =>
    simp only [cliIoWriteStdoutSaved, ← hsp_in,
      show s0.sp - 56#64 = s'.sp + 8#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 48#64 = s'.sp + 16#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 40#64 = s'.sp + 24#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 32#64 = s'.sp + 32#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 24#64 = s'.sp + 40#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 16#64 = s'.sp + 48#64 by rw [hsp_in]; bv_lin,
      show s0.sp - 8#64 = s'.sp + 56#64 by rw [hsp_in]; bv_lin]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sf hcpu_f _hcl_f hnsp_f => ?_
  have hpres_f : SyscallPreserved se sf :=
    syscallPreserved_of_seg hcpu hcpu_f hnsp_f (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc_f : sf.pc = s0.readReg64 .lr := by
    rw [hcpu_f.pc_eq]; simp [arm64_norm]
  have hrun_f : sf.status = .Running :=
    hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun')
  have hsp_f : sf.sp = s0.sp := by
    rw [hcpu_f.sp_eq]; simp [arm64_norm]
  have hx0_f : sf.readReg64 .x0 = 0#64 := by
    rw [hcpu_f.readReg64 .x0]
    have hw21_eq : (s'.readReg64 (.gpr 21#5)).setWidth 32 = 0#32 := hw21'
    simp [arm64_norm, hw21_eq]
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64 .x19]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x20]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x21]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x22]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x23]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x24]; simp [arm64_norm]
    · rw [hcpu_f.readReg64 .x25]; simp [arm64_norm]
      exact (hcpu.readReg64 (.gpr 25#5)).trans hup_e.1
    · rw [hcpu_f.readReg64 .x26]; simp [arm64_norm]
      exact (hcpu.readReg64 (.gpr 26#5)).trans hup_e.2.1
    · rw [hcpu_f.readReg64 .x27]; simp [arm64_norm]
      exact (hcpu.readReg64 (.gpr 27#5)).trans hup_e.2.2.1
    · rw [hcpu_f.readReg64 .x28]; simp [arm64_norm]
      exact (hcpu.readReg64 (.gpr 28#5)).trans hup_e.2.2.2.1
    · rw [hcpu_f.readReg64 .fp]; simp [arm64_norm]
    · rw [hcpu_f.calleeSavedVRegs]; simp only [arm64_norm]
      exact hcpu.calleeSavedVRegs.trans hup_e.2.2.2.2
  have hfs_f : sf.fs = se.fs := hnsp_f.2.2.2.2.2.2
  have htr_f : sf.trace = se.trace := hnsp_f.1
  refine SepWP.weaken_pre ?_
    (SepWP.done hpc_f hrun_f
      (hcont sf (Entails.refl _) hpc_f hrun_f hsp_f hcs_f hpres_f hfs_f htr_f hx0_f))
  rw [show stackAt s0.sp 96 = stackAt (s0.sp - 64#64) 32 ∗ cells (s0.sp - 64#64) 8 from
    stackAt_split_cells s0.sp 32 8 (by decide)]
  dsimp only [cells]
  simp only [bv_lin_norm, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, hsp_in]
  refine Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)

set_option maxHeartbeats 800000 in
/-- Inductive `0x7fff_f000`-chunk `write(1, ...)` loop from `+0x024` (`36#64`) through `+0x084`
    and epilogue return (`+0x098`). -/
theorem cliIoWriteStdout_loop [CliIoPlacement] {keep : Nat → Bool}
    (hk2 : keep 2 = true) {P : Program}
    (hext2 : CliIoBlockNoExtern cliIoMpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere keep cliIoMpl muslWriteStdout32Spec))
    (n : Nat) :
    ∀ {s0 sl : State} {ro : Bool} {buf : BitVec 64} {written : Nat}
      {rem : List (BitVec 8)} {F : SepProp}
      {post : State → SepProp → Prop} {oomProp : State → SepProp},
      rem.length ≤ n →
      written + rem.length < 2 ^ 63 →
      (0 < rem.length →
        (buf + BitVec.ofNat 64 written).toNat + rem.length ≤ Arm64.USER_VA_LIMIT) →
      s0.spAligned = true →
      signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl sl.mem →
      sl.pc = cliIoPl02.base + 36#64 →
      sl.status = .Running →
      sl.sp = s0.sp - 64#64 →
      sl.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (written + rem.length) →
      sl.readReg64 (.gpr 20#5) = buf →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written →
      sl.readReg64 (.gpr 24#5) = 0x7ffff000#64 →
      WriteStdoutUpperSaved s0 sl →
      (∀ sf : State, ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp 96 ∗ stdoutBytesAt ro (buf + BitVec.ofNat 64 written) rem ∗ F) →
        sf.pc = s0.readReg64 .lr →
        sf.status = .Running →
        sf.sp = s0.sp →
        CalleeSavedPreserved s0 sf →
        SyscallPreserved sl sf →
        sf.fs = sl.fs →
        sf.trace = sl.trace ++ TraceEvent.ofBytes .stdout rem →
        sf.readReg64 .x0 = 0#64 →
        post sf Pre_f) →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 64#64) 32 ∗ cliIoWriteStdoutSaved s0 ∗
          stdoutBytesAt ro (buf + BitVec.ofNat 64 written) rem ∗ F)
        post oomProp := by
  induction n with
  | zero =>
    intro s0 sl ro buf written rem F post oomProp
      hrem_le _htot _hva hsp0 hcl_l hpc_l hrun_l hsp_l
      hx19_l hx20_l hx23_l hx24_l hup_l hcont
    have hrem_nil : rem = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hrem_le)
    subst hrem_nil
    simp only [List.length_nil, Nat.add_zero] at hx19_l
    apply sepWP_seg_cliIo_block2_pureWhere hk2 hext2 hcl_l (mid := cliIoPl02.base + 132#64)
    intro s' hcpu
    have hpc' : s'.pc = cliIoPl02.base + 36#64 := hcpu.pc_eq.trans hpc_l
    have hrun' : s'.status = .Running := hcpu.status_eq.trans hrun_l
    have hx19' : s'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 written :=
      (hcpu.readReg64 (.gpr 19#5)).trans hx19_l
    have hx23' : s'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written :=
      (hcpu.readReg64 (.gpr 23#5)).trans hx23_l
    have hx24' : s'.readReg64 (.gpr 24#5) = 0x7ffff000#64 :=
      (hcpu.readReg64 (.gpr 24#5)).trans hx24_l
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm])
      (by simpa [arm64_norm] using hrun')
      fun se hcpu_e hcl_e hnsp_e => ?_
    have hpres_le : SyscallPreserved sl se :=
      syscallPreserved_of_seg hcpu hcpu_e hnsp_e (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc_e : se.pc = cliIoPl02.base + 132#64 := by
      rw [hcpu_e.pc_eq]; simp [arm64_norm]
    have hrun_e : se.status = .Running :=
      hcpu_e.status_eq.trans (by simpa [arm64_norm] using hrun')
    have hsp_e : se.sp = s0.sp - 64#64 :=
      hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = s'.sp).trans (hcpu.sp_eq.trans hsp_l))
    have hw21_e : se.readReg32 (.gpr 21#5) = 0#32 := by
      rw [hcpu_e.readReg32 (.gpr 21#5)]; simp [arm64_norm]
    have hup_e : WriteStdoutUpperSaved s0 se := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_e.readReg64 (.gpr 25#5)]; simp only [arm64_norm]
        exact (hcpu.readReg64 (.gpr 25#5)).trans hup_l.1
      · rw [hcpu_e.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
        exact (hcpu.readReg64 (.gpr 26#5)).trans hup_l.2.1
      · rw [hcpu_e.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
        exact (hcpu.readReg64 (.gpr 27#5)).trans hup_l.2.2.1
      · rw [hcpu_e.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
        exact (hcpu.readReg64 (.gpr 28#5)).trans hup_l.2.2.2.1
      · rw [hcpu_e.calleeSavedVRegs]; simp only [arm64_norm]
        exact hcpu.calleeSavedVRegs.trans hup_l.2.2.2.2
    have hfs_le : se.fs = sl.fs := hnsp_e.2.2.2.2.2.2
    have htr_le : se.trace = sl.trace := hnsp_e.1
    refine cliIoWriteStdout_epilogue hk2 hext2 hsp0 hcl_e hpc_e hrun_e hsp_e hw21_e hup_e
      fun sf {Pre_f} hent hpc_f hrun_f hsp_f hcs_f hpres_ef hfs_ef htr_ef hx0_f => ?_
    have htr_f : sf.trace = sl.trace ++ TraceEvent.ofBytes .stdout [] := by
      rw [htr_ef, htr_le]; simp [TraceEvent.ofBytes]
    exact hcont sf hent hpc_f hrun_f hsp_f hcs_f (hpres_le.trans hpres_ef)
      (hfs_ef.trans hfs_le) htr_f hx0_f
  | succ n' ih =>
    intro s0 sl ro buf written rem F post oomProp
      hrem_le htot hva hsp0 hcl_l hpc_l hrun_l hsp_l
      hx19_l hx20_l hx23_l hx24_l hup_l hcont
    by_cases hrem0 : rem.length = 0
    · exact ih (by omega) htot hva
        hsp0 hcl_l hpc_l hrun_l hsp_l hx19_l hx20_l hx23_l hx24_l hup_l hcont
    · have hrem_pos : 0 < rem.length := Nat.pos_of_ne_zero hrem0
      have hrem_lt63 : rem.length < 2 ^ 63 := by omega
      have hva_cur : (buf + BitVec.ofNat 64 written).toNat + rem.length ≤ Arm64.USER_VA_LIMIT :=
        hva hrem_pos
      obtain ⟨want, hwant_def⟩ : ∃ want, want = min rem.length Arm64.MAX_RW_COUNT := ⟨_, rfl⟩
      have hwant_le : want ≤ rem.length := hwant_def ▸ Nat.min_le_left _ _
      have hwant_max : want ≤ Arm64.MAX_RW_COUNT := hwant_def ▸ Nat.min_le_right _ _
      have hwant_pos : 0 < want := by rw [hwant_def]; simp only [Arm64.MAX_RW_COUNT]; omega
      have hwant_lt63 : want < 2 ^ 63 := Nat.lt_of_le_of_lt hwant_max (by decide)
      -- Step `+0x024 .. +0x048` up to `bl write`
      apply sepWP_seg_cliIo_block2_pureWhere hk2 hext2 hcl_l
        (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym)
      intro s' hcpu
      have hpc' : s'.pc = cliIoPl02.base + 36#64 := hcpu.pc_eq.trans hpc_l
      have hrun' : s'.status = .Running := hcpu.status_eq.trans hrun_l
      have hx19' : s'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (written + rem.length) :=
        (hcpu.readReg64 (.gpr 19#5)).trans hx19_l
      have hx20' : s'.readReg64 (.gpr 20#5) = buf :=
        (hcpu.readReg64 (.gpr 20#5)).trans hx20_l
      have hx23' : s'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written :=
        (hcpu.readReg64 (.gpr 23#5)).trans hx23_l
      have hx24' : s'.readReg64 (.gpr 24#5) = 0x7ffff000#64 :=
        (hcpu.readReg64 (.gpr 24#5)).trans hx24_l
      have hsub_rem : BitVec.ofNat 64 (written + rem.length) - BitVec.ofNat 64 written =
          BitVec.ofNat 64 rem.length := bv64_sub_ofNat_add written rem.length
      have hult_hi : (BitVec.ofNat 64 (written + rem.length)).ult (BitVec.ofNat 64 written) =
          false := bv64_ult_add_false htot
      have hule_hi : (BitVec.ofNat 64 (written + rem.length)).ule (BitVec.ofNat 64 written) =
          false := bv64_ule_add_false hrem_pos htot
      have hrem_ne0 : BitVec.ofNat 64 rem.length ≠ 0#64 := bv64_ofNat_ne_zero hrem_pos hrem_lt63
      have hrem_beq0 : (BitVec.ofNat 64 rem.length == 0#64) = false := beq_false_of_ne hrem_ne0
      have hcsel : (if (BitVec.ofNat 64 rem.length).ult 0x7ffff000#64 then
            BitVec.ofNat 64 rem.length else 0x7ffff000#64) = BitVec.ofNat 64 want := by
        rw [hwant_def]; exact bv64_csel_want hrem_lt63
      wp_sym_steps
      refine SepWP.done
        (by simp [arm64_norm, cliIoWriteStdout_write_pc])
        (by simpa [arm64_norm] using hrun')
        fun sm1 hcpu_m1 hcl_m1 hnsp_m1 => ?_
      have hpres_01 : SyscallPreserved sl sm1 :=
        syscallPreserved_of_seg hcpu hcpu_m1 hnsp_m1 (by simp [arm64_norm]) (by simp [arm64_norm])
      have hfs_01 : sm1.fs = sl.fs := hnsp_m1.2.2.2.2.2.2
      have htr_01 : sm1.trace = sl.trace := hnsp_m1.1
      have hpc_m1 : sm1.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym := by
        rw [hcpu_m1.pc_eq]
        simp [arm64_norm, cliIoWriteStdout_write_pc]
      have hrun_m1 : sm1.status = .Running :=
        hcpu_m1.status_eq.trans (by simpa [arm64_norm] using hrun')
      have hsp_m1_eq : sm1.sp = s0.sp - 64#64 :=
        hcpu_m1.sp_eq.trans ((by simp [arm64_norm] : _ = s'.sp).trans (hcpu.sp_eq.trans hsp_l))
      have hsp_m1 : sm1.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_m1_eq]; exact s0.spAligned_sub 64#64 hsp0
      have hlr_m1 : sm1.readReg64 .lr = cliIoPl02.base + 76#64 := by
        rw [hcpu_m1.readReg64 .lr]
        simp [arm64_norm]
      have hx0_m1 : sm1.readReg32 .x0 = 1#32 := by
        rw [hcpu_m1.readReg32 .x0]
        simp [arm64_norm]
      have hx1_m1 : sm1.readReg64 .x1 = buf + BitVec.ofNat 64 written := by
        rw [hcpu_m1.readReg64 .x1]
        simp [arm64_norm]
      have hx2_m1 : sm1.readReg64 .x2 = BitVec.ofNat 64 want := by
        rw [hcpu_m1.readReg64 .x2, hwant_def]
        simp [arm64_norm]
      have hx19_m1 : sm1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (written + rem.length) := by
        rw [hcpu_m1.readReg64 (.gpr 19#5)]; simp only [arm64_norm]; exact hx19'
      have hx20_m1 : sm1.readReg64 (.gpr 20#5) = buf := by
        rw [hcpu_m1.readReg64 (.gpr 20#5)]; simp only [arm64_norm]; exact hx20'
      have hx22_m1 : sm1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want := by
        rw [hcpu_m1.readReg64 (.gpr 22#5), hwant_def]
        simp [arm64_norm]
      have hx23_m1 : sm1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written := by
        rw [hcpu_m1.readReg64 (.gpr 23#5)]; simp only [arm64_norm]; exact hx23'
      have hx24_m1 : sm1.readReg64 (.gpr 24#5) = 0x7ffff000#64 := by
        rw [hcpu_m1.readReg64 (.gpr 24#5)]; simp only [arm64_norm]; exact hx24'
      have hup_m1 : WriteStdoutUpperSaved s0 sm1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hcpu_m1.readReg64 (.gpr 25#5)]; simp only [arm64_norm]
          exact (hcpu.readReg64 (.gpr 25#5)).trans hup_l.1
        · rw [hcpu_m1.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
          exact (hcpu.readReg64 (.gpr 26#5)).trans hup_l.2.1
        · rw [hcpu_m1.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
          exact (hcpu.readReg64 (.gpr 27#5)).trans hup_l.2.2.1
        · rw [hcpu_m1.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
          exact (hcpu.readReg64 (.gpr 28#5)).trans hup_l.2.2.2.1
        · rw [hcpu_m1.calleeSavedVRegs]; simp only [arm64_norm]
          exact hcpu.calleeSavedVRegs.trans hup_l.2.2.2.2
      -- Split `rem` into `chunk := rem.take want` and `rest := rem.drop want`
      let chunk := rem.take want
      let rest := rem.drop want
      have hchunk_len : chunk.length = want := List.length_take_of_le hwant_le
      have hchunk_min : min chunk.length Arm64.MAX_RW_COUNT = want := by
        rw [hchunk_len]; exact Nat.min_eq_left hwant_max
      have hchunk_take_self : chunk.take (min chunk.length Arm64.MAX_RW_COUNT) = chunk := by
        rw [hchunk_min, ← hchunk_len, List.take_length]
      wp_conv_pre =>
        rw [stdoutBytesAt_take_drop_local ro (buf + BitVec.ofNat 64 written) want rem hwant_le,
            ← hsp_m1_eq]
      apply seqCodeLoadedWhere hcl_m1 (mid := cliIoPl02.base + 76#64)
      apply (SepWP.call_subroutine_frame
        (F := cliIoWriteStdoutSaved s0 ∗
          stdoutBytesAt ro (buf + BitVec.ofNat 64 written + BitVec.ofNat 64 want) rest ∗ F)
        hwrite
        (x := (ro, buf + BitVec.ofNat 64 written, chunk))
        hpc_m1 hrun_m1 hsp_m1 hlr_m1
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [MultiPlacedLib.withCodeLoadedWhere, muslWriteStdout32Spec]
        rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoadedWhere keep cliIoMpl sm1.mem⌝,
            sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨hcl_m1, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0_m1, hx1_m1, by rw [hchunk_len]; exact hx2_m1,
          by rw [hchunk_len]; exact hwant_pos,
          by rw [hchunk_len]; exact hwant_lt63,
          by rw [hchunk_len]; omega⟩,
          Satisfies.mono (by dsimp only [chunk, rest]; sep_frame) hm'⟩
      · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
        refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
        dsimp only [MultiPlacedLib.withCodeLoadedWhere, muslWriteStdout32Spec]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim
        rintro ⟨hx0_sf1, hfs_12, htr_12, hpres_12⟩
        rw [hchunk_take_self, hchunk_len] at hx0_sf1
        rw [hchunk_take_self] at htr_12
        have hup_sf1 : WriteStdoutUpperSaved s0 sf1 := hup_m1.of_calleeSaved hcs_sf1
        rw [CalleeSavedPreserved.iff_regs] at hcs_sf1
        rcases hcs_sf1 with ⟨hx19_cs, hx20_cs, _, hx22_cs, hx23_cs, hx24_cs, _, _, _, _, _, _⟩
        have hsp_sf1_eq : sf1.sp = s0.sp - 64#64 := hsp_sf1.trans hsp_m1_eq
        have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (written + rem.length) :=
          hx19_cs.trans hx19_m1
        have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = buf := hx20_cs.trans hx20_m1
        have hx22_sf1 : sf1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want := hx22_cs.trans hx22_m1
        have hx23_sf1 : sf1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written :=
          hx23_cs.trans hx23_m1
        have hx24_sf1 : sf1.readReg64 (.gpr 24#5) = 0x7ffff000#64 := hx24_cs.trans hx24_m1
        -- Step `+0x04c .. +0x070 -> +0x024` back-edge
        have hwant_ne0 : BitVec.ofNat 64 want ≠ 0#64 := bv64_ofNat_ne_zero hwant_pos hwant_lt63
        have hwant_beq0 : (BitVec.ofNat 64 want == 0#64) = false := beq_false_of_ne hwant_ne0
        have hwant_bit63 : (BitVec.ofNat 64 want).getLsbD 63 = false :=
          bv64_getLsbD_63_false hwant_lt63
        have hsub_want : BitVec.ofNat 64 want - BitVec.ofNat 64 want = 0#64 := by bv_omega
        apply sepWP_seg_cliIo_block2_pureWhere hk2 hext2 hcl_sf1 (mid := cliIoPl02.base + 36#64)
        intro s2' hcpu2
        have hpc2' : s2'.pc = cliIoPl02.base + 76#64 := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 want :=
          (hcpu2.readReg64 .x0).trans hx0_sf1
        have hx22_2' : s2'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want :=
          (hcpu2.readReg64 (.gpr 22#5)).trans hx22_sf1
        have hx23_2' : s2'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 written :=
          (hcpu2.readReg64 (.gpr 23#5)).trans hx23_sf1
        wp_sym_steps
        refine SepWP.done
          (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun2')
          fun s_next hcpu_n hcl_n hnsp_n => ?_
        have hpres_2n : SyscallPreserved sf1 s_next :=
          syscallPreserved_of_seg hcpu2 hcpu_n hnsp_n (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpres_0n : SyscallPreserved sl s_next := hpres_01.trans (hpres_12.trans hpres_2n)
        have hfs_0n : s_next.fs = sl.fs := hnsp_n.2.2.2.2.2.2.trans (hfs_12.trans hfs_01)
        have htr_0n : s_next.trace = sl.trace ++ TraceEvent.ofBytes .stdout chunk := by
          rw [hnsp_n.1, htr_12, htr_01]
        have hpc_n : s_next.pc = cliIoPl02.base + 36#64 := by
          rw [hcpu_n.pc_eq]; simp [arm64_norm]
        have hrun_n : s_next.status = .Running :=
          hcpu_n.status_eq.trans (by simpa [arm64_norm] using hrun2')
        have hsp_n : s_next.sp = s0.sp - 64#64 :=
          hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = s2'.sp).trans (hcpu2.sp_eq.trans hsp_sf1_eq))
        have hrest_len : rest.length = rem.length - want := List.length_drop
        have htot_eq : (written + want) + rest.length = written + rem.length := by
          rw [hrest_len]; omega
        have hx19_n : s_next.readReg64 (.gpr 19#5) = BitVec.ofNat 64 ((written + want) + rest.length) := by
          rw [hcpu_n.readReg64 (.gpr 19#5), htot_eq]
          simp only [arm64_norm]
          exact (hcpu2.readReg64 (.gpr 19#5)).trans hx19_sf1
        have hx20_n : s_next.readReg64 (.gpr 20#5) = buf := by
          rw [hcpu_n.readReg64 (.gpr 20#5)]
          simp only [arm64_norm]
          exact (hcpu2.readReg64 (.gpr 20#5)).trans hx20_sf1
        have hx23_n : s_next.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (written + want) := by
          rw [hcpu_n.readReg64 (.gpr 23#5)]
          simp only [arm64_norm]
          rw [← BitVec.ofNat_add]
          exact congrArg (BitVec.ofNat 64)
            (by rw [hwant_def]; dsimp only [Arm64.MAX_RW_COUNT]; omega)
        have hx24_n : s_next.readReg64 (.gpr 24#5) = 0x7ffff000#64 := by
          rw [hcpu_n.readReg64 (.gpr 24#5)]
          simp only [arm64_norm]
          exact (hcpu2.readReg64 (.gpr 24#5)).trans hx24_sf1
        have hup_n : WriteStdoutUpperSaved s0 s_next := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [hcpu_n.readReg64 (.gpr 25#5)]; simp only [arm64_norm]
            exact (hcpu2.readReg64 (.gpr 25#5)).trans hup_sf1.1
          · rw [hcpu_n.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
            exact (hcpu2.readReg64 (.gpr 26#5)).trans hup_sf1.2.1
          · rw [hcpu_n.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
            exact (hcpu2.readReg64 (.gpr 27#5)).trans hup_sf1.2.2.1
          · rw [hcpu_n.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
            exact (hcpu2.readReg64 (.gpr 28#5)).trans hup_sf1.2.2.2.1
          · rw [hcpu_n.calleeSavedVRegs]; simp only [arm64_norm]
            exact hcpu2.calleeSavedVRegs.trans hup_sf1.2.2.2.2
        have hptr_add : buf + BitVec.ofNat 64 written + BitVec.ofNat 64 want =
            buf + BitVec.ofNat 64 (written + want) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add]
        have hva_rest : 0 < rest.length →
            (buf + BitVec.ofNat 64 (written + want)).toNat + rest.length ≤ Arm64.USER_VA_LIMIT := by
          intro _
          rw [← hptr_add]
          have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
          have hadd_nat :
              ((buf + BitVec.ofNat 64 written) + BitVec.ofNat 64 want).toNat =
                (buf + BitVec.ofNat 64 written).toNat + want := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (show want < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show (buf + BitVec.ofNat 64 written).toNat + want < 2 ^ 64 by omega)]
          rw [hadd_nat, hrest_len]
          omega
        wp_conv_pre =>
          rw [hsp_m1_eq, hptr_add]
          simp only [show stackAt (s0.sp - 64#64) 32 ∗ stdoutBytesAt ro (buf + BitVec.ofNat 64 written) chunk ∗
              cliIoWriteStdoutSaved s0 ∗ stdoutBytesAt ro (buf + BitVec.ofNat 64 (written + want)) rest ∗ F =
            stackAt (s0.sp - 64#64) 32 ∗ cliIoWriteStdoutSaved s0 ∗
              stdoutBytesAt ro (buf + BitVec.ofNat 64 (written + want)) rest ∗
              (stdoutBytesAt ro (buf + BitVec.ofNat 64 written) chunk ∗ F) by sep_ac_rfl]
        refine ih (by rw [hrest_len]; omega) (by rw [htot_eq]; exact htot) hva_rest
          hsp0 hcl_n hpc_n hrun_n hsp_n hx19_n hx20_n hx23_n hx24_n hup_n
          fun sf {Pre_f} hent hpc_f hrun_f hsp_f hcs_f hpres_nf hfs_nf htr_nf hx0_f => ?_
        have hent_full :
            Pre_f ⊢ stackAt s0.sp 96 ∗ stdoutBytesAt ro (buf + BitVec.ofNat 64 written) rem ∗ F := by
          refine Entails.trans hent ?_
          rw [stdoutBytesAt_take_drop_local ro (buf + BitVec.ofNat 64 written) want rem hwant_le,
              hptr_add]
          dsimp only [chunk, rest]
          sep_entail
        have htr_full : sf.trace = sl.trace ++ TraceEvent.ofBytes .stdout rem := by
          rw [htr_nf, htr_0n, List.append_assoc, ← traceEvent_ofBytes_append_local]
          dsimp only [chunk, rest]
          rw [List.take_append_drop]
        exact hcont sf hent_full hpc_f hrun_f hsp_f hcs_f (hpres_0n.trans hpres_nf)
          (hfs_nf.trans hfs_0n) htr_full hx0_f

end

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps
