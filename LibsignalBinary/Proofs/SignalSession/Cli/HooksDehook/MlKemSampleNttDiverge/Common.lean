/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Shared Operational Divergence & Run-Level Corollaries for `SampleNTT` (`MlKemSampleNttDiverge.Common`)

Shared untrusted infrastructure for proving that a real 0-hook execution entering any of the 5
`libcrux_ml_kem` `SampleNTT` entry points with `¬ *StateTerminates u` stays `.Running` forever:
1. `falsePostSpec`: partial-correctness `Spec` with `post = onPanic = onExit = onOom = ⌜False⌝` whose
   `safe_subroutine_ok` immediately yields operational divergence (`status = .Running ∧ ∃ w, Step`).
2. `matrixTerminates{3,4}_of_rows_{ij,ji}`: closes `¬ Shake128MatrixTerminates rho k` once all `k`
   matrix rows reach `allLanesDone k … = true` (avoiding first-bad-row case splits).
3. `steps_diverge_of_stripS_standard` & `c2_mlkem_diverge_of_blockSafeOk_false`: lifts stripped
   block-level divergence (`mlkemMultiLib.blockProgram c2MlkemMpl j` on `stripS (mlkemKeep …) u`)
   to both `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `Placed.cliProgPlacedSig` via
   `Step.deterministic` and `ExecFrozen` preservation (zero `CallerLrUnmapped` premise required).
4. Run-level corollaries: `cliRunPlacedSig_eq_none_of_reaches_diverge`,
   `not_cliReachesOOMPlaced_of_reaches_diverge`, and `no_oom_after_diverge`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement MultiPlacedLib PlacedLib)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (
  CliHooks Inputs cliElfBytes cliExternsPlaced cliProcessInputs libsignalSessionLib
)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (CliReachesOOMPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig cliRunPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_pc stripS_spAligned stripS_status
  strip_codeLoaded_mlkem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockSafeOk MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone allLanesDone_eq_true_iff
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Shake128MatrixTerminates Shake128SeedTerminates
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_stripExecOutside standard_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
  cliRunExtPlacedSigAt_cliExternsPlaced_eq cliRunsToExtOnInputsAt_of_eq_some
  externAt?_cliProgExtPlacedSigAt_eq_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem (
  c2_mlkem_invMem_of_f3CodeInv
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts f3RxSeg_realProg617_externAt_none
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

/-! ## 1. `falsePostSpec` & `SubroutineOutcome` Elimination -/

/-- Specification wrapper with `post = onPanic = onExit = onOom = ⌜False⌝`: proving
    `safe_subroutine_ok` for `falsePostSpec pre` establishes that execution from `pre` never halts,
    faults, panics, exits, OOMs, or returns. -/
@[expose] def falsePostSpec {α : Type} (pre : α → State → SepProp) : Spec α where
  pre := pre
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem not_subroutineOutcome_falsePostSpec {α : Type} {pre : α → State → SepProp}
    {x : α} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome (falsePostSpec pre) x R s0 sf) : False := by
  rcases h with ⟨_, _, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
    exact not_satisfies_false_sepConj hq

theorem not_subroutineOutcome_withCodeLoaded_withMlKemRoOk_falsePostSpec {α : Type}
    {mpl : MultiPlacement} {pre : α → State → SepProp}
    {x : α} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (mlkemMultiLib.withCodeLoaded mpl (withMlKemRoOk mpl (falsePostSpec pre))) x R s0 sf) :
    False := by
  rcases h with ⟨_, _, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
    exact not_satisfies_false_sepConj hq

/-- Close `safe_subroutine_ok` for `mlkemMultiLib.withCodeLoaded mpl (falsePostSpec pre)` directly
    from a `SafeSepWP … (fun _ _ => False)`. -/
theorem safe_subroutine_ok_falsePostSpec_of_safeSepWP {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {mpl : MultiPlacement}
    {pre : α → State → SepProp}
    (h : ∀ (x : α) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running → s0.spAligned = true →
      mlkemMultiLib.CodeLoaded mpl s0.mem →
      SafeSepWP prog s0 (pre x s0) (fun _ _ => False)) :
    safe_subroutine_ok prog entry_pc
      (mlkemMultiLib.withCodeLoaded mpl (falsePostSpec pre)) := by
  refine safe_subroutine_ok_of_safeSepWP fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [MultiPlacedLib.withCodeLoaded, falsePostSpec] at hpre
  rw [sepConj_comm (pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre'⟩ := hpre
  exact ⟨pre x s0, hpre', (h x s0 hpc hrun hsp hcl).mono fun _ _ hf => False.elim hf⟩

/-- Close `safe_subroutine_ok` for
    `mlkemMultiLib.withCodeLoaded mpl (ToBaseSpec.toSpec (withMlKemRoOk mpl (falsePostSpec pre)) entry_pc)`
    directly from a `SafeSepWP … (fun _ _ => False)`. -/
theorem safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {mpl : MultiPlacement}
    {pre : α → State → SepProp}
    (h : ∀ (x : α) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running → s0.spAligned = true →
      mlkemMultiLib.CodeLoaded mpl s0.mem →
      SafeSepWP prog s0
        ((ToBaseSpec.toSpec (withMlKemRoOk mpl (falsePostSpec pre)) entry_pc).pre x s0)
        (fun _ _ => False)) :
    safe_subroutine_ok prog entry_pc
      (mlkemMultiLib.withCodeLoaded mpl
        (ToBaseSpec.toSpec (withMlKemRoOk mpl (falsePostSpec pre)) entry_pc)) :=
  safe_subroutine_ok_falsePostSpec_of_safeSepWP h

/-! ## 2. Row `allLanesDone` → `Shake128MatrixTerminates` Contradiction Helpers -/

theorem row_terminates_of_allLanesDone {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    (h : allLanesDone N seeds extra = true) :
    ∀ col : Nat, col < N → Shake128SeedTerminates (seeds col) :=
  fun col hcol => ⟨extra, allLanesDone_eq_true_iff.mp h col hcol⟩

/-- `3 × 3` non-transposed (`[row, col]`) matrix termination from all 3 row `allLanesDone` flags. -/
theorem matrixTerminates3_of_rows_ij {rho : List (BitVec 8)} {e0 e1 e2 : Nat}
    (h0 : allLanesDone 3 (fun col => rho.take 32 ++ [0#8, BitVec.ofNat 8 col]) e0 = true)
    (h1 : allLanesDone 3 (fun col => rho.take 32 ++ [1#8, BitVec.ofNat 8 col]) e1 = true)
    (h2 : allLanesDone 3 (fun col => rho.take 32 ++ [2#8, BitVec.ofNat 8 col]) e2 = true) :
    Shake128MatrixTerminates rho 3 := by
  intro i j hi hj
  match i with
  | 0 => exact row_terminates_of_allLanesDone h0 j hj
  | 1 => exact row_terminates_of_allLanesDone h1 j hj
  | 2 => exact row_terminates_of_allLanesDone h2 j hj
  | n + 3 => omega

/-- `3 × 3` transposed (`[col, row]`) matrix termination from all 3 row `allLanesDone` flags. -/
theorem matrixTerminates3_of_rows_ji {rho : List (BitVec 8)} {e0 e1 e2 : Nat}
    (h0 : allLanesDone 3 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 0#8]) e0 = true)
    (h1 : allLanesDone 3 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 1#8]) e1 = true)
    (h2 : allLanesDone 3 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 2#8]) e2 = true) :
    Shake128MatrixTerminates rho 3 := by
  intro i j hi hj
  match j with
  | 0 => exact row_terminates_of_allLanesDone h0 i hi
  | 1 => exact row_terminates_of_allLanesDone h1 i hi
  | 2 => exact row_terminates_of_allLanesDone h2 i hi
  | n + 3 => omega

/-- `4 × 4` non-transposed (`[row, col]`) matrix termination from all 4 row `allLanesDone` flags. -/
theorem matrixTerminates4_of_rows_ij {rho : List (BitVec 8)} {e0 e1 e2 e3 : Nat}
    (h0 : allLanesDone 4 (fun col => rho.take 32 ++ [0#8, BitVec.ofNat 8 col]) e0 = true)
    (h1 : allLanesDone 4 (fun col => rho.take 32 ++ [1#8, BitVec.ofNat 8 col]) e1 = true)
    (h2 : allLanesDone 4 (fun col => rho.take 32 ++ [2#8, BitVec.ofNat 8 col]) e2 = true)
    (h3 : allLanesDone 4 (fun col => rho.take 32 ++ [3#8, BitVec.ofNat 8 col]) e3 = true) :
    Shake128MatrixTerminates rho 4 := by
  intro i j hi hj
  match i with
  | 0 => exact row_terminates_of_allLanesDone h0 j hj
  | 1 => exact row_terminates_of_allLanesDone h1 j hj
  | 2 => exact row_terminates_of_allLanesDone h2 j hj
  | 3 => exact row_terminates_of_allLanesDone h3 j hj
  | n + 4 => omega

/-- `4 × 4` transposed (`[col, row]`) matrix termination from all 4 row `allLanesDone` flags. -/
theorem matrixTerminates4_of_rows_ji {rho : List (BitVec 8)} {e0 e1 e2 e3 : Nat}
    (h0 : allLanesDone 4 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 0#8]) e0 = true)
    (h1 : allLanesDone 4 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 1#8]) e1 = true)
    (h2 : allLanesDone 4 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 2#8]) e2 = true)
    (h3 : allLanesDone 4 (fun col => rho.take 32 ++ [BitVec.ofNat 8 col, 3#8]) e3 = true) :
    Shake128MatrixTerminates rho 4 := by
  intro i j hi hj
  match j with
  | 0 => exact row_terminates_of_allLanesDone h0 i hi
  | 1 => exact row_terminates_of_allLanesDone h1 i hi
  | 2 => exact row_terminates_of_allLanesDone h2 i hi
  | 3 => exact row_terminates_of_allLanesDone h3 i hi
  | n + 4 => omega

/-! ## 3. Operational `stripS` Divergence Lift (`steps_diverge_of_stripS_standard`) -/

private theorem strip_read32_local (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, strip_read8]

private theorem externAt?_mlkemBlockProgram_none_local (mpl : MultiPlacement) (j : Nat)
    (pc : BitVec 64) :
    (mlkemMultiLib.blockProgram mpl j).externAt? pc = none := by
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none]

private theorem step_lift_of_stripS_running
    {keep : BitVec 64 → Bool} {P1 P_sub : Program}
    (hsvc1 : P1.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    {sa sb' : State}
    (hstep_sub : Step P_sub (stripS keep sa) sb')
    (hsb_run : sb'.status = .Running)
    (hfra : ExecFrozen sa.mem) :
    ∃ sb : State, Step P1 sa sb ∧ sb' = stripS keep sb ∧ ExecFrozen sb.mem := by
  cases hstep_sub with
  | halt_unmapped _ _ _ => cases hsb_run
  | extern _ he _ _ => rw [hsub_no] at he; cases he
  | extern_fault _ he _ => rw [hsub_no] at he; cases he
  | @exec inst hr' hfm' =>
    have hra : sa.status = .Running := by simpa [stripS_status] using hr'
    rw [stripS_pc, stripS_mem] at hfm'
    unfold Program.fetchMem at hfm'
    rw [hsub_no sa.pc] at hfm'
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
    by_cases hal_pc : sa.pc.toNat % 4 = 0
    · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
      by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
      · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
        have hx4 :
            ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
            ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
            ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
            ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
          simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
        obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
        obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
        obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
        obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
        have hce : sa.mem.canExec sa.pc 4 = true := by
          simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
        rw [strip_read32_local] at hfm'
        have hext1 : P1.externAt? sa.pc = none := hext1_no sa.pc hkp0
        have hfm1 : P1.fetchMem sa.mem sa.pc = some inst := by
          unfold Program.fetchMem
          simp [hext1, hal_pc, hce, hfm']
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
          have hev_strip :
              P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                stripS keep (Syscall.standard sa) := by
            simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
          have hev1 :
              P1.evalInst (.system false 0#16) sa = Syscall.standard sa := by
            simp [Program.evalInst, execInstWithSvc, hsvc1]
          exact ⟨Syscall.standard sa, hev1 ▸ Step.exec hra hfm1, hev_strip, hfr_sb⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_strip :
              P_sub.evalInst inst (stripS keep sa) =
                stripS keep (execInst inst sa) := by
            rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, execInst_stripS hnsvc0]
          have hev1 : P1.evalInst inst sa = execInst inst sa :=
            evalInst_eq_execInst_of_not_isSvc0 hnsvc0 sa
          have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
          have hfr_sb : ExecFrozen (execInst inst sa).mem :=
            ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
          exact ⟨execInst inst sa, hev1 ▸ Step.exec hra hfm1, hev_strip, hfr_sb⟩
      · simp [hce'] at hfm'
    · simp [hal_pc] at hfm'

/-- Lift operational divergence from `stripS keep u` on a hook-free `P_sub` (`Syscall.standard`)
    to any target program `P1` (`Syscall.standard`, no externs inside `keep`) under `ExecFrozen u.mem`.
    Requires no `CallerLrUnmapped` or `lr ∉ keep` premise because `P_sub` never halts (`status = .Running`
    at every reachable stripped state forces `keep pc = true` on every step). -/
theorem steps_diverge_of_stripS_standard
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {u : State}
    (hsvc1 : P1.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hfr0 : ExecFrozen u.mem)
    (hdiv : ∀ u' : State, Steps P_sub (stripS keep u) u' →
      u'.status = .Running ∧ ∃ v' : State, Step P_sub u' v') :
    ∀ v : State, Steps P1 u v → v.status = .Running ∧ ∃ w : State, Step P1 v w := by
  have key : ∀ {sa v : State}, Steps P1 sa v →
      Steps P_sub (stripS keep u) (stripS keep sa) →
      ExecFrozen sa.mem →
      v.status = .Running ∧ ∃ w : State, Step P1 v w := by
    intro sa v hv
    induction hv with
    | refl sa =>
      intro hsteps_sub hfra
      obtain ⟨hrun', sb', hstep_sub⟩ := hdiv (stripS keep sa) hsteps_sub
      have hsb_run : sb'.status = .Running :=
        (hdiv sb' (hsteps_sub.trans (Steps.step hstep_sub (Steps.refl sb')))).1
      obtain ⟨sb, hstep1, _, _⟩ :=
        step_lift_of_stripS_running hsvc1 hsvc_sub hext1_no hsub_no hstep_sub hsb_run hfra
      exact ⟨by simpa [stripS_status] using hrun', sb, hstep1⟩
    | @step sa sa1 v h1 _ ih =>
      intro hsteps_sub hfra
      obtain ⟨_, sb', hstep_sub⟩ := hdiv (stripS keep sa) hsteps_sub
      have hsb_run : sb'.status = .Running :=
        (hdiv sb' (hsteps_sub.trans (Steps.step hstep_sub (Steps.refl sb')))).1
      obtain ⟨sb, hstep1, hsb_eq, hfr_sb⟩ :=
        step_lift_of_stripS_running hsvc1 hsvc_sub hext1_no hsub_no hstep_sub hsb_run hfra
      cases Step.deterministic h1 hstep1
      exact ih (hsteps_sub.trans (Steps.step (hsb_eq ▸ hstep_sub) (Steps.refl _))) hfr_sb
  exact fun v hv => key hv (Steps.refl _) hfr0

/-! ## 4. `0d6227d2…` Block-to-Real-ELF Divergence Runner -/

private theorem mlkemKeep_eq_c2MlkemKeep (mpl : MultiPlacement) :
    mlkemKeep mpl = c2MlkemKeep mpl := rfl

/-- Lift a block-level `MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl (falsePostSpec pre))`
    at `c2MlkemMpl` directly to operational divergence (`status = .Running ∧ ∃ w, Step`) on BOTH
    `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `cliProgPlacedSig mpl mmpl W`. -/
theorem c2_mlkem_diverge_of_blockSafeOk_false
    {j : Nat} {lsSym : String} {α : Type}
    {pre : α → State → SepProp}
    (hj : j < mlkemMultiLib.blocks.length)
    (hok : MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl (falsePostSpec pre)))
    (h_pre_mem : ∀ x (s : State) (m : Memory), pre x (s.setMem m) = pre x s := by
      intro _ s _; cases s; rfl)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSym = c2MlkemMpl.base j)
    (W : CliHooks)
    {x : α} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsSym)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ pre x u ∗ R) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  obtain ⟨hpl, hcl, hro⟩ := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  let keep := mlkemKeep c2MlkemMpl
  let u' := stripS keep u
  have hpc_base : u.pc = c2MlkemMpl.base j := hpc.trans hRes
  have hcl' : mlkemMultiLib.CodeLoaded c2MlkemMpl u'.mem := strip_codeLoaded_mlkem hcl
  have hro' : MlKemRoOk c2MlkemMpl u'.mem := by
    simpa [u', stripS_mem] using mlkemRoOk_stripExecOutside keep hro
  have hpre_strip : u'.mem ⊨ pre x u' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hpre
    have hu'_set : u' = u.setMem (stripExecOutside keep u.mem) := by cases u; rfl
    rw [hu'_set, h_pre_mem]
    exact hsat
  have hpre_full : u'.mem ⊨
      (mlkemMultiLib.withCodeLoaded c2MlkemMpl
        (withMlKemRoOk c2MlkemMpl (falsePostSpec pre))).pre x u' ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, falsePostSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl',
      sepConj_assoc, pure_sepConj_of_true hro']
    exact hpre_strip
  have hentry' : AapcsEntry u' (c2MlkemMpl.base j) :=
    ⟨by simpa [u', stripS_pc] using hpc_base,
     by simpa [u', stripS_status] using hrun,
     by simpa [u', stripS_spAligned] using hsp⟩
  have hdiv_sub : ∀ u'' : State, Steps (mlkemMultiLib.blockProgram c2MlkemMpl j) u' u'' →
      u''.status = .Running ∧
        ∃ v'' : State, Step (mlkemMultiLib.blockProgram c2MlkemMpl j) u'' v'' := by
    rcases @hok ⟨c2MlkemMpl, hpl⟩ x R u' hentry' hpre_full (hcl' j hj) with ⟨_, _, hout'⟩ | hall'
    · exact False.elim (not_subroutineOutcome_withCodeLoaded_withMlKemRoOk_falsePostSpec hout')
    · exact hall'
  have hext617_no : ∀ pc, keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
    intro pc hk
    dsimp only [keep] at hk
    rw [mlkemKeep_eq_c2MlkemKeep] at hk
    exact f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg hk)
      (c2_mlkemKeep_noPanic hk)
  have hextSig_no : ∀ pc, keep pc = true →
      (cliProgPlacedSig mpl mmpl W).externAt? pc = none := by
    intro pc hk
    rw [← cliProgExtPlacedSigAt_cliExternsPlaced_eq]
    exact externAt?_cliProgExtPlacedSigAt_eq_none.mpr (hext617_no pc hk)
  exact ⟨
    steps_diverge_of_stripS_standard rfl rfl hext617_no
      (externAt?_mlkemBlockProgram_none_local c2MlkemMpl j) hFr hdiv_sub,
    steps_diverge_of_stripS_standard rfl rfl hextSig_no
      (externAt?_mlkemBlockProgram_none_local c2MlkemMpl j) hFr hdiv_sub⟩

/-! ## 5. Run-Level Corollaries (`cliRunPlacedSig = none` & `¬ CliReachesOOMPlaced`) -/

/-- If `s_init` deterministically reaches `u` and every state reachable from `u` is `.Running`,
    then EVERY state reachable from `s_init` is `.Running` (`Steps.running_or_steps_of`). -/
theorem all_running_of_reaches_diverge {prog : Program} {s_init u : State}
    (hReach : Steps prog s_init u)
    (hDiv : ∀ v : State, Steps prog u v → v.status = .Running) :
    ∀ w : State, Steps prog s_init w → w.status = .Running := by
  intro w hw
  rcases Steps.running_or_steps_of hReach hw with hrun | hafter
  · exact hrun
  · exact hDiv w hafter

/-- No `.OutOfMemory` state is reachable after entering a diverging state `u`. -/
theorem no_oom_after_diverge {prog : Program} {u : State}
    (hDiv : ∀ v : State, Steps prog u v → v.status = .Running) :
    ∀ v : State, Steps prog u v → v.status ≠ .OutOfMemory := by
  intro v hv hoom
  have hr := hDiv v hv
  rw [hoom] at hr
  cases hr

/-- If the real 0-hook execution on input `i` reaches a diverging state `u`,
    `cliRunPlacedSig mpl mmpl elf W i = none`. -/
theorem cliRunPlacedSig_eq_none_of_reaches_diverge
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {s0 u : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s0)
    (hReach : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) u)
    (hDiv : ∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v → v.status = .Running) :
    cliRunPlacedSig mpl mmpl elf W i = none := by
  have hall := all_running_of_reaches_diverge hReach hDiv
  cases hrun : cliRunPlacedSig mpl mmpl elf W i with
  | none => rfl
  | some o =>
    rw [← cliRunExtPlacedSigAt_cliExternsPlaced_eq] at hrun
    rcases cliRunsToExtOnInputsAt_of_eq_some hrun with
      ⟨s0', hLoad', ⟨out, ⟨sf, hSteps, hTerm⟩, _⟩ | ⟨_, _, _, hFalse⟩, _⟩
    · rw [hLoad] at hLoad'
      cases hLoad'
      rw [cliProgExtPlacedSigAt_cliExternsPlaced_eq] at hSteps
      have hsf_run := hall sf hSteps
      rcases hTerm with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] at hsf_run <;> cases hsf_run
    · exact False.elim hFalse

/-- If the real 0-hook execution on input `i` reaches a diverging state `u`,
    `¬ CliReachesOOMPlaced mpl mmpl elf W i`. -/
theorem not_cliReachesOOMPlaced_of_reaches_diverge
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {s0 u : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s0)
    (hReach : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) u)
    (hDiv : ∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v → v.status = .Running) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  have hall := all_running_of_reaches_diverge hReach hDiv
  rintro ⟨s0', sf, hLoad', hSteps, hOom⟩
  rw [hLoad] at hLoad'
  cases hLoad'
  have hsf_run := hall sf hSteps
  rw [hOom] at hsf_run
  cases hsf_run

/-- Bundled run-level corollary: reaching a diverging state `u` forces BOTH
    `cliRunPlacedSig mpl mmpl elf W i = none` AND `¬ CliReachesOOMPlaced mpl mmpl elf W i`. -/
theorem cliRunPlacedSig_none_and_not_oom_of_reaches_diverge
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {s0 u : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s0)
    (hReach : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) u)
    (hDiv : ∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v → v.status = .Running) :
    cliRunPlacedSig mpl mmpl elf W i = none ∧ ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  ⟨cliRunPlacedSig_eq_none_of_reaches_diverge hLoad hReach hDiv,
   not_cliReachesOOMPlaced_of_reaches_diverge hLoad hReach hDiv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common
