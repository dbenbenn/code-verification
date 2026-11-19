/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1

/-!
# Non-`SampleNTT` ML-KEM Ghost Rows (`B20`, `B21`) & Shared Active-Run Helpers (`ElfSampleNttStuckDivergeMlKemAvoidNonSntt`)

1. **Shared active-run & `StepsStrictAvoid` infrastructure** (reused across `B20`, `B21`, and the
   5 `SampleNTT` wrapper/core rows):
   - `mlkemBlockGhost_eq_of_visitedIn`: pins `mlkemBlockGhost c2MlkemMpl j master fallback u = sf`
     from any `h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf` returning run.
   - `stepsStrictAvoid_realProg617_of_visitedIn`: lifts `h2fsgen_StepsVisitedIn D emptyStdProg s sf`
     to `StepsStrictAvoid bad (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf`.
   - `step_emptyStdProg_of_mlkem_block_fetch`: single-instruction `emptyStdProg` step + keep witness
     for `mlkemMultiLib` ABI wrapper prologues.
   - `not_mem_mlkemSampleNttSyms_resolve_of_activeKeep`, `not_mlKemSampleNttStuckAt_of_activeKeep`,
     `not_mlKemSampleNttStuckAt_of_entry_term`, and `not_mlKemSampleNttStuckAt_of_s5_offset`.
   - `RwOnlyPred` / `BddPred` combinators for `mlkemActive_run_visitedIn` spatial locality hypotheses.
2. **Non-`SampleNTT` ML-KEM rows (`nonSnttAvoidS5`)**:
   - `c2_mlkemEncaps2_avoidS5` (`B20` `lsMlkemEncaps2Sym`, `mlkemEncaps2GhostAt c2MlkemMpl stk`).
   - `c2_mlkemValidatePk_avoidS5` (`B21` `lsMlkemValidatePkSym`,
     `mlkemValidatePkGhostAt c2MlkemMpl stk`, handling arbitrary caller `hdr`/`ek` slice lengths by
     splitting at `65536` bytes and proving `blk21_invalidLen_ok` on the early-exit prologue when
     either slice exceeds `65536` bytes).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (MlkemEncaps2Call MlkemValidatePkCall)
open CryptoVerification.SignalSession (
  CliHooks MlKemSampleNttStuckAt cliElfBytes cliExternsPlaced libsignalSessionLib
  lsKemDecapsSym lsKemEncapsSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemEncaps2Sym
  lsMlkemFromSeedSym lsMlkemValidatePkSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  externAt?_mlkemBlockProgram_ext_none mlkemEncaps2AtSpec mlkemValidatePkAtSpec withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved mlkemKeep mlkemRoOk_stripExecOutside stripS_mem
  stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2 (blk20_encaps2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  mlkemEncaps2CoreSpec mlkemEncaps2RawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk (
  blk21_validate_pk_validPk_ok mlkemValidatePkValidCoreSpec mlkemValidatePkValidRawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (blkPC21 blkPl21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  RetPost SavedFrame UnspilledSaved entails_sub seg_epilogue sepWP_elim_cell8 sepWP_elim_region32
  sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemPlacement mlkemCaller_ok mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkem768Encaps2List mlkem768Incremental mlkem768ValidPk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality (
  BoundedHeapIntervals RwOnlyHeap boundedHeapIntervals_memRegion boundedHeapIntervals_mono
  boundedHeapIntervals_pointsToBytes boundedHeapIntervals_pure boundedHeapIntervals_sepConj
  boundedHeapIntervals_stackAt rwOnlyHeap_memRegion rwOnlyHeap_pointsToBytes rwOnlyHeap_pure
  rwOnlyHeap_sepConj rwOnlyHeap_stackAt)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem (
  c2_mlkem_invMem_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkemKeep_lr_false c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg
  c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq c2_resolve_mlkem768Decaps_eq
  c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768Encaps2_eq c2_resolve_mlkem768FromSeed_eq
  c2_resolve_mlkem768ValidatePk_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG_activeRealPre_of_noException linkedCallHookG_eq_of_guard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer (
  mlKemSampleNttStuckAt_iff mlkemSampleNttSyms mlkemSampleNttTermOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook (
  codeLoaded_mlkem_stripExecOutside mlkemActiveGuard mlkemBlockGhost
  mlkemBlockGhost_keepLr_false_of_noException mlkemEncaps2GhostAt mlkemInvMem
  mlkemValidatePkGhostAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (extract_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  mlkemEncaps2TightStack mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts f3RxSeg_realProg617_externAt_none)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore (
  StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality (
  c2_mlkemActiveInvMem_of_codeLoaded_roOk c2_mlkemActiveKeep_ne_s5Base
  mlkemActiveKeep mlkemActiveKeep_sub_c2MlkemKeep mlkemActive_run_visitedIn mlkemS5Blocks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det)

/-! ## 1. Shared `mlkemBlockGhost` & `StepsStrictAvoid` Trajectory Helpers -/

theorem setPC_self_of_pc_eq {u : State} {pc : BitVec 64} (h : u.pc = pc) :
    u.setPC pc = u := by
  cases u; dsimp [State.setPC] at *; subst h; rfl

theorem evalInst_eq_of_svc_eq {P₁ P₂ : Program} (h : P₁.svc = P₂.svc)
    (inst : Instr) (s : State) :
    P₁.evalInst inst s = P₂.evalInst inst s := by
  cases inst <;> try rfl
  case system isMrs imm16 =>
    cases isMrs
    · simp only [Program.evalInst, execInstWithSvc, h]
    · rfl

theorem stepsUntil_subroutineStop_of_visitedIn {u s sf : State}
    (hvis : h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg s sf)
    (hlr : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hstop_sf : SubroutineStop u sf) :
    StepsUntil emptyStdProg (SubroutineStop u) s sf := by
  induction hvis with
  | refl z => exact .refl z
  | @step z1 z2 _ hz1 hstep _ ih =>
    have hrun1 : z1.status = .Running := by cases hstep <;> assumption
    have hnot : ¬ SubroutineStop u z1 := by
      rintro (⟨hpc_lr, _, _⟩ | hp | ⟨_, he⟩ | ho)
      · rw [hpc_lr, hlr] at hz1; cases hz1
      · rw [hp] at hrun1; cases hrun1
      · rw [he] at hrun1; cases hrun1
      · rw [ho] at hrun1; cases hrun1
    exact .step hnot hstep (ih hstop_sf)

/-- Pin `mlkemBlockGhost c2MlkemMpl j master fallback u = sf` from any `c2MlkemKeep`-scoped
    returning execution `h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf`. -/
theorem mlkemBlockGhost_eq_of_visitedIn [LibsignalPlacement]
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {j : Nat} (hj : j < mlkemMultiLib.blocks.length)
    {α : Type} {master : Spec α} {fallback : State → State} {u sf : State}
    (hInvM : mlkemInvMem c2MlkemMpl u.mem)
    (hfr : ExecFrozen u.mem)
    (hnoex : ∀ msg, (mlkemBlockGhost c2MlkemMpl j master fallback u).status ≠ .Exception msg)
    (hpc : u.pc = c2MlkemMpl.base j)
    (hvis : h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf)
    (hret : Returned u sf)
    (hnsp : ProofLib.NonSyscallPreserved u sf) :
    mlkemBlockGhost c2MlkemMpl j master fallback u = sf := by
  classical
  have hGu : mlkemActiveGuard c2MlkemMpl u := hInvM
  have hActPre : ActiveRealPre (withLsRet master) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr : mlkemKeep c2MlkemMpl (u.readReg64 .lr) = false :=
    mlkemBlockGhost_keepLr_false_of_noException (fun _ h => c2_mlkemKeep_lr_false hLs_ls h) hnoex
  have hlr_c2 : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false := hlr
  have hset : u.setPC (c2MlkemMpl.base j) = u := setPC_self_of_pc_eq hpc
  have hstop : SubroutineStop u sf := Or.inl hret
  have huntil : StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (c2MlkemMpl.base j)) sf := by
    rw [hset]; exact stepsUntil_subroutineStop_of_visitedIn hvis hlr_c2 hstop
  have hcl_strip :
      (mlkemMultiLib.blockProgram c2MlkemMpl j).CodeLoaded
        (stripExecOutside (mlkemKeep c2MlkemMpl) u.mem) :=
    codeLoaded_mlkem_stripExecOutside hInvM.2.1 j hj
  have hfs_sf : sf.fs = u.fs := hnsp.2.2.2.2.2.2
  have hfst_sf : FsTraced IsFsC u sf := FsTraced.of_eq hnsp.1 (congrArg (·.files) hfs_sf)
  have hfr_sf : ExecFrozen sf.mem := ExecFrozen.of_perm_eq hfr (fun a => congrFun hnsp.2.1 a)
  have hReal : ActiveRealRun (mlkemKeep c2MlkemMpl) emptyStdProg
      (mlkemMultiLib.blockProgram c2MlkemMpl j) (c2MlkemMpl.base j) u :=
    ⟨hfr, hlr, hcl_strip, sf, huntil, hstop, hfs_sf, hfst_sf, hfr_sf⟩
  rw [mlkemBlockGhost, linkedCallHookG_eq_of_guard hGu]
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop

theorem visitedIn_mono_keep {D₁ D₂ : BitVec 64 → Bool} {P : Program} {a b : State}
    (hSub : ∀ pc, D₁ pc = true → D₂ pc = true)
    (h : h2fsgen_StepsVisitedIn D₁ P a b) :
    h2fsgen_StepsVisitedIn D₂ P a b := by
  induction h with
  | refl s => exact .refl s
  | step hd h1 _ ih => exact .step (hSub _ hd) h1 ih

/-- Lift `h2fsgen_StepsVisitedIn D emptyStdProg s sf` (`D ⊆ c2MlkemKeep c2MlkemMpl`) to
    `StepsStrictAvoid bad (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf`. -/
theorem stepsStrictAvoid_realProg617_of_visitedIn
    {D : BitVec 64 → Bool} {mpl mmpl : MultiPlacement} {bad : State → Prop}
    (hSub : ∀ a, D a = true → c2MlkemKeep c2MlkemMpl a = true)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks)
    (hNotBad : ∀ z : State, z.status = .Running → D z.pc = true → ¬ bad z)
    {s sf : State}
    (hvis : h2fsgen_StepsVisitedIn D emptyStdProg s sf) :
    StepsStrictAvoid bad (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf := by
  let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have hsvc : emptyStdProg.svc = P_real.svc := rfl
  induction hvis with
  | refl z => exact .refl z
  | @step z1 z2 _ hDz1 h1 _ ih =>
    have hrun1 : z1.status = .Running := by cases h1 <;> assumption
    have he1 : emptyStdProg.externAt? z1.pc = none := emptyStdProg_externAt_none z1.pc
    have he2 : P_real.externAt? z1.pc = none :=
      f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg (hSub z1.pc hDz1))
        (c2_mlkemKeep_noPanic (hSub z1.pc hDz1))
    have hfm : P_real.fetchMem z1.mem z1.pc = emptyStdProg.fetchMem z1.mem z1.pc := by
      unfold Program.fetchMem; rw [he1, he2]
    have hstep2 : Step P_real z1 z2 := by
      cases h1 with
      | @exec inst hr hfm1 =>
        rw [evalInst_eq_of_svc_eq hsvc inst z1]
        exact Step.exec hr (hfm.trans hfm1)
      | halt_unmapped hr hfm1 _ => exact Step.halt_unmapped hr (hfm.trans hfm1) he2
      | extern _ he _ _ => rw [he1] at he; cases he
      | extern_fault _ he _ => rw [he1] at he; cases he
    exact .step (hNotBad z1 hrun1 hDz1) hstep2 ih

/-- Single-instruction `emptyStdProg` step + `c2MlkemKeep` witness from a `blockProgram` fetch. -/
theorem step_emptyStdProg_of_mlkem_block_fetch {j : Nat}
    (hj : j < mlkemMultiLib.blocks.length) {s : State} {inst : Instr}
    (hcl : (mlkemMultiLib.blockProgram c2MlkemMpl j).CodeLoaded s.mem)
    (hf : (mlkemMultiLib.blockProgram c2MlkemMpl j).fetch s.pc = some inst)
    (hsvc0 : inst.isSvc0 = false)
    (hrun : s.status = .Running) :
    c2MlkemKeep c2MlkemMpl s.pc = true ∧ Step emptyStdProg s (execInst inst s) := by
  have hk : c2MlkemKeep c2MlkemMpl s.pc = true := by
    unfold c2MlkemKeep; rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    unfold ProofLib.progKeep; apply decide_eq_true
    have hf' := hf
    unfold Program.fetch Program.readWordOff at hf'
    split at hf'
    · simp at hf'
    · split at hf'
      · simp at hf'
      · split at hf'
        · rename_i b0 b1 b2 b3 tl hdrop
          have hlen := congrArg List.length hdrop
          rw [List.length_drop] at hlen
          simp only [List.length_cons] at hlen
          omega
        · simp at hf'
  have hfm_j : (mlkemMultiLib.blockProgram c2MlkemMpl j).fetchMem s.mem s.pc = some inst :=
    Program.fetchMem_of_fetch hcl hf
  have hext_j : (mlkemMultiLib.blockProgram c2MlkemMpl j).externAt? s.pc = none :=
    externAt?_mlkemBlockProgram_ext_none c2MlkemMpl hj (fun _ => none) s.pc
  have hext_e : emptyStdProg.externAt? s.pc = none := emptyStdProg_externAt_none s.pc
  have hfm_e : emptyStdProg.fetchMem s.mem s.pc = some inst := by
    unfold Program.fetchMem at hfm_j ⊢
    rwa [hext_j, ← hext_e] at hfm_j
  have heval : emptyStdProg.evalInst inst s = execInst inst s := by
    cases inst <;> simp [Instr.isSvc0] at hsvc0
    case system isMrs imm16 =>
      cases isMrs
      · simp at hsvc0
        simp [Program.evalInst, execInst, execInstWithSvc, hsvc0]
      · rfl
    all_goals rfl
  exact ⟨hk, heval ▸ Step.exec hrun hfm_e⟩

/-! ## 2. `mlkemSampleNttSyms` / `MlKemSampleNttStuckAt` Disjointness & Heap Predicates -/

@[expose] def RwOnlyPred (P : SepProp) : Prop := ∀ h, P.holds h → RwOnlyHeap h
@[expose] def BddPred (k : Nat) (P : SepProp) : Prop := ∀ h, P.holds h → BoundedHeapIntervals k 65536 h

theorem rwP_pure {P : Prop} : RwOnlyPred ⌜P⌝ := fun _ hh => rwOnlyHeap_pure hh
theorem rwP_bytes (a : BitVec 64) (bs : List (BitVec 8)) : RwOnlyPred (a ↦ₛ bs) :=
  fun _ hh => rwOnlyHeap_pointsToBytes a bs hh
theorem rwP_mem (a : BitVec 64) (n : Nat) : RwOnlyPred (memRegion a n) :=
  fun _ hh => rwOnlyHeap_memRegion a n hh
theorem rwP_stk (sp : BitVec 64) (n : Nat) : RwOnlyPred (stackAt sp n) :=
  fun _ hh => rwOnlyHeap_stackAt sp n hh
theorem rwP_sep {P Q : SepProp} (hp : RwOnlyPred P) (hq : RwOnlyPred Q) : RwOnlyPred (P ∗ Q) :=
  fun _ hh => rwOnlyHeap_sepConj hp hq hh

theorem bddP_pure {P : Prop} : BddPred 0 ⌜P⌝ := fun _ hh => boundedHeapIntervals_pure hh
theorem bddP_bytes (a : BitVec 64) (bs : List (BitVec 8)) (hl : bs.length ≤ 65536) :
    BddPred 1 (a ↦ₛ bs) := fun _ hh => boundedHeapIntervals_pointsToBytes a bs hl hh
theorem bddP_mem (a : BitVec 64) (n : Nat) (hl : n ≤ 65536) :
    BddPred 1 (memRegion a n) := fun _ hh => boundedHeapIntervals_memRegion a n hl hh
theorem bddP_stk (sp : BitVec 64) (n : Nat) (hl : n ≤ 65536) :
    BddPred 1 (stackAt sp n) := fun _ hh => boundedHeapIntervals_stackAt sp n hl hh
theorem bddP_sep {k₁ k₂ : Nat} {P Q : SepProp} (hp : BddPred k₁ P) (hq : BddPred k₂ Q) :
    BddPred (k₁ + k₂) (P ∗ Q) := fun _ hh => boundedHeapIntervals_sepConj hp hq hh
theorem bddP_to6 {k : Nat} {P : SepProp} (hk : k ≤ 6) (hp : BddPred k P) :
    ∀ h, P.holds h → BoundedHeapIntervals 6 65536 h :=
  fun _ hh => boundedHeapIntervals_mono hk (Nat.le_refl _) (hp _ hh)

theorem not_mem_mlkemSampleNttSyms_resolve_of_activeKeep {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) {pc : BitVec 64}
    (hk : mlkemActiveKeep c2MlkemMpl pc = true) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  simp only [mlkemSampleNttSyms, List.map, List.mem_cons, List.not_mem_nil, or_false]
  rw [show lsKemEncapsSym = _ from rfl, c2_resolve_kyber1024Encaps_eq hLs,
    show lsKemDecapsSym = _ from rfl, c2_resolve_kyber1024Decaps_eq hLs,
    show lsMlkemFromSeedSym = _ from rfl, c2_resolve_mlkem768FromSeed_eq hLs,
    show lsMlkemEncaps1Sym = _ from rfl, c2_resolve_mlkem768Encaps1_eq hLs,
    show lsMlkemDecapsSym = _ from rfl, c2_resolve_mlkem768Decaps_eq hLs]
  rintro (h | h | h | h | h)
  · exact c2_mlkemActiveKeep_ne_s5Base hk (by decide : 24 ∈ mlkemS5Blocks) h
  · exact c2_mlkemActiveKeep_ne_s5Base hk (by decide : 23 ∈ mlkemS5Blocks) h
  · exact c2_mlkemActiveKeep_ne_s5Base hk (by decide : 10 ∈ mlkemS5Blocks) h
  · exact c2_mlkemActiveKeep_ne_s5Base hk (by decide : 19 ∈ mlkemS5Blocks) h
  · exact c2_mlkemActiveKeep_ne_s5Base hk (by decide : 22 ∈ mlkemS5Blocks) h

theorem not_mlKemSampleNttStuckAt_of_activeKeep {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) {z : State}
    (hk : mlkemActiveKeep c2MlkemMpl z.pc = true) :
    ¬ MlKemSampleNttStuckAt mpl z := by
  rw [mlKemSampleNttStuckAt_iff]
  rintro ⟨sym, hmem, hpc, _⟩
  exact not_mem_mlkemSampleNttSyms_resolve_of_activeKeep hLs hk
    (hpc ▸ List.mem_map_of_mem hmem)

private theorem c2_s5_bases_inj {i j : Nat}
    (hi : i ∈ mlkemS5Blocks) (hj : j ∈ mlkemS5Blocks)
    (heq : c2MlkemMpl.base i = c2MlkemMpl.base j) : i = j := by
  have hall :
      (mlkemS5Blocks.all fun a =>
        mlkemS5Blocks.all fun b => (c2MlkemMpl.base a != c2MlkemMpl.base b) || (a == b)) = true := by
    decide
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hall i hi) j hj
  simp [heq] at h1
  exact h1

theorem resolve_mlkemSampleNttSyms_inj {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) {s₁ s₂ : String}
    (h1 : s₁ ∈ mlkemSampleNttSyms) (h2 : s₂ ∈ mlkemSampleNttSyms)
    (heq : libsignalSessionLib.resolve mpl s₁ = libsignalSessionLib.resolve mpl s₂) :
    s₁ = s₂ := by
  have hr24 : libsignalSessionLib.resolve mpl lsKemEncapsSym = c2MlkemMpl.base 24 :=
    c2_resolve_kyber1024Encaps_eq hLs
  have hr23 : libsignalSessionLib.resolve mpl lsKemDecapsSym = c2MlkemMpl.base 23 :=
    c2_resolve_kyber1024Decaps_eq hLs
  have hr10 : libsignalSessionLib.resolve mpl lsMlkemFromSeedSym = c2MlkemMpl.base 10 :=
    c2_resolve_mlkem768FromSeed_eq hLs
  have hr19 : libsignalSessionLib.resolve mpl lsMlkemEncaps1Sym = c2MlkemMpl.base 19 :=
    c2_resolve_mlkem768Encaps1_eq hLs
  have hr22 : libsignalSessionLib.resolve mpl lsMlkemDecapsSym = c2MlkemMpl.base 22 :=
    c2_resolve_mlkem768Decaps_eq hLs
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso
       simp only [hr24, hr23, hr10, hr19, hr22] at heq
       have hinj := c2_s5_bases_inj (by decide) (by decide) heq
       cases hinj)

theorem not_mlKemSampleNttStuckAt_of_entry_term {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) {sym : String} {u : State}
    (hsym : sym ∈ mlkemSampleNttSyms)
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hTerm : mlkemSampleNttTermOf sym u) :
    ¬ MlKemSampleNttStuckAt mpl u := by
  rw [mlKemSampleNttStuckAt_iff]
  rintro ⟨sym', hmem', hpc', hnot'⟩
  have hsame : sym = sym' :=
    resolve_mlkemSampleNttSyms_inj hLs hsym hmem' (hpc.symm.trans hpc')
  subst hsame
  exact hnot' hTerm

theorem not_mlKemSampleNttStuckAt_of_s5_offset {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {j off : Nat} (hj : j ∈ mlkemS5Blocks) (hoff0 : 0 < off)
    (hoff_len : off < min 32 (mlkemMultiLib.blockLib j).text.code.length)
    {z : State} (hpc : z.pc = c2MlkemMpl.base j + BitVec.ofNat 64 off) :
    ¬ MlKemSampleNttStuckAt mpl z := by
  have hall :
      (mlkemS5Blocks.all fun a =>
        (List.range (min 32 (mlkemMultiLib.blockLib a).text.code.length)).all fun d =>
          (d == 0) || mlkemS5Blocks.all fun k =>
            c2MlkemMpl.base a + BitVec.ofNat 64 d != c2MlkemMpl.base k) = true := by
    decide
  have hrow := List.all_eq_true.mp (List.all_eq_true.mp hall j hj) off (List.mem_range.mpr hoff_len)
  have hd0 : (off == 0) = false := beq_false_of_ne (by omega)
  rw [hd0, Bool.false_or] at hrow
  have hne : ∀ k ∈ mlkemS5Blocks, c2MlkemMpl.base j + BitVec.ofNat 64 off ≠ c2MlkemMpl.base k :=
    fun k hk => bne_iff_ne.mp (List.all_eq_true.mp hrow k hk)
  rw [mlKemSampleNttStuckAt_iff]
  rintro ⟨sym, hmem, hzpc, _⟩
  rw [hpc] at hzpc
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · rw [c2_resolve_kyber1024Encaps_eq hLs] at hzpc; exact hne 24 (by decide) hzpc
  · rw [c2_resolve_kyber1024Decaps_eq hLs] at hzpc; exact hne 23 (by decide) hzpc
  · rw [c2_resolve_mlkem768FromSeed_eq hLs] at hzpc; exact hne 10 (by decide) hzpc
  · rw [c2_resolve_mlkem768Encaps1_eq hLs] at hzpc; exact hne 19 (by decide) hzpc
  · rw [c2_resolve_mlkem768Decaps_eq hLs] at hzpc; exact hne 22 (by decide) hzpc

/-! ## 3. Row `B20`: `mlkemEncaps2GhostAt` (`lsMlkemEncaps2Sym`) -/

private def encaps2TightMaster (x : MlkemEncaps2Call) : Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.esA ∧ s.readReg64 .x1 = x.ekA⌝ ∗
      (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      memRegion x.ret 128 ∗ stackAt s.sp 6128
  post := fun _ s0 _ =>
    (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      (x.ret ↦ₛ mlkem768Encaps2List x.es.toList x.ek.toList) ∗ stackAt s0.sp 6128
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem encaps2Core_simulates_tight (x : MlkemEncaps2Call) (mpl : MultiPlacement) :
    SpecSimulates (mlkemEncaps2CoreSpec mpl) (withMlKemRoOk mpl (encaps2TightMaster x)) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, encaps2TightMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  refine ⟨(x.ret, x.esA, x.es.toList, x.ekA, x.ek.toList), R, ?_, ?_⟩
  · dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved, mlkemEncaps2RawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, x.es.toList_length, x.ek.toList_length, hro⟩,
      Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved, mlkemEncaps2RawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [withMlKemRoOk, encaps2TightMaster]
    exact Satisfies.mono (by sep_frame) hpost.2

/-- Non-`SampleNTT` `StepsStrictAvoid` replay for `B20` (`mlkemEncaps2GhostAt c2MlkemMpl stk`). -/
theorem c2_mlkemEncaps2_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    {stk : Nat} (hstk : mlkemEncaps2TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkemEncaps2Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemEncaps2GhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemEncaps2GhostAt c2MlkemMpl stk u) := by
  have hInvM : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hInvA := c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2
  have hpc20 : u.pc = c2MlkemMpl.base 20 := hpc.trans (c2_resolve_mlkem768Encaps2_eq hLs)
  obtain ⟨_, hsp, x, R, hpre_ls⟩ := linkedCallHookG_activeRealPre_of_noException hnoex
  have hpre_at : u.mem ⊨ (mlkemEncaps2AtSpec stk mlkem768Incremental).pre x u ∗ R := by
    simpa only [keepsFs] using (extract_withLsRet hpre_ls).2
  dsimp only [mlkemEncaps2AtSpec] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre_at
  obtain ⟨hpure_u, hspat⟩ := hpre_at
  rw [stackAt_shrink u.sp stk 6128 hstk hfit] at hspat
  let slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 6128)
  have hpre_tight : u.mem ⊨ (encaps2TightMaster x).pre () u ∗ (slack ∗ R) := by
    dsimp only [encaps2TightMaster, slack]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure_u, Satisfies.mono (by sep_frame) hspat⟩
  obtain ⟨sf, hvis_act, hret, _, _, _, hnsp, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 20) (by decide) c2MlkemMpl blk20_encaps2_ok
      (encaps2Core_simulates_tight x) rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_mem _ _) (rwP_stk _ _)))))
      (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure
        (bddP_sep (bddP_bytes _ _ (by rw [x.es.toList_length]; decide))
          (bddP_sep (bddP_bytes _ _ (by rw [x.ek.toList_length]; decide))
            (bddP_sep (bddP_mem _ _ (by decide)) (bddP_stk _ _ (by decide)))))))
      (fun _ _ _ => rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _) (rwP_stk _ _))))
      hpc20 hrun hsp hInvA hpre_tight
  have hvis_c2 := visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act
  have hghost_eq : mlkemEncaps2GhostAt c2MlkemMpl stk u = sf :=
    mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc20 hvis_c2 hret hnsp
  rw [hghost_eq]
  exact stepsStrictAvoid_realProg617_of_visitedIn
    (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
    (fun _ _ hk => not_mem_mlkemSampleNttSyms_resolve_of_activeKeep hLs hk) hvis_act

/-! ## 4. Row `B21`: `mlkemValidatePkGhostAt` (`lsMlkemValidatePkSym`) -/

private def validatePkBoundedMaster (x : MlkemValidatePkCall) : Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = x.hdrA ∧ (s.readReg64 .x1).toNat = x.hdr.length ∧
      s.readReg64 .x2 = x.ekA ∧ (s.readReg64 .x3).toNat = x.ek.length⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s.sp 5824
  post := fun _ s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = 255#8 ↔ mlkem768ValidPk x.hdr x.ek = true⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s0.sp 5824
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem validatePkCore_simulates_bounded (x : MlkemValidatePkCall) (mpl : MultiPlacement) :
    SpecSimulates (mlkemValidatePkValidCoreSpec mpl)
      (withMlKemRoOk mpl (validatePkBoundedMaster x)) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, validatePkBoundedMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hx3⟩, hm⟩
  refine ⟨(x.hdrA, x.hdr, x.ekA, x.ek), R, ?_, ?_⟩
  · dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved, mlkemValidatePkValidRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hro⟩, Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkValidRawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hsp_post := hpost.2
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsp_post
    dsimp only [withMlKemRoOk, validatePkBoundedMaster]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hsp_post.1, Satisfies.mono (by sep_frame) hsp_post.2⟩

/-- Early-exit (`¬ (x1 = 64#64 ∧ x3 = 1152#64)`) raw contract for `B21`, owning ONLY
    `stackAt s0.sp 5824` so arbitrarily large caller slices stay framed outside `pre`. -/
private def mlkemValidatePkInvalidLenRawSpec (mpl : MultiPlacement) : Spec Unit where
  pre := fun _ s0 =>
    ⌜¬ (s0.readReg64 .x1 = 64#64 ∧ s0.readReg64 .x3 = 1152#64) ∧ MlKemRoOk mpl s0.mem⌝ ∗
      stackAt s0.sp 5824
  post := fun _ s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = 0#8⌝ ∗ stackAt s0.sp 5824
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def mlkemValidatePkInvalidLenCoreSpec (mpl : MultiPlacement) : Spec Unit :=
  withNonSyscallPreserved (mlkemValidatePkInvalidLenRawSpec mpl)

private theorem stackAt_prologue_split_local (sp0 : BitVec 64) :
    stackAt sp0 5824 =
      memRegion (sp0 - 4160#64) 8 ∗
      memRegion (sp0 - 64#64) 32 ∗
      memRegion (sp0 - 32#64) 32 ∗
      memRegion (sp0 - 4784#64) 624 ∗
      memRegion (sp0 - 4152#64) 4088 ∗
      stackAt (sp0 - 4784#64) 1040 := by
  have htop :
      stackAt sp0 5824 =
        stackAt (sp0 - 4784#64) 1040 ∗ memRegion (sp0 - 4784#64) 4720 ∗
          memRegion (sp0 - 64#64) 64 := by
    unfold stackAt
    have h1 : sp0 - 4784#64 - 1040#64 = sp0 - 5824#64 := by bv_omega
    rw [show memRegion (sp0 - BitVec.ofNat 64 5824) 5824 = memRegion (sp0 - 5824#64) 5824 from rfl,
      show memRegion (sp0 - 4784#64 - BitVec.ofNat 64 1040) 1040 =
        memRegion (sp0 - 5824#64) 1040 from congrArg (memRegion · 1040) h1]
    rw [memRegion_split' (b' := sp0 - 4784#64) (n := 1040) (k := (4784 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 64#64) (n := 4720) (k := 64) rfl (by bv_omega) (by decide)]
  have hmid :
      memRegion (sp0 - 4784#64) 4720 =
        memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4160#64) 8 ∗
          memRegion (sp0 - 4152#64) 4088 := by
    rw [memRegion_split' (b' := sp0 - 4160#64) (n := 624) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4152#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  have hhi :
      memRegion (sp0 - 64#64) 64 =
        memRegion (sp0 - 64#64) 32 ∗ memRegion (sp0 - 32#64) 32 :=
    memRegion_split' (b' := sp0 - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)
  rw [htop, hmid, hhi]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem probe_restore_entails_local (sp0 v : BitVec 64) :
    ((sp0 - 4160#64) ↦₆₄ v) ∗ memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4152#64) 4088 ⊢
      memRegion (sp0 - 4784#64) 4720 := by
  have hmid :
      memRegion (sp0 - 4784#64) 4720 =
        memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4160#64) 8 ∗
          memRegion (sp0 - 4152#64) 4088 := by
    rw [memRegion_split' (b' := sp0 - 4160#64) (n := 624) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4152#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hmid]
  exact entails_sub (pointsTo64_entails_memRegion (sp0 - 4160#64) v) (by sep_frame) (by sep_frame)

private theorem seg1_prologue_local [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 : State) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 44#64) s0
      (stackAt s0.sp 5824 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 4784#64 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x0 = 0#64 ∧
        s1.pstate = subsPState64 (s0.readReg64 .x1) 64#64 ∧
        UnspilledSaved s0 s1 ∧
        (P1 ⊢ SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗
          stackAt (s0.sp - 4784#64) 1040 ∗ F)) := by
  rw [stackAt_prologue_split_local s0.sp]
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 4160#64)); intro p0
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro f0 f1 f2 f3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro f4 f5 f6 f7
  have a1 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have a2 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have a3 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_omega
  have a5 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  have a6 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_omega
  have a7 : s0.sp - 32#64 + 24#64 = s0.sp - 8#64 := by bv_omega
  rw [a1, a2, a3, a5, a6, a7]
  have hsp64 : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 hsp0 (by decide)
  have hsp4160 : ((s0.sp - 64#64 - 4096#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 64#64) 4096#64 hsp64 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩, ?_⟩
  unfold SavedFrame
  exact entails_sub (probe_restore_entails_local s0.sp 0#64) (by sep_frame) (by sep_frame)

private theorem sepWP_mono_ret0 {prog : Program} {s0 s : State} {P : SepProp}
    (hwp : SepWP prog (s0.readReg64 .lr) s P
      (RetPost s0 ((s.readReg64 .x0).setWidth 8) emp))
    (h0 : (s.readReg64 .x0).setWidth 8 = 0#8) :
    SepWP prog (s0.readReg64 .lr) s P (RetPost s0 0#8 emp) :=
  SepWP.mono hwp (fun _ _ _ _ hp => by simpa [RetPost, h0] using hp)

private theorem blk21_invalidLen_raw_ok : MlKemBlockOk 21 mlkemValidatePkInvalidLenRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC21 blkPl21 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    mlkemValidatePkInvalidLenRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hnotLen, hro0⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 5824 ∗ emp, Satisfies.mono (by sep_frame) hspat, ?_⟩
  have hwp_all : SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s0
      (stackAt s0.sp 5824 ∗ emp) (RetPost s0 0#8 emp) := by
    refine sepWP_seq_env hcl0 hro0
      (seg1_prologue_local hb hbase s0 emp hpc hrun hsp0) ?_
    intro s1 P1 hpc1 hrun1 _ _ ⟨hsp1, hx3_1, hx0_1, hps1, hus1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    wp_step
    wp_if hne1
    · exact sepWP_mono_ret0
        (seg_epilogue hb hbase s0 _ emp
          (by simp [wp_norm, arm64_norm]) (by simp [hrun1]) (by simp [hsp1]) hsp0
          ⟨by simp [hus1.1], by simp [hus1.2.1], by simp [hus1.2.2.1], by simp [hus1.2.2.2.1],
            by simpa using hus1.2.2.2.2⟩)
        (by simp [hx0_1])
    · have hx1_eq : s0.readReg64 .x1 = 64#64 := by simpa using hne1
      wp_steps 2
      wp_if hne2
      · exact sepWP_mono_ret0
          (seg_epilogue hb hbase s0 _ emp
            (by simp [wp_norm, arm64_norm]) (by simp [hrun1]) (by simp [hsp1]) hsp0
            ⟨by simp [hus1.1], by simp [hus1.2.1], by simp [hus1.2.2.1], by simp [hus1.2.2.2.1],
              by simpa using hus1.2.2.2.2⟩)
          (by simp [hx0_1])
      · exfalso
        have hx3_eq : s0.readReg64 .x3 = 1152#64 := by simpa [hx3_1] using hne2
        exact hnotLen ⟨hx1_eq, hx3_eq⟩
  refine SepWP.mono hwp_all ?_
  intro sf Pf _ _ ⟨hx0_sf, hsp_sf, hcs_sf, hPf⟩
  refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hx0_sf, Satisfies.mono (by sep_frame) hm1⟩

private theorem blk21_invalidLen_ok : MlKemBlockOk 21 mlkemValidatePkInvalidLenCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk21_invalidLen_raw_ok (by decide)
    (h_pre := fun mpl _ _R _s0 h => by
      dsimp only [mlkemValidatePkInvalidLenRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2⟩, h.2⟩)
    (h_post := fun _mpl _ _R _s0 _sf _ h => by
      dsimp only [mlkemValidatePkInvalidLenRawSpec] at h ⊢
      simpa only [stripS_readReg64, stripS_sp] using h)

private def validatePkInvalidMaster (hguard : State → Prop) : Spec Unit where
  pre := fun _ s => ⌜hguard s⌝ ∗ stackAt s.sp 5824
  post := fun _ s0 sf => ⌜(sf.readReg64 .x0).setWidth 8 = 0#8⌝ ∗ stackAt s0.sp 5824
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem validatePkInvalidCore_simulates (mpl : MultiPlacement) :
    SpecSimulates (mlkemValidatePkInvalidLenCoreSpec mpl)
      (withMlKemRoOk mpl
        (validatePkInvalidMaster
          (fun s => ¬ (s.readReg64 .x1 = 64#64 ∧ s.readReg64 .x3 = 1152#64)))) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, validatePkInvalidMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hnot, hm⟩
  refine ⟨(), R, ?_, ?_⟩
  · dsimp only [mlkemValidatePkInvalidLenCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkInvalidLenRawSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hnot, hro⟩, hm⟩
  · intro sf _ _ hpost
    dsimp only [mlkemValidatePkInvalidLenCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkInvalidLenRawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

/-- Non-`SampleNTT` `StepsStrictAvoid` replay for `B21` (`mlkemValidatePkGhostAt c2MlkemMpl stk`). -/
theorem c2_mlkemValidatePk_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    {stk : Nat} (hstk : mlkemValidatePkTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkemValidatePkSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemValidatePkGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemValidatePkGhostAt c2MlkemMpl stk u) := by
  have hInvM : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hInvA := c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2
  have hpc21 : u.pc = c2MlkemMpl.base 21 := hpc.trans (c2_resolve_mlkem768ValidatePk_eq hLs)
  obtain ⟨_, hsp, x, R, hpre_ls⟩ := linkedCallHookG_activeRealPre_of_noException hnoex
  have hpre_at : u.mem ⊨ (mlkemValidatePkAtSpec stk mlkem768Incremental).pre x u ∗ R := by
    simpa only [keepsFs] using (extract_withLsRet hpre_ls).2
  dsimp only [mlkemValidatePkAtSpec] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_at
  obtain ⟨hpure_u, hspat⟩ := hpre_at
  rw [stackAt_shrink u.sp stk 5824 hstk hfit] at hspat
  let slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 5824)
  by_cases hlen : x.hdr.length ≤ 65536 ∧ x.ek.length ≤ 65536
  · have hpre_bdd : u.mem ⊨ (validatePkBoundedMaster x).pre () u ∗ (slack ∗ R) := by
      dsimp only [validatePkBoundedMaster, slack]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure_u, Satisfies.mono (by sep_frame) hspat⟩
    obtain ⟨sf, hvis_act, hret, _, _, _, hnsp, _, _⟩ :=
      mlkemActive_run_visitedIn (j := 21) (by decide) c2MlkemMpl blk21_validate_pk_validPk_ok
        (validatePkCore_simulates_bounded x) rfl rfl rfl
        (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
        (fun _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _)
          (rwP_sep (rwP_bytes _ _) (rwP_stk _ _))))
        (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure
          (bddP_sep (bddP_bytes _ _ hlen.1)
            (bddP_sep (bddP_bytes _ _ hlen.2) (bddP_stk _ _ (by decide))))))
        (fun _ _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _)
          (rwP_sep (rwP_bytes _ _) (rwP_stk _ _))))
        hpc21 hrun hsp hInvA hpre_bdd
    have hvis_c2 := visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act
    have hghost_eq : mlkemValidatePkGhostAt c2MlkemMpl stk u = sf :=
      mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc21 hvis_c2 hret hnsp
    rw [hghost_eq]
    exact stepsStrictAvoid_realProg617_of_visitedIn
      (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
      (fun _ _ hk => not_mem_mlkemSampleNttSyms_resolve_of_activeKeep hLs hk) hvis_act
  · obtain ⟨_, hx1, _, hx3⟩ := hpure_u
    have hnot64_1152 : ¬ (u.readReg64 .x1 = 64#64 ∧ u.readReg64 .x3 = 1152#64) := by
      rintro ⟨h1, h3⟩
      have hh : x.hdr.length = 64 := by simpa [h1] using hx1.symm
      have he : x.ek.length = 1152 := by simpa [h3] using hx3.symm
      exact hlen ⟨by omega, by omega⟩
    let M := validatePkInvalidMaster
      (fun s => ¬ (s.readReg64 .x1 = 64#64 ∧ s.readReg64 .x3 = 1152#64))
    have hpre_inv : u.mem ⊨ M.pre () u ∗ ((x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ slack ∗ R) := by
      dsimp only [M, validatePkInvalidMaster, slack]
      rw [sepConj_assoc, pure_sepConj_of_true hnot64_1152]
      exact Satisfies.mono (by sep_frame) hspat
    obtain ⟨sf, hvis_act, hret, _, _, _, hnsp, _, _⟩ :=
      mlkemActive_run_visitedIn (j := 21) (by decide) c2MlkemMpl blk21_invalidLen_ok
        validatePkInvalidCore_simulates rfl rfl rfl
        (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
        (fun _ _ => rwP_sep rwP_pure (rwP_stk _ _))
        (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure (bddP_stk _ _ (by decide))))
        (fun _ _ _ => rwP_sep rwP_pure (rwP_stk _ _))
        hpc21 hrun hsp hInvA hpre_inv
    have hvis_c2 := visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act
    have hghost_eq : mlkemValidatePkGhostAt c2MlkemMpl stk u = sf :=
      mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc21 hvis_c2 hret hnsp
    rw [hghost_eq]
    exact stepsStrictAvoid_realProg617_of_visitedIn
      (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
      (fun _ _ hk => not_mem_mlkemSampleNttSyms_resolve_of_activeKeep hLs hk) hvis_act

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt
