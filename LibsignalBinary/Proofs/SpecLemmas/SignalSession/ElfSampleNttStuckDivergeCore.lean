/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
import ProofLib.ProgramReflection

/-!
# Core Stuck-`SampleNTT` Ghost-vs-Real Case-Split Engine (`ElfSampleNttStuckDivergeCore`)

Proves the core `hStuckDiv` + `¬ CliReachesOOMPlaced` case-split engine from:
1. `GhostMainArmsFor mpl mmpl (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))`
   (`ElfSampleNttStuckDomainArms.v2F3StuckDomain_ghostMainCase_of_arms`),
2. `NamedHarnessBelow4b0000` and `NamedGhostStepsBelow4b0000` (provided by
   `ElfSampleNttStuckDivergeNamedAvoid`), and
3. `H2KSnttExtraFacts` over `(h2k_ghFixedK mpl mmpl).extra`.

Given `hStuck : CliReachesSampleNttStuckPlaced mpl mmpl cliElfImage W i` on any `V2F3StuckDomain`
input `i`, splits on whether the block-617 ghost trajectory `sm →* sr` visits a state strictly
before `sr` satisfying `BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf`:
- **Case A (hits `BadAtFamily`)**: extracts the first bad state `u_first` on `sm →* sr`, replays
  `s0 →* sm →* u_first` onto `Placed.cliProgPlacedSig mpl mmpl W`, dispatches the 5 `SampleNTT`
  entry rows into `MlKemSampleNttDiverge`, and concludes
  `cliRunPlacedSig mpl mmpl cliElfImage W i = none ∧ ¬ CliReachesOOMPlaced mpl mmpl cliElfImage W i`.
- **Case B (avoids `BadAtFamily` strictly before `sr`)**: lifts `sm →* sr` onto the termination-
  checked program `P_checkedSntt` (`snttCheckedExt`), appends musl exit `sr →* sx` (or keeps
  `.Panicked` at `sr`), lifts the full process trace `s0 →* s_end` via `stepsStrictAvoid_of_checkedSntt`
  onto `Placed.cliProgPlacedSig` strictly avoiding `.Running ∧ MlKemSampleNttStuckAt`, and
  contradicts `hStuck` by `Step` determinism.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open Arm64.Obj (MultiPlacedLib MultiPlacement)
open CryptoVerification
  (LibsignalFrozen LibsignalPlacement libsignalFrozen_of_keepsFrozen libsignalHookedExterns)
open CryptoVerification.SignalSession
  (CliHooks Inputs MlKemSampleNttStuckAt abortOnPanic cliElfBytes cliElfImage cliElf_staticOk
   cliExternsPlaced cliProcessInputs libsignalSessionLib loadState_status_running lsKemDecapsSym
   lsKemEncapsSym lsMemcpySym lsMemsetSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemFromSeedSym
   lsReadFileSym lsRustNoAllocShimSymCli lsStringCloneSym sigAbrt)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk InputsLoadable IsSendOverCap IsStdinOverCap MainCaseB2 MainResult RunAnswer
   loadState_fs_trace)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_eq_withExtra)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesOOMPlainPanPlaced CliReachesSampleNttStuckPlainPanPlaced
   cliRunPlainPanPlacedSig cliRunsToPlainPanPlaced_of_eq_some)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MuslHarnessFineNeedLocksGuardedPerInput b2MainEntryPreFine b2MainSpecTightNeedLocksFineAt
   cliBudgetLimits exit_frame_needLocks_n)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliProgExtPlacedSigAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
   cliStaticsPlacedAt externAt?_cliProgExtPlacedSigAt
   externAt?_cliProgExtPlacedSigAt_eq_none fetchMem_cliProgExtPlacedSigAt
   loadState_patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostSymActive cliExternsPlaced_preserves_execFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (noNewHooks_cliProgExtPlacedAt_of_ext_none_imp)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (F3C2EntryGuard c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
   c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraListReplaysOn ExtraRowReplayOn GhostSymActiveNamed GhostSymActiveWithExtra
   GhostSymActiveWithExtra_iff_named_or_extra cliGhostExternsWithExtra_eq_some_of_active
   cliGhostExternsWithExtra_nil_of_named cliGhostExternsWithExtra_none_imp
   cliGhostExternsWithExtra_some_cases extraListReplaysOn_arm)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet
  (Blk20TrapHook blk20_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
  (Blk21TrapHook blk21_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (AtCallRowReplayOn BadAtFamily badAtFamily_mlkemSampleNtt_iff
   mlKemSampleNttStuckAt_iff mlkemBlockGhost_activeRealPre_of_noException mlkemSampleNttSyms
   mlkemSampleNttSyms_subset_extra mlkemSampleNttTermOf mlkemSampleNttTermOf_kemDecaps
   mlkemSampleNttTermOf_kemEncaps mlkemSampleNttTermOf_mlkemDecaps
   mlkemSampleNttTermOf_mlkemEncaps1 mlkemSampleNttTermOf_mlkemFromSeed
   prefixExternReplaysUntil_of_atCallFamily stepsUntil_transfer_ghost
   steps_cliProgPlacedSig_of_running termOf_of_not_badAtFamily)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
  (kemDecapsGhostAt kemEncapsGhostAt mlkemDecapsGhostAt mlkemEncaps1GhostAt mlkemFromSeedGhostAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge
  (activeRealPre_of_withLsRet all_running_of_reaches_diverge
   kemDecaps_diverge_of_not_stateTerminates kemEncaps_diverge_of_not_stateTerminates
   mlkemDecaps_diverge_of_not_stateTerminates mlkemEncaps1_diverge_of_not_stateTerminates
   mlkemFromSeed_diverge_of_not_stateTerminates)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemFromSeedTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsBlocksLen libsignalBlocks_len lsInternedMultiLib ls_block617_externs_eq ls_sharedExterns_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3RxSeg_ghostProg617_externAt_entry)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk cliElf_frozen_of_linkedAt cliElf_tokenCellsPlacedAt_of_linkedAt
   f3CodeOk_of_plainLoadState keepsFrozen_cliTokenPatchPlacedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_firstStop_of_steps h2fsgen_step_det)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2RxDehookedSyms)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `StepsStrictAvoid` & `cliProgPlacedSig` Terminal Non-Visitation -/

/-- `P` steps from `s1` to `s3`, and every state strictly before `s3` along the trace
    satisfies `¬ bad`. -/
inductive StepsStrictAvoid (bad : State → Prop) (P : Program) : State → State → Prop where
  | refl (s : State) : StepsStrictAvoid bad P s s
  | step {s1 s2 s3 : State} :
      ¬ bad s1 → Step P s1 s2 → StepsStrictAvoid bad P s2 s3 → StepsStrictAvoid bad P s1 s3

theorem StepsStrictAvoid.toSteps {bad : State → Prop} {P : Program} {a b : State}
    (h : StepsStrictAvoid bad P a b) : Steps P a b := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ h1 _ ih => exact Steps.step h1 ih

theorem StepsStrictAvoid.trans {bad : State → Prop} {P : Program} {a b c : State}
    (hab : StepsStrictAvoid bad P a b) (hbc : StepsStrictAvoid bad P b c) :
    StepsStrictAvoid bad P a c := by
  induction hab with
  | refl _ => exact hbc
  | step hnb h1 _ ih => exact StepsStrictAvoid.step hnb h1 (ih hbc)

theorem StepsStrictAvoid.mono_bad {bad bad' : State → Prop} {P : Program} {a b : State}
    (hImp : ∀ z : State, bad' z → bad z) (h : StepsStrictAvoid bad P a b) :
    StepsStrictAvoid bad' P a b := by
  induction h with
  | refl s => exact StepsStrictAvoid.refl s
  | step hnb h1 _ ih => exact StepsStrictAvoid.step (fun hb' => hnb (hImp _ hb')) h1 ih

private theorem steps_eq_of_not_running_local {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    have hrun : s1.status = .Running := by cases h1 <;> assumption
    exact absurd hrun hnr

/-- If `s0 →* sf` strictly avoids `bad`, `sf.status ≠ .Running`, and `¬ bad sf`, then no state `u`
    reachable from `s0` on `P` can satisfy `bad u`. -/
theorem not_reaches_bad_of_stepsStrictAvoid_not_running {bad : State → Prop} {P : Program}
    {s0 sf u : State}
    (hAvoid : StepsStrictAvoid bad P s0 sf)
    (hnr_sf : sf.status ≠ .Running)
    (hnb_sf : ¬ bad sf)
    (hReach : Steps P s0 u) :
    ¬ bad u := by
  induction hAvoid with
  | refl s =>
    have heq : s = u := steps_eq_of_not_running_local hnr_sf hReach
    subst heq
    exact hnb_sf
  | @step s1 s2 _ hnb1 h1 _ ih =>
    cases hReach with
    | refl _ => exact hnb1
    | step h1' hrest =>
      have hs2 : s2 = _ := h2fsgen_step_det h1 h1'
      subst hs2
      exact ih hnr_sf hnb_sf hrest

/-- Convert `.Panicked` to `.Signaled sigAbrt`, leaving all other statuses unchanged. -/
@[expose] def toSigStateLocal (s : State) : State :=
  match s.status with
  | .Panicked => s.setStatus (.Signaled sigAbrt)
  | _ => s

private theorem abortOnPanic_eq_toSigStateLocal (h : State → State) (s : State) :
    abortOnPanic h s = toSigStateLocal (h s) := rfl

private theorem toSigStateLocal_of_ne_panicked {s : State} (h : s.status ≠ .Panicked) :
    toSigStateLocal s = s := by
  unfold toSigStateLocal
  split
  · rename_i hp; exact absurd hp h
  · rfl

private theorem toSigStateLocal_mem (s : State) : (toSigStateLocal s).mem = s.mem := by
  unfold toSigStateLocal; split <;> rfl

private theorem toSigStateLocal_symtab (s : State) : (toSigStateLocal s).symtab = s.symtab := by
  unfold toSigStateLocal; split <;> rfl

private theorem step_cliProgExtPlacedAt_to_sig_local {mpl : MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {s s' : State}
    (h : Step (cliProgExtPlacedAt mpl ext idx W) s s') :
    Step (cliProgExtPlacedSigAt mpl ext idx W) s (toSigStateLocal s') := by
  cases h with
  | @exec inst h_run h_fetch =>
    have hs_ne : s.status ≠ .Panicked := by rw [h_run]; nofun
    have h_ne : ((cliProgExtPlacedAt mpl ext idx W).evalInst inst s).status ≠ .Panicked :=
      evalInst_standard_status_ne_panicked rfl inst hs_ne
    rw [toSigStateLocal_of_ne_panicked h_ne]
    exact Step.exec h_run ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
  | halt_unmapped h_run h_fetch h_ext =>
    have h_ne : ({ s with status := .Halted } : State).status ≠ .Panicked := by nofun
    rw [toSigStateLocal_of_ne_panicked h_ne]
    exact Step.halt_unmapped h_run
      ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
      (externAt?_cliProgExtPlacedSigAt_eq_none.mpr h_ext)
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    rw [← abortOnPanic_eq_toSigStateLocal]
    refine Step.extern h_run h_ext_sig ?_ ?_
    · rw [abortOnPanic_eq_toSigStateLocal, toSigStateLocal_mem]; exact h_keep
    · rw [abortOnPanic_eq_toSigStateLocal, toSigStateLocal_symtab]; exact h_sym
  | @extern_fault f h_run h_ext h_nkeep =>
    have h_ne :
        ({ s with status := .Exception "extern hook modified read-only memory or symbol table" } :
          State).status ≠ .Panicked := by nofun
    rw [toSigStateLocal_of_ne_panicked h_ne]
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    refine Step.extern_fault h_run h_ext_sig ?_
    rw [abortOnPanic_eq_toSigStateLocal, toSigStateLocal_mem, toSigStateLocal_symtab]
    exact h_nkeep

/-- Lift `StepsStrictAvoid bad (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s0 sf`
    (`s0.status = .Running`) to `Placed.cliProgPlacedSig mpl mmpl W` ending at `toSigStateLocal sf`. -/
theorem stepsStrictAvoid_to_sig {mpl mmpl : MultiPlacement} {bad : State → Prop}
    {W : CliHooks} {s0 sf : State}
    (hrun0 : s0.status = .Running)
    (h : StepsStrictAvoid bad (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s0 sf) :
    StepsStrictAvoid bad (cliProgPlacedSig mpl mmpl W) s0 (toSigStateLocal sf) := by
  rw [← cliProgExtPlacedSigAt_cliExternsPlaced_eq]
  induction h with
  | refl s =>
    have hne : s.status ≠ .Panicked := by rw [hrun0]; nofun
    rw [toSigStateLocal_of_ne_panicked hne]
    exact StepsStrictAvoid.refl s
  | @step s1 s2 s3 hnb h1 h2 ih =>
    cases h2 with
    | refl _ =>
      exact StepsStrictAvoid.step hnb (step_cliProgExtPlacedAt_to_sig_local h1) (StepsStrictAvoid.refl _)
    | step _ h2a _ =>
      have hrun2 : s2.status = .Running := h2a.status_running
      have hne2 : s2.status ≠ .Panicked := by rw [hrun2]; nofun
      have h1' : Step (cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 W) s1 s2 := by
        have hs := step_cliProgExtPlacedAt_to_sig_local h1
        rwa [toSigStateLocal_of_ne_panicked hne2] at hs
      exact StepsStrictAvoid.step hnb h1' (ih hrun2)

/-! ## 2. Termination-Checked `SampleNTT` Program `P_checkedSntt` (`snttCheckedExt`) -/

private def orbitSum {Q : Type} (step : Q → Q) (w : Q → Nat) (q₀ : Q) : Nat → Nat
  | 0 => 0
  | n + 1 => orbitSum step w q₀ n + w (step^[n] q₀)

private theorem orbitSum_mono {Q : Type} (step : Q → Q) (w : Q → Nat) (q₀ : Q) :
    ∀ {m n : Nat}, m ≤ n → orbitSum step w q₀ m ≤ orbitSum step w q₀ n
  | _, 0, h => by
    have hm : _ = 0 := Nat.eq_zero_of_le_zero h
    subst hm; exact Nat.le_refl _
  | m, n + 1, h => by
    by_cases hmn : m ≤ n
    · exact Nat.le_trans (orbitSum_mono step w q₀ hmn) (Nat.le_add_right _ _)
    · have hm : m = n + 1 := by omega
      subst hm; exact Nat.le_refl _

private theorem orbitSum_add {Q : Type} (step : Q → Q) (w : Q → Nat) (q₀ : Q) (a : Nat) :
    ∀ k : Nat,
      orbitSum step w q₀ (a + k) = orbitSum step w q₀ a + orbitSum step w (step^[a] q₀) k
  | 0 => by simp [orbitSum]
  | k + 1 => by
    rw [← Nat.add_assoc, orbitSum, orbitSum_add step w q₀ a k, orbitSum, Nat.add_assoc,
      Nat.add_comm a k, Function.iterate_add_apply]

private theorem orbitSum_le_of_zero_from {Q : Type} (step : Q → Q) (w : Q → Nat) (q₀ : Q)
    {a : Nat} (hz : ∀ m, a ≤ m → w (step^[m] q₀) = 0) :
    ∀ n : Nat, orbitSum step w q₀ n ≤ orbitSum step w q₀ a
  | 0 => Nat.zero_le _
  | n + 1 => by
    by_cases han : a ≤ n
    · rw [orbitSum, hz n han, Nat.add_zero]
      exact orbitSum_le_of_zero_from step w q₀ hz n
    · exact orbitSum_mono step w q₀ (by omega)

private theorem iterate_periodic_zero {Q : Type} {step : Q → Q} {w : Q → Nat} {q₀ : Q}
    {a b : Nat} (hab : a < b) (hper : step^[b] q₀ = step^[a] q₀)
    (hz : ∀ i, a ≤ i → i < b → w (step^[i] q₀) = 0) :
    ∀ m, a ≤ m → w (step^[m] q₀) = 0 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro ham
    by_cases hmb : m < b
    · exact hz m ham hmb
    · have hbm : b ≤ m := by omega
      let m' := m - (b - a)
      have hm'_lt : m' < m := by omega
      have hm'_ge : a ≤ m' := by omega
      have hsplit : m = (m - b) + b := by omega
      have hsplit' : m' = (m - b) + a := by omega
      have hiter : step^[m] q₀ = step^[m'] q₀ := by
        rw [hsplit, Function.iterate_add_apply, hper, ← Function.iterate_add_apply, ← hsplit']
      rw [hiter]
      exact ih m' hm'_lt hm'_ge

private theorem orbitSum_progress {Q : Type} [Fintype Q] (step : Q → Q) (w : Q → Nat) (q₀ : Q)
    {a n : Nat} (hlt : orbitSum step w q₀ a < orbitSum step w q₀ n) :
    orbitSum step w q₀ a + 1 ≤ orbitSum step w q₀ (a + (Fintype.card Q + 1)) := by
  by_contra hnot
  have hzero_win : ∀ r < Fintype.card Q + 1, w (step^[a + r] q₀) = 0 := by
    intro r hr
    have h1 := orbitSum_mono step w q₀ (m := a + (r + 1)) (n := a + (Fintype.card Q + 1)) (by omega)
    have h2 : orbitSum step w q₀ a ≤ orbitSum step w q₀ (a + r) :=
      orbitSum_mono step w q₀ (by omega)
    rw [show a + (r + 1) = (a + r) + 1 by omega, orbitSum] at h1
    omega
  have hcard_lt : Fintype.card Q < Fintype.card (Fin (Fintype.card Q + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨r₁, r₂, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun r : Fin (Fintype.card Q + 1) => step^[a + r.1] q₀)
      hcard_lt
  have hne_val : r₁.1 ≠ r₂.1 := fun h => hne (Fin.ext h)
  have hrep : ∃ i j : Nat, i < j ∧ j < Fintype.card Q + 1 ∧ step^[a + j] q₀ = step^[a + i] q₀ := by
    rcases Nat.lt_or_gt_of_ne hne_val with h12 | h21
    · exact ⟨r₁.1, r₂.1, h12, r₂.2, heq.symm⟩
    · exact ⟨r₂.1, r₁.1, h21, r₁.2, heq⟩
  obtain ⟨r_lo, r_hi, hlo_hi, hhi_lt, hper⟩ := hrep
  have hz_from_lo : ∀ m, a + r_lo ≤ m → w (step^[m] q₀) = 0 :=
    iterate_periodic_zero (by omega) hper fun i hge hlt_b => by
      have hi_eq : i = a + (i - a) := by omega
      rw [hi_eq]
      exact hzero_win (i - a) (by omega)
  have hz_from_a : ∀ m, a ≤ m → w (step^[m] q₀) = 0 := fun m ham => by
    by_cases hmlo : m < a + r_lo
    · have hm_eq : m = a + (m - a) := by omega
      rw [hm_eq]
      exact hzero_win (m - a) (by omega)
    · exact hz_from_lo m (by omega)
  have hle_n := orbitSum_le_of_zero_from step w q₀ hz_from_a n
  omega

private theorem orbitSum_reach {Q : Type} [Fintype Q] (step : Q → Q) (w : Q → Nat) (q₀ : Q)
    {T : Nat} (hex : ∃ n, T ≤ orbitSum step w q₀ n) :
    ∀ k ≤ T, k ≤ orbitSum step w q₀ (k * (Fintype.card Q + 1))
  | 0, _ => Nat.zero_le _
  | k + 1, hkT => by
    obtain ⟨n, hn⟩ := hex
    have ih := orbitSum_reach step w q₀ ⟨n, hn⟩ k (by omega)
    let a := k * (Fintype.card Q + 1)
    by_cases hka : k + 1 ≤ orbitSum step w q₀ a
    · exact Nat.le_trans hka
        (orbitSum_mono step w q₀ (by show a ≤ (k + 1) * (Fintype.card Q + 1); simp [a, Nat.succ_mul]))
    · have hlt : orbitSum step w q₀ a < orbitSum step w q₀ n := by omega
      have hprog := orbitSum_progress step w q₀ hlt
      have heq_idx : a + (Fintype.card Q + 1) = (k + 1) * (Fintype.card Q + 1) := by
        simp [a, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add_right ih 1) (heq_idx ▸ hprog)

private abbrev KeccakQ := Fin 25 → Fin (2 ^ 64)

private def toKeccakQ (s : CryptoGames.SHA3.KeccakState) : KeccakQ :=
  fun i => (s.getD i.1 0#64).toFin

private def fromKeccakQ (q : KeccakQ) : CryptoGames.SHA3.KeccakState :=
  Array.ofFn fun i : Fin 25 => BitVec.ofFin (q i)

private theorem fromKeccakQ_toKeccakQ_getD (s : CryptoGames.SHA3.KeccakState) {idx : Nat}
    (h : idx < 25) :
    (fromKeccakQ (toKeccakQ s)).getD idx 0#64 = s.getD idx 0#64 := by
  simp [fromKeccakQ, toKeccakQ, Array.getD, h]

private theorem laneGet_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState) {x y : Nat}
    (hx : x < 5) (hy : y < 5) :
    CryptoGames.SHA3.laneGet (fromKeccakQ (toKeccakQ s)) x y = CryptoGames.SHA3.laneGet s x y := by
  unfold CryptoGames.SHA3.laneGet
  exact fromKeccakQ_toKeccakQ_getD s (by omega)

private def keccakColParity (s : CryptoGames.SHA3.KeccakState) : Array (BitVec 64) :=
  Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    CryptoGames.SHA3.laneGet s x 0 ^^^ CryptoGames.SHA3.laneGet s x 1 ^^^
    CryptoGames.SHA3.laneGet s x 2 ^^^ CryptoGames.SHA3.laneGet s x 3 ^^^
    CryptoGames.SHA3.laneGet s x 4

private def keccakDFromC (c : Array (BitVec 64)) : Array (BitVec 64) :=
  Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    c.getD ((x + 4) % 5) 0#64 ^^^ (c.getD ((x + 1) % 5) 0#64).rotateLeft 1

private def keccakThetaFromD (s : CryptoGames.SHA3.KeccakState) (d : Array (BitVec 64)) :
    CryptoGames.SHA3.KeccakState :=
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x := idx % 5
    let y := idx / 5
    CryptoGames.SHA3.laneGet s x y ^^^ d.getD x 0#64

private def keccakPostTheta (aTheta : CryptoGames.SHA3.KeccakState) (rc : BitVec 64) :
    CryptoGames.SHA3.KeccakState :=
  let bRhoPi : CryptoGames.SHA3.KeccakState := Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x' := idx % 5
    let y' := idx / 5
    let x := (x' + 3 * y') % 5
    let y := x'
    (CryptoGames.SHA3.laneGet aTheta x y).rotateLeft (CryptoGames.SHA3.keccakRhoOffset (5 * y + x))
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x := idx % 5
    let y := idx / 5
    let chi := CryptoGames.SHA3.laneGet bRhoPi x y ^^^
      ((~~~(CryptoGames.SHA3.laneGet bRhoPi ((x + 1) % 5) y)) &&&
        CryptoGames.SHA3.laneGet bRhoPi ((x + 2) % 5) y)
    if idx == 0 then chi ^^^ rc else chi

private theorem keccakF1600Round_eq_parts (s : CryptoGames.SHA3.KeccakState) (rc : BitVec 64) :
    CryptoGames.SHA3.keccakF1600Round s rc =
      keccakPostTheta (keccakThetaFromD s (keccakDFromC (keccakColParity s))) rc := rfl

private theorem keccakColParity_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState) :
    keccakColParity (fromKeccakQ (toKeccakQ s)) = keccakColParity s := by
  unfold keccakColParity
  apply congrArg (Array.ofFn (n := 5))
  funext ⟨x, hx⟩
  dsimp only
  rw [laneGet_fromKeccakQ_toKeccakQ s hx (by omega),
      laneGet_fromKeccakQ_toKeccakQ s hx (by omega),
      laneGet_fromKeccakQ_toKeccakQ s hx (by omega),
      laneGet_fromKeccakQ_toKeccakQ s hx (by omega),
      laneGet_fromKeccakQ_toKeccakQ s hx (by omega)]

private theorem keccakThetaFromD_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState)
    (d : Array (BitVec 64)) :
    keccakThetaFromD (fromKeccakQ (toKeccakQ s)) d = keccakThetaFromD s d := by
  unfold keccakThetaFromD
  apply congrArg (Array.ofFn (n := 25))
  funext ⟨idx, hidx⟩
  dsimp only
  rw [laneGet_fromKeccakQ_toKeccakQ s (by omega) (by omega)]

private theorem keccakF1600Round_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState)
    (rc : BitVec 64) :
    CryptoGames.SHA3.keccakF1600Round (fromKeccakQ (toKeccakQ s)) rc =
      CryptoGames.SHA3.keccakF1600Round s rc := by
  rw [keccakF1600Round_eq_parts, keccakF1600Round_eq_parts,
      keccakColParity_fromKeccakQ_toKeccakQ, keccakThetaFromD_fromKeccakQ_toKeccakQ]

private theorem keccakF1600_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState) :
    CryptoGames.SHA3.keccakF1600 (fromKeccakQ (toKeccakQ s)) = CryptoGames.SHA3.keccakF1600 s := by
  unfold CryptoGames.SHA3.keccakF1600 CryptoGames.SHA3.keccakRoundConstants
  simp only [List.foldl_cons, keccakF1600Round_fromKeccakQ_toKeccakQ]

private theorem keccakExtractRate21_fromKeccakQ_toKeccakQ (s : CryptoGames.SHA3.KeccakState) :
    CryptoGames.SHA3.keccakExtractRate 21 (fromKeccakQ (toKeccakQ s)) =
      CryptoGames.SHA3.keccakExtractRate 21 s := by
  unfold CryptoGames.SHA3.keccakExtractRate
  apply congrArg List.flatten
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  rw [fromKeccakQ_toKeccakQ_getD s (by omega)]

/-- Pigeonhole bound reducing `Shake128SeedTerminates` to the finite prefix of
`256 * ((2 ^ 64) ^ 25 + 1) + 3` SHAKE128 blocks over the 1,600-bit Keccak-f[1600] state space.
Note: this bound witnesses constructive decidability without altering `Shake128SeedTerminates`;
evaluating the full `(2 ^ 64) ^ 25` worst-case bound at runtime is infeasible. -/
theorem shake128SeedTerminates_iff_bounded (seed34 : List (BitVec 8)) :
    CryptoGames.MLKEM.Shake128SeedTerminates seed34 ↔
      256 ≤ (CryptoGames.MLKEM.parseRej12Candidates
        (CryptoGames.MLKEM.shake128FirstBlocks seed34 (256 * ((2 ^ 64) ^ 25 + 1) + 3))).length := by
  let N : Nat := 256 * ((2 ^ 64) ^ 25 + 1)
  change CryptoGames.MLKEM.Shake128SeedTerminates seed34 ↔
    256 ≤ (CryptoGames.MLKEM.parseRej12Candidates
      (CryptoGames.MLKEM.shake128FirstBlocks seed34 (N + 3))).length
  constructor
  · rintro ⟨extra, hge⟩
    let stepQ : KeccakQ → KeccakQ := fun q => toKeccakQ (CryptoGames.SHA3.keccakF1600 (fromKeccakQ q))
    let wQ : KeccakQ → Nat := fun q =>
      (CryptoGames.MLKEM.parseRej12Candidates (CryptoGames.SHA3.keccakExtractRate 21 (fromKeccakQ q))).length
    let s₀ := CryptoGames.SHA3.keccakAbsorb 21 0x1f#8 seed34
    have hperm : ∀ n : Nat, toKeccakQ (CryptoGames.SHA3.keccakPermuteN n s₀) = stepQ^[n] (toKeccakQ s₀) := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
        rw [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec.keccakPermuteN_succ_right,
          Function.iterate_succ_apply']
        dsimp only [stepQ]
        rw [← ih, keccakF1600_fromKeccakQ_toKeccakQ]
    have hsum : ∀ n : Nat,
        (CryptoGames.MLKEM.parseRej12Candidates (CryptoGames.MLKEM.shake128FirstBlocks seed34 n)).length =
          orbitSum stepQ wQ (toKeccakQ s₀) n := by
      intro n
      induction n with
      | zero =>
        simp [CryptoGames.MLKEM.shake128FirstBlocks, CryptoGames.SHA3.keccakSqueezeBlocks,
          CryptoGames.MLKEM.parseRej12Candidates, orbitSum]
      | succ k ih =>
        rw [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec.parseRej12Candidates_shake128FirstBlocks_succ,
          List.length_append, ih, orbitSum]
        apply congrArg (orbitSum stepQ wQ (toKeccakQ s₀) k + ·)
        rw [CryptoGames.SHA3.shake128BlockAt]
        dsimp only [wQ]
        rw [← hperm k]
        exact (congrArg (fun bs => (CryptoGames.MLKEM.parseRej12Candidates bs).length)
          (keccakExtractRate21_fromKeccakQ_toKeccakQ (CryptoGames.SHA3.keccakPermuteN k s₀))).symm
    have hreach : 256 ≤ orbitSum stepQ wQ (toKeccakQ s₀) (256 * (Fintype.card KeccakQ + 1)) :=
      orbitSum_reach stepQ wQ (toKeccakQ s₀) ⟨extra + 3, hsum (extra + 3) ▸ hge⟩ 256 (Nat.le_refl _)
    have hN_eq : 256 * (Fintype.card KeccakQ + 1) = N := by
      have hcard : Fintype.card KeccakQ = (2 ^ 64) ^ 25 := by
        simp [KeccakQ]
      dsimp only [N]
      rw [hcard]
    rw [hN_eq] at hreach
    have hreach' : 256 ≤ (CryptoGames.MLKEM.parseRej12Candidates
        (CryptoGames.MLKEM.shake128FirstBlocks seed34 N)).length := by
      rwa [hsum N]
    exact Nat.le_trans hreach'
      (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec.parseRej12Candidates_shake128_mono
        (Nat.le_add_right N 3))
  · intro h
    exact ⟨N, h⟩

local instance instDecidableShake128SeedTerminates (seed34 : List (BitVec 8)) :
    Decidable (CryptoGames.MLKEM.Shake128SeedTerminates seed34) :=
  decidable_of_iff _ (shake128SeedTerminates_iff_bounded seed34).symm

theorem shake128MatrixTerminates_iff_bounded (rho : List (BitVec 8)) (k : Nat) :
    CryptoGames.MLKEM.Shake128MatrixTerminates rho k ↔
      ∀ i < k, ∀ j < k,
        CryptoGames.MLKEM.Shake128SeedTerminates (rho.take 32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j]) :=
  ⟨fun h i hi j hj => h i j hi hj, fun h i j hi hj => h i hi j hj⟩

local instance instDecidableShake128MatrixTerminates (rho : List (BitVec 8)) (k : Nat) :
    Decidable (CryptoGames.MLKEM.Shake128MatrixTerminates rho k) :=
  decidable_of_iff _ (shake128MatrixTerminates_iff_bounded rho k).symm

local instance instDecidableMlkemSampleNttTermOf (sym : String) (u : State) :
    Decidable (mlkemSampleNttTermOf sym u) := by
  unfold mlkemSampleNttTermOf
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook.KemEncapsStateTerminates
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook.KemDecapsStateTerminates
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook.MlkemFromSeedStateTerminates
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook.MlkemEncaps1StateTerminates
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook.MlkemDecapsStateTerminates
  unfold CryptoGames.MLKEM.Kyber1024EncapsTerminates
  unfold CryptoGames.MLKEM.Kyber1024DecapsTerminates
  unfold CryptoGames.MLKEM.Mlkem768FromSeedTerminates
  unfold CryptoGames.MLKEM.Mlkem768Encaps1Terminates
  unfold CryptoGames.MLKEM.Mlkem768DecapsTerminates
  infer_instance

/-- Wrapper around a `mlkemSampleNttSyms` ghost hook `f_ghost` that raises `.Exception "sntt_stuck"`
    whenever `mlkemSampleNttTermOf sym u` fails and otherwise delegates to `f_ghost u`. -/
@[expose] def f_snttChecked (sym : String) (f_ghost : State → State) (u : State) :
    State :=
  if mlkemSampleNttTermOf sym u then f_ghost u
  else { u with status := .Exception "sntt_stuck" }

/-- Extern table installing `f_snttChecked sym f_ghost` on the 5 `mlkemSampleNttSyms` entries and
    delegating all other symbols to `cliExternsPlaced mmpl W`. -/
@[expose] noncomputable def snttCheckedExt (mmpl : MultiPlacement) (extra : ExtraGhostTable)
    (W : CliHooks) (sym : String) : Option (State → State) :=
  if mlkemSampleNttSyms.contains sym then (extra.lookup sym).map (f_snttChecked sym)
  else cliExternsPlaced mmpl W sym

private theorem mlkemSampleNttSyms_contains_iff (sym : String) :
    mlkemSampleNttSyms.contains sym = true ↔ sym ∈ mlkemSampleNttSyms :=
  List.contains_iff_mem

private theorem mlkemSampleNttSyms_sub_c2Rx {sym : String} (h : sym ∈ mlkemSampleNttSyms) :
    sym ∈ c2RxDehookedSyms := by
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem mlkemSampleNttSyms_sub_hooked {sym : String} (h : sym ∈ mlkemSampleNttSyms) :
    sym ∈ libsignalHookedExterns := by
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem mlkemSampleNttSyms_resolve_ge_4b0000 {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} (h : sym ∈ mlkemSampleNttSyms) :
    0x4b0000 ≤ (libsignalSessionLib.resolve mpl sym).toNat := by
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · rw [c2_resolve_kyber1024Encaps_eq hLs]; decide
  · rw [c2_resolve_kyber1024Decaps_eq hLs]; decide
  · rw [c2_resolve_mlkem768FromSeed_eq hLs]; decide
  · rw [c2_resolve_mlkem768Encaps1_eq hLs]; decide
  · rw [c2_resolve_mlkem768Decaps_eq hLs]; decide

private theorem findSome?_congr_local {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.findSome?_cons, h a (.head _)]
    rw [ih (fun x hx => h x (.tail _ hx))]

theorem externAt?_snttCheckedExt_eq_of_not_mem {mpl mmpl : MultiPlacement}
    (extra : ExtraGhostTable) (W : CliHooks) {pc : BitVec 64}
    (hnot : pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl)) :
    (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).externAt? pc =
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc := by
  rw [externAt?_cliProgExtPlacedAt_617, externAt?_cliProgExtPlacedAt_617]
  refine findSome?_congr_local _ _ _ fun e _ => ?_
  cases heq : libsignalSessionLib.resolve mpl e == pc with
  | false => rfl
  | true =>
    have hres : libsignalSessionLib.resolve mpl e = pc := beq_iff_eq.mp heq
    have hnc : mlkemSampleNttSyms.contains e = false := by
      cases hc : mlkemSampleNttSyms.contains e with
      | false => rfl
      | true =>
        exfalso
        exact hnot (hres ▸ List.mem_map_of_mem ((mlkemSampleNttSyms_contains_iff e).mp hc))
    simp only [↓reduceIte, snttCheckedExt, hnc, Bool.false_eq_true]

theorem snttChecked_externAt?_eq_of_lt_4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (extra : ExtraGhostTable) (W : CliHooks) {pc : BitVec 64}
    (hpc : pc.toNat < 0x4b0000) :
    (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).externAt? pc =
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc := by
  refine externAt?_snttCheckedExt_eq_of_not_mem extra W fun hmem => ?_
  obtain ⟨sym, hsym, rfl⟩ := List.mem_map.mp hmem
  exact Nat.not_lt.mpr (mlkemSampleNttSyms_resolve_ge_4b0000 hLs hsym) hpc

theorem externAt?_snttCheckedExt_entry {mpl mmpl : MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (extra : ExtraGhostTable) (W : CliHooks) {sym : String}
    (hsym : sym ∈ mlkemSampleNttSyms) :
    (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) =
      (extra.lookup sym).map (f_snttChecked sym) := by
  rw [f3RxSeg_ghostProg617_externAt_entry hExt
    (snttCheckedExt mmpl extra) W (mlkemSampleNttSyms_sub_c2Rx hsym)
    (mlkemSampleNttSyms_sub_hooked hsym)]
  have hc : mlkemSampleNttSyms.contains sym = true := (mlkemSampleNttSyms_contains_iff sym).mpr hsym
  simp only [snttCheckedExt, hc, ↓reduceIte]

private theorem step_of_externAt?_and_svc_eq {P1 P2 : Program} {s1 s2 : State}
    (hsvc : P2.svc = P1.svc)
    (hext : P2.externAt? s1.pc = P1.externAt? s1.pc)
    (h : Step P1 s1 s2) :
    Step P2 s1 s2 := by
  have hfm : P2.fetchMem s1.mem s1.pc = P1.fetchMem s1.mem s1.pc := by
    unfold Program.fetchMem
    rw [hext]
  cases h with
  | @exec inst hrun hfetch =>
    have hev : P2.evalInst inst s1 = P1.evalInst inst s1 := by
      unfold Program.evalInst execInstWithSvc
      rw [hsvc]
    rw [← hev]
    exact Step.exec hrun (hfm.trans hfetch)
  | halt_unmapped hrun hfetch hnone =>
    exact Step.halt_unmapped hrun (hfm.trans hfetch) (hext.trans hnone)
  | @extern f hrun hext1 hkf hsym =>
    exact Step.extern hrun (hext.trans hext1) hkf hsym
  | @extern_fault f hrun hext1 hnkf =>
    exact Step.extern_fault hrun (hext.trans hext1) hnkf

/-- Any `P_real` trace strictly avoiding the 5 `mlkemSampleNttSyms` entry `pc`s is a valid
    `P_checkedSntt` trace. -/
theorem steps_checkedSntt_of_real_avoidS5 {mpl mmpl : MultiPlacement}
    (extra : ExtraGhostTable) (W : CliHooks) {a b : State}
    (h : StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) a b) :
    Steps (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W) a b := by
  induction h with
  | refl s => exact Steps.refl s
  | step hnot h1 _ ih =>
    exact Steps.step
      (step_of_externAt?_and_svc_eq
        (P1 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (P2 := cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W)
        rfl (externAt?_snttCheckedExt_eq_of_not_mem (mmpl := mmpl) extra W hnot) h1)
      ih

/-! ## 3. Seam Interfaces (`NamedHarnessBelow4b0000`, `NamedGhostStepsBelow4b0000`, `H2KSnttExtraFacts`) -/

/-- Program-parametric startup + exit harness requiring `externAt?` agreement with `P_real`
    only at `pc.toNat < 0x4b0000` (provided by `ElfSampleNttStuckDivergeNamedAvoid`). -/
@[expose] def NamedHarnessBelow4b0000 (mpl mmpl : MultiPlacement) : Prop :=
  ∀ (P : Program) (W : CliHooks),
    P.svc = Syscall.standard →
    (∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) →
    MuslHarnessFineNeedLocksGuardedPerInput 80 (mallocngAddrsOfPlacement mmpl).libc
      cliElfImage P (mpl.base 617) cliProcessInputs mmpl
      cliBudgetLimits fineCostModel.init cliMainStk (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3C2EntryGuard mpl mmpl)

/-- Program-parametric replay of the 9 Block-`617` named ghost hooks (`GhostSymActiveNamed`) onto
    any program `P` agreeing with `P_real` at `pc.toNat < 0x4b0000`
    (provided by `ElfSampleNttStuckDivergeNamedAvoid`). -/
@[expose] def NamedGhostStepsBelow4b0000 [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (keepSub : BitVec 64 → Bool) (ghFixed : CliGhostHooks) : Prop :=
  ∀ (P : Program) (W : CliHooks),
    P.svc = Syscall.standard →
    (∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) →
    ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActiveNamed ghFixed sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps P u (f u)

/-- Named `CliGhostHooks` facts consumed by the stuck-`SampleNTT` divergence engine
    (instantiated at `keepSub := hole2_keepSub`, `ghFixed := h2k_ghFixedK mpl mmpl`). -/
structure GhostFixedFacts [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (keepSub : BitVec 64 → Bool) (ghFixed : CliGhostHooks) : Prop where
  realNone :
    ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActiveNamed ghFixed sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none
  noExLr :
    ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExternsWithExtra ghFixed [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      keepSub (a.readReg64 .lr) = false
  noExFds :
    ∀ {f : State → State} {a : State},
      cliGhostExterns ghFixed (fun _ => none) lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs
  trap21 :
    ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra ghFixed [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f
  trap20 :
    ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra ghFixed [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f
  blk21Ext :
    ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f
  blk20Ext :
    ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f
  preservesExecFrozen :
    ∀ {sym : String} {f : State → State},
      GhostSymActiveNamed ghFixed sym f →
      ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem

/-- 38-row `ExtraGhostTable` facts consumed by the stuck-`SampleNTT` divergence proof (instantiated
    at `ghFixed := h2k_ghFixedK mpl mmpl`, `extra := ghFixed.extra`). -/
structure H2KSnttExtraFacts [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable) : Prop where
  lookup_kemEncaps :
    ∃ stk, kemEncapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
      extra.lookup lsKemEncapsSym = some (kemEncapsGhostAt c2MlkemMpl stk)
  lookup_kemDecaps :
    ∃ stk, kemDecapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
      extra.lookup lsKemDecapsSym = some (kemDecapsGhostAt c2MlkemMpl stk)
  lookup_mlkemFromSeed :
    ∃ stk, mlkemFromSeedTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
      extra.lookup lsMlkemFromSeedSym = some (mlkemFromSeedGhostAt c2MlkemMpl stk)
  lookup_mlkemEncaps1 :
    ∃ stk, mlkemEncaps1TightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
      extra.lookup lsMlkemEncaps1Sym = some (mlkemEncaps1GhostAt c2MlkemMpl stk)
  lookup_mlkemDecaps :
    ∃ stk, mlkemDecapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
      extra.lookup lsMlkemDecapsSym = some (mlkemDecapsGhostAt c2MlkemMpl stk)
  atCallSntt :
    ∀ sym f, sym ∈ mlkemSampleNttSyms → extra.lookup sym = some f →
      AtCallRowReplayOn mpl (fun v : State => F3CodeInv mpl mmpl v.mem ∧ True)
        (cliExternsPlaced mmpl) sym (mlkemSampleNttTermOf sym) f
  replaysNonSntt :
    ∀ sym f, cliExtraGhostSyms.contains sym = true →
      mlkemSampleNttSyms.contains sym = false →
      extra.lookup sym = some f →
      ExtraRowReplayOn mpl mmpl (fun v : State => F3CodeInv mpl mmpl v.mem ∧ True)
        (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W'))
        sym (c2GuardOf mpl sym) f
  nonSnttAvoidS5 :
    ∀ (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W'))
        617 W
      let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      c2GuardOf mpl sym s0 →
      (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      cliExtraGhostSyms.contains sym = true →
      mlkemSampleNttSyms.contains sym = false →
      extra.lookup sym = some f →
      ∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f u) sf →
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        F3CodeInv mpl mmpl u.mem →
        StepsStrictAvoid
          (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
          P_real u (f u)
  snttStrictAvoid :
    ∀ (W : CliHooks) (sym : String) (f : State → State) (u : State),
      sym ∈ mlkemSampleNttSyms →
      extra.lookup sym = some f →
      mlkemSampleNttTermOf sym u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f u).mem →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        ExecFrozen (f u).mem

private theorem H2KSnttExtraFacts.lookup_isSome [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed extra)
    {sym : String} (hsym : sym ∈ mlkemSampleNttSyms) :
    ∃ f, extra.lookup sym = some f := by
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hsym
  rcases hsym with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, _, hlk⟩ := hExtra.lookup_kemEncaps; exact ⟨_, hlk⟩
  · obtain ⟨_, _, _, hlk⟩ := hExtra.lookup_kemDecaps; exact ⟨_, hlk⟩
  · obtain ⟨_, _, _, hlk⟩ := hExtra.lookup_mlkemFromSeed; exact ⟨_, hlk⟩
  · obtain ⟨_, _, _, hlk⟩ := hExtra.lookup_mlkemEncaps1; exact ⟨_, hlk⟩
  · obtain ⟨_, _, _, hlk⟩ := hExtra.lookup_mlkemDecaps; exact ⟨_, hlk⟩

private theorem steps_preserves_halted_local {P : Program} {s sf : State}
    (h : Steps P s sf) (hs : s.status = .Halted) : sf.status = .Halted := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem steps_preserves_exception_local {P : Program} {s sf : State} {msg : String}
    (h : Steps P s sf) (hs : s.status = .Exception msg) : sf.status = .Exception msg := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem execInst_preserves_execFrozen_local {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1)

private theorem evalInst_eq_execInst_of_not_isSvc0_local (P : Program) {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    P.evalInst inst s = execInst inst s := by
  cases inst <;> simp [Instr.isSvc0] at h
  case system isMrs imm16 =>
    cases isMrs
    · simp at h
      simp [Program.evalInst, execInst, execInstWithSvc, h]
    · rfl
  all_goals rfl

private theorem findSome?_table_exists_local (tbl : List (String × Nat))
    {ext : String → Option (State → State)} (off : Nat) {f : State → State}
    (h : (tbl.findSome? fun (n, o) => if o == off then ext n else none) = some f) :
    ∃ sym : String, ext sym = some f := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?_cons] at h
    cases hoo : (o == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h
      cases he : ext n with
      | none => rw [he] at h; exact ih h
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        exact ⟨n, he⟩

private theorem blockProgram_externAt?_some_exists_local
    {lib : MultiPlacedLib} {mpl : MultiPlacement} {idx : Nat}
    {ext : String → Option (State → State)} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx ext).externAt? pc = some f) :
    ∃ sym : String, ext sym = some f := by
  have h0 : ∀ L : List (String × Nat),
      (L.findSome? fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  unfold MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h
  simp only [ite_self] at h
  rw [h0, Option.or_none] at h
  exact findSome?_table_exists_local _ _ h

/-- Every non-`.Exception`, non-`.Halted` trace of `P_checkedSntt` lifts to a `P_real` trace
    strictly avoiding `.Running ∧ MlKemSampleNttStuckAt mpl`, preserving `ExecFrozen` & `F3CodeInv`. -/
theorem stepsStrictAvoid_of_checkedSntt [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed extra)
    {W : CliHooks} {a b : State}
    (hsteps : Steps (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W) a b)
    (hnoex_b : ∀ msg, b.status ≠ .Exception msg)
    (hnhalt_b : b.status ≠ .Halted)
    (hFr_a : ExecFrozen a.mem)
    (hInv_a : F3CodeInv mpl mmpl a.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) a b ∧
      ExecFrozen b.mem ∧ F3CodeInv mpl mmpl b.mem := by
  induction hsteps with
  | refl s => exact ⟨StepsStrictAvoid.refl s, hFr_a, hInv_a⟩
  | @step s1 s2 s3 h1 hrest ih =>
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_b (steps_preserves_halted_local hrest rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_b _ (steps_preserves_exception_local hrest rfl))
    | @exec inst hrun hfm =>
      have hfm_orig := hfm
      unfold Program.fetchMem at hfm
      cases hchk : (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).externAt? s1.pc with
      | some g => simp [hchk] at hfm
      | none =>
        have hnot_s5 : s1.pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
          intro hmem
          obtain ⟨sym, hsym, hpc_eq⟩ := List.mem_map.mp hmem
          obtain ⟨f_g, hlk⟩ := hExtra.lookup_isSome hsym
          have he := externAt?_snttCheckedExt_entry (mmpl := mmpl) hExt extra W hsym
          rw [hpc_eq, hlk] at he
          rw [he] at hchk
          cases hchk
        have hnb1 : ¬ (s1.status = .Running ∧ MlKemSampleNttStuckAt mpl s1) := by
          rintro ⟨_, hst⟩
          obtain ⟨sym, hsym, hpc_eq, _⟩ := (mlKemSampleNttStuckAt_iff mpl s1).mp hst
          exact hnot_s5 (hpc_eq ▸ List.mem_map_of_mem hsym)
        have her : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc = none :=
          (externAt?_snttCheckedExt_eq_of_not_mem (mmpl := mmpl) extra W hnot_s5).symm.trans hchk
        have hstep1_r :
            Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1
              ((cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).evalInst inst s1) :=
          step_of_externAt?_and_svc_eq
            (P1 := cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W)
            (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
            rfl (her.trans hchk.symm) (Step.exec hrun hfm_orig)
        have hFr2 :
            ExecFrozen ((cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).evalInst inst s1).mem := by
          by_cases hsvc0 : inst.isSvc0 = true
          · have hinst : inst = .system false 0#16 := by
              cases inst <;> simp [Instr.isSvc0] at hsvc0
              rcases hsvc0 with ⟨rfl, rfl⟩; rfl
            subst hinst
            have hev :
                (cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W).evalInst
                  (.system false 0#16) s1 = Syscall.standard s1 := by
              simp [Program.evalInst, execInstWithSvc, cliProgExtPlacedAt,
                MultiPlacedLib.blockProgram, Obj.PlacedLib.program]
            rw [hev]
            exact (standard_stripS (keep := fun _ => false) hFr_a).2
          · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
            rw [evalInst_eq_execInst_of_not_isSvc0_local _ hnsvc0 s1]
            exact execInst_preserves_execFrozen_local hnsvc0 hFr_a
        have hInv2 := hInv_a.of_keepsFrozen hstep1_r.keepsFrozen
        obtain ⟨hAvoidRest, hFr3, hInv3⟩ := ih hnoex_b hnhalt_b hFr2 hInv2
        exact ⟨StepsStrictAvoid.step hnb1 hstep1_r hAvoidRest, hFr3, hInv3⟩
    | @extern g hrun hchk hkf hsym =>
      by_cases hmem_s5 : s1.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl)
      · obtain ⟨sym, hsym_in, hpc_eq⟩ := List.mem_map.mp hmem_s5
        have he := externAt?_snttCheckedExt_entry (mmpl := mmpl) hExt extra W hsym_in
        rw [hpc_eq, hchk] at he
        cases hlk : extra.lookup sym with
        | none => rw [hlk] at he; cases he
        | some f_ghost =>
          rw [hlk] at he
          simp only [Option.map, Option.some.injEq] at he
          subst he
          have hnoex_g : ∀ msg, (f_snttChecked sym f_ghost s1).status ≠ .Exception msg :=
            fun msg hex => hnoex_b msg (steps_preserves_exception_local hrest hex)
          have hTerm : mlkemSampleNttTermOf sym s1 := by
            refine Classical.byContradiction fun hnot => ?_
            apply hnoex_g "sntt_stuck"
            unfold f_snttChecked
            simp [hnot]
          have hfg_eq : f_snttChecked sym f_ghost s1 = f_ghost s1 := by
            unfold f_snttChecked
            simp [hTerm]
          rw [hfg_eq] at hrest hkf hsym ih hnoex_g
          obtain ⟨hAvoidCall, hFr2⟩ :=
            hExtra.snttStrictAvoid W sym f_ghost s1 hsym_in hlk hTerm hpc_eq.symm hrun hnoex_g
              hkf hFr_a hInv_a
          have hInv2 := hInv_a.of_keepsFrozen hkf
          obtain ⟨hAvoidRest, hFr3, hInv3⟩ := ih hnoex_b hnhalt_b hFr2 hInv2
          exact ⟨hAvoidCall.trans hAvoidRest, hFr3, hInv3⟩
      · have her : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc = some g :=
          (externAt?_snttCheckedExt_eq_of_not_mem (mmpl := mmpl) extra W hmem_s5).symm.trans hchk
        have hnb1 : ¬ (s1.status = .Running ∧ MlKemSampleNttStuckAt mpl s1) := by
          rintro ⟨_, hst⟩
          obtain ⟨sym, hsym_in, hpc_eq, _⟩ := (mlKemSampleNttStuckAt_iff mpl s1).mp hst
          exact hmem_s5 (hpc_eq ▸ List.mem_map_of_mem hsym_in)
        obtain ⟨sym_ext, hsym_ext⟩ := blockProgram_externAt?_some_exists_local her
        have hFr2 : ExecFrozen (g s1).mem :=
          cliExternsPlaced_preserves_execFrozen mmpl W hsym_ext s1 hFr_a
        have hInv2 := hInv_a.of_keepsFrozen hkf
        have hstep1_r : Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1 (g s1) :=
          Step.extern hrun her hkf hsym
        obtain ⟨hAvoidRest, hFr3, hInv3⟩ := ih hnoex_b hnhalt_b hFr2 hInv2
        exact ⟨StepsStrictAvoid.step hnb1 hstep1_r hAvoidRest, hFr3, hInv3⟩

/-! ## 4. Strict-Prefix First-Bad Extraction & 5-Row Divergence Dispatch (Case A) -/

/-- Strict-prefix counterpart of `MlKemFirstStopTransfer.firstBadOnGhostRun_extract` requiring no
    `¬ BadAtFamily ... sf_end` assumption: if `u` lies strictly before `sf_end` (`Step P_ghost u u'`,
    `Steps P_ghost u' sf_end`) and satisfies `BadAtFamily`, then the first bad state `u_first` along
    `s0 →* u` also lies strictly before `sf_end`, so `(f u_first).status ≠ .Exception msg`. -/
theorem firstBadStrictPrefix_extract
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {W : CliHooks} {s0 sf_end : State}
    (hNoNewHooks : ∀ pc : BitVec 64,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hnoex_sf : ∀ msg, sf_end.status ≠ .Exception msg)
    (hnhalt_sf : sf_end.status ≠ .Halted)
    (hClassifyOnEnd :
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      let InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs
      ∀ (pc : BitVec 64) (f : State → State),
        P_ghost.externAt? pc = some f →
        (∃ sym : String,
          sym ∈ S ∧ pc = libsignalSessionLib.resolve mpl sym ∧
          AtCallRowReplayOn mpl InvS ER sym (termOf sym) f) ∨
        ((P_real.externAt? pc = some f ∧
            ∀ a : State,
              Steps P_ghost s0 a → Steps P_ghost (f a) sf_end →
              a.pc = pc → a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem → InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a → Steps P_ghost (f a) sf_end →
              a.pc = pc → a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false → InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))))
    (hSvcFs : ∀ z : State,
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      InvMem z.mem →
      PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ z : State,
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      Steps P_ghost s0 z →
      Steps P_ghost z sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false)
    {u u' : State}
    (hpre_u : Steps (cliProgExtPlacedAt mpl EG 617 W) s0 u)
    (hstep_u : Step (cliProgExtPlacedAt mpl EG 617 W) u u')
    (hsuf_u' : Steps (cliProgExtPlacedAt mpl EG 617 W) u' sf_end)
    (hbad_u : BadAtFamily mpl S termOf u) :
    let P_ghost := cliProgExtPlacedAt mpl EG 617 W
    let P_real  := cliProgExtPlacedAt mpl ER 617 W
    ∃ u_first : State,
      Steps P_real s0 u_first ∧
      BadAtFamily mpl S termOf u_first ∧
      ExecFrozen u_first.mem ∧
      InvMem u_first.mem ∧
      PredFs u_first.fs ∧
      (∀ f : State → State,
        P_ghost.externAt? u_first.pc = some f →
        ∀ msg, (f u_first).status ≠ .Exception msg) := by
  obtain ⟨u_first, huntil, hbad_uf, hmid_u⟩ := h2fsgen_firstStop_of_steps hpre_u hbad_u
  have hsuf_u : Steps (cliProgExtPlacedAt mpl EG 617 W) u sf_end := Steps.step hstep_u hsuf_u'
  have hsuf_uf : Steps (cliProgExtPlacedAt mpl EG 617 W) u_first sf_end := hmid_u.trans hsuf_u
  have hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg := fun msg hex =>
    hnoex_sf msg (steps_preserves_exception_local hsuf_uf hex)
  have hnhalt_uf : u_first.status ≠ .Halted := fun hhalt =>
    hnhalt_sf (steps_preserves_halted_local hsuf_uf hhalt)
  have hPref := prefixExternReplaysUntil_of_atCallFamily
    (keep := keep) (InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs)
    (EG := EG) (ER := ER) (S := S) (termOf := termOf)
    (W := W) (s0 := s0) (u_first := u_first) (sf_end := sf_end)
    fun pc f heg => by
      rcases hClassifyOnEnd pc f heg with hAt | (⟨her, ha1⟩ | ⟨hn, ha2⟩)
      · exact Or.inl hAt
      · exact Or.inr (Or.inl ⟨her, fun a hpre _ hre hpc hr hnx hkf hfr hinv =>
          ha1 a hpre hre hpc hr hnx hkf hfr hinv⟩)
      · exact Or.inr (Or.inr ⟨hn, fun a hpre _ hre hpc hr hnx hkf hfr hlr hinv =>
          ha2 a hpre hre hpc hr hnx hkf hfr hlr hinv⟩)
  obtain ⟨hsteps_real, hfr_uf, hinv_uf, hfs_uf⟩ :=
    stepsUntil_transfer_ghost
      (keep := keep) (InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs)
      (stop := BadAtFamily mpl S termOf)
      (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
      (P_real := cliProgExtPlacedAt mpl ER 617 W)
      rfl rfl hNoNewHooks huntil hsuf_uf
      hnoex_uf hnhalt_uf hFr0 ⟨hInv0, hFs0⟩ hPref
      (fun z inst _ _ _ _ _ _ _ hns hkf _ ⟨hinv, hfs⟩ =>
        ⟨hInvStable z.mem _ hinv hkf, by
          have hfs_eq := (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns z).2.2.2.2.2.2
          rwa [hfs_eq]⟩)
      (fun z _ hpre _ hre hrun heg hfm hkf hfr ⟨hinv, hfs⟩ =>
        ⟨hInvStable z.mem _ hinv hkf, hSvcFs z hpre hre hrun heg hfm hfr hinv hfs⟩)
      (fun z _ hpre _ hre hrun hne => hlr_calls z hpre hre hrun hne)
  have hnonempty : ∃ s1, Step (cliProgExtPlacedAt mpl EG 617 W) u_first s1 ∧
      Steps (cliProgExtPlacedAt mpl EG 617 W) s1 sf_end := by
    cases hmid_u with
    | refl _ => exact ⟨u', hstep_u, hsuf_u'⟩
    | step h1 hm => exact ⟨_, h1, hm.trans hsuf_u⟩
  obtain ⟨s1, h1, hrest1⟩ := hnonempty
  refine ⟨u_first, hsteps_real, hbad_uf, hfr_uf, hinv_uf, hfs_uf, ?_⟩
  intro f heg_uf
  cases h1 with
  | halt_unmapped _ _ _ =>
    exact False.elim (hnhalt_sf (steps_preserves_halted_local hrest1 rfl))
  | extern_fault _ _ _ =>
    exact False.elim (hnoex_sf _ (steps_preserves_exception_local hrest1 rfl))
  | exec _ hfm =>
    unfold Program.fetchMem at hfm
    simp [heg_uf] at hfm
  | @extern f' _ heg' _ _ =>
    rw [heg_uf] at heg'
    injection heg' with hf_eq
    subst hf_eq
    exact fun msg hex => hnoex_sf msg (steps_preserves_exception_local hrest1 hex)

/-- 5-row `SampleNTT` divergence dispatcher at `u_first` from `BadAtFamily`, `H2KSnttExtraFacts`,
    and non-`.Exception` of the ghost hook at `u_first.pc`. -/
theorem snttDiverge_of_badAtFamily [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed extra)
    (W : CliHooks) {u : State}
    (hBad : BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf u)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hNoEx : ∀ f : State → State,
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W'))
        617 W).externAt? u.pc = some f →
      ∀ msg, (f u).status ≠ .Exception msg) :
    ∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v → v.status = .Running := by
  obtain ⟨_, sym, hsym, hpc_u, hNotTerm⟩ := hBad
  have hDom : cliExtraGhostSyms.contains sym = true :=
    List.all_eq_true.mp mlkemSampleNttSyms_subset_extra sym hsym
  have heg_entry : ∀ f_g : State → State, extra.lookup sym = some f_g →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W'))
        617 W).externAt? u.pc = some f_g := by
    intro f_g hlk
    rw [hpc_u, f3RxSeg_ghostProg617_externAt_entry hExt _ W
      (mlkemSampleNttSyms_sub_c2Rx hsym) (mlkemSampleNttSyms_sub_hooked hsym)]
    exact cliGhostExternsWithExtra_eq_some_of_active ghFixed extra
      (cliExternsPlaced mmpl W)
      ((GhostSymActiveWithExtra_iff_named_or_extra _ _ _ _).mpr (Or.inr ⟨hDom, hlk⟩))
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hsym
  rcases hsym with rfl | rfl | rfl | rfl | rfl
  · rw [mlkemSampleNttTermOf_kemEncaps] at hNotTerm
    obtain ⟨stk, hstk, hfit, hlk⟩ := hExtra.lookup_kemEncaps
    have hnoex := hNoEx _ (heg_entry _ hlk)
    obtain ⟨hrun, hsp, x, R, hpre⟩ :=
      activeRealPre_of_withLsRet (mlkemBlockGhost_activeRealPre_of_noException hnoex)
    exact (kemEncaps_diverge_of_not_stateTerminates hstk hfit hLs hExt W hpc_u hrun hsp
      hInv hFr hpre hNotTerm).2
  · rw [mlkemSampleNttTermOf_kemDecaps] at hNotTerm
    obtain ⟨stk, hstk, hfit, hlk⟩ := hExtra.lookup_kemDecaps
    have hnoex := hNoEx _ (heg_entry _ hlk)
    obtain ⟨hrun, hsp, x, R, hpre⟩ :=
      activeRealPre_of_withLsRet (mlkemBlockGhost_activeRealPre_of_noException hnoex)
    exact (kemDecaps_diverge_of_not_stateTerminates hstk hfit hLs hExt W hpc_u hrun hsp
      hInv hFr hpre hNotTerm).2
  · rw [mlkemSampleNttTermOf_mlkemFromSeed] at hNotTerm
    obtain ⟨stk, hstk, hfit, hlk⟩ := hExtra.lookup_mlkemFromSeed
    have hnoex := hNoEx _ (heg_entry _ hlk)
    obtain ⟨hrun, hsp, x, R, hpre⟩ :=
      activeRealPre_of_withLsRet (mlkemBlockGhost_activeRealPre_of_noException hnoex)
    exact (mlkemFromSeed_diverge_of_not_stateTerminates hstk hfit hLs hExt W hpc_u hrun hsp
      hInv hFr hpre hNotTerm).2
  · rw [mlkemSampleNttTermOf_mlkemEncaps1] at hNotTerm
    obtain ⟨stk, hstk, hfit, hlk⟩ := hExtra.lookup_mlkemEncaps1
    have hnoex := hNoEx _ (heg_entry _ hlk)
    obtain ⟨hrun, hsp, x, R, hpre⟩ :=
      activeRealPre_of_withLsRet (mlkemBlockGhost_activeRealPre_of_noException hnoex)
    exact (mlkemEncaps1_diverge_of_not_stateTerminates hstk hfit hLs hExt W hpc_u hrun hsp
      hInv hFr hpre hNotTerm).2
  · rw [mlkemSampleNttTermOf_mlkemDecaps] at hNotTerm
    obtain ⟨stk, hstk, hfit, hlk⟩ := hExtra.lookup_mlkemDecaps
    have hnoex := hNoEx _ (heg_entry _ hlk)
    obtain ⟨hrun, hsp, x, R, hpre⟩ :=
      activeRealPre_of_withLsRet (mlkemBlockGhost_activeRealPre_of_noException hnoex)
    exact (mlkemDecaps_diverge_of_not_stateTerminates hstk hfit hLs hExt W hpc_u hrun hsp
      hInv hFr hpre hNotTerm).2

/-! ## 5. Ghost-to-`P_checkedSntt` Replay Along Non-Violating Trajectories (Case B) -/

set_option maxRecDepth 2000000 in
private theorem strClone_not_mem_lsNamesB_local :
    List.elem lsStringCloneSym lsInternedMultiLib.names = false := by
  rfl_kernel

private theorem strClone_not_mem_ext617_local :
    lsStringCloneSym ∉ (libsignalSessionLib.blockLib 617).text.externs := by
  intro hmem
  rw [ls_block617_externs_eq, List.mem_map] at hmem
  obtain ⟨idx, hidx_mem, hget⟩ := hmem
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx_mem)
  have hmem_names : lsStringCloneSym ∈ lsInternedMultiLib.names := by
    rw [← hget, Obj.Interned.getD_of_lt hlt]
    exact List.getElem_mem hlt
  have htrue : List.elem lsStringCloneSym lsInternedMultiLib.names = true :=
    List.elem_eq_true_of_mem hmem_names
  rw [strClone_not_mem_lsNamesB_local] at htrue
  cases htrue

private theorem pGhost617_codeLoaded_of_libsignalFrozen_local
    {mpl : MultiPlacement}
    (EG : CliHooks → String → Option (State → State))
    (W : CliHooks) (m : Memory)
    (hFrz : LibsignalFrozen mpl m) :
    (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m := by
  have h617 : 617 < libsignalSessionLib.blocks.length := by
    have hlen := Nat.beq_eq.mp libsignalBlocks_len
    have hge : 618 ≤ f3LsBlocksLen := by decide
    omega
  have hc := hFrz.2 617 h617
  exact Program.CodeLoaded.intro hc.aligned hc.no_wrap fun i hi =>
    ⟨hc.byte_eq i hi, hc.perm_eq i hi, hc.isLazyFree_eq i hi⟩

set_option maxRecDepth 400000 in
private theorem f3CodeOk_to_libsignalFrozen_local
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {m : Memory}
    (hCO : F3CodeOk mpl mmpl m) :
    LibsignalFrozen mpl m := by
  obtain ⟨inputs, sLoad, hload, hkf_load⟩ := hCO.1.fromLoad
  have htok := cliElf_tokenCellsPlacedAt_of_linkedAt hLs
  have hmap := loadState_patchElfTokensPlacedAt cliElf_staticOk htok inputs
  rw [hmap] at hload
  cases hraw : cliElfImage.loadState inputs with
  | error _ =>
    rw [hraw] at hload
    cases hload
  | ok sRaw =>
    rw [hraw] at hload
    simp only [Except.map, Except.ok.injEq] at hload
    have hkf0 : sRaw.mem.KeepsFrozen sLoad.mem := by
      rw [← hload]
      exact keepsFrozen_cliTokenPatchPlacedAt cliElf_staticOk htok hraw
    exact libsignalFrozen_of_keepsFrozen (cliElf_frozen_of_linkedAt hLs hraw) (hkf0.trans hkf_load)

private theorem findSome?_stubs_cliGhostExternsWithExtra_mem_cases_local
    (exts : List String) (ρ : String → BitVec 64) (base pc : BitVec 64)
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {f : State → State}
    (h : ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) =>
        if o == (pc - base).toNat then cliGhostExternsWithExtra ghFixed extra baseExt n
        else none) = some f) :
    ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then baseExt n else none) = some f ∨
    ∃ sym : String, sym ∈ exts ∧ GhostSymActiveWithExtra ghFixed extra sym f ∧ pc = ρ sym := by
  induction exts with
  | nil => simp at h
  | cons e tl ih =>
    simp only [List.map_cons, List.findSome?_cons] at h ⊢
    cases hoo : ((ρ e - base).toNat == (pc - base).toNat) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
      · exact Or.inl hL
      · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he : cliGhostExternsWithExtra ghFixed extra baseExt e with
      | none =>
        rw [he] at h
        rw [cliGhostExternsWithExtra_none_imp ghFixed extra baseExt he]
        rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
        · exact Or.inl hL
        · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        rcases cliGhostExternsWithExtra_some_cases ghFixed extra baseExt he with hAct | hBase
        · have heq : ρ e - base = pc - base := BitVec.eq_of_toNat_eq (beq_iff_eq.mp hoo)
          have hpc_eq : pc = ρ e := by
            have h1 := congrArg (· + base) heq.symm
            simpa only [BitVec.sub_add_cancel] using h1
          exact Or.inr ⟨e, List.Mem.head _, hAct, hpc_eq⟩
        · rw [hBase]
          exact Or.inl rfl

private theorem blockProgram_cliGhostExternsWithExtra_externAt?_mem_cases_local
    {lib : MultiPlacedLib} {mpl : MultiPlacement} {idx : Nat}
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx (cliGhostExternsWithExtra ghFixed extra baseExt)).externAt? pc =
      some f) :
    (lib.blockProgram mpl idx baseExt).externAt? pc = some f ∨
      ∃ sym : String, sym ∈ (lib.blockLib idx).text.externs ∧
        GhostSymActiveWithExtra ghFixed extra sym f ∧ pc = lib.resolve mpl sym := by
  have h0 : ∀ L : List (String × Nat),
      (L.findSome? fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  unfold MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h ⊢
  simp only [ite_self] at h ⊢
  rw [h0, Option.or_none] at h ⊢
  exact findSome?_stubs_cliGhostExternsWithExtra_mem_cases_local
    (lib.blockLib idx).text.externs (lib.blockPlacement mpl idx).ρ
    (lib.blockPlacement mpl idx).base pc ghFixed extra baseExt h

/-- Shared block-617 extern classification on `(sm, sr)` into:
    (i) the 5 `mlkemSampleNttSyms` rows (`AtCallRowReplayOn`),
    (ii) pass-through `cliExternsPlaced` hooks, or
    (iii) the 9 named + 33 non-`SampleNTT` `extra` rows replaying onto `P_real`. -/
private theorem classifyOnEnd_h2k [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    {keepSub : BitVec 64 → Bool} {ghFixed : CliGhostHooks}
    (hGh : GhostFixedFacts mpl mmpl keepSub ghFixed)
    (hNamedSteps : NamedGhostStepsBelow4b0000 mpl mmpl keepSub ghFixed)
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed ghFixed.extra)
    (W : CliHooks) {sm sr : State}
    (hG : F3C2EntryGuard mpl mmpl sm)
    (hret_pc : sr.status = .Running → sr.pc = sm.readReg64 .lr)
    (hnoex_sr : ∀ msg, sr.status ≠ .Exception msg)
    (hnhalt_sr : sr.status ≠ .Halted) :
    let EG := fun W' =>
      cliGhostExternsWithExtra ghFixed ghFixed.extra
        (cliExternsPlaced mmpl W')
    let P_ghost := cliProgExtPlacedAt mpl EG 617 W
    let P_real  := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    let InvS := fun v : State => F3CodeInv mpl mmpl v.mem ∧ True
    ∀ (pc : BitVec 64) (f : State → State),
      P_ghost.externAt? pc = some f →
      (∃ sym : String,
        sym ∈ mlkemSampleNttSyms ∧ pc = libsignalSessionLib.resolve mpl sym ∧
        AtCallRowReplayOn mpl InvS (cliExternsPlaced mmpl) sym (mlkemSampleNttTermOf sym) f) ∨
      ((P_real.externAt? pc = some f ∧
          ∀ a : State,
            Steps P_ghost sm a → Steps P_ghost (f a) sr →
            a.pc = pc → a.status = .Running →
            (∀ msg, (f a).status ≠ .Exception msg) →
            a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem → InvS a →
            ExecFrozen (f a).mem ∧ InvS (f a)) ∨
        (P_real.externAt? pc = none ∧
          ∀ a : State,
            Steps P_ghost sm a → Steps P_ghost (f a) sr →
            a.pc = pc → a.status = .Running →
            (∀ msg, (f a).status ≠ .Exception msg) →
            a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem →
            (fun _ => false) (a.readReg64 .lr) = false → InvS a →
            Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))) := by
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  have hrun_sr21 : sr.status = .Running → keepMemsetBlk21 mmpl sr.pc = false :=
    fun hrs => hret_pc hrs ▸ hG.1.1
  have hrun_sr20 : sr.status = .Running → keepMemcpyBlk20 mmpl sr.pc = false :=
    fun hrs => hret_pc hrs ▸ hG.1.2
  have hBlk21 := hGh.blk21Ext W
  have hBlk20 := hGh.blk20Ext W
  rw [cliGhostExterns_eq_withExtra ghFixed] at hBlk21 hBlk20
  dsimp only
  intro pc f heg
  rcases blockProgram_cliGhostExternsWithExtra_externAt?_mem_cases_local
      ghFixed ghFixed.extra (cliExternsPlaced mmpl W) heg with
    her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
  · obtain ⟨sym_r, hsym_r⟩ := blockProgram_externAt?_some_exists_local her
    refine Or.inr (Or.inl ⟨her, fun a _ _ _ _ _ hkf hfr ⟨hinv, _⟩ => ?_⟩)
    exact ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym_r a hfr,
      hinv.of_keepsFrozen hkf, trivial⟩
  · rcases (GhostSymActiveWithExtra_iff_named_or_extra _ _ _ _).mp hAct with
      hActNamed | ⟨hDom, hLook⟩
    · have hActG : GhostSymActive ghFixed sym f :=
        (GhostSymActiveWithExtra_iff_named_or_extra _ ghFixed.extra _ _).mpr
          (Or.inl hActNamed)
      refine Or.inr (Or.inr ⟨hpc_eq ▸ hGh.realNone W sym f hsym_ext hActNamed,
        fun a _ hrest hpc hrun hnoex_fa hkf hfr _ ⟨hinv, _⟩ => ?_⟩)
      have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
        strClone_not_mem_ext617_local (heq ▸ hsym_ext)
      have hext_nil :
          cliGhostExternsWithExtra ghFixed [] (fun _ => none) sym = some f :=
        cliGhostExternsWithExtra_nil_of_named ghFixed (fun _ => none) hActNamed
      have hext_full :
          cliGhostExterns ghFixed (fun _ => none) sym = some f := by
        rw [cliGhostExterns_eq_withExtra]
        exact cliGhostExternsWithExtra_eq_some_of_active ghFixed
          ghFixed.extra (fun _ => none) hActG
      have hinv_fa : F3CodeInv mpl mmpl (f a).mem := hinv.of_keepsFrozen hkf
      have hlr_sub : sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          keepSub (a.readReg64 .lr) = false :=
        fun hnoShim hnoMs hnoMc =>
          hGh.noExLr hext_nil hnoShim hnoex_fa hnoMs hnoMc
      have hlr_blk21 : sym = lsMemsetSym → keepMemsetBlk21 mmpl (a.readReg64 .lr) = false :=
        fun hms => blk21_lr_trap_after_hook_ret
          (hGh.trap21 hext_nil (by subst hms; decide)) hBlk21
          (hinv_fa.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
          hrest hrun hrun_sr21 hnoex_sr hnhalt_sr
      have hlr_blk20 : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (a.readReg64 .lr) = false :=
        fun hmc => blk20_lr_trap_after_hook_ret
          (hGh.trap20 hext_nil (by subst hmc; decide)) hBlk20
          (hinv_fa.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
          hrest hrun hrun_sr20 hnoex_sr hnhalt_sr
      have hread_fds : sym = lsReadFileSym → FdsGe3Closed a.fs :=
        fun hrd => hGh.noExFds (hrd ▸ hext_full) hnoex_fa
      have hst_r : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) a (f a) :=
        hNamedSteps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) W rfl (fun _ _ => rfl)
          sym f hsym_ext hne_sc hActNamed a (hpc.trans hpc_eq) hrun hnoex_fa hkf hfr
          hlr_sub hlr_blk21 hlr_blk20 hinv hread_fds
      exact ⟨hst_r, hGh.preservesExecFrozen hActNamed a hfr,
        hinv_fa, trivial⟩
    · cases hsntt : mlkemSampleNttSyms.contains sym with
      | true =>
        have hsym_s5 : sym ∈ mlkemSampleNttSyms := (mlkemSampleNttSyms_contains_iff sym).mp hsntt
        exact Or.inl ⟨sym, hsym_s5, hpc_eq, hExtra.atCallSntt sym f hsym_s5 hLook⟩
      | false =>
        have hRow := hExtra.replaysNonSntt sym f hDom hsntt hLook
        have hGs : c2GuardOf mpl sym sm := hG.2 sym hDom
        rcases hRow.replay_at_stub W sm sr hGs hret_pc hnoex_sr hnhalt_sr with
          ⟨her_stub, hfn1⟩ | ⟨hn_stub, hfn2⟩
        · exact Or.inr (Or.inl ⟨hpc_eq ▸ her_stub, fun a hpre hre hpc hr hnx hkf hfr hinv =>
            hfn1 a hpre hre (hpc.trans hpc_eq) hr hnx hkf hfr hinv⟩)
        · exact Or.inr (Or.inr ⟨hpc_eq ▸ hn_stub, fun a hpre hre hpc hr hnx hkf hfr _ hinv =>
            hfn2 a hpre hre (hpc.trans hpc_eq) hr hnx hkf hfr hinv⟩)

/-- Lift a ghost trajectory `u →* sr` (`sm →* u →* sr`) that visits no `BadAtFamily` state strictly
    before `sr` onto `P_checkedSntt`. -/
private theorem steps_checkedSntt_of_ghost_noStrictBad_aux [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    {keepSub : BitVec 64 → Bool} {ghFixed : CliGhostHooks}
    (hGh : GhostFixedFacts mpl mmpl keepSub ghFixed)
    (hNamedSteps : NamedGhostStepsBelow4b0000 mpl mmpl keepSub ghFixed)
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed ghFixed.extra)
    (W : CliHooks) {sm u sr : State}
    (hG : F3C2EntryGuard mpl mmpl sm)
    (hret_pc : sr.status = .Running → sr.pc = sm.readReg64 .lr)
    (hnoex_sr : ∀ msg, sr.status ≠ .Exception msg)
    (hnhalt_sr : sr.status ≠ .Halted)
    (hNoStrictBad : ∀ z z' : State,
      let EG := fun W' =>
        cliGhostExternsWithExtra ghFixed ghFixed.extra
          (cliExternsPlaced mmpl W')
      Steps (cliProgExtPlacedAt mpl EG 617 W) sm z →
      Step (cliProgExtPlacedAt mpl EG 617 W) z z' →
      Steps (cliProgExtPlacedAt mpl EG 617 W) z' sr →
      ¬ BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf z)
    (hpre_u : Steps (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExternsWithExtra ghFixed ghFixed.extra
        (cliExternsPlaced mmpl W')) 617 W) sm u)
    (hsuf_u : Steps (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExternsWithExtra ghFixed ghFixed.extra
        (cliExternsPlaced mmpl W')) 617 W) u sr)
    (hFr_u : ExecFrozen u.mem)
    (hInv_u : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W) u sr := by
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  have hBlk21 := hGh.blk21Ext W
  have hBlk20 := hGh.blk20Ext W
  rw [cliGhostExterns_eq_withExtra ghFixed] at hBlk21 hBlk20
  induction hsuf_u with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 hrest ih =>
    have hnot_bad1 : ¬ BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf s1 :=
      hNoStrictBad s1 s2 hpre_u h1 hrest
    have hpre2 := hpre_u.trans (Steps.step h1 (Steps.refl _))
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_sr (steps_preserves_halted_local hrest rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_sr _ (steps_preserves_exception_local hrest rfl))
    | @exec inst hrun hfm =>
      have hfm_orig := hfm
      unfold Program.fetchMem at hfm
      cases heg : (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra ghFixed ghFixed.extra
          (cliExternsPlaced mmpl W')) 617 W).externAt? s1.pc with
      | some _ => simp [heg] at hfm
      | none =>
        have her : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc = none :=
          noNewHooks_cliProgExtPlacedAt_of_ext_none_imp mpl 617
            (fun W' _sym h => cliGhostExternsWithExtra_none_imp ghFixed
              ghFixed.extra (cliExternsPlaced mmpl W') h) W s1.pc heg
        have hnot_s5 : s1.pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
          intro hmem
          obtain ⟨sym, hsym, hpc_eq⟩ := List.mem_map.mp hmem
          obtain ⟨f_g, hlk⟩ := hExtra.lookup_isSome hsym
          have hDom : cliExtraGhostSyms.contains sym = true :=
            List.all_eq_true.mp mlkemSampleNttSyms_subset_extra sym hsym
          have he := f3RxSeg_ghostProg617_externAt_entry hExt
            (fun W' => cliGhostExternsWithExtra ghFixed
              ghFixed.extra (cliExternsPlaced mmpl W')) W
            (mlkemSampleNttSyms_sub_c2Rx hsym) (mlkemSampleNttSyms_sub_hooked hsym)
          have hsome := cliGhostExternsWithExtra_eq_some_of_active ghFixed
            ghFixed.extra (cliExternsPlaced mmpl W)
            ((GhostSymActiveWithExtra_iff_named_or_extra _ _ _ _).mpr (Or.inr ⟨hDom, hlk⟩))
          rw [hsome, hpc_eq] at he
          rw [he] at heg
          cases heg
        have hchk :
            (cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W).externAt?
              s1.pc = none :=
          (externAt?_snttCheckedExt_eq_of_not_mem (mmpl := mmpl) ghFixed.extra W hnot_s5).trans her
        have hstep1_chk :=
          step_of_externAt?_and_svc_eq
            (P1 := cliProgExtPlacedAt mpl
              (fun W' => cliGhostExternsWithExtra ghFixed
                ghFixed.extra (cliExternsPlaced mmpl W')) 617 W)
            (P2 := cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W)
            rfl (hchk.trans heg.symm) (Step.exec hrun hfm_orig)
        have hFr2 : ExecFrozen
            ((cliProgExtPlacedAt mpl
              (fun W' => cliGhostExternsWithExtra ghFixed
                ghFixed.extra (cliExternsPlaced mmpl W'))
              617 W).evalInst inst s1).mem := by
          by_cases hsvc0 : inst.isSvc0 = true
          · have hinst : inst = .system false 0#16 := by
              cases inst <;> simp [Instr.isSvc0] at hsvc0
              rcases hsvc0 with ⟨rfl, rfl⟩; rfl
            subst hinst
            have hev :
                (cliProgExtPlacedAt mpl
                  (fun W' => cliGhostExternsWithExtra ghFixed
                    ghFixed.extra (cliExternsPlaced mmpl W'))
                  617 W).evalInst (.system false 0#16) s1 = Syscall.standard s1 := by
              simp [Program.evalInst, execInstWithSvc, cliProgExtPlacedAt,
                MultiPlacedLib.blockProgram, Obj.PlacedLib.program]
            rw [hev]
            exact (standard_stripS (keep := fun _ => false) hFr_u).2
          · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
            rw [evalInst_eq_execInst_of_not_isSvc0_local _ hnsvc0 s1]
            exact execInst_preserves_execFrozen_local hnsvc0 hFr_u
        have hInv2 := hInv_u.of_keepsFrozen (Step.exec hrun hfm_orig).keepsFrozen
        exact Steps.step hstep1_chk (ih hret_pc hnoex_sr hnhalt_sr hNoStrictBad hpre2 hFr2 hInv2)
    | @extern f hrun heg hkf hsym =>
      have hnoex_f : ∀ msg, (f s1).status ≠ .Exception msg :=
        fun msg hex => hnoex_sr msg (steps_preserves_exception_local hrest hex)
      have hInv2 := hInv_u.of_keepsFrozen hkf
      rcases blockProgram_cliGhostExternsWithExtra_externAt?_mem_cases_local
          ghFixed ghFixed.extra (cliExternsPlaced mmpl W) heg with
        her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
      · have hnot_s5 : s1.pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
          intro hmem
          obtain ⟨sym_s, hsym_s, hpc_s⟩ := List.mem_map.mp hmem
          obtain ⟨f_s, hlk_s⟩ := hExtra.lookup_isSome hsym_s
          have hrn := (hExtra.atCallSntt sym_s f_s hsym_s hlk_s).real_stub_none W
          change (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc = some f at her
          rw [← hpc_s, hrn] at her
          cases her
        have hchk :
            (cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W).externAt?
              s1.pc = some f :=
          (externAt?_snttCheckedExt_eq_of_not_mem (mmpl := mmpl) ghFixed.extra W hnot_s5).trans her
        obtain ⟨sym_r, hsym_r⟩ := blockProgram_externAt?_some_exists_local her
        have hFr2 := cliExternsPlaced_preserves_execFrozen mmpl W hsym_r s1 hFr_u
        exact Steps.step (Step.extern hrun hchk hkf hsym)
          (ih hret_pc hnoex_sr hnhalt_sr hNoStrictBad hpre2 hFr2 hInv2)
      · rcases (GhostSymActiveWithExtra_iff_named_or_extra _ _ _ _).mp hAct with
          hActNamed | ⟨hDom, hLook⟩
        · have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
            strClone_not_mem_ext617_local (heq ▸ hsym_ext)
          have hext_nil :
              cliGhostExternsWithExtra ghFixed [] (fun _ => none) sym = some f :=
            cliGhostExternsWithExtra_nil_of_named ghFixed (fun _ => none) hActNamed
          have hext_full :
              cliGhostExterns ghFixed (fun _ => none) sym = some f := by
            rw [cliGhostExterns_eq_withExtra]
            exact cliGhostExternsWithExtra_eq_some_of_active ghFixed
              ghFixed.extra (fun _ => none) hAct
          have hrun_sr21 : s3.status = .Running → keepMemsetBlk21 mmpl s3.pc = false :=
            fun hrs => hret_pc hrs ▸ hG.1.1
          have hrun_sr20 : s3.status = .Running → keepMemcpyBlk20 mmpl s3.pc = false :=
            fun hrs => hret_pc hrs ▸ hG.1.2
          have hlr_sub : sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
              keepSub (s1.readReg64 .lr) = false :=
            fun hnoShim hnoMs hnoMc =>
              hGh.noExLr hext_nil hnoShim hnoex_f hnoMs hnoMc
          have hlr_blk21 : sym = lsMemsetSym → keepMemsetBlk21 mmpl (s1.readReg64 .lr) = false :=
            fun hms => blk21_lr_trap_after_hook_ret
              (hGh.trap21 hext_nil (by subst hms; decide)) hBlk21
              (hInv2.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
              hrest hrun hrun_sr21 hnoex_sr hnhalt_sr
          have hlr_blk20 : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (s1.readReg64 .lr) = false :=
            fun hmc => blk20_lr_trap_after_hook_ret
              (hGh.trap20 hext_nil (by subst hmc; decide)) hBlk20
              (hInv2.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
              hrest hrun hrun_sr20 hnoex_sr hnhalt_sr
          have hread_fds : sym = lsReadFileSym → FdsGe3Closed s1.fs :=
            fun hrd => hGh.noExFds (hrd ▸ hext_full) hnoex_f
          have hsteps_chk := hNamedSteps
            (cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W)
            W rfl (fun _ hlt => snttChecked_externAt?_eq_of_lt_4b0000 hLs _ W hlt)
            sym f hsym_ext hne_sc hActNamed s1 hpc_eq hrun hnoex_f hkf hFr_u
            hlr_sub hlr_blk21 hlr_blk20 hInv_u hread_fds
          have hFr2 := hGh.preservesExecFrozen hActNamed s1 hFr_u
          exact hsteps_chk.trans (ih hret_pc hnoex_sr hnhalt_sr hNoStrictBad hpre2 hFr2 hInv2)
        · cases hsntt : mlkemSampleNttSyms.contains sym with
          | true =>
            have hsym_s5 : sym ∈ mlkemSampleNttSyms :=
              (mlkemSampleNttSyms_contains_iff sym).mp hsntt
            have hTerm : mlkemSampleNttTermOf sym s1 :=
              termOf_of_not_badAtFamily hnot_bad1 hsym_s5 hpc_eq hrun
            have hfg_eq : f_snttChecked sym f s1 = f s1 := by
              unfold f_snttChecked
              simp [hTerm]
            have hchk :
                (cliProgExtPlacedAt mpl (snttCheckedExt mmpl ghFixed.extra) 617 W).externAt?
                  s1.pc = some (f_snttChecked sym f) := by
              rw [hpc_eq, externAt?_snttCheckedExt_entry (mmpl := mmpl) hExt ghFixed.extra W hsym_s5,
                hLook]
              rfl
            have hstep1_chk :
                Step (cliProgExtPlacedAt mpl
                  (snttCheckedExt mmpl ghFixed.extra) 617 W) s1 (f s1) := by
              rw [← hfg_eq]
              exact Step.extern hrun hchk (hfg_eq.symm ▸ hkf) (hfg_eq.symm ▸ hsym)
            have hFr2 :=
              ((hExtra.atCallSntt sym f hsym_s5 hLook).preserves_execFrozen s1 hrun hnoex_f hFr_u).1
            exact Steps.step hstep1_chk
              (ih hret_pc hnoex_sr hnhalt_sr hNoStrictBad hpre2 hFr2 hInv2)
          | false =>
            have hAvoidS5 := hExtra.nonSnttAvoidS5 W sm s3 sym f
              (hG.2 sym hDom) hret_pc hnoex_sr hnhalt_sr hDom hsntt hLook
              s1 hpre_u hrest hpc_eq hrun hnoex_f hkf hFr_u hInv_u
            have hsteps_chk :=
              steps_checkedSntt_of_real_avoidS5 ghFixed.extra W hAvoidS5
            have hFr2 :=
              ((hExtra.replaysNonSntt sym f hDom hsntt hLook).preserves_execFrozen
                s1 hrun hnoex_f hFr_u).1
            exact hsteps_chk.trans
              (ih hret_pc hnoex_sr hnhalt_sr hNoStrictBad hpre2 hFr2 hInv2)

/-! ## 6. Top-Level Core Theorems (`cliRunPlainPanPlacedSig = none ∧ ¬ CliReachesOOMPlainPanPlaced`) -/

/-- Plain-memory bundled run-level corollary: reaching a diverging state `u` from `s0` on
    `cliProgPlacedSig mpl mmpl W` forces both `cliRunPlainPanPlacedSig mpl mmpl elf W i = none`
    and `¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i`. -/
theorem cliRunPlainPanPlacedSig_none_and_not_oom_of_reaches_diverge
    {mpl mmpl : MultiPlacement} {elf : Process.ElfImage} {W : CliHooks} {i : Inputs}
    {s0 u : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s0)
    (hReach : Steps (cliProgPlacedSig mpl mmpl W) s0 u)
    (hDiv : ∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v → v.status = .Running) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i := by
  have hall := all_running_of_reaches_diverge hReach hDiv
  refine ⟨?_, ?_⟩
  · cases hrun : cliRunPlainPanPlacedSig mpl mmpl elf W i with
    | none => rfl
    | some _ =>
      rcases cliRunsToPlainPanPlaced_of_eq_some hrun with
        ⟨_, hLoad', ⟨_, ⟨sf, hSteps, hTerm⟩, _⟩ | ⟨_, _, _, hFalse⟩, _⟩
      · cases hLoad.symm.trans hLoad'
        have hsf_run := hall sf hSteps
        rcases hTerm with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] at hsf_run <;> cases hsf_run
      · exact False.elim hFalse
  · rintro ⟨_, sf, hLoad', hSteps, hOom⟩
    cases hLoad.symm.trans hLoad'
    have hsf_run := hall sf hSteps
    rw [hOom] at hsf_run
    cases hsf_run

set_option maxRecDepth 1000000 in
/-- Core single-input theorem: given `CliInputsOk i`, `InputsLoadable i`, a ghost Block-`617`
    `subroutine_ok` witness `Run` with `MainCaseB2`, and `CliReachesSampleNttStuckPlainPanPlaced`,
    the real plain-memory 0-hook run diverges
    (`cliRunPlainPanPlacedSig = none ∧ ¬ CliReachesOOMPlainPanPlaced`). -/
theorem cliRunPlacedSig_none_and_not_oom_of_ghostMainCase [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hExt : C2ExternTableFacts mpl)
    {keepSub : BitVec 64 → Bool} {ghFixed : CliGhostHooks}
    (hGh : GhostFixedFacts mpl mmpl keepSub ghFixed)
    (hHarness : NamedHarnessBelow4b0000 mpl mmpl)
    (hNamedSteps : NamedGhostStepsBelow4b0000 mpl mmpl keepSub ghFixed)
    (hExtra : H2KSnttExtraFacts mpl mmpl ghFixed ghFixed.extra)
    (W : CliHooks) {i : Inputs} {Run : Inputs → RunAnswer → Prop} {r : MainResult}
    (hi : CliInputsOk i)
    (hl : InputsLoadable i)
    (hSubGhost : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
          617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
          (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          Run cliProcessInputs))
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r)
    (hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i) :
    cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i := by
  let extra := ghFixed.extra
  let P_chk := cliProgExtPlacedAt mpl (snttCheckedExt mmpl extra) 617 W
  let EG_we := fun W' =>
    cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  let P_ghost := cliProgExtPlacedAt mpl EG_we 617 W
  have hHarnessChk :=
    hHarness P_chk W rfl (fun _ hlt => snttChecked_externAt?_eq_of_lt_4b0000 hLs extra W hlt)
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0_chk, hpc_sm, hrun_sm, hal_sm, hfs_sm, htr_sm,
      hG, hx0_sm, hmem_sm, hexit_chk⟩ :=
    hHarnessChk cliElf_staticOk i ⟨hi, hl⟩
  obtain ⟨s_elf, u_stuck, hLoadElf, hStepsStuck, hRunStuck, hStuckAt⟩ := hStuck
  have hs0_eq : s_elf = s0 := Except.ok.inj (hLoadElf.symm.trans hload)
  have hCO0 : F3CodeOk mpl mmpl s0.mem := f3CodeOk_of_plainLoadState hLs hMm hload
  have hnoex_sm : ∀ msg, sm.status ≠ .Exception msg := by rw [hrun_sm]; nofun
  have hnhalt_sm : sm.status ≠ .Halted := by rw [hrun_sm]; nofun
  obtain ⟨hAvoid0_real, hFr_sm, hInv_sm⟩ :=
    stepsStrictAvoid_of_checkedSntt hExt hExtra hsteps0_chk hnoex_sm hnhalt_sm hCO0.2 hCO0.1
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  change sm.mem ⊨
    b2MainEntryPreFine (F3CodeOk mpl mmpl)
      (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 cliElfImage.brkStart)
      cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) i sm ∗ Fr at hmem_sm
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem_sm
  obtain ⟨⟨hCO_sm, hsp_sm⟩, hmem_sm⟩ := hmem_sm
  have hFrz_sm : LibsignalFrozen mpl sm.mem := f3CodeOk_to_libsignalFrozen_local hLs hCO_sm
  let baseSpec :=
    b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
      (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 cliElfImage.brkStart)
      cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs
  have hpre_ghost : sm.mem ⊨ baseSpec.pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [baseSpec, b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hFrz_sm, hc, hi, ⟨hx0_sm, hfs_sm.trans hfs0, htr_sm.trans htr0⟩, hsp_sm⟩, hmem_sm⟩
  have hSubWe : subroutine_ok P_ghost (mpl.base 617) baseSpec := by
    have h := hSubGhost γ sm.tpidrEl0
    rwa [cliGhostExterns_eq_withExtra ghFixed] at h
  have hCL_ghost : P_ghost.CodeLoaded sm.mem :=
    pGhost617_codeLoaded_of_libsignalFrozen_local EG_we W sm.mem hFrz_sm
  obtain ⟨sr, hsteps1_ghost, hout, _⟩ :=
    hSubWe.no_fault_before_outcome ⟨i, r⟩ Fr sm hpc_sm hrun_sm hpre_ghost hal_sm hCL_ghost
  have hOutFacts :
      (sr.status = .Running → sr.pc = sm.readReg64 .lr) ∧
      (∀ msg, sr.status ≠ .Exception msg) ∧
      sr.status ≠ .Halted ∧
      ((Returned sm sr ∧
          sr.mem ⊨ (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗
            stackAt sm.sp 80 ∗ Fr ∗ anyHeap) ∨
        sr.status = .Panicked) := by
    rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, _⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · simp only [baseSpec, b2MainSpecTightNeedLocksFineAt, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨_, hpost_mem⟩ := hpost
      have hpost' :
          sr.mem ⊨ ((((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗
            stackAt sm.sp cliMainStk ∗ anyHeap) ∗ Fr := by
        simpa only [sepConj_assoc] using hpost_mem
      have hstkLo : (80 : Nat) ≤ cliMainStk := by decide
      have hstkHi : cliMainStk ≤ 2 ^ 64 := by decide
      refine ⟨fun _ => hret.1, ?_, ?_, Or.inl ⟨hret, exit_frame_needLocks_n hstkLo hstkHi hpost'⟩⟩
      · rw [hret.2.2]; nofun
      · rw [hret.2.2]; nofun
    · refine ⟨fun hr => absurd hr (by rw [hpan]; nofun), ?_, ?_, Or.inr hpan⟩
      · rw [hpan]; nofun
      · rw [hpan]; nofun
    · simp only [baseSpec, b2MainSpecTightNeedLocksFineAt] at hpost
      exact (not_satisfies_false_sepConj hpost).elim
    · simp only [baseSpec, b2MainSpecTightNeedLocksFineAt] at hpost
      exact (not_satisfies_false_sepConj hpost).elim
  obtain ⟨hret_pc, hnoex_sr, hnhalt_sr, hRetOrPan⟩ := hOutFacts
  by_cases hHit : ∃ u u' : State,
      Steps P_ghost sm u ∧ Step P_ghost u u' ∧ Steps P_ghost u' sr ∧
      BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf u
  · -- Case A: `sm →* sr` visits a bad `SampleNTT` entry state strictly before `sr`
    obtain ⟨u, u', hpre_u, hstep_u, hsuf_u', hbad_u⟩ := hHit
    have hCls := classifyOnEnd_h2k hGh hNamedSteps hExtra W hG hret_pc hnoex_sr hnhalt_sr
    obtain ⟨u_first, hsteps_sm_uf, hbad_uf, hFr_uf, hInv_uf, _, hNoEx_uf⟩ :=
      firstBadStrictPrefix_extract
        (keep := fun _ => false) (InvMem := F3CodeInv mpl mmpl) (PredFs := fun _ => True)
        (EG := EG_we) (ER := cliExternsPlaced mmpl)
        (S := mlkemSampleNttSyms) (termOf := mlkemSampleNttTermOf)
        (W := W) (s0 := sm) (sf_end := sr)
        (noNewHooks_cliProgExtPlacedAt_of_ext_none_imp mpl 617
          (fun W' _sym h => cliGhostExternsWithExtra_none_imp ghFixed extra
            (cliExternsPlaced mmpl W') h) W)
        hFr_sm hInv_sm (fun _ _ h hkf => h.of_keepsFrozen hkf) trivial
        hnoex_sr hnhalt_sr hCls
        (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => rfl)
        hpre_u hstep_u hsuf_u' hbad_u
    have hDiv := snttDiverge_of_badAtFamily hLs hExt hExtra W hbad_uf hInv_uf hFr_uf hNoEx_uf
    have hReach_s0_uf : Steps (cliProgPlacedSig mpl mmpl W) s0 u_first :=
      steps_cliProgPlacedSig_of_running W W (loadState_status_running hload) hbad_uf.1
        (hAvoid0_real.toSteps.trans hsteps_sm_uf)
    have hReach_init_uf : Steps (cliProgPlacedSig mpl mmpl W) s_elf u_first :=
      hs0_eq.symm ▸ hReach_s0_uf
    exact cliRunPlainPanPlacedSig_none_and_not_oom_of_reaches_diverge hLoadElf hReach_init_uf hDiv
  · -- Case B: no state strictly before `sr` violates `BadAtFamily`; refute `hStuck`
    exfalso
    have hNoStrict : ∀ z z' : State,
        Steps P_ghost sm z → Step P_ghost z z' → Steps P_ghost z' sr →
        ¬ BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf z :=
      fun z z' h1 h2 h3 hb => hHit ⟨z, z', h1, h2, h3, hb⟩
    have hsteps1_chk : Steps P_chk sm sr :=
      steps_checkedSntt_of_ghost_noStrictBad_aux hLs hExt hGh hNamedSteps hExtra W
        hG hret_pc hnoex_sr hnhalt_sr hNoStrict (Steps.refl sm) hsteps1_ghost hFr_sm hInv_sm
    have hTermChk : ∃ s_end : State,
        Steps P_chk s0 s_end ∧
        (∀ msg, s_end.status ≠ .Exception msg) ∧
        s_end.status ≠ .Halted ∧
        (toSigStateLocal s_end).status ≠ .Running := by
      rcases hRetOrPan with ⟨hret, hexit_mem⟩ | hpan
      · obtain ⟨sx, hsteps2_chk, hst_sx, _, _⟩ := hexit_chk sr hsteps1_chk hret hexit_mem
        refine ⟨sx, hsteps0_chk.trans (hsteps1_chk.trans hsteps2_chk), ?_, ?_, ?_⟩
        · rw [hst_sx]; nofun
        · rw [hst_sx]; nofun
        · have hne_pan : sx.status ≠ .Panicked := by rw [hst_sx]; nofun
          rw [toSigStateLocal_of_ne_panicked hne_pan, hst_sx]; nofun
      · refine ⟨sr, hsteps0_chk.trans hsteps1_chk, hnoex_sr, hnhalt_sr, ?_⟩
        unfold toSigStateLocal
        simp [hpan]
    obtain ⟨s_end, hsteps_all_chk, hnoex_end, hnhalt_end, hnr_sig_end⟩ := hTermChk
    obtain ⟨hAvoid_all_real, _, _⟩ :=
      stepsStrictAvoid_of_checkedSntt hExt hExtra hsteps_all_chk hnoex_end hnhalt_end hCO0.2 hCO0.1
    have hAvoid_sig :=
      stepsStrictAvoid_to_sig (loadState_status_running hload) hAvoid_all_real
    have hStepsStuck_s0 : Steps (cliProgPlacedSig mpl mmpl W) s0 u_stuck :=
      hs0_eq ▸ hStepsStuck
    exact not_reaches_bad_of_stepsStrictAvoid_not_running hAvoid_sig hnr_sig_end
      (fun hbad_end => hnr_sig_end hbad_end.1) hStepsStuck_s0 ⟨hRunStuck, hStuckAt⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
