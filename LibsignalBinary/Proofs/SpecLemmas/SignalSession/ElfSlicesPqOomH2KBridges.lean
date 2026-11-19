/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import ProofLib.SepLogic
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget

/-!
# K-to-Plain Non-`readFile` Hook Bridges and Witness Constructors (`ElfSlicesPqOomH2KBridges`)

**Checked by Lean.**

Bridges the K-narrowed ghost-hook contracts at `h2k_ghFixedK mpl mmpl` (`ElfSlicesPqOomH2KHooks`)
to plain (`h2k_withKeepLrFalse`-free) `HookSat` contracts for the six non-`readFile` ghost hooks
(`alloc`, `dealloc`, `realloc`, `allocZeroed`, `readStdin`, and `stringClone`) via
`ElfSlicesPqOomH2LsRetAddrKeep`:
1. Generic `HookOk` / `HookSat` precondition-weakening combinators (`h2kb_hook*_of_withKeepLr*`).
2. Plain `HookSat` bridges at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base` for `alloc`,
   `dealloc`, `realloc`, `allocZeroed`, `readStdin`, and `stringClone` (`NoOom` and `Budget`).
3. Closed non-`readFile` fields of `F3CliElfGhostWitness` (`hGSpqr`, `hFs`, `hghNoAlloc`,
   13-field `RunHooksPlaced`, and non-`readFile` `MainIoOfPlaced`) plus split constructors
   assembling `F3CliElfGhostWitness` from the remaining `readFile` and transfer obligations.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges

open Arm64 (GhostName HookOk HookSat SepProp Spec State StepsUntil subroutine_ok)
open Arm64.Obj (MultiPlacement)
open ProofLib (satisfies_pure_sepConj sepConj_assoc)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsFmtWriteSym
   lsFormatInnerSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustReallocSymCli lsStringCloneSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (IoModel ReadStdinGhost cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooksFs cliGhostExterns cliGhostExterns_alloc cliGhostExterns_allocZeroed
   cliGhostExterns_dealloc cliGhostExterns_readStdin_some
   cliGhostExterns_realloc cliGhostExterns_stringClone_some)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec stringCloneNoOomSpec)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre ActiveF3ReadStdinPre f3ReadStdinGhostHook f3ReadStdinGhostHookFine
   f3ReadStdinGhostHookFine_ok_bounded f3StringCloneFallback f3StringCloneFallback_ok_noOom_fine)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (fmtWriteProtoAddrCliLsSpec formatInnerCallCliLsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeStdoutSpecPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxProg_no_ext f3TrialRxProg_svc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_allocSpecK h2k_allocZeroedSpecK h2k_deallocSpecK h2k_ghFixedK h2k_hole2_hFmtWriteSatK
   h2k_hole2_hFormatInnerSatK h2k_hole2_hFsK h2k_hole2_hGSpqrK h2k_hole2_hghNoAllocK
   h2k_hole2_hioOfK h2k_readStdinGhostHookFineK h2k_readStdinSpecK h2k_reallocSpecK
   h2k_segc_strCloneGhostHook_okK h2k_strCloneGhostHookK h2k_stringCloneBudgetSpecK
   h2k_stringCloneSpecK h2k_withKeepLrAndFds h2k_withKeepLrFalse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false h2lr_lsRetAddr_keep_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (g1fr_strClone_real_run_outcome hole2_ActiveStrCloneRun hole2_emptyProg
   hole2_hPl_mng hole2_hblk hole2_hext_nodup hole2_hookStack hole2_keep
   hole2_keepMallocng hole2_keepSub hole2_readStdinCond_ok hole2_targets)

/-! ## Precondition-Weakening `HookOk` and `HookSat` Combinators -/

/-- Lift `HookOk f (h2k_withKeepLrFalse keepSet spec)` to plain `HookOk f spec` whenever `spec.pre`
    already implies `keepSet (s0.readReg64 .lr) = false`. -/
theorem h2kb_hookOk_of_withKeepLrFalse {α : Type} {keepSet : BitVec 64 → Bool}
    {spec : Spec α} {f : State → State}
    (hK : HookOk f (h2k_withKeepLrFalse keepSet spec))
    (hlr : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → keepSet (s0.readReg64 .lr) = false) :
    HookOk f spec := by
  intro x R s0 hrun hpre hsp
  have hpreK : s0.mem ⊨ (h2k_withKeepLrFalse keepSet spec).pre x s0 ∗ R := by
    dsimp only [h2k_withKeepLrFalse]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hlr x R s0 hpre, hpre⟩
  exact hK x R s0 hrun hpreK hsp

/-- Lift `HookSat H sym (h2k_withKeepLrFalse keepSet spec)` to plain `HookSat H sym spec` whenever
    `spec.pre` already implies `keepSet (s0.readReg64 .lr) = false`. -/
theorem h2kb_hookSat_of_withKeepLrFalse {α : Type} {keepSet : BitVec 64 → Bool}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hK : HookSat H sym (h2k_withKeepLrFalse keepSet spec))
    (hlr : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → keepSet (s0.readReg64 .lr) = false) :
    HookSat H sym spec := by
  rcases hK with ⟨f, hf, hOkK⟩
  exact ⟨f, hf, h2kb_hookOk_of_withKeepLrFalse hOkK hlr⟩

/-- Lift `HookOk f (h2k_withKeepLrAndFds keepSet spec)` to plain `HookOk f spec` whenever `spec.pre`
    implies both `keepSet (s0.readReg64 .lr) = false` and `FdsGe3Closed s0.fs` (for S1/S3 `readFile`). -/
theorem h2kb_hookOk_of_withKeepLrAndFds {α : Type} {keepSet : BitVec 64 → Bool}
    {spec : Spec α} {f : State → State}
    (hK : HookOk f (h2k_withKeepLrAndFds keepSet spec))
    (hguard : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      keepSet (s0.readReg64 .lr) = false ∧ FdsGe3Closed s0.fs) :
    HookOk f spec := by
  intro x R s0 hrun hpre hsp
  have hpreK : s0.mem ⊨ (h2k_withKeepLrAndFds keepSet spec).pre x s0 ∗ R := by
    dsimp only [h2k_withKeepLrAndFds]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hguard x R s0 hpre, hpre⟩
  exact hK x R s0 hrun hpreK hsp

/-- Lift `HookSat H sym (h2k_withKeepLrAndFds keepSet spec)` to plain `HookSat H sym spec` whenever
    `spec.pre` implies both `keepSet (s0.readReg64 .lr) = false` and `FdsGe3Closed s0.fs`. -/
theorem h2kb_hookSat_of_withKeepLrAndFds {α : Type} {keepSet : BitVec 64 → Bool}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hK : HookSat H sym (h2k_withKeepLrAndFds keepSet spec))
    (hguard : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      keepSet (s0.readReg64 .lr) = false ∧ FdsGe3Closed s0.fs) :
    HookSat H sym spec := by
  rcases hK with ⟨f, hf, hOkK⟩
  exact ⟨f, hf, h2kb_hookOk_of_withKeepLrAndFds hOkK hguard⟩

/-! ## Plain Precondition to `keepSet lr = false` Lemmas -/

/-- `rustCliAllocBudgetSpec` (`zeroed = false` for `alloc`, `zeroed = true` for `allocZeroed`)
    carries `LsRetAddr624 (s0.readReg64 .lr)`, hence `hole2_keepSub (s0.readReg64 .lr) = false`. -/
theorem h2kb_alloc_pre_keepSub_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool}
    (x : Nat × Nat × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (rustCliAllocBudgetSpec M A lim zeroed).pre x s0 ∗ R) :
    hole2_keepSub (s0.readReg64 .lr) = false := by
  rcases x with ⟨size, align, st⟩
  dsimp only [rustCliAllocBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h2lr_lsRetAddr624_keepSub_false hLs hpre.1.2.2.2

/-- `rustCliDeallocBudgetSpec` carries `LsRetAddr624 (s0.readReg64 .lr)`, hence
    `hole2_keepSub (s0.readReg64 .lr) = false`. -/
theorem h2kb_dealloc_pre_keepSub_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : BitVec 64 × Nat × Nat × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre x s0 ∗ R) :
    hole2_keepSub (s0.readReg64 .lr) = false := by
  rcases x with ⟨p, size, align, st⟩
  dsimp only [rustCliDeallocBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h2lr_lsRetAddr624_keepSub_false hLs hpre.1.2.2.2

/-- `rustCliReallocBudgetSpec` carries `LsRetAddr624 (s0.readReg64 .lr)`, hence
    `hole2_keepSub (s0.readReg64 .lr) = false`. -/
theorem h2kb_realloc_pre_keepSub_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (rustCliReallocBudgetSpec M A lim).pre x s0 ∗ R) :
    hole2_keepSub (s0.readReg64 .lr) = false := by
  rcases x with ⟨p, old, align, new, bs, st⟩
  dsimp only [rustCliReallocBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  exact h2lr_lsRetAddr624_keepSub_false hLs hpre.1.2.2.2.2.2.2.2

/-- `readStdinSpecOfPlaced` carries `LsRetAddr624 (s0.readReg64 .lr)`, hence
    `hole2_keepSub (s0.readReg64 .lr) = false`. -/
theorem h2kb_readStdin_pre_keepSub_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {io : IoModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (x : ReadStdinGhost × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (readStdinSpecOfPlaced io A lim stk StdinEnv).pre x s0 ∗ R) :
    hole2_keepSub (s0.readReg64 .lr) = false := by
  rcases x with ⟨xg, st⟩
  dsimp only [readStdinSpecOfPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h2lr_lsRetAddr624_keepSub_false hLs hpre.1.2.2.2

/-- `stringCloneNoOomSpec` carries `LsRetAddr (s0.readReg64 .lr)`, hence
    `hole2_keep (s0.readReg64 .lr) = false` via `h2lr_lsRetAddr_keep_false`. -/
theorem h2kb_stringCloneNoOom_pre_keep_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : BitVec 64 × BitVec 64 × VecGhost × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (stringCloneNoOomSpec M A lim).pre x s0 ∗ R) :
    hole2_keep (s0.readReg64 .lr) = false := by
  rcases x with ⟨p, ret, g, st⟩
  dsimp only [stringCloneNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (h2lr_lsRetAddr_keep_false hLs hpre.1.2.2.2).1

/-- `stringCloneBudgetSpec` carries `LsRetAddr (s0.readReg64 .lr)`, hence
    `hole2_keep (s0.readReg64 .lr) = false` via `h2lr_lsRetAddr_keep_false`. -/
theorem h2kb_stringCloneBudget_pre_keep_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : BitVec 64 × BitVec 64 × VecGhost × M.σ) (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ (stringCloneBudgetSpec M A lim).pre x s0 ∗ R) :
    hole2_keep (s0.readReg64 .lr) = false := by
  rcases x with ⟨p, ret, g, st⟩
  dsimp only [stringCloneBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (h2lr_lsRetAddr_keep_false hLs hpre.1.2.2.2).1

/-! ## Per-Hook K `HookSat` Witnesses and Plain `HookSat` Bridges -/

/-- K `HookSat` for `alloc` (`lsRustAllocSymCli`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_alloc_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustAllocSymCli
      (h2k_allocSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨(h2k_ghFixedK mpl mmpl).alloc,
   cliGhostExterns_alloc (h2k_ghFixedK mpl mmpl) base,
   (h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp).alloc⟩

/-- K `HookSat` for `dealloc` (`lsRustDeallocSymCli`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_dealloc_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustDeallocSymCli
      (h2k_deallocSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨(h2k_ghFixedK mpl mmpl).dealloc,
   cliGhostExterns_dealloc (h2k_ghFixedK mpl mmpl) base,
   (h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp).dealloc⟩

/-- K `HookSat` for `realloc` (`lsRustReallocSymCli`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_realloc_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustReallocSymCli
      (h2k_reallocSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨(h2k_ghFixedK mpl mmpl).realloc,
   cliGhostExterns_realloc (h2k_ghFixedK mpl mmpl) base,
   (h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp).realloc⟩

/-- K `HookSat` for `allocZeroed` (`lsRustAllocZeroedSymCli`) at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_allocZeroed_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustAllocZeroedSymCli
      (h2k_allocZeroedSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨(h2k_ghFixedK mpl mmpl).allocZeroed,
   cliGhostExterns_allocZeroed (h2k_ghFixedK mpl mmpl) base,
   (h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp).allocZeroed⟩

/-- K `HookOk` for `h2k_readStdinGhostHookFineK` at `h2k_readStdinSpecK`. -/
theorem h2kb_readStdin_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk
      (h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack ReadStdinBoundedEnv) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hLs
  have hOrig :=
    f3ReadStdinGhostHookFine_ok_bounded
      (keep := hole2_keepSub) (P_real := hole2_emptyProg) (P_sub := f3TrialRxProg)
      (entry_io := (hole2_targets mpl).readStdin) (mmpl := mmpl) (brkStart := cliElfImage.brkStart)
      (lim := cliBudgetLimits) (stk := hole2_hookStack)
      rfl f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext
      (hole2_hPl_mng mmpl hMm) (hole2_keepMallocng mmpl hMm) (Nat.le_refl _)
      (hole2_readStdinCond_ok mmpl hMm) γ tp
  dsimp only [HookOk]
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [h2k_readStdinSpecK, h2k_withKeepLrFalse] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hlr, hpreOrig⟩
  classical
  have hActK : ActiveF3CallPre
      (fun γ' tp' => h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack ReadStdinBoundedEnv) s0 := by
    refine ⟨hrun, hsp, γ, tp, (x, st), R, ?_⟩
    dsimp only [h2k_readStdinSpecK, h2k_withKeepLrFalse]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hlr, hpreOrig⟩
  have hAct : ActiveF3ReadStdinPre
      (fun γ' tp' => fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart)
      cliBudgetLimits hole2_hookStack s0 :=
    ⟨hrun, hsp, γ, tp, (x, st), R, hpreOrig⟩
  have hEq :
      h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack s0 =
      f3ReadStdinGhostHookFine hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack s0 := by
    unfold h2k_readStdinGhostHookFineK f3ReadStdinGhostHookFine f3ReadStdinGhostHook
    rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]
  rw [hEq]
  exact hOrig (x, st) R s0 hrun hpreOrig hsp

/-- K `HookSat` for `readStdin` (`lsReadStdinSym`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_readStdin_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsReadStdinSym
      (h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack ReadStdinBoundedEnv) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨_, cliGhostExterns_readStdin_some (h2k_ghFixedK mpl mmpl) base rfl,
   h2kb_readStdin_okK mpl mmpl hLs hMm γ tp⟩

/-- K `HookOk` for `h2k_strCloneGhostHookK` at `h2k_stringCloneSpecK` (`NoOom` form). -/
theorem h2kb_stringCloneNoOom_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_strCloneGhostHookK mpl mmpl)
      (h2k_stringCloneSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  classical
  intro x R s0 hrun hpreK hsp
  have hActK : ActiveF3CallPre
      (fun γ' tp' => h2k_stringCloneSpecK fineCostModel
        (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits) s0 :=
    ⟨hrun, hsp, γ, tp, x, R, hpreK⟩
  have hEq : h2k_strCloneGhostHookK mpl mmpl s0 =
      (if hReal : hole2_ActiveStrCloneRun mpl s0 then Classical.choose hReal.2.2.2.2
       else keepFsTrace (f3StringCloneFallback mmpl) s0) := by
    unfold h2k_strCloneGhostHookK
    exact dite_eq_left_of_eq_true (eq_true hActK)
  rw [hEq]
  dsimp only [h2k_stringCloneSpecK, h2k_withKeepLrFalse] at hpreK
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreK
  rcases hpreK with ⟨_hlr, hpre⟩
  by_cases hReal : hole2_ActiveStrCloneRun mpl s0
  · rw [dite_eq_left_of_eq_true (eq_true hReal)]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      g1fr_strClone_real_run_outcome mpl mmpl hLs hMm γ tp x R s0 hrun hsp hpre
        hReal.1 hReal.2.1 hReal.2.2.1 hReal.2.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2.2
    have hdet : Classical.choose hReal.2.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · rw [dite_eq_right_of_eq_false (eq_false hReal)]
    have hidem : keepFsTrace (f3StringCloneFallback mmpl) = f3StringCloneFallback mmpl :=
      funext fun _ => rfl
    rw [hidem]
    exact f3StringCloneFallback_ok_noOom_fine cliElfImage.brkStart cliBudgetLimits
      (hole2_hPl_mng mmpl hMm) γ tp x R s0 hrun hpre hsp

/-- K `HookSat` for `stringClone` (`NoOom` form, `h2k_stringCloneSpecK`) at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_stringCloneNoOom_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (h2k_stringCloneSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨h2k_strCloneGhostHookK mpl mmpl,
   cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) base rfl,
   h2kb_stringCloneNoOom_okK mpl mmpl hLs hMm γ tp⟩

/-- K `HookSat` for `stringClone` (`Budget` form, `h2k_stringCloneBudgetSpecK`) at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_stringCloneBudget_hookSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (h2k_stringCloneBudgetSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨h2k_strCloneGhostHookK mpl mmpl,
   cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) base rfl,
   h2k_segc_strCloneGhostHook_okK mpl mmpl hLs hMm γ tp⟩

/-- Plain `HookSat` for `alloc` at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_alloc_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustAllocSymCli
      (rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits false) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_alloc_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_alloc_pre_keepSub_false hLs)

/-- Plain `HookSat` for `dealloc` at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_dealloc_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustDeallocSymCli
      (rustCliDeallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_dealloc_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_dealloc_pre_keepSub_false hLs)

/-- Plain `HookSat` for `realloc` at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_realloc_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustReallocSymCli
      (rustCliReallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_realloc_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_realloc_pre_keepSub_false hLs)

/-- Plain `HookSat` for `allocZeroed` at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_allocZeroed_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsRustAllocZeroedSymCli
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_allocZeroed_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_alloc_pre_keepSub_false hLs)

/-- Plain `HookSat` for `readStdin` at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_readStdin_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsReadStdinSym
      (readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack ReadStdinBoundedEnv) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_readStdin_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_readStdin_pre_keepSub_false hLs)

/-- Plain `HookSat` for `stringClone` (`NoOom`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_stringCloneNoOom_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_stringCloneNoOom_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_stringCloneNoOom_pre_keep_false hLs)

/-- Plain `HookSat` for `stringClone` (`Budget`) at `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_stringCloneBudget_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (stringCloneBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2kb_hookSat_of_withKeepLrFalse
    (h2kb_stringCloneBudget_hookSatK mpl mmpl hLs hMm base γ tp)
    (h2kb_stringCloneBudget_pre_keep_false hLs)

/-! ## Non-`readFile` `F3CliElfGhostWitness` Fields and Split Constructors -/

private theorem h2kb_hookOk_alloc_of_sat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).alloc
      (rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits false) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨f, hf, hOk⟩ := h2kb_alloc_hookSat mpl mmpl hLs hMm (fun _ => none) γ tp
  rw [cliGhostExterns_alloc (h2k_ghFixedK mpl mmpl) (fun _ => none)] at hf
  injection hf with hfeq
  exact hfeq ▸ hOk

private theorem h2kb_hookOk_dealloc_of_sat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).dealloc
      (rustCliDeallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨f, hf, hOk⟩ := h2kb_dealloc_hookSat mpl mmpl hLs hMm (fun _ => none) γ tp
  rw [cliGhostExterns_dealloc (h2k_ghFixedK mpl mmpl) (fun _ => none)] at hf
  injection hf with hfeq
  exact hfeq ▸ hOk

private theorem h2kb_hookOk_realloc_of_sat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).realloc
      (rustCliReallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨f, hf, hOk⟩ := h2kb_realloc_hookSat mpl mmpl hLs hMm (fun _ => none) γ tp
  rw [cliGhostExterns_realloc (h2k_ghFixedK mpl mmpl) (fun _ => none)] at hf
  injection hf with hfeq
  exact hfeq ▸ hOk

private theorem h2kb_hookOk_allocZeroed_of_sat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).allocZeroed
      (rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits true) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨f, hf, hOk⟩ := h2kb_allocZeroed_hookSat mpl mmpl hLs hMm (fun _ => none) γ tp
  rw [cliGhostExterns_allocZeroed (h2k_ghFixedK mpl mmpl) (fun _ => none)] at hf
  injection hf with hfeq
  exact hfeq ▸ hOk

/-- Plain `CliGhostSpqrAllocHooks` at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2kb_hole2_hGSpqr
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro γ tp
  have hK := h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp
  exact
    { alloc := h2kb_hookOk_alloc_of_sat mpl mmpl hLs hMm γ tp
      dealloc := h2kb_hookOk_dealloc_of_sat mpl mmpl hLs hMm γ tp
      realloc := h2kb_hookOk_realloc_of_sat mpl mmpl hLs hMm γ tp
      alloc_fs := hK.alloc_fs
      dealloc_fs := hK.dealloc_fs
      realloc_fs := hK.realloc_fs
      alloc_fsT := hK.alloc_fsT
      dealloc_fsT := hK.dealloc_fsT
      realloc_fsT := hK.realloc_fsT
      shim_eq := hK.shim_eq
      memset := hK.memset
      memcpy := hK.memcpy
      memcpy_exact := hK.memcpy_exact
      memset_acp := hK.memset_acp
      extraOk := hK.extraOk
      allocZeroed := h2kb_hookOk_allocZeroed_of_sat mpl mmpl hLs hMm γ tp
      allocZeroed_fs := hK.allocZeroed_fs
      allocZeroed_fsT := hK.allocZeroed_fsT
      onceCall := hK.onceCall
      onceCall_unique := hK.onceCall_unique }

theorem h2kb_hole2_hG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => (h2kb_hole2_hGSpqr mpl mmpl hLs hMm γ tp).toCliGhostAllocHooks

theorem h2kb_hole2_hFs
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    CliGhostHooksFs (h2k_ghFixedK mpl mmpl) :=
  h2k_hole2_hFsK mpl mmpl hLs hMm

theorem h2kb_hole2_hghNoAlloc
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ExternNoAllocFailed (cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)) :=
  h2k_hole2_hghNoAllocK mpl mmpl hLs hMm

/-- Plain `HookSat` for `lsFormatInnerSym` (`formatInnerCallCliLsSpec`) at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_formatInnerCallCliLs_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsFormatInnerSym
      (formatInnerCallCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  h2k_hole2_hFormatInnerSatK mpl mmpl hLs hMm base γ tp

/-- Plain `HookSat` for `lsFmtWriteSym` (`fmtWriteProtoAddrCliLsSpec`) at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) base`. -/
theorem h2kb_fmtWriteProtoAddrCliLs_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  h2k_hole2_hFmtWriteSatK mpl mmpl hLs hMm base γ tp

/-- Closes the 14-field `RunHooksPlaced` half of `CliRunHooksBundle` at `h2k_ghFixedK`. -/
theorem h2kb_hole2_runHooksPlaced
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  exact RunHooksPlaced.of_hooks mmpl (h2k_ghFixedK mpl mmpl) W
    (h2kb_hole2_hGSpqr mpl mmpl hLs hMm γ tp)
    (h2kb_hole2_hFs mpl mmpl hLs hMm).stringClone_fsT
    (h2kb_stringCloneBudget_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)
    (h2kb_formatInnerCallCliLs_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)
    (h2kb_fmtWriteProtoAddrCliLs_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)

/-- Assembles `CliRunHooksBundle` at `h2k_ghFixedK mpl mmpl` from `readFile579`. -/
theorem h2kb_hole2_hHooksBundle_of_readFile579
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hRead579 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (lsProg_579 (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)))
          (lsρ lsReadFileSym)
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (h2k_ghFixedK mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    { runHooks := h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp
      readFile579 := hRead579 W γ tp }

/-- Plain `MainIoOfPlacedSat.readStdin` at `ghFixed := h2k_ghFixedK mpl mmpl` from `h2kb_readStdin_hookSat`. -/
theorem h2kb_hole2_hioOf_readStdin
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    subroutine_ok
      (lsProg_617 (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)))
      (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl
        (readStdinSpecOfPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          hole2_hookStack ReadStdinBoundedEnv)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem
      (prog := lsProg_617 (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)))
      (i := 617)
      (h2kb_readStdin_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)
      (by decide)

/-- `MainIoOfPlacedSat.writeFile` (`withLsRet` form) at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2kb_hole2_hioOf_writeFile
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    subroutine_ok
      (lsProg_617 (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)))
      (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl
        (withLsRet
          (writeFileSpecPlacedSat cliIo
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            hole2_hookStack))) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  (h2k_hole2_hioOfK mpl mmpl hLs hMm W γ tp).writeFile

/-- `MainIoOfPlacedSat.writeStdout` (`withLsRet` form) at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2kb_hole2_hioOf_writeStdout
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    subroutine_ok
      (lsProg_617 (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)))
      (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl
        (withLsRet
          (writeStdoutSpecPlacedSat
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            hole2_hookStack))) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  (h2k_hole2_hioOfK mpl mmpl hLs hMm W γ tp).writeStdout

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
