/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Predicate-Parametric First-Stop Ghost-to-Real Transfer for `SampleNTT`

`CliElf`-free first-stop prefix transfer discharging the `SampleNTT` trajectory entry guards
(`mlkemStubStateEntryGuard`) across the 5 matrix-generating `libcrux_ml_kem` entry points
(`B24` `kemEncaps`, `B23` `kemDecaps`, `B10` `mlkemFromSeed`, `B19` `mlkemEncaps1`,
`B22` `mlkemDecaps`):

1. Real-side non-violation hypotheses and zero-hook/startup bridges (`RealNeverViolatesEntry`,
   `RealNeverViolatesFamily`, `steps_cliProgPlacedSig_of_running`): express that a real run never
   reaches a `.Running` state at an ML-KEM entry PC where `¬ P` (per symbol or across a coupled
   family `S`), and bridge `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` to
   `Placed.cliProgPlacedSig` (eliminating `∀ W : CliHooks` at zero hooks) and to process startup
   from `Placed.cliTokenPatchPlaced`.
2. Pointwise at-call replay (`AtCallRowReplayOn`) and predicate-parametric ML-KEM bridges: factor
   per-call replay at a single `.Running` stub state `u` satisfying `P u` (for any
   `P : State → Prop` with `∀ u, P u → *StateTerminates u`), independent of full-trajectory
   `mlkemStubStateEntryGuard`.
3. `StepsUntil` prefix transfer (`stepsUntil_transfer_ghost`): walks a deterministic first-stop
   prefix `StepsUntil P_ghost stop s0 u_first`, transferring `s0 →* u_first` to
   `Steps P_real s0 u_first` while supplying `¬ stop a` pointwise before `u_first`.
4. `mlkemStubStateEntryGuard` dischargers:
   - `mlkemStubStateEntryGuard_family_of_prefix` / `mlkemStubStateEntryGuard_of_prefix`: discharge
     `mlkemStubStateEntryGuard mpl EG sym P s0` from prefix-replayable non-`S` externs without
     assuming a ghost-return endpoint at `s0`.
   - `noBadOnGhostRun`, `mlkemStubStateEntryGuard_family_of_ghostRun`, and
     `mlkemStubStateEntryGuard_of_ghostRun`: discharge `mlkemStubStateEntryGuard` using existing
     `(s0, sf_end)` `GhostRowReplayOn` / `ExtraListReplaysOn` rows whenever `s0` has a ghost run
     `Steps P_ghost s0 sf_end` with no post-`sf_end` `.Running` visit to `S`.
5. `GhostExternReplaysOn` and `Block617TransferFixedHypG` combinators
   (`ghostExternReplaysOn_of_atCallFamily`, `block617TransferFixedG_of_replaysOn_withAtCallFamily`):
   discharge all `sym ∈ S` calls along `s0 →* sf` via first-stop contradiction against
   `RealNeverViolatesFamily`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (mlkemEncaps1Hook readVecN)
open CryptoVerification.E2E.Pqxdh (readVecN_eq_of_pointsToBytes)
open CryptoVerification.SignalSession
  (CliHooks Inputs MlKemSampleNttStuckAt abortOnPanic
   cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsKemDecapsSym lsKemEncapsSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemFromSeedSym)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliReachesSampleNttStuckPlaced cliExternsPlacedSig cliHookTablePlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges
  (KemDecapsCallTerminates KemEncapsCallTerminates MlkemDecapsCallTerminates
   MlkemEncaps1CallTerminates MlkemFromSeedCallTerminates
   kemDecaps_at_keepsFs_vm_premise_subroutineOk
   kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk
   mlkemDecaps_at_keepsFs_vm_premise_subroutineOk
   mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk
   mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk
   withPremise)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
  (externAt?_mlkemBlockProgram_ext_none kemDecapsAtSpec kemEncapsPreservedAtSpec
   mlkemDecapsAtSpec mlkemEncaps1AtSpec mlkemFromSeedAtSpec withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
  (mlkemKeep stripS_mem stripS_readReg64 strip_readBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
  (kyber1024DecapsVec kyber1024DecapsVec_toList kyber1024EncapsVec kyber1024EncapsVec_fst_toList
   kyber1024EncapsVec_snd_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
  (mlkem768Incremental_fromSeed_dk_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (mlkem768DecapsWith mlkem768Incremental sampleNtt toByteVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (PureFallbackPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.Placed.BridgeReloc (ls_resolve_data)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealPre ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace
   linkedCallHook standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (CallerLrUnmapped)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliProgExtPlacedSigAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
   cliStaticsPlacedAt externAt?_cliProgExtPlacedSigAt fetchMem_cliProgExtPlacedSigAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraListEntryGuard GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (linkedCallHookG linkedCallHookG_activeRealPre_of_noException linkedCallHookG_eq_of_guard
   linkedCallHookG_eq_of_not_guard linkedCallHookG_visitedIn withStateGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_externAt_none emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
  (KemDecapsStateTerminates KemEncapsStateTerminates MlKemSafeBridge MlkemDecapsStateTerminates
   MlkemEncaps1StateTerminates MlkemFromSeedStateTerminates kemDecapsGhost kemDecapsGhostAt
   kemDecapsSafeBridge kemEncapsGhost kemEncapsGhostAt kemEncapsSafeBridge
   mlkemActiveGuard mlkemActiveGuard_stripS_setPC mlkemBlockGhost mlkemBlockGhost_fs
   mlkemBlockGhost_keepLr_false_of_noException mlkemBlockGhost_preserves_execFrozen
   mlkemDecapsGhost mlkemDecapsGhostAt mlkemDecapsSafeBridge mlkemEncaps1Ghost mlkemEncaps1GhostAt
   mlkemEncaps1SafeBridge mlkemFromSeedGhost mlkemFromSeedGhostAt mlkemFromSeedSafeBridge
   mlkemInvMem mlkemInvMem_stripExecOutside mlkemStubStateEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (subroutine_ok_withLsRet withLsRet withLsRet_frameLeft withLsRet_outcome_setPC withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsFallback kemDecapsTightStack kemEncapsFallback kemEncapsTightStack kyber1024Prims₀
   mlkemDecapsFallback mlkemDecapsTightStack mlkemEncaps1Fallback mlkemEncaps1TightStack
   mlkemFromSeedFallback mlkemFromSeedTightStack mlkemHookStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_firstStop_of_steps h2fsgen_step_det h2fsgen_steps_lift_of_visitedIn_noExtern)

/-! ## 1. Real-Side Trajectory Hypotheses & 0-Hook / Startup Bridges -/

/-- Real-side non-violation hypothesis at stub symbol `sym`: starting from `s0`, the real program
    `cliProgExtPlacedAt mpl ER 617 W` never reaches a `.Running` state `u` at
    `u.pc = libsignalSessionLib.resolve mpl sym` with `¬ P u`. -/
@[expose] def RealNeverViolatesEntry (mpl : MultiPlacement)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop) (s0 : State) : Prop :=
  ∀ (W : CliHooks) (u : State),
    Steps (cliProgExtPlacedAt mpl ER 617 W) s0 u →
    u.pc = libsignalSessionLib.resolve mpl sym →
    u.status = .Running →
    P u

/-- Coupled family form of `RealNeverViolatesEntry` across a symbol list `S` with per-symbol state
    predicate `termOf : String → State → Prop`. -/
@[expose] def RealNeverViolatesFamily (mpl : MultiPlacement)
    (ER : CliHooks → String → Option (State → State))
    (S : List String) (termOf : String → State → Prop) (s0 : State) : Prop :=
  ∀ sym : String, sym ∈ S → RealNeverViolatesEntry mpl ER sym (termOf sym) s0

theorem RealNeverViolatesEntry.mono {mpl : MultiPlacement}
    {ER : CliHooks → String → Option (State → State)} {sym : String}
    {P P' : State → Prop} {s0 : State}
    (hImp : ∀ u : State, P u → P' u)
    (h : RealNeverViolatesEntry mpl ER sym P s0) :
    RealNeverViolatesEntry mpl ER sym P' s0 :=
  fun W u hsteps hpc hrun => hImp u (h W u hsteps hpc hrun)

theorem RealNeverViolatesFamily.mono {mpl : MultiPlacement}
    {ER : CliHooks → String → Option (State → State)} {S : List String}
    {termOf termOf' : String → State → Prop} {s0 : State}
    (hImp : ∀ sym u, sym ∈ S → termOf sym u → termOf' sym u)
    (h : RealNeverViolatesFamily mpl ER S termOf s0) :
    RealNeverViolatesFamily mpl ER S termOf' s0 :=
  fun sym hmem => (h sym hmem).mono (hImp sym · hmem)

theorem realNeverViolatesFamily_singleton {mpl : MultiPlacement}
    {ER : CliHooks → String → Option (State → State)} {sym : String}
    {P : State → Prop} {s0 : State}
    (h : RealNeverViolatesEntry mpl ER sym P s0) :
    RealNeverViolatesFamily mpl ER [sym] (fun _ => P) s0 := by
  intro sym' hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  exact h

/-- Canonical list of the 5 matrix-generating `libcrux_ml_kem` extern symbols in
    `libsignalSessionLib` / `cliExtraGhostSyms` whose real execution runs `SampleNTT`
    (`B24`, `B23`, `B10`, `B19`, `B22`). -/
@[expose] def mlkemSampleNttSyms : List String :=
  [lsKemEncapsSym, lsKemDecapsSym, lsMlkemFromSeedSym, lsMlkemEncaps1Sym, lsMlkemDecapsSym]

theorem mlkemSampleNttSyms_subset_extra :
    (mlkemSampleNttSyms.all cliExtraGhostSyms.contains) = true := by
  decide

/-- Default per-symbol `SampleNTT` state-termination predicate map for `mlkemSampleNttSyms`. -/
@[expose] def mlkemSampleNttTermOf (sym : String) (u : State) : Prop :=
  if sym == lsKemEncapsSym then KemEncapsStateTerminates u
  else if sym == lsKemDecapsSym then KemDecapsStateTerminates u
  else if sym == lsMlkemFromSeedSym then MlkemFromSeedStateTerminates u
  else if sym == lsMlkemEncaps1Sym then MlkemEncaps1StateTerminates u
  else if sym == lsMlkemDecapsSym then MlkemDecapsStateTerminates u
  else True

theorem mlkemSampleNttTermOf_kemEncaps (u : State) :
    mlkemSampleNttTermOf lsKemEncapsSym u = KemEncapsStateTerminates u := by
  have h1 : (lsKemEncapsSym == lsKemEncapsSym) = true := by decide
  simp only [mlkemSampleNttTermOf, h1, ↓reduceIte]

theorem mlkemSampleNttTermOf_kemDecaps (u : State) :
    mlkemSampleNttTermOf lsKemDecapsSym u = KemDecapsStateTerminates u := by
  have h1 : (lsKemDecapsSym == lsKemEncapsSym) = false := by decide
  have h2 : (lsKemDecapsSym == lsKemDecapsSym) = true := by decide
  simp only [mlkemSampleNttTermOf, h1, h2, Bool.false_eq_true, ↓reduceIte]

theorem mlkemSampleNttTermOf_mlkemFromSeed (u : State) :
    mlkemSampleNttTermOf lsMlkemFromSeedSym u = MlkemFromSeedStateTerminates u := by
  have h1 : (lsMlkemFromSeedSym == lsKemEncapsSym) = false := by decide
  have h2 : (lsMlkemFromSeedSym == lsKemDecapsSym) = false := by decide
  have h3 : (lsMlkemFromSeedSym == lsMlkemFromSeedSym) = true := by decide
  simp only [mlkemSampleNttTermOf, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

theorem mlkemSampleNttTermOf_mlkemEncaps1 (u : State) :
    mlkemSampleNttTermOf lsMlkemEncaps1Sym u = MlkemEncaps1StateTerminates u := by
  have h1 : (lsMlkemEncaps1Sym == lsKemEncapsSym) = false := by decide
  have h2 : (lsMlkemEncaps1Sym == lsKemDecapsSym) = false := by decide
  have h3 : (lsMlkemEncaps1Sym == lsMlkemFromSeedSym) = false := by decide
  have h4 : (lsMlkemEncaps1Sym == lsMlkemEncaps1Sym) = true := by decide
  simp only [mlkemSampleNttTermOf, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]

theorem mlkemSampleNttTermOf_mlkemDecaps (u : State) :
    mlkemSampleNttTermOf lsMlkemDecapsSym u = MlkemDecapsStateTerminates u := by
  have h1 : (lsMlkemDecapsSym == lsKemEncapsSym) = false := by decide
  have h2 : (lsMlkemDecapsSym == lsKemDecapsSym) = false := by decide
  have h3 : (lsMlkemDecapsSym == lsMlkemFromSeedSym) = false := by decide
  have h4 : (lsMlkemDecapsSym == lsMlkemEncaps1Sym) = false := by decide
  have h5 : (lsMlkemDecapsSym == lsMlkemDecapsSym) = true := by decide
  simp only [mlkemSampleNttTermOf, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

/-- Concrete instantiation of `RealNeverViolatesFamily` at the 5 `SampleNTT` entry symbols and their
    `*StateTerminates` predicates. -/
@[expose] def RealNeverViolatesSampleNtt (mpl : MultiPlacement)
    (ER : CliHooks → String → Option (State → State)) (s0 : State) : Prop :=
  RealNeverViolatesFamily mpl ER mlkemSampleNttSyms mlkemSampleNttTermOf s0

/-- At 0 hooks (`cliHookTablePlaced mmpl W = []`), `cliExternsPlaced mmpl W` is independent of
    `W : CliHooks` (`hTbl` defaults to `by rfl` at 0 hooks). -/
theorem cliExternsPlaced_congr_W (mmpl : MultiPlacement) (W₁ W₂ : CliHooks)
    (hTbl : cliHookTablePlaced mmpl W₁ = cliHookTablePlaced mmpl W₂ := by rfl) :
    cliExternsPlaced mmpl W₁ = cliExternsPlaced mmpl W₂ := by
  funext name
  unfold cliExternsPlaced
  rw [hTbl]

/-- At 0 hooks, `Placed.cliProgPlacedSig mpl mmpl W` is independent of `W` (`hTbl` defaults to
    `by rfl` at 0 hooks). -/
theorem cliProgPlacedSig_congr_W (mpl mmpl : MultiPlacement) (W₁ W₂ : CliHooks)
    (hTbl : cliHookTablePlaced mmpl W₁ = cliHookTablePlaced mmpl W₂ := by rfl) :
    cliProgPlacedSig mpl mmpl W₁ = cliProgPlacedSig mpl mmpl W₂ := by
  have hExt : cliExternsPlacedSig mmpl W₁ = cliExternsPlacedSig mmpl W₂ := by
    funext name
    unfold cliExternsPlacedSig
    rw [cliExternsPlaced_congr_W mmpl W₁ W₂ hTbl]
  unfold cliProgPlacedSig
  rw [hExt]

private theorem step_cliProgExtPlacedAt_to_sig_of_running
    {mpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {W : CliHooks} {s s' : State}
    (h : Step (cliProgExtPlacedAt mpl ext idx W) s s')
    (hrun' : s'.status = .Running) :
    Step (cliProgExtPlacedSigAt mpl ext idx W) s s' := by
  cases h with
  | @exec inst h_run h_fetch =>
    exact Step.exec h_run ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
  | halt_unmapped => cases hrun'
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig :
        (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    have hab : abortOnPanic f s = f s := by
      unfold abortOnPanic; dsimp only; rw [hrun']
    rw [← hab]
    exact Step.extern h_run h_ext_sig (hab ▸ h_keep) (hab ▸ h_sym)
  | extern_fault => cases hrun'

private theorem steps_cliProgExtPlacedAt_to_sig_of_running
    {mpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {W : CliHooks} {s0 sf : State}
    (hsteps : Steps (cliProgExtPlacedAt mpl ext idx W) s0 sf)
    (hrun_sf : sf.status = .Running) :
    Steps (cliProgExtPlacedSigAt mpl ext idx W) s0 sf := by
  induction hsteps with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    have hrun2 : s2.status = .Running := by
      cases h2 with
      | refl => exact hrun_sf
      | step h2a _ => exact h2a.status_running
    exact Steps.step (step_cliProgExtPlacedAt_to_sig_of_running h1 hrun2) (ih hrun_sf)

/-- Any `.Running →* .Running` trajectory of `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
    is also a trajectory of `Placed.cliProgPlacedSig mpl mmpl W₀` for any witness `W₀ : CliHooks`. -/
theorem steps_cliProgPlacedSig_of_running
    {mpl mmpl : MultiPlacement} (W₀ W : CliHooks) {s0 u : State}
    (_hrun0 : s0.status = .Running)
    (hrun_u : u.status = .Running)
    (hsteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s0 u)
    (hTbl : cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by rfl) :
    Steps (cliProgPlacedSig mpl mmpl W₀) s0 u := by
  have hsig := steps_cliProgExtPlacedAt_to_sig_of_running hsteps hrun_u
  rwa [cliProgExtPlacedSigAt_cliExternsPlaced_eq,
    cliProgPlacedSig_congr_W mpl mmpl W W₀ hTbl] at hsig

/-- Lift a single-`W₀` `cliProgPlacedSig` non-violation hypothesis at `.Running` state `s0` to
    `RealNeverViolatesEntry mpl (cliExternsPlaced mmpl) sym P s0` across all `W : CliHooks`. -/
theorem realNeverViolatesEntry_of_cliProgPlacedSig
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {sym : String} {P : State → Prop} {s0 : State}
    (hrun0 : s0.status = .Running)
    (hSig : ∀ u : State,
      Steps (cliProgPlacedSig mpl mmpl W₀) s0 u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      P u)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesEntry mpl (cliExternsPlaced mmpl) sym P s0 :=
  fun W u hsteps hpc hrun =>
    hSig u (steps_cliProgPlacedSig_of_running W₀ W hrun0 hrun hsteps (hTbl W)) hpc hrun

/-- Family counterpart of `realNeverViolatesEntry_of_cliProgPlacedSig`. -/
theorem realNeverViolatesFamily_of_cliProgPlacedSig
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {S : List String}
    {termOf : String → State → Prop} {s0 : State}
    (hrun0 : s0.status = .Running)
    (hSig : ∀ sym u,
      sym ∈ S →
      Steps (cliProgPlacedSig mpl mmpl W₀) s0 u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      termOf sym u)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesFamily mpl (cliExternsPlaced mmpl) S termOf s0 :=
  fun sym hmem =>
    realNeverViolatesEntry_of_cliProgPlacedSig W₀ hrun0
      (fun u hs hpc hr => hSig sym u hmem hs hpc hr) hTbl

/-- Chain process startup `Steps (cliProgPlacedSig mpl mmpl W₀) s_init sm` (`sm.status = .Running`)
    with process-level non-violation from `s_init` (e.g. `cliTokenPatchPlaced mpl s_elf`) to obtain
    `RealNeverViolatesEntry` at `main` entry `sm`. -/
theorem realNeverViolatesEntry_of_startup
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {sym : String} {P : State → Prop}
    {s_init sm : State}
    (hStart : Steps (cliProgPlacedSig mpl mmpl W₀) s_init sm)
    (hrun_sm : sm.status = .Running)
    (hProc : ∀ u : State,
      Steps (cliProgPlacedSig mpl mmpl W₀) s_init u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      P u)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesEntry mpl (cliExternsPlaced mmpl) sym P sm :=
  realNeverViolatesEntry_of_cliProgPlacedSig W₀ hrun_sm
    (fun u hsteps hpc hrun => hProc u (hStart.trans hsteps) hpc hrun) hTbl

/-- Family counterpart of `realNeverViolatesEntry_of_startup` (e.g. from `s_init :=
    cliTokenPatchPlaced mpl s_elf` to `main` entry `sm`). -/
theorem realNeverViolatesFamily_of_startup
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {S : List String}
    {termOf : String → State → Prop} {s_init sm : State}
    (hStart : Steps (cliProgPlacedSig mpl mmpl W₀) s_init sm)
    (hrun_sm : sm.status = .Running)
    (hProc : ∀ sym u,
      sym ∈ S →
      Steps (cliProgPlacedSig mpl mmpl W₀) s_init u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      termOf sym u)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesFamily mpl (cliExternsPlaced mmpl) S termOf sm :=
  fun sym hmem =>
    realNeverViolatesEntry_of_startup W₀ hStart hrun_sm
      (fun u hs hpc hr => hProc sym u hmem hs hpc hr) hTbl

/-- Specialization of `realNeverViolatesFamily_of_startup` to `cliTokenPatchPlaced mpl s_elf` for a
    loaded ELF initial state `elf.loadState (cliProcessInputs i) = .ok s_elf`. -/
theorem realNeverViolatesFamily_of_elfLoad
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {elf : ElfImage} {i : Inputs}
    {S : List String} {termOf : String → State → Prop} {s_elf sm : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s_elf)
    (hStart : Steps (cliProgPlacedSig mpl mmpl W₀) (cliTokenPatchPlaced mpl s_elf) sm)
    (hrun_sm : sm.status = .Running)
    (hNotStuck : ¬ ∃ s0 u,
      elf.loadState (cliProcessInputs i) = .ok s0 ∧
      Steps (cliProgPlacedSig mpl mmpl W₀) (cliTokenPatchPlaced mpl s0) u ∧
      u.status = .Running ∧
      ∃ sym ∈ S, u.pc = libsignalSessionLib.resolve mpl sym ∧ ¬ termOf sym u)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesFamily mpl (cliExternsPlaced mmpl) S termOf sm := by
  refine realNeverViolatesFamily_of_startup W₀ hStart hrun_sm
    (fun sym u hmem hsteps hpc hrun => ?_) hTbl
  exact Classical.byContradiction fun hnot =>
    hNotStuck ⟨s_elf, u, hLoad, hsteps, hrun, sym, hmem, hpc, hnot⟩

/-! ## 2. Pointwise At-Call Replay (`AtCallRowReplayOn`) & Predicate-Parametric ML-KEM Bridges -/

/-- Pointwise per-call behind-stub replay obligation at a single `.Running` call state `u`
    satisfying `P u` (with zero dependence on a global trajectory `mlkemStubStateEntryGuard` or
    subroutine return endpoint `sf`). -/
structure AtCallRowReplayOn
    (mpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State))
    (sym : String) (P : State → Prop) (f : State → State) : Prop where
  preserves_execFrozen :
    ∀ u : State, u.status = .Running → (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → ExecFrozen (f u).mem ∧ (f u).fs = u.fs
  preserves_symtab :
    ∀ u : State, (f u).symtab = u.symtab
  real_stub_none :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = none
  replay_at_call :
    ∀ (W : CliHooks) (u : State),
      P u →
      u.pc = libsignalSessionLib.resolve mpl sym →
      u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f u).mem →
      ExecFrozen u.mem →
      InvS u →
      Steps (cliProgExtPlacedAt mpl ER 617 W) u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u)

/-- Contravariant weakening of `AtCallRowReplayOn` in the call-state predicate `P`. -/
theorem AtCallRowReplayOn.mono_pred
    {mpl : MultiPlacement} {InvS : State → Prop}
    {ER : CliHooks → String → Option (State → State)}
    {sym : String} {P P' : State → Prop} {f : State → State}
    (hImp : ∀ u : State, P' u → P u)
    (h : AtCallRowReplayOn mpl InvS ER sym P f) :
    AtCallRowReplayOn mpl InvS ER sym P' f where
  preserves_execFrozen := h.preserves_execFrozen
  preserves_symtab := h.preserves_symtab
  real_stub_none := h.real_stub_none
  replay_at_call := fun W u hP' => h.replay_at_call W u (hImp u hP')

/-- Any `AtCallRowReplayOn` at `ER := cliExternsPlaced mmpl` immediately lifts to a trajectory-level
    `GhostRowReplayOn` guarded by `mlkemStubStateEntryGuard mpl EG sym P`. -/
theorem AtCallRowReplayOn.toGhostRowReplayOn
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {sym : String} {P : State → Prop} {f : State → State}
    (EG : CliHooks → String → Option (State → State))
    (h : AtCallRowReplayOn mpl InvS (cliExternsPlaced mmpl) sym P f) :
    GhostRowReplayOn mpl mmpl InvS EG sym (mlkemStubStateEntryGuard mpl EG sym P) f where
  preserves_execFrozen := h.preserves_execFrozen
  replay_at_stub := fun W _s0 _sf hEntry _hret _hnoex _hnhalt =>
    Or.inr ⟨h.real_stub_none W, fun u hsteps_u _ hpc hrun hnoex hkf hfr hinv =>
      h.replay_at_call W u (hEntry W u hsteps_u hpc hrun) hpc hrun hnoex hkf hfr hinv⟩

section MlKemAtCall

variable [LibsignalPlacement]

private theorem mlkem768Incremental_decaps_eq_local
    (d : List.Vector (BitVec 8) 2400) (c1 : List.Vector (BitVec 8) 960)
    (c2 : List.Vector (BitVec 8) 128) :
    mlkem768Incremental.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList) :=
  rfl

attribute [local irreducible] kyber1024EncapsVec kyber1024DecapsVec mlkem768Incremental

private theorem stripS_setPC_readBytes_local (keep : BitVec 64 → Bool) (s : State)
    (pc a : BitVec 64) (n : Nat) :
    (stripS keep (s.setPC pc)).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem]
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [hmem]
  exact strip_readBytes keep s.mem a n

private theorem stripS_setPC_readVecN_local (keep : BitVec 64 → Bool) (s : State)
    (pc a : BitVec 64) (n : Nat) :
    readVecN (stripS keep (s.setPC pc)).mem a n = readVecN s.mem a n :=
  Subtype.ext (stripS_setPC_readBytes_local keep s pc a n)

private theorem keepsFs_strip_inv_local {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (keepsFs master) where
  pre_eq := fun x s => by
    dsimp only [keepsFs]
    have hs : stripS keep s = s.setMem (stripExecOutside keep s.mem) := by cases s; rfl
    rw [hs, B.m_pre_mem]
  post_eq := fun x s0 sf => by
    dsimp only [keepsFs]
    have hs0 : stripS keep s0 = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    have hsf : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
    have hfs : (stripS keep sf).fs = sf.fs ∧ (stripS keep s0).fs = s0.fs := by
      cases s0; cases sf; exact ⟨rfl, rfl⟩
    rw [hfs.1, hfs.2, hs0, hsf, B.m_post_mem]
  onPanic_eq := fun _ _ _ => by dsimp only [keepsFs]; rw [B.m_pan]
  onExit_eq := fun _ _ _ _ => by dsimp only [keepsFs]; rw [B.m_ex]
  onOom_eq := fun _ _ _ => by dsimp only [keepsFs]; rw [B.m_oom]

private theorem keepsFs_fsT_local {α : Type} {master : Spec α} {j : Nat} {sym : String}
    {fallback : State → State} (B : MlKemSafeBridge j sym master fallback) :
    SpecPreservesFsTrace (keepsFs master) := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1, FsTraced.of_eq (B.post_tr x R s0 sf hpost.2) (congrArg (·.files) hpost.1)⟩
  · dsimp only [keepsFs] at hp; rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
  · dsimp only [keepsFs] at he; rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
  · dsimp only [keepsFs] at ho; rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem specStripSInvariant_withLsRet_local {keep : BitVec 64 → Bool} {α : Type}
    {spec : Spec α} (h : SpecStripSInvariant keep spec) :
    SpecStripSInvariant keep (withLsRet spec) where
  pre_eq := fun x s => by dsimp only [withLsRet]; rw [stripS_readReg64, h.pre_eq x s]
  post_eq := h.post_eq
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq

private theorem specPreservesFsTrace_withLsRet_local {α : Type} {spec : Spec α}
    (h : SpecPreservesFsTrace spec) :
    SpecPreservesFsTrace (withLsRet spec) := h

private theorem subroutineOk_guarded_from_multi_local {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {CallTerm : α → Prop} {StateTerm : State → Prop}
    (mlkemMpl : MultiPlacement)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0))
    (hmok : mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (withPremise CallTerm (keepsFs (withVmPreserved master))))
      (fun _ => none))
    (hStateImpCall : ∀ (x : α) (R : SepProp) (s : State),
      StateTerm s → s.mem ⊨ master.pre x s ∗ R → CallTerm x) :
    subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)
        (withLsRet (keepsFs master))) := by
  obtain ⟨_, i, off, hsym', hsub⟩ := hmok
  have hij : i = j ∧ off = 0 := by
    rw [hsym] at hsym'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsym'
    exact ⟨hsym'.1.symm, hsym'.2.symm⟩
  rcases hij with ⟨hi, hoff⟩
  subst i
  subst off
  have hfn : mlkemMultiLib.fnAddr mlkemMpl sym = mlkemMpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  have hBase : subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u) (keepsFs master)) := by
    apply subroutine_ok.of_codeLoaded
    intro x R s0 hpc hrun hpre hsp _hL
    dsimp only [withStateGuard, keepsFs] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hG, hT⟩, hpreM⟩ := hpre
    have hCall : CallTerm x := hStateImpCall x R s0 hT hpreM
    have hok_mpl := hsub mlkemMpl hG.1
    rw [hfn] at hok_mpl
    have hpre_sub : s0.mem ⊨
        (mlkemMultiLib.withCodeLoaded mlkemMpl
          (withMlKemRoOk mlkemMpl (withPremise CallTerm (keepsFs (withVmPreserved master))))).pre
          x s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs, withVmPreserved]
      rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hG.2.1,
        sepConj_assoc, pure_sepConj_of_true hG.2.2,
        sepConj_assoc, pure_sepConj_of_true hCall]
      exact hpreM
    exact hok_mpl.mono_outcome x R s0 hpc hrun hpre_sub hsp fun sf hout => by
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, he, hex⟩ | ⟨ho, hoom⟩
      · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
          withVmPreserved] at hpost
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
        obtain ⟨hfs, hvm_post⟩ := hpost
        rw [sepConj_assoc, satisfies_pure_sepConj] at hvm_post
        refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withStateGuard, keepsFs]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hfs, hvm_post.2⟩
      · exact Or.inr (Or.inl ⟨hp, hpan⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))
  have hLs := subroutine_ok_withLsRet hBase
  have hComm :
      withLsRet (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u) (keepsFs master)) =
        withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u) (withLsRet (keepsFs master)) :=
    withLsRet_frameLeft (keepsFs master)
      (fun _ s => ⌜mlkemActiveGuard mlkemMpl s ∧ StateTerm s⌝) (keepsFs master).post
  rwa [hComm] at hLs

/-- Symbol-table preservation for `mlkemBlockGhost` whenever `fallback` preserves `.symtab`. -/
theorem mlkemBlockGhost_symtab
    (mlkemMpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) {fallback : State → State}
    (hfb_sym : ∀ s : State, (fallback s).symtab = s.symtab)
    (u : State) :
    (mlkemBlockGhost mlkemMpl j master fallback u).symtab = u.symtab := by
  classical
  have hkfb_sym : ∀ s : State, (keepFsTrace fallback s).symtab = s.symtab := by
    intro s
    unfold keepFsTrace
    simpa using hfb_sym s
  unfold mlkemBlockGhost linkedCallHookG
  split
  · unfold linkedCallHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).1.toSteps.symtab_eq
      · exact hkfb_sym u
    · rfl
  · split
    · exact hkfb_sym u
    · rfl

/-- Generic pointwise `AtCallRowReplayOn` builder for `mlkemBlockGhost`, requiring `StateTerm u`
    only at the call state `u` (with zero trajectory-level `mlkemStubStateEntryGuard` premise). -/
theorem mlkemBlockGhost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    {j : Nat} (hj : j < mlkemMultiLib.blocks.length) {α : Type}
    {master : Spec α} {fallback : State → State}
    (StateTerm : State → Prop)
    (hTermStrip : ∀ s0 : State, StateTerm s0 →
      StateTerm (stripS (mlkemKeep mlkemMpl) (s0.setPC (mlkemMpl.base j))))
    (hSubOk : subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)
        (withLsRet (keepsFs master))))
    (hStripInv : SpecStripSInvariant (mlkemKeep mlkemMpl) (keepsFs master))
    (hFsT : SpecPreservesFsTrace (keepsFs master))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (keepsFs master).pre x (s.setPC pc) = (keepsFs master).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (keepsFs master) x R (s0.setPC pc) sf →
        SubroutineOutcome (keepsFs master) x R s0 sf)
    (hfb : PureFallbackPreserved fallback)
    (hfb_sym : ∀ s : State, (fallback s).symtab = s.symtab)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base j)) :
    AtCallRowReplayOn mpl InvS ER sym StateTerm
      (mlkemBlockGhost mlkemMpl j (keepsFs master) fallback) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨mlkemBlockGhost_preserves_execFrozen mlkemMpl j (keepsFs master) hfb hfr,
     mlkemBlockGhost_fs mlkemMpl j (keepsFs master) fallback u⟩
  preserves_symtab := mlkemBlockGhost_symtab mlkemMpl j (keepsFs master) hfb_sym
  real_stub_none := hRealStubNone
  replay_at_call := by
    intro W u hTu hpc hrun hnoex hkf hfr hInvU
    have hInvM : mlkemInvMem mlkemMpl u.mem := hInvMlkem u hInvU
    have hGu : mlkemActiveGuard mlkemMpl u := hInvM
    have hlr : mlkemKeep mlkemMpl (u.readReg64 .lr) = false :=
      mlkemBlockGhost_keepLr_false_of_noException hKeep hnoex
    have hCodeSub : (mlkemMultiLib.blockProgram mlkemMpl j).CodeLoaded
        (stripExecOutside (mlkemKeep mlkemMpl) u.mem) :=
      (mlkemInvMem_stripExecOutside hInvM).2.1 j hj
    have hEqG : mlkemBlockGhost mlkemMpl j (keepsFs master) fallback u =
        linkedCallHookG (fun v => mlkemActiveGuard mlkemMpl v ∧ StateTerm v)
          (mlkemKeep mlkemMpl) emptyStdProg (mlkemMultiLib.blockProgram mlkemMpl j)
          (mlkemMpl.base j) (withLsRet (keepsFs master)) fallback u := by
      unfold mlkemBlockGhost
      rw [linkedCallHookG_eq_of_guard hGu, linkedCallHookG_eq_of_guard ⟨hGu, hTu⟩]
    have hActPre : ActiveRealPre (withLsRet (keepsFs master)) u :=
      linkedCallHookG_activeRealPre_of_noException hnoex
    obtain ⟨hvis, hfr_out⟩ :=
      linkedCallHookG_visitedIn (Guard := fun v => mlkemActiveGuard mlkemMpl v ∧ StateTerm v)
        (fallback := fallback) emptyStdProg_svc (rfl : (mlkemMultiLib.blockProgram mlkemMpl j).svc = Syscall.standard)
        (fun pc _ => emptyStdProg_externAt_none pc)
        (externAt?_mlkemBlockProgram_ext_none mlkemMpl hj (fun _ => none))
        (fun v _ ⟨hg, ht⟩ => ⟨mlkemActiveGuard_stripS_setPC mlkemMpl _ v hg, hTermStrip v ht⟩)
        hSubOk (specStripSInvariant_withLsRet_local hStripInv)
        (specPreservesFsTrace_withLsRet_local hFsT)
        (withLsRet_pre_setPC hPrePC) (withLsRet_outcome_setPC hOutPC)
        ⟨hGu, hTu⟩ hActPre hfr hlr hCodeSub
    rw [← hEqG] at hvis hfr_out
    have hStubSteps := hStub W u hpc hrun hfr hInvM
    have hBodySteps := h2fsgen_steps_lift_of_visitedIn_noExtern
      (D := mlkemKeep mlkemMpl) (P1 := emptyStdProg)
      (P2 := cliProgExtPlacedAt mpl ER 617 W)
      emptyStdProg_svc
      (fun pc _ => emptyStdProg_externAt_none pc) (fun _ hk => hRealMlkemNoExt W hk) hvis
    exact ⟨hStubSteps.trans hBodySteps, hfr_out,
      hInvKeep u _ hInvU hkf (mlkemBlockGhost_fs mlkemMpl j (keepsFs master) fallback u)⟩

/-- Hook #1 (`kemEncapsGhostAt`, `B24`): predicate-parametric pointwise `AtCallRowReplayOn`,
    parametric in `P : State → Prop` under `∀ u, P u → KemEncapsStateTerminates u`
    (defaults to `P := KemEncapsStateTerminates`). -/
theorem kemEncapsGhostAt_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → KemEncapsStateTerminates u)
    (stk : Nat) (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 24)) :
    AtCallRowReplayOn mpl InvS ER sym P (kemEncapsGhostAt mlkemMpl stk) := by
  let B := kemEncapsSafeBridge stk hstk hfit
  have hSub := kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
    (fun pk rand => ⟨kyber1024EncapsVec_fst_toList pk rand, kyber1024EncapsVec_snd_toList pk rand⟩)
    stk hstk hfit (fun _ => none)
  have hBase : AtCallRowReplayOn mpl InvS ER sym KemEncapsStateTerminates
      (kemEncapsGhostAt mlkemMpl stk) :=
    mlkemBlockGhost_atCallReplayOn mpl mlkemMpl InvS ER sym B.hj
      KemEncapsStateTerminates
      (fun s0 hT => by
        unfold KemEncapsStateTerminates at hT ⊢
        rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 24)).readReg64 .x0 = s0.readReg64 .x0
          by cases s0; rfl, stripS_setPC_readBytes_local]
        exact hT)
      (subroutineOk_guarded_from_multi_local mlkemMpl B.hsym hSub
        fun ⟨pkA, pk, rA, rnd, ret⟩ R s hT hpre => by
          dsimp only [kemEncapsPreservedAtSpec, withStack] at hpre
          simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
          obtain ⟨⟨hx0, _, _⟩, hmem⟩ := hpre
          obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes pkA pk.toList).read hmem
          rw [pk.toList_length] at hread
          unfold KemEncapsCallTerminates
          unfold KemEncapsStateTerminates at hT
          rwa [hx0, hread] at hT)
      (keepsFs_strip_inv_local B (mlkemKeep mlkemMpl)) (keepsFs_fsT_local B)
      (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
      B.fb_pres (fun _ => rfl) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact hBase.mono_pred hImp

/-- Hook #2 (`kemDecapsGhostAt`, `B23`): predicate-parametric pointwise `AtCallRowReplayOn`. -/
theorem kemDecapsGhostAt_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → KemDecapsStateTerminates u)
    (stk : Nat) (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 23)) :
    AtCallRowReplayOn mpl InvS ER sym P (kemDecapsGhostAt mlkemMpl stk) := by
  let B := kemDecapsSafeBridge stk hstk hfit
  have hSub := kemDecaps_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
    kyber1024DecapsVec_toList stk hstk hfit (fun _ => none)
  have hBase : AtCallRowReplayOn mpl InvS ER sym KemDecapsStateTerminates
      (kemDecapsGhostAt mlkemMpl stk) :=
    mlkemBlockGhost_atCallReplayOn mpl mlkemMpl InvS ER sym B.hj
      KemDecapsStateTerminates
      (fun s0 hT => by
        unfold KemDecapsStateTerminates at hT ⊢
        rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 23)).readReg64 .x0 = s0.readReg64 .x0
          by cases s0; rfl, stripS_setPC_readBytes_local]
        exact hT)
      (subroutineOk_guarded_from_multi_local mlkemMpl B.hsym hSub
        fun ⟨skA, sk, ctA, ct, ret⟩ R s hT hpre => by
          dsimp only [kemDecapsAtSpec, withStack] at hpre
          simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
          obtain ⟨⟨hx0, _, _⟩, hmem⟩ := hpre
          obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes skA sk.toList).read hmem
          rw [sk.toList_length] at hread
          unfold KemDecapsCallTerminates
          unfold KemDecapsStateTerminates at hT
          rwa [hx0, hread] at hT)
      (keepsFs_strip_inv_local B (mlkemKeep mlkemMpl)) (keepsFs_fsT_local B)
      (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
      B.fb_pres (fun _ => rfl) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact hBase.mono_pred hImp

/-- Hook #3 (`mlkemFromSeedGhostAt`, `B10`): predicate-parametric pointwise `AtCallRowReplayOn`. -/
theorem mlkemFromSeedGhostAt_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemFromSeedStateTerminates u)
    (stk : Nat) (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 10)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemFromSeedGhostAt mlkemMpl stk) := by
  let B := mlkemFromSeedSafeBridge stk hstk hfit
  have hSub := mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList stk hstk hfit (fun _ => none)
  have hBase : AtCallRowReplayOn mpl InvS ER sym MlkemFromSeedStateTerminates
      (mlkemFromSeedGhostAt mlkemMpl stk) :=
    mlkemBlockGhost_atCallReplayOn mpl mlkemMpl InvS ER sym B.hj
      MlkemFromSeedStateTerminates
      (fun s0 hT => by
        unfold MlkemFromSeedStateTerminates at hT ⊢
        rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 10)).readReg64 .x0 = s0.readReg64 .x0
          by cases s0; rfl, stripS_setPC_readVecN_local]
        exact hT)
      (subroutineOk_guarded_from_multi_local mlkemMpl B.hsym hSub fun x R s hT hpre => by
        dsimp only [mlkemFromSeedAtSpec] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨⟨hx0, _⟩, hmem⟩ := hpre
        have hread : readVecN s.mem x.seedA 64 = x.seed := readVecN_eq_of_pointsToBytes hmem
        unfold MlkemFromSeedCallTerminates
        unfold MlkemFromSeedStateTerminates at hT
        rwa [hx0, hread] at hT)
      (keepsFs_strip_inv_local B (mlkemKeep mlkemMpl)) (keepsFs_fsT_local B)
      (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
      B.fb_pres (fun _ => rfl) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact hBase.mono_pred hImp

/-- Hook #4 (`mlkemEncaps1GhostAt`, `B19`): predicate-parametric pointwise `AtCallRowReplayOn`. -/
theorem mlkemEncaps1GhostAt_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemEncaps1StateTerminates u)
    (stk : Nat) (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 19)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemEncaps1GhostAt mlkemMpl stk) := by
  let B := mlkemEncaps1SafeBridge stk hstk hfit
  have hSub := mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    (fun _ _ => rfl) stk hstk hfit (fun _ => none)
  have hBase : AtCallRowReplayOn mpl InvS ER sym MlkemEncaps1StateTerminates
      (mlkemEncaps1GhostAt mlkemMpl stk) :=
    mlkemBlockGhost_atCallReplayOn mpl mlkemMpl InvS ER sym B.hj
      MlkemEncaps1StateTerminates
      (fun s0 hT => by
        unfold MlkemEncaps1StateTerminates at hT ⊢
        rw [stripS_readReg64, stripS_readReg64,
          show (s0.setPC (mlkemMpl.base 19)).readReg64 .x0 = s0.readReg64 .x0 by cases s0; rfl,
          show (s0.setPC (mlkemMpl.base 19)).readReg64 .x1 = s0.readReg64 .x1 by cases s0; rfl,
          stripS_setPC_readBytes_local]
        exact hT)
      (subroutineOk_guarded_from_multi_local mlkemMpl B.hsym hSub fun x R s hT hpre => by
        dsimp only [mlkemEncaps1AtSpec] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨⟨_, hx0, hx1, _, _, _, _, _⟩, hmem⟩ := hpre
        obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
        unfold MlkemEncaps1CallTerminates
        unfold MlkemEncaps1StateTerminates at hT
        rwa [hx0, hx1, hread] at hT)
      (keepsFs_strip_inv_local B (mlkemKeep mlkemMpl)) (keepsFs_fsT_local B)
      (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
      B.fb_pres
      (fun s => by
        unfold mlkemEncaps1Fallback mlkemEncaps1Hook retHook
        dsimp only
        split <;> (try split) <;> rfl)
      hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact hBase.mono_pred hImp

/-- Hook #6 (`mlkemDecapsGhostAt`, `B22`): predicate-parametric pointwise `AtCallRowReplayOn`. -/
theorem mlkemDecapsGhostAt_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemDecapsStateTerminates u)
    (stk : Nat) (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 22)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemDecapsGhostAt mlkemMpl stk) := by
  let B := mlkemDecapsSafeBridge stk hstk hfit
  have hSub := mlkemDecaps_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_decaps_eq_local stk hstk hfit (fun _ => none)
  have hBase : AtCallRowReplayOn mpl InvS ER sym MlkemDecapsStateTerminates
      (mlkemDecapsGhostAt mlkemMpl stk) :=
    mlkemBlockGhost_atCallReplayOn mpl mlkemMpl InvS ER sym B.hj
      MlkemDecapsStateTerminates
      (fun s0 hT => by
        unfold MlkemDecapsStateTerminates at hT ⊢
        rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 22)).readReg64 .x0 = s0.readReg64 .x0
          by cases s0; rfl, stripS_setPC_readVecN_local]
        exact hT)
      (subroutineOk_guarded_from_multi_local mlkemMpl B.hsym hSub fun x R s hT hpre => by
        dsimp only [mlkemDecapsAtSpec] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨⟨_, hx0, _, _⟩, hmem⟩ := hpre
        have hread : readVecN s.mem x.dkA 2400 = x.dk := readVecN_eq_of_pointsToBytes hmem
        unfold MlkemDecapsCallTerminates
        unfold MlkemDecapsStateTerminates at hT
        rwa [hx0, hread] at hT)
      (keepsFs_strip_inv_local B (mlkemKeep mlkemMpl)) (keepsFs_fsT_local B)
      (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
      B.fb_pres (fun _ => rfl) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact hBase.mono_pred hImp

/-- Default-stack (`mlkemHookStack = 65536`) specialization of `kemEncapsGhostAt_atCallReplayOn`. -/
theorem kemEncapsGhost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → KemEncapsStateTerminates u)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 24)) :
    AtCallRowReplayOn mpl InvS ER sym P (kemEncapsGhost mlkemMpl) :=
  kemEncapsGhostAt_atCallReplayOn mpl mlkemMpl InvS ER sym P hImp mlkemHookStack (by decide)
    (by decide) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Default-stack (`mlkemHookStack = 65536`) specialization of `kemDecapsGhostAt_atCallReplayOn`. -/
theorem kemDecapsGhost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → KemDecapsStateTerminates u)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 23)) :
    AtCallRowReplayOn mpl InvS ER sym P (kemDecapsGhost mlkemMpl) :=
  kemDecapsGhostAt_atCallReplayOn mpl mlkemMpl InvS ER sym P hImp mlkemHookStack (by decide)
    (by decide) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Default-stack (`mlkemHookStack = 65536`) specialization of `mlkemFromSeedGhostAt_atCallReplayOn`. -/
theorem mlkemFromSeedGhost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemFromSeedStateTerminates u)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 10)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemFromSeedGhost mlkemMpl) :=
  mlkemFromSeedGhostAt_atCallReplayOn mpl mlkemMpl InvS ER sym P hImp mlkemHookStack (by decide)
    (by decide) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Default-stack (`mlkemHookStack = 65536`) specialization of `mlkemEncaps1GhostAt_atCallReplayOn`. -/
theorem mlkemEncaps1Ghost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemEncaps1StateTerminates u)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 19)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemEncaps1Ghost mlkemMpl) :=
  mlkemEncaps1GhostAt_atCallReplayOn mpl mlkemMpl InvS ER sym P hImp mlkemHookStack (by decide)
    (by decide) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Default-stack (`mlkemHookStack = 65536`) specialization of `mlkemDecapsGhostAt_atCallReplayOn`. -/
theorem mlkemDecapsGhost_atCallReplayOn
    (mpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (ER : CliHooks → String → Option (State → State)) (sym : String)
    (P : State → Prop)
    (hImp : ∀ u : State, P u → MlkemDecapsStateTerminates u)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl ER 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 22)) :
    AtCallRowReplayOn mpl InvS ER sym P (mlkemDecapsGhost mlkemMpl) :=
  mlkemDecapsGhostAt_atCallReplayOn mpl mlkemMpl InvS ER sym P hImp mlkemHookStack (by decide)
    (by decide) hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

end MlKemAtCall

/-! ## 3. Operational Determinism & `StepsUntil` Prefix Ghost-to-Real Transfer -/

private theorem execInst_preserves_execFrozen_and_fs {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem ∧ (execInst inst s).fs = s.fs := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ⟨ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1), hpf.2.2.2.2.2.2⟩

private theorem evalInst_eq_execInst_of_not_isSvc0 (P : Program) {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    P.evalInst inst s = execInst inst s := by
  cases inst <;> simp [Instr.isSvc0] at h
  case system isMrs imm16 =>
    cases isMrs
    · simp at h
      simp [Program.evalInst, execInst, execInstWithSvc, h]
    · rfl
  all_goals rfl

private theorem steps_preserves_halted {P : Program} {s sf : State}
    (h : Steps P s sf) (hs : s.status = .Halted) : sf.status = .Halted := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem steps_preserves_exception {P : Program} {s sf : State} {msg : String}
    (h : Steps P s sf) (hs : s.status = .Exception msg) : sf.status = .Exception msg := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem h2fsgen_steps_eq_of_not_running {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    have hrun : s1.status = .Running := by cases h1 <;> assumption
    exact absurd hrun hnr

/-- Operational comparability of two `Steps P` prefixes from the same start state `s0`:
    by `h2fsgen_step_det`, one state lies on the trajectory to the other. -/
theorem steps_comparable {P : Program} {s0 a b : State}
    (hsa : Steps P s0 a) (hsb : Steps P s0 b) :
    Steps P a b ∨ Steps P b a := by
  induction hsa with
  | refl _ => exact Or.inl hsb
  | @step x y _ hxy hya ih =>
    cases hsb with
    | refl _ => exact Or.inr (Steps.step hxy hya)
    | step hxy' hy'b =>
      have hy : y = _ := h2fsgen_step_det hxy hxy'
      subst hy
      exact ih hy'b

/-- Pointwise-clean (`¬ stop a`) prefix extern-replay obligation along a first-stop trajectory
    `s0 →* u_first` with optional post-stop suffix `u_first →* sf_end`. At every step `a → f a`
    strictly before `u_first`, the caller receives `¬ stop a`, `Steps P_ghost s0 a`,
    `Steps P_ghost (f a) u_first`, and `Steps P_ghost (f a) sf_end`. -/
@[expose] def PrefixExternReplaysUntil
    (keep : BitVec 64 → Bool) (InvS : State → Prop) (stop : State → Prop)
    (P_ghost P_real : Program) (s0 u_first sf_end : State) : Prop :=
  ∀ (pc : BitVec 64) (f : State → State),
    P_ghost.externAt? pc = some f →
    (P_real.externAt? pc = some f ∧
      ∀ a : State,
        ¬ stop a →
        Steps P_ghost s0 a →
        Steps P_ghost (f a) u_first →
        Steps P_ghost (f a) sf_end →
        a.pc = pc →
        a.status = .Running →
        (∀ msg, (f a).status ≠ .Exception msg) →
        a.mem.KeepsFrozen (f a).mem →
        ExecFrozen a.mem →
        InvS a →
        ExecFrozen (f a).mem ∧ InvS (f a)) ∨
    (P_real.externAt? pc = none ∧
      ∀ a : State,
        ¬ stop a →
        Steps P_ghost s0 a →
        Steps P_ghost (f a) u_first →
        Steps P_ghost (f a) sf_end →
        a.pc = pc →
        a.status = .Running →
        (∀ msg, (f a).status ≠ .Exception msg) →
        a.mem.KeepsFrozen (f a).mem →
        ExecFrozen a.mem →
        keep (a.readReg64 .lr) = false →
        InvS a →
        Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))

private theorem stepsUntil_transfer_ghost_aux
    {keep : BitVec 64 → Bool} {InvS : State → Prop} {stop : State → Prop}
    {P_ghost P_real : Program} {s0 sf_end : State}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    {u u_first : State}
    (huntil : StepsUntil P_ghost stop u u_first)
    (hpre : Steps P_ghost s0 u)
    (hsuf : Steps P_ghost u_first sf_end)
    (hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg)
    (hnhalt_uf : u_first.status ≠ .Halted)
    (hfr_u : ExecFrozen u.mem)
    (hinv_u : InvS u)
    (hReplays : PrefixExternReplaysUntil keep InvS stop P_ghost P_real s0 u_first sf_end)
    (hExecInv : ∀ z inst,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost (execInst inst z) u_first →
      Steps P_ghost (execInst inst z) sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some inst →
      inst.isSvc0 = false →
      z.mem.KeepsFrozen (execInst inst z).mem →
      ExecFrozen z.mem →
      InvS z →
      InvS (execInst inst z))
    (hSvcInv : ∀ z,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) u_first →
      Steps P_ghost (Syscall.standard z) sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      z.mem.KeepsFrozen (Syscall.standard z).mem →
      ExecFrozen z.mem →
      InvS z →
      InvS (Syscall.standard z))
    (hlr_calls : ∀ z : State,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost z u_first →
      Steps P_ghost z sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Steps P_real u u_first ∧ ExecFrozen u_first.mem ∧ InvS u_first := by
  induction huntil with
  | refl s => exact ⟨Steps.refl s, hfr_u, hinv_u⟩
  | @step a b c hnot_stop h1 hrest ih =>
    have hrest_uf : Steps P_ghost b c := hrest.toSteps
    have hrest_end : Steps P_ghost b sf_end := hrest_uf.trans hsuf
    have hstep_uf : Steps P_ghost a c := Steps.step h1 hrest_uf
    have hstep_end : Steps P_ghost a sf_end := hstep_uf.trans hsuf
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_uf (steps_preserves_halted hrest_uf rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_uf _ (steps_preserves_exception hrest_uf rfl))
    | @exec inst hrun hfm =>
      have hfm_orig := hfm
      unfold Program.fetchMem at hfm
      cases heg : P_ghost.externAt? a.pc with
      | some f => simp [heg] at hfm
      | none =>
        have her : P_real.externAt? a.pc = none := hno_new_hooks a.pc heg
        have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem
          simpa [heg, her] using hfm
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hev_g : P_ghost.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_ghost]
          have hev_r : P_real.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_real]
          have hstep1_g : Step P_ghost a (Syscall.standard a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (Syscall.standard a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨_, hfr_b⟩ := standard_stripS (keep := keep) hfr_u
          rw [hev_g] at hrest_uf hrest_end ih
          have hinv_b : InvS (Syscall.standard a) :=
            hSvcInv a hnot_stop hpre hrest_uf hrest_end hrun heg hfm_orig
              hstep1_r.keepsFrozen hfr_u hinv_u
          have hpre_b : Steps P_ghost s0 (Syscall.standard a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
            ih hpre_b hsuf hnoex_uf hnhalt_uf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_g : P_ghost.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hev_r : P_real.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hstep1_g : Step P_ghost a (execInst inst a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (execInst inst a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨hfr_b, _⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr_u
          rw [hev_g] at hrest_uf hrest_end ih
          have hinv_b : InvS (execInst inst a) :=
            hExecInv a inst hnot_stop hpre hrest_uf hrest_end hrun heg hfm_orig hnsvc0
              hstep1_r.keepsFrozen hfr_u hinv_u
          have hpre_b : Steps P_ghost s0 (execInst inst a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
            ih hpre_b hsuf hnoex_uf hnhalt_uf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
    | @extern f hrun heg hkf hsym =>
      have hstep1_g : Step P_ghost a (f a) := Step.extern hrun heg hkf hsym
      have hnoex_fa : ∀ msg, (f a).status ≠ .Exception msg := fun msg hex =>
        hnoex_uf msg (steps_preserves_exception hrest_uf hex)
      have hpre_b : Steps P_ghost s0 (f a) :=
        hpre.trans (Steps.step hstep1_g (Steps.refl _))
      rcases hReplays a.pc f heg with ⟨her, hfr_pres⟩ | ⟨her_none, hghost_run⟩
      · have hstep1_r : Step P_real a (f a) := Step.extern hrun her hkf hsym
        obtain ⟨hfr_b, hinv_b⟩ :=
          hfr_pres a hnot_stop hpre hrest_uf hrest_end rfl hrun hnoex_fa hkf hfr_u hinv_u
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
          ih hpre_b hsuf hnoex_uf hnhalt_uf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
        exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
      · have hne_ext : P_ghost.externAt? a.pc ≠ P_real.externAt? a.pc := by
          rw [heg, her_none]; nofun
        have hlr_a : keep (a.readReg64 .lr) = false :=
          hlr_calls a hnot_stop hpre hstep_uf hstep_end hrun hne_ext
        obtain ⟨hsteps_fa, hfr_b, hinv_b⟩ :=
          hghost_run a hnot_stop hpre hrest_uf hrest_end rfl hrun hnoex_fa hkf hfr_u hlr_a hinv_u
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
          ih hpre_b hsuf hnoex_uf hnhalt_uf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
        exact ⟨hsteps_fa.trans hrest_r, hfr_c, hinv_c⟩

/-- First-stop `StepsUntil` ghost-to-real transfer from `s0` to `u_first` (with optional post-stop
    ghost continuation `hsuf : Steps P_ghost u_first sf_end`). -/
theorem stepsUntil_transfer_ghost
    {keep : BitVec 64 → Bool} {InvS : State → Prop} {stop : State → Prop}
    {P_ghost P_real : Program} {s0 u_first sf_end : State}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (huntil : StepsUntil P_ghost stop s0 u_first)
    (hsuf : Steps P_ghost u_first sf_end)
    (hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg)
    (hnhalt_uf : u_first.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvS s0)
    (hReplays : PrefixExternReplaysUntil keep InvS stop P_ghost P_real s0 u_first sf_end)
    (hExecInv : ∀ z inst,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost (execInst inst z) u_first →
      Steps P_ghost (execInst inst z) sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some inst →
      inst.isSvc0 = false →
      z.mem.KeepsFrozen (execInst inst z).mem →
      ExecFrozen z.mem →
      InvS z →
      InvS (execInst inst z))
    (hSvcInv : ∀ z,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) u_first →
      Steps P_ghost (Syscall.standard z) sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      z.mem.KeepsFrozen (Syscall.standard z).mem →
      ExecFrozen z.mem →
      InvS z →
      InvS (Syscall.standard z))
    (hlr_calls : ∀ z : State,
      ¬ stop z →
      Steps P_ghost s0 z →
      Steps P_ghost z u_first →
      Steps P_ghost z sf_end →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Steps P_real s0 u_first ∧ ExecFrozen u_first.mem ∧ InvS u_first :=
  stepsUntil_transfer_ghost_aux hsvc_ghost hsvc_real hno_new_hooks huntil (Steps.refl s0) hsuf
    hnoex_uf hnhalt_uf hfr0 hinv0 hReplays hExecInv hSvcInv hlr_calls

/-! ## 4. Predicate-Parametric First-Stop Dischargers Producing `mlkemStubStateEntryGuard` -/

/-- Violation predicate across a coupled symbol family `S`: state `u` is `.Running` at
    `u.pc = libsignalSessionLib.resolve mpl sym` for some `sym ∈ S` where `¬ termOf sym u`. -/
@[expose] def BadAtFamily (mpl : MultiPlacement) (S : List String)
    (termOf : String → State → Prop) (u : State) : Prop :=
  u.status = .Running ∧
    ∃ sym : String, sym ∈ S ∧ u.pc = libsignalSessionLib.resolve mpl sym ∧ ¬ termOf sym u

/-- At any `.Running` state `a` with `¬ BadAtFamily mpl S termOf a`, every `sym ∈ S` with
    `a.pc = libsignalSessionLib.resolve mpl sym` satisfies `termOf sym a` (with zero stub-PC
    injectivity assumption). -/
theorem termOf_of_not_badAtFamily
    {mpl : MultiPlacement} {S : List String} {termOf : String → State → Prop}
    {a : State} {sym : String}
    (hnot_bad : ¬ BadAtFamily mpl S termOf a)
    (hsym : sym ∈ S)
    (hpc : a.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : a.status = .Running) :
    termOf sym a :=
  Classical.byContradiction fun hnot => hnot_bad ⟨hrun, sym, hsym, hpc, hnot⟩

/-- Combine non-`S` extern replayability with `AtCallRowReplayOn` on `S` into
    `PrefixExternReplaysUntil` for `BadAtFamily mpl S termOf`. -/
theorem prefixExternReplaysUntil_of_atCallFamily
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {W : CliHooks} {s0 u_first sf_end : State}
    (hClassify : ∀ (pc : BitVec 64) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      P_ghost.externAt? pc = some f →
      (∃ sym : String,
        sym ∈ S ∧ pc = libsignalSessionLib.resolve mpl sym ∧
        AtCallRowReplayOn mpl InvS ER sym (termOf sym) f) ∨
      ((P_real.externAt? pc = some f ∧
          ∀ a : State,
            Steps P_ghost s0 a →
            Steps P_ghost (f a) u_first →
            Steps P_ghost (f a) sf_end →
            a.pc = pc →
            a.status = .Running →
            (∀ msg, (f a).status ≠ .Exception msg) →
            a.mem.KeepsFrozen (f a).mem →
            ExecFrozen a.mem →
            InvS a →
            ExecFrozen (f a).mem ∧ InvS (f a)) ∨
        (P_real.externAt? pc = none ∧
          ∀ a : State,
            Steps P_ghost s0 a →
            Steps P_ghost (f a) u_first →
            Steps P_ghost (f a) sf_end →
            a.pc = pc →
            a.status = .Running →
            (∀ msg, (f a).status ≠ .Exception msg) →
            a.mem.KeepsFrozen (f a).mem →
            ExecFrozen a.mem →
            keep (a.readReg64 .lr) = false →
            InvS a →
            Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a)))) :
    PrefixExternReplaysUntil keep InvS (BadAtFamily mpl S termOf)
      (cliProgExtPlacedAt mpl EG 617 W) (cliProgExtPlacedAt mpl ER 617 W)
      s0 u_first sf_end := by
  intro pc f heg
  rcases hClassify pc f heg with ⟨sym, hsym_S, hpc_eq, hAtCall⟩ | (⟨her, harm1⟩ | ⟨hnone, harm2⟩)
  · subst hpc_eq
    refine Or.inr ⟨hAtCall.real_stub_none W, ?_⟩
    intro a hnot_bad _ _ _ hpc hrun hnoex hkf hfr _ hinv
    have hTermA : termOf sym a := termOf_of_not_badAtFamily hnot_bad hsym_S hpc hrun
    exact hAtCall.replay_at_call W a hTermA hpc hrun hnoex hkf hfr hinv
  · exact Or.inl ⟨her, fun a _ hpre hru hre hpc hr hnx hkf hfr hinv =>
      harm1 a hpre hru hre hpc hr hnx hkf hfr hinv⟩
  · exact Or.inr ⟨hnone, fun a _ hpre hru hre hpc hr hnx hkf hfr hlr hinv =>
      harm2 a hpre hru hre hpc hr hnx hkf hfr hlr hinv⟩

/-- Prefix-only family discharger: proves
    `∀ sym ∈ S, mlkemStubStateEntryGuard mpl EG sym (termOf sym) s0` from
    `RealNeverViolatesFamily mpl ER S termOf s0`, with no ghost-return endpoint assumption at `s0`,
    given prefix replayability of non-`S` ghost externs up to any `.Running` stub entry `u_first`
    in `S` and `AtCallRowReplayOn` on `S`. -/
theorem mlkemStubStateEntryGuard_family_of_prefix
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {s0 : State}
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hClassifyPrefix : ∀ (W : CliHooks) (u_first : State) (sym₁ : String),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      let InvS := fun u : State => InvMem u.mem ∧ PredFs u.fs
      sym₁ ∈ S →
      u_first.pc = libsignalSessionLib.resolve mpl sym₁ →
      u_first.status = .Running →
      StepsUntil P_ghost (BadAtFamily mpl S termOf) s0 u_first →
      (∀ (pc : BitVec 64) (f : State → State),
        P_ghost.externAt? pc = some f →
        (∃ sym : String,
          sym ∈ S ∧ pc = libsignalSessionLib.resolve mpl sym ∧
          AtCallRowReplayOn mpl InvS ER sym (termOf sym) f) ∨
        ((P_real.externAt? pc = some f ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) u_first →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) u_first →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a)))) ∧
      (∀ z : State,
        Steps P_ghost s0 z →
        Steps P_ghost (Syscall.standard z) u_first →
        z.status = .Running →
        P_ghost.externAt? z.pc = none →
        P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
        ExecFrozen z.mem →
        InvMem z.mem →
        PredFs z.fs →
        PredFs (Syscall.standard z).fs) ∧
      (∀ z : State,
        Steps P_ghost s0 z →
        Steps P_ghost z u_first →
        z.status = .Running →
        P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
        keep (z.readReg64 .lr) = false))
    (hReal : RealNeverViolatesFamily mpl ER S termOf s0) :
    ∀ sym : String, sym ∈ S → mlkemStubStateEntryGuard mpl EG sym (termOf sym) s0 := by
  intro sym₀ hsym₀ W u hsteps_u hpc_u hrun_u
  by_contra hnot_u
  have hbad_u : BadAtFamily mpl S termOf u := ⟨hrun_u, sym₀, hsym₀, hpc_u, hnot_u⟩
  obtain ⟨u_first, huntil, hbad_uf, _⟩ := h2fsgen_firstStop_of_steps hsteps_u hbad_u
  rcases hbad_uf with ⟨hrun_uf, sym₁, hsym₁, hpc_uf, hnot_uf⟩
  have hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg := by
    intro _ hex; rw [hrun_uf] at hex; cases hex
  have hnhalt_uf : u_first.status ≠ .Halted := by
    rw [hrun_uf]; nofun
  obtain ⟨hCls, hSvcFs, hLr⟩ := hClassifyPrefix W u_first sym₁ hsym₁ hpc_uf hrun_uf huntil
  have hPref := prefixExternReplaysUntil_of_atCallFamily
    (keep := keep) (InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs)
    (EG := EG) (ER := ER) (S := S) (termOf := termOf)
    (W := W) (s0 := s0) (u_first := u_first) (sf_end := u_first)
    fun pc f heg => by
      rcases hCls pc f heg with hAt | (⟨her, ha1⟩ | ⟨hn, ha2⟩)
      · exact Or.inl hAt
      · exact Or.inr (Or.inl ⟨her, fun a hpre hru _ hpc hr hnx hkf hfr hinv =>
          ha1 a hpre hru hpc hr hnx hkf hfr hinv⟩)
      · exact Or.inr (Or.inr ⟨hn, fun a hpre hru _ hpc hr hnx hkf hfr hlr hinv =>
          ha2 a hpre hru hpc hr hnx hkf hfr hlr hinv⟩)
  obtain ⟨hsteps_real, _, _⟩ :=
    stepsUntil_transfer_ghost
      (keep := keep) (InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs)
      (stop := BadAtFamily mpl S termOf)
      (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
      (P_real := cliProgExtPlacedAt mpl ER 617 W)
      rfl rfl (hNoNewHooks W) huntil (Steps.refl u_first)
      hnoex_uf hnhalt_uf hFr0 ⟨hInv0, hFs0⟩ hPref
      (fun z inst _ _ _ _ _ _ _ hns hkf _ ⟨hinv, hfs⟩ =>
        ⟨hInvStable z.mem _ hinv hkf, by
          have hfs_eq := (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns z).2.2.2.2.2.2
          rwa [hfs_eq]⟩)
      (fun z _ hpre hru _ hrun heg hfm hkf hfr ⟨hinv, hfs⟩ =>
        ⟨hInvStable z.mem _ hinv hkf, hSvcFs z hpre hru hrun heg hfm hfr hinv hfs⟩)
      (fun z _ hpre hru _ hrun hne => hLr z hpre hru hrun hne)
  exact hnot_uf (hReal sym₁ hsym₁ W u_first hsteps_real hpc_uf hrun_uf)

/-- Single-symbol specialization of `mlkemStubStateEntryGuard_family_of_prefix`: for any
    `P : State → Prop`, concludes `mlkemStubStateEntryGuard mpl EG sym P s0` from
    `RealNeverViolatesEntry mpl ER sym P s0`. -/
theorem mlkemStubStateEntryGuard_of_prefix
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {sym : String} {P : State → Prop} {s0 : State}
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hClassifyPrefix : ∀ (W : CliHooks) (u_first : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      let InvS := fun u : State => InvMem u.mem ∧ PredFs u.fs
      u_first.pc = libsignalSessionLib.resolve mpl sym →
      u_first.status = .Running →
      StepsUntil P_ghost (BadAtFamily mpl [sym] (fun _ => P)) s0 u_first →
      (∀ (pc : BitVec 64) (f : State → State),
        P_ghost.externAt? pc = some f →
        (pc = libsignalSessionLib.resolve mpl sym ∧
          AtCallRowReplayOn mpl InvS ER sym P f) ∨
        ((P_real.externAt? pc = some f ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) u_first →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) u_first →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a)))) ∧
      (∀ z : State,
        Steps P_ghost s0 z →
        Steps P_ghost (Syscall.standard z) u_first →
        z.status = .Running →
        P_ghost.externAt? z.pc = none →
        P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
        ExecFrozen z.mem →
        InvMem z.mem →
        PredFs z.fs →
        PredFs (Syscall.standard z).fs) ∧
      (∀ z : State,
        Steps P_ghost s0 z →
        Steps P_ghost z u_first →
        z.status = .Running →
        P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
        keep (z.readReg64 .lr) = false))
    (hReal : RealNeverViolatesEntry mpl ER sym P s0) :
    mlkemStubStateEntryGuard mpl EG sym P s0 := by
  have hFam := mlkemStubStateEntryGuard_family_of_prefix
    (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
    (EG := EG) (ER := ER) (S := [sym]) (termOf := fun _ => P)
    hNoNewHooks hFr0 hInv0 hInvStable hFs0
    (fun W u_first sym₁ hmem₁ hpc₁ hrun₁ huntil => by
      simp only [List.mem_singleton] at hmem₁
      cases hmem₁
      obtain ⟨hCls, hSvc, hLr⟩ := hClassifyPrefix W u_first hpc₁ hrun₁ huntil
      refine ⟨fun pc f heg => ?_, hSvc, hLr⟩
      rcases hCls pc f heg with ⟨hpc_eq, hAt⟩ | hRest
      · exact Or.inl ⟨sym, List.mem_singleton_self sym, hpc_eq, hAt⟩
      · exact Or.inr hRest)
    (realNeverViolatesFamily_singleton hReal)
  exact hFam sym (List.mem_singleton_self sym)

/-- Endpoint-backed first-stop lemma: along a ghost trajectory `s0 →* sf_end` (`hnoex_sf`,
    `hnhalt_sf`), no intermediate state `u` (`Steps P_ghost s0 u` and `Steps P_ghost u sf_end`)
    satisfies `BadAtFamily mpl S termOf u`, assuming only `(s0, sf_end)` replayability of non-`S`
    ghost externs (as provided by `GhostRowReplayOn` / `ExtraListReplaysOn`) and
    `AtCallRowReplayOn` on `S`. -/
theorem noBadOnGhostRun
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
              Steps P_ghost s0 a →
              Steps P_ghost (f a) sf_end →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) sf_end →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
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
    (hReal : RealNeverViolatesFamily mpl ER S termOf s0)
    {u : State}
    (hpre_u : Steps (cliProgExtPlacedAt mpl EG 617 W) s0 u)
    (hsuf_u : Steps (cliProgExtPlacedAt mpl EG 617 W) u sf_end) :
    ¬ BadAtFamily mpl S termOf u := by
  intro hbad_u
  obtain ⟨u_first, huntil, hbad_uf, hmid_u⟩ := h2fsgen_firstStop_of_steps hpre_u hbad_u
  have hsuf_uf : Steps (cliProgExtPlacedAt mpl EG 617 W) u_first sf_end := hmid_u.trans hsuf_u
  rcases hbad_uf with ⟨hrun_uf, sym₁, hsym₁, hpc_uf, hnot_uf⟩
  have hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg := fun msg hex =>
    hnoex_sf msg (steps_preserves_exception hsuf_uf hex)
  have hnhalt_uf : u_first.status ≠ .Halted := fun hhalt =>
    hnhalt_sf (steps_preserves_halted hsuf_uf hhalt)
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
  obtain ⟨hsteps_real, _, _⟩ :=
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
  exact hnot_uf (hReal sym₁ hsym₁ W u_first hsteps_real hpc_uf hrun_uf)

/-- Helper: any non-`.Running` terminal ghost state (`Exited`, `Panicked`, `OutOfMemory`, etc.)
    trivially has no `.Running` continuation state `u` (`Steps P sf_end u → u.status = .Running → False`). -/
theorem noRunningAfter_of_status_ne_running {P : Program} {sf_end : State}
    (hnot_run : sf_end.status ≠ .Running) :
    ∀ u : State, Steps P sf_end u → u.status = .Running → False := by
  intro u hsteps hrun_u
  have heq : sf_end = u := h2fsgen_steps_eq_of_not_running hnot_run hsteps
  exact hnot_run (heq ▸ hrun_u)

/-- Helper: if `sf_end` has returned to `s0.readReg64 .lr` under `CallerLrUnmapped P s0` (with
    `s0.mem.KeepsFrozen sf_end.mem`) and `s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl sym`
    for all `sym ∈ S`, then no `.Running` state `u` reachable from `sf_end` lies at an entry of `S`. -/
theorem noEntryAfter_of_callerLrUnmapped {P : Program} {mpl : MultiPlacement} {S : List String}
    {s0 sf_end : State}
    (hLr : CallerLrUnmapped P s0)
    (hkf : s0.mem.KeepsFrozen sf_end.mem)
    (hret : sf_end.status = .Running → sf_end.pc = s0.readReg64 .lr)
    (hlr_ne : ∀ sym : String, sym ∈ S → s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl sym) :
    ∀ u : State, Steps P sf_end u → u.status = .Running →
      ∀ sym : String, sym ∈ S → u.pc ≠ libsignalSessionLib.resolve mpl sym := by
  intro u hsteps hrun_u sym hsym hpc_u
  by_cases hrun_sf : sf_end.status = .Running
  · have hpc_sf : sf_end.pc = s0.readReg64 .lr := hret hrun_sf
    obtain ⟨hfetch_none, hext_none⟩ := hLr sf_end.mem hkf
    rw [← hpc_sf] at hfetch_none hext_none
    cases hsteps with
    | refl _ =>
      exact hlr_ne sym hsym (hpc_sf.symm.trans hpc_u)
    | @step _ s2 _ h1 h2 =>
      cases h1 with
      | exec _ hf => rw [hfetch_none] at hf; cases hf
      | extern _ he _ _ => rw [hext_none] at he; cases he
      | extern_fault _ he _ => rw [hext_none] at he; cases he
      | halt_unmapped _ _ _ =>
        have hs2 : { sf_end with status := .Halted } = u :=
          h2fsgen_steps_eq_of_not_running (by simp) h2
        have hhalt_u : u.status = .Halted := by rw [← hs2]
        rw [hrun_u] at hhalt_u
        cases hhalt_u
  · exact False.elim (noRunningAfter_of_status_ne_running hrun_sf u hsteps hrun_u)

/-- Ghost-run family discharger: proves
    `∀ sym ∈ S, mlkemStubStateEntryGuard mpl EG sym (termOf sym) s0` using `(s0, sf_end)`
    replayability of non-`S` ghost externs whenever each `W` has a ghost run
    `Steps P_ghost s0 (sfOf W)` with no `.Running` continuation into `S` after `sfOf W`. -/
theorem mlkemStubStateEntryGuard_family_of_ghostRun
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {s0 : State}
    (sfOf : CliHooks → State)
    (hStepsEnd : ∀ W : CliHooks, Steps (cliProgExtPlacedAt mpl EG 617 W) s0 (sfOf W))
    (hNoExEnd : ∀ (W : CliHooks) (msg : String), (sfOf W).status ≠ .Exception msg)
    (hNoHaltEnd : ∀ W : CliHooks, (sfOf W).status ≠ .Halted)
    (hNoPostEntry : ∀ (W : CliHooks) (u : State),
      Steps (cliProgExtPlacedAt mpl EG 617 W) (sfOf W) u →
      u.status = .Running →
      ∀ sym : String, sym ∈ S → u.pc ≠ libsignalSessionLib.resolve mpl sym)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hClassifyOnEnd : ∀ (W : CliHooks),
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
              Steps P_ghost s0 a →
              Steps P_ghost (f a) (sfOf W) →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) (sfOf W) →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))))
    (hSvcFs : ∀ (W : CliHooks) (z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) (sfOf W) →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      InvMem z.mem →
      PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ (W : CliHooks) (z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      Steps P_ghost s0 z →
      Steps P_ghost z (sfOf W) →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false)
    (hReal : RealNeverViolatesFamily mpl ER S termOf s0) :
    ∀ sym : String, sym ∈ S → mlkemStubStateEntryGuard mpl EG sym (termOf sym) s0 := by
  intro sym hsym W u hsteps_u hpc_u hrun_u
  rcases steps_comparable hsteps_u (hStepsEnd W) with hsuf_u | hpost_u
  · have hnot_bad := noBadOnGhostRun
      (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
      (EG := EG) (ER := ER) (S := S) (termOf := termOf)
      (W := W) (s0 := s0) (sf_end := sfOf W)
      (hNoNewHooks W) hFr0 hInv0 hInvStable hFs0 (hNoExEnd W) (hNoHaltEnd W)
      (hClassifyOnEnd W) (hSvcFs W) (hlr_calls W) hReal hsteps_u hsuf_u
    exact termOf_of_not_badAtFamily hnot_bad hsym hpc_u hrun_u
  · exact False.elim (hNoPostEntry W u hpost_u hrun_u sym hsym hpc_u)

/-- Single-symbol specialization of `mlkemStubStateEntryGuard_family_of_ghostRun`: for any
    `P : State → Prop`, concludes `mlkemStubStateEntryGuard mpl EG sym P s0` from
    `RealNeverViolatesEntry mpl ER sym P s0` and an `(s0, sfOf W)` ghost trajectory. -/
theorem mlkemStubStateEntryGuard_of_ghostRun
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {sym : String} {P : State → Prop} {s0 : State}
    (sfOf : CliHooks → State)
    (hStepsEnd : ∀ W : CliHooks, Steps (cliProgExtPlacedAt mpl EG 617 W) s0 (sfOf W))
    (hNoExEnd : ∀ (W : CliHooks) (msg : String), (sfOf W).status ≠ .Exception msg)
    (hNoHaltEnd : ∀ W : CliHooks, (sfOf W).status ≠ .Halted)
    (hNoPostEntry : ∀ (W : CliHooks) (u : State),
      Steps (cliProgExtPlacedAt mpl EG 617 W) (sfOf W) u →
      u.status = .Running →
      u.pc ≠ libsignalSessionLib.resolve mpl sym)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hClassifyOnEnd : ∀ (W : CliHooks),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      let InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs
      ∀ (pc : BitVec 64) (f : State → State),
        P_ghost.externAt? pc = some f →
        (pc = libsignalSessionLib.resolve mpl sym ∧
          AtCallRowReplayOn mpl InvS ER sym P f) ∨
        ((P_real.externAt? pc = some f ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) (sfOf W) →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) (sfOf W) →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))))
    (hSvcFs : ∀ (W : CliHooks) (z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) (sfOf W) →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      InvMem z.mem →
      PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ (W : CliHooks) (z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      Steps P_ghost s0 z →
      Steps P_ghost z (sfOf W) →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false)
    (hReal : RealNeverViolatesEntry mpl ER sym P s0) :
    mlkemStubStateEntryGuard mpl EG sym P s0 := by
  have hFam := mlkemStubStateEntryGuard_family_of_ghostRun
    (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
    (EG := EG) (ER := ER) (S := [sym]) (termOf := fun _ => P)
    sfOf hStepsEnd hNoExEnd hNoHaltEnd
    (fun W u hpost hrun sym' hmem' => by
      simp only [List.mem_singleton] at hmem'
      subst hmem'
      exact hNoPostEntry W u hpost hrun)
    hNoNewHooks hFr0 hInv0 hInvStable hFs0
    (fun W pc f heg => by
      rcases hClassifyOnEnd W pc f heg with ⟨hpc_eq, hAt⟩ | hRest
      · exact Or.inl ⟨sym, List.mem_singleton_self sym, hpc_eq, hAt⟩
      · exact Or.inr hRest)
    hSvcFs hlr_calls
    (realNeverViolatesFamily_singleton hReal)
  exact hFam sym (List.mem_singleton_self sym)

/-! ## 5. Direct `GhostExternReplaysOn` & `Block617TransferFixedHypG` First-Stop Combinators -/

/-- Upgrades non-`S` `(s0, sf)` extern replayability, `AtCallRowReplayOn` on `S`, and
    `RealNeverViolatesFamily mpl ER S termOf s0` into
    `GhostExternReplaysOn keep (fun v => InvMem v.mem ∧ PredFs v.fs) P_ghost P_real s0 sf`,
    reusing existing `(s0, sf)` `GhostRowReplayOn` / `ExtraListReplaysOn` proofs for the non-`S`
    rows unchanged. -/
theorem ghostExternReplaysOn_of_atCallFamily
    {mpl : MultiPlacement} {keep : BitVec 64 → Bool}
    {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {W : CliHooks} {s0 sf : State}
    (hNoNewHooks : ∀ pc : BitVec 64,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFr0 : ExecFrozen s0.mem)
    (hInv0 : InvMem s0.mem)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : PredFs s0.fs)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
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
              Steps P_ghost s0 a →
              Steps P_ghost (f a) sf →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a →
              Steps P_ghost (f a) sf →
              a.pc = pc →
              a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem →
              ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false →
              InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a))))
    (hSvcFs : ∀ z : State,
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
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
      Steps P_ghost z sf →
      z.status = .Running →
      P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false)
    (hReal : RealNeverViolatesFamily mpl ER S termOf s0) :
    GhostExternReplaysOn keep (fun v : State => InvMem v.mem ∧ PredFs v.fs)
      (cliProgExtPlacedAt mpl EG 617 W) (cliProgExtPlacedAt mpl ER 617 W) s0 sf := by
  intro pc f heg
  rcases hClassifyOnEnd pc f heg with ⟨sym, hsym_S, hpc_eq, hAtCall⟩ | hRest
  · subst hpc_eq
    refine Or.inr ⟨hAtCall.real_stub_none W, ?_⟩
    intro u hpre_u hrest_fu hpc_u hrun_u hnoex_fu hkf_u hfr_u _hlr_u hinv_u
    have heg_u : (cliProgExtPlacedAt mpl EG 617 W).externAt? u.pc = some f := hpc_u ▸ heg
    have hstep_u : Step (cliProgExtPlacedAt mpl EG 617 W) u (f u) :=
      Step.extern hrun_u heg_u hkf_u (hAtCall.preserves_symtab u)
    have hsuf_u : Steps (cliProgExtPlacedAt mpl EG 617 W) u sf :=
      Steps.step hstep_u hrest_fu
    have hnot_bad := noBadOnGhostRun
      (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
      (EG := EG) (ER := ER) (S := S) (termOf := termOf)
      (W := W) (s0 := s0) (sf_end := sf)
      hNoNewHooks hFr0 hInv0 hInvStable hFs0 hnoex_sf hnhalt_sf
      hClassifyOnEnd hSvcFs hlr_calls hReal hpre_u hsuf_u
    have hTermU : termOf sym u := termOf_of_not_badAtFamily hnot_bad hsym_S hpc_u hrun_u
    exact hAtCall.replay_at_call W u hTermU hpc_u hrun_u hnoex_fu hkf_u hfr_u hinv_u
  · exact hRest

/-- Split `ExtraListEntryGuard guardOf extra s0` across a guarded symbol subset `S` (discharged by
    `mlkemStubStateEntryGuard_family_of_prefix` or `mlkemStubStateEntryGuard_family_of_ghostRun`)
    and its complement `sym ∉ S` (discharged by `c2EntryGuard_of_codeOk`). -/
theorem extraListEntryGuard_of_split
    {guardOf : String → State → Prop} {extra : ExtraGhostTable} {s0 : State}
    (S : List String)
    (hInS : ∀ sym f, sym ∈ S → cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → guardOf sym s0)
    (hNotInS : ∀ sym f, sym ∉ S → cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → guardOf sym s0) :
    ExtraListEntryGuard guardOf extra s0 := by
  intro sym f hDom hLook
  by_cases hmem : sym ∈ S
  · exact hInS sym f hmem hDom hLook
  · exact hNotInS sym f hmem hDom hLook

/-- Direct `Block617TransferFixedHypG` discharger combining `block617TransferFixedG_of_replaysOn`
    and `ghostExternReplaysOn_of_atCallFamily`: proves
    `Block617TransferFixedHypG mpl mmpl EG ER (RealNeverViolatesFamily mpl ER S termOf) …`
    with zero `mlkemStubStateEntryGuard` obligation in `Guard`, discharging every `sym ∈ S` call
    along `s0 →* sf` via first-stop contradiction against `RealNeverViolatesFamily`. -/
theorem block617TransferFixedG_of_replaysOn_withAtCallFamily
    {mpl mmpl : MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {S : List String} {termOf : String → State → Prop}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool) (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hTraj : ∀ (W : CliHooks) (i : Inputs) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl ER 617 W
      let InvS := fun v : State => InvMem v.mem ∧ PredFs v.fs
      RealNeverViolatesFamily mpl ER S termOf s0 →
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 sf →
      (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      (∀ (pc : BitVec 64) (f : State → State),
        P_ghost.externAt? pc = some f →
        (∃ sym : String,
          sym ∈ S ∧ pc = libsignalSessionLib.resolve mpl sym ∧
          AtCallRowReplayOn mpl InvS ER sym (termOf sym) f) ∨
        ((P_real.externAt? pc = some f ∧
            ∀ a : State,
              Steps P_ghost s0 a → Steps P_ghost (f a) sf →
              a.pc = pc → a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem → InvS a →
              ExecFrozen (f a).mem ∧ InvS (f a)) ∨
          (P_real.externAt? pc = none ∧
            ∀ a : State,
              Steps P_ghost s0 a → Steps P_ghost (f a) sf →
              a.pc = pc → a.status = .Running →
              (∀ msg, (f a).status ≠ .Exception msg) →
              a.mem.KeepsFrozen (f a).mem → ExecFrozen a.mem →
              keep (a.readReg64 .lr) = false → InvS a →
              Steps P_real a (f a) ∧ ExecFrozen (f a).mem ∧ InvS (f a)))) ∧
      (∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
        z.status = .Running → P_ghost.externAt? z.pc = none →
        P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
        ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
        PredFs (Syscall.standard z).fs) ∧
      (∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
        z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
        keep (z.readReg64 .lr) = false)) :
    Block617TransferFixedHypG mpl mmpl EG ER
      (RealNeverViolatesFamily mpl ER S termOf)
      CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  refine block617TransferFixedG_of_replaysOn keep InvMem PredFs
    hNoNewHooks hCode hGhostCL hFr0 hInv0 hInvStable hFs0
    fun W i s0 sf hReal hReal0 hpc hfs0 htr0 hsteps hret_pc hnoex hnhalt => ?_
  obtain ⟨hClassify, hSvcFs, hlr_calls⟩ :=
    hTraj W i s0 sf hReal hReal0 hpc hfs0 htr0 hsteps hret_pc hnoex hnhalt
  refine ⟨ghostExternReplaysOn_of_atCallFamily
    (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
    (EG := EG) (ER := ER) (S := S) (termOf := termOf)
    (W := W) (s0 := s0) (sf := sf)
    (hNoNewHooks W) (hFr0 s0.mem hReal0) (hInv0 s0.mem hReal0) hInvStable
    (hfs0 ▸ hFs0 i) hnoex hnhalt hClassify hSvcFs hlr_calls hReal,
    hSvcFs, hlr_calls⟩

/-! ## 6. First-Bad Extraction & Non-Visitation Helpers for `MlKemSampleNttDiverge` -/

/-- Extract `ActiveRealPre (withLsRet spec)` directly from non-`.Exception` of `mlkemBlockGhost`. -/
theorem mlkemBlockGhost_activeRealPre_of_noException [LibsignalPlacement]
    {mlkemMpl : MultiPlacement} {j : Nat} {α : Type}
    {spec : Spec α} {fallback : State → State} {u : State}
    (hnoex : ∀ msg, (mlkemBlockGhost mlkemMpl j spec fallback u).status ≠ .Exception msg) :
    ActiveRealPre (withLsRet spec) u :=
  linkedCallHookG_activeRealPre_of_noException hnoex

/-- Transitivity of "no intermediate state satisfies `stop`" along deterministic `Steps P`:
    if `a →* b` and `b →* c` each visit no `stop` state, then `a →* c` visits no `stop` state. -/
theorem steps_noStopBetween_trans {P : Program} {stop : State → Prop} {a b c : State}
    (hab : Steps P a b)
    (hno_ab : ∀ z : State, Steps P a z → Steps P z b → ¬ stop z)
    (hno_bc : ∀ z : State, Steps P b z → Steps P z c → ¬ stop z) :
    ∀ z : State, Steps P a z → Steps P z c → ¬ stop z := by
  intro z haz hzc
  rcases steps_comparable hab haz with hbz | hzb
  · exact hno_bc z hbz hzc
  · exact hno_ab z haz hzb

/-- First-bad state extraction: if a ghost trajectory `s0 →* u →* sf_end` (`hnoex_sf`,
    `hnhalt_sf`, `¬ BadAtFamily … sf_end`) visits a bad state `u` (`BadAtFamily mpl S termOf u`),
    then there is a first bad state `u_first` along `s0 →* sf_end` such that:
    1. `StepsUntil P_ghost (BadAtFamily mpl S termOf) s0 u_first` and `Steps P_ghost u_first sf_end`,
    2. `Steps P_real s0 u_first` (every step strictly before `u_first` replays on `P_real`),
    3. `BadAtFamily mpl S termOf u_first` and `ExecFrozen u_first.mem ∧ InvMem u_first.mem ∧ PredFs u_first.fs`,
    4. for the ghost hook `f` at `u_first.pc` (`P_ghost.externAt? u_first.pc = some f`),
       `Steps P_ghost (f u_first) sf_end` and `∀ msg, (f u_first).status ≠ .Exception msg`
       (feeding `mlkemBlockGhost_activeRealPre_of_noException` to yield `ActiveRealPre`). -/
theorem firstBadOnGhostRun_extract
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
    (hNoBadSf : ¬ BadAtFamily mpl S termOf sf_end)
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
    {u : State}
    (hpre_u : Steps (cliProgExtPlacedAt mpl EG 617 W) s0 u)
    (hsuf_u : Steps (cliProgExtPlacedAt mpl EG 617 W) u sf_end)
    (hbad_u : BadAtFamily mpl S termOf u) :
    let P_ghost := cliProgExtPlacedAt mpl EG 617 W
    let P_real  := cliProgExtPlacedAt mpl ER 617 W
    ∃ u_first : State,
      StepsUntil P_ghost (BadAtFamily mpl S termOf) s0 u_first ∧
      Steps P_ghost u_first sf_end ∧
      Steps P_real s0 u_first ∧
      BadAtFamily mpl S termOf u_first ∧
      ExecFrozen u_first.mem ∧
      InvMem u_first.mem ∧
      PredFs u_first.fs ∧
      (∀ f : State → State,
        P_ghost.externAt? u_first.pc = some f →
        Steps P_ghost (f u_first) sf_end ∧
          (∀ msg, (f u_first).status ≠ .Exception msg)) := by
  obtain ⟨u_first, huntil, hbad_uf, hmid_u⟩ := h2fsgen_firstStop_of_steps hpre_u hbad_u
  have hsuf_uf : Steps (cliProgExtPlacedAt mpl EG 617 W) u_first sf_end := hmid_u.trans hsuf_u
  have hnoex_uf : ∀ msg, u_first.status ≠ .Exception msg := fun msg hex =>
    hnoex_sf msg (steps_preserves_exception hsuf_uf hex)
  have hnhalt_uf : u_first.status ≠ .Halted := fun hhalt =>
    hnhalt_sf (steps_preserves_halted hsuf_uf hhalt)
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
  refine ⟨u_first, huntil, hsuf_uf, hsteps_real, hbad_uf, hfr_uf, hinv_uf, hfs_uf, ?_⟩
  intro f heg_uf
  cases hsuf_uf with
  | refl _ => exact False.elim (hNoBadSf hbad_uf)
  | @step _ s1 _ h1 hrest_uf =>
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_sf (steps_preserves_halted hrest_uf rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_sf _ (steps_preserves_exception hrest_uf rfl))
    | exec _ hfm =>
      unfold Program.fetchMem at hfm
      simp [heg_uf] at hfm
    | @extern f' _ heg' _ _ =>
      rw [heg_uf] at heg'
      injection heg' with hf_eq
      subst hf_eq
      exact ⟨hrest_uf, fun msg hex => hnoex_sf msg (steps_preserves_exception hrest_uf hex)⟩

/-! ## 7. Concrete Instantiation (`CliReachesSampleNttStuckPlaced`) -/

private theorem resolve_lsKemEncapsSym_eq_rho (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsKemEncapsSym = mpl.ρ lsKemEncapsSym :=
  ls_resolve_data (pl := mpl) (tgt := lsKemEncapsSym) (by decide +kernel)

private theorem resolve_lsKemDecapsSym_eq_rho (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsKemDecapsSym = mpl.ρ lsKemDecapsSym :=
  ls_resolve_data (pl := mpl) (tgt := lsKemDecapsSym) (by decide +kernel)

private theorem resolve_lsMlkemFromSeedSym_eq_rho (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkemFromSeedSym = mpl.ρ lsMlkemFromSeedSym :=
  ls_resolve_data (pl := mpl) (tgt := lsMlkemFromSeedSym) (by decide +kernel)

private theorem resolve_lsMlkemEncaps1Sym_eq_rho (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkemEncaps1Sym = mpl.ρ lsMlkemEncaps1Sym :=
  ls_resolve_data (pl := mpl) (tgt := lsMlkemEncaps1Sym) (by decide +kernel)

private theorem resolve_lsMlkemDecapsSym_eq_rho (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkemDecapsSym = mpl.ρ lsMlkemDecapsSym :=
  ls_resolve_data (pl := mpl) (tgt := lsMlkemDecapsSym) (by decide +kernel)

/-- Equivalence between the trusted `MlKemSampleNttStuckAt mpl u` disjunction (`CliBinaryPq.lean`)
    and `∃ sym ∈ mlkemSampleNttSyms, u.pc = libsignalSessionLib.resolve mpl sym ∧ ¬ mlkemSampleNttTermOf sym u`. -/
theorem mlKemSampleNttStuckAt_iff (mpl : MultiPlacement) (u : State) :
    MlKemSampleNttStuckAt mpl u ↔
      ∃ sym ∈ mlkemSampleNttSyms,
        u.pc = libsignalSessionLib.resolve mpl sym ∧ ¬ mlkemSampleNttTermOf sym u := by
  constructor
  · intro hStuck
    rcases hStuck with ⟨hpc, hnot⟩ | ⟨hpc, hnot⟩ | ⟨hpc, hnot⟩ | ⟨hpc, hnot⟩ | ⟨hpc, hnot⟩
    · exact ⟨lsKemEncapsSym, by simp [mlkemSampleNttSyms],
        hpc.trans (resolve_lsKemEncapsSym_eq_rho mpl).symm,
        by rwa [mlkemSampleNttTermOf_kemEncaps]⟩
    · exact ⟨lsKemDecapsSym, by simp [mlkemSampleNttSyms],
        hpc.trans (resolve_lsKemDecapsSym_eq_rho mpl).symm,
        by rwa [mlkemSampleNttTermOf_kemDecaps]⟩
    · exact ⟨lsMlkemFromSeedSym, by simp [mlkemSampleNttSyms],
        hpc.trans (resolve_lsMlkemFromSeedSym_eq_rho mpl).symm,
        by rwa [mlkemSampleNttTermOf_mlkemFromSeed]⟩
    · exact ⟨lsMlkemEncaps1Sym, by simp [mlkemSampleNttSyms],
        hpc.trans (resolve_lsMlkemEncaps1Sym_eq_rho mpl).symm,
        by rwa [mlkemSampleNttTermOf_mlkemEncaps1]⟩
    · exact ⟨lsMlkemDecapsSym, by simp [mlkemSampleNttSyms],
        hpc.trans (resolve_lsMlkemDecapsSym_eq_rho mpl).symm,
        by rwa [mlkemSampleNttTermOf_mlkemDecaps]⟩
  · rintro ⟨sym, hmem, hpc, hnot⟩
    simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · rw [mlkemSampleNttTermOf_kemEncaps] at hnot
      exact Or.inl ⟨hpc.trans (resolve_lsKemEncapsSym_eq_rho mpl), hnot⟩
    · rw [mlkemSampleNttTermOf_kemDecaps] at hnot
      exact Or.inr (Or.inl ⟨hpc.trans (resolve_lsKemDecapsSym_eq_rho mpl), hnot⟩)
    · rw [mlkemSampleNttTermOf_mlkemFromSeed] at hnot
      exact Or.inr (Or.inr (Or.inl ⟨hpc.trans (resolve_lsMlkemFromSeedSym_eq_rho mpl), hnot⟩))
    · rw [mlkemSampleNttTermOf_mlkemEncaps1] at hnot
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hpc.trans (resolve_lsMlkemEncaps1Sym_eq_rho mpl), hnot⟩)))
    · rw [mlkemSampleNttTermOf_mlkemDecaps] at hnot
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hpc.trans (resolve_lsMlkemDecapsSym_eq_rho mpl), hnot⟩)))

/-- Equivalence between `BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf u` and
    `u.status = .Running ∧ MlKemSampleNttStuckAt mpl u`. -/
theorem badAtFamily_mlkemSampleNtt_iff (mpl : MultiPlacement) (u : State) :
    BadAtFamily mpl mlkemSampleNttSyms mlkemSampleNttTermOf u ↔
      u.status = .Running ∧ MlKemSampleNttStuckAt mpl u :=
  and_congr_right' (mlKemSampleNttStuckAt_iff mpl u).symm

/-- Top-level bridge (`¬ CliReachesSampleNttStuckPlaced → RealNeverViolatesSampleNtt`):
    for any loaded ELF initial state `elf.loadState (cliProcessInputs i) = .ok s_elf` and `.Running`
    state `sm` reached along `Placed.cliProgPlacedSig mpl mmpl W₀` from `cliTokenPatchPlaced mpl s_elf`
    (such as `main` entry `sm`), `¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W₀ i` implies
    `RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) sm` (`hTbl` defaults to `by intro _; rfl`
    at zero hooks). -/
theorem realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {elf : ElfImage} {i : Inputs}
    {s_elf sm : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s_elf)
    (hStart : Steps (cliProgPlacedSig mpl mmpl W₀) (cliTokenPatchPlaced mpl s_elf) sm)
    (hrun_sm : sm.status = .Running)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W₀ i)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) sm :=
  realNeverViolatesFamily_of_elfLoad W₀ hLoad hStart hrun_sm
    (fun ⟨s0, u, hL, hS, hR, hBad⟩ =>
      hNoStuck ⟨s0, u, hL, hS, hR, (mlKemSampleNttStuckAt_iff mpl u).mpr hBad⟩)
    hTbl

/-- Process-entry (`cliTokenPatchPlaced mpl s_elf`, `0` startup steps) specialization of
    `realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced`. -/
theorem realNeverViolatesSampleNtt_init_of_not_cliReachesSampleNttStuckPlaced
    {mpl mmpl : MultiPlacement} (W₀ : CliHooks) {elf : ElfImage} {i : Inputs}
    {s_elf : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s_elf)
    (hrun_init : (cliTokenPatchPlaced mpl s_elf).status = .Running)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W₀ i)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) (cliTokenPatchPlaced mpl s_elf) :=
  realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced W₀ hLoad (Steps.refl _)
    hrun_init hNoStuck hTbl

/-- Unpack `∀ sym ∈ mlkemSampleNttSyms, mlkemStubStateEntryGuard mpl EG sym (mlkemSampleNttTermOf sym) s0`
    directly into the 5 individual `mlkemStubStateEntryGuard` obligations for `lsKemEncapsSym`,
    `lsKemDecapsSym`, `lsMlkemFromSeedSym`, `lsMlkemEncaps1Sym`, and `lsMlkemDecapsSym`. -/
theorem mlkemStubStateEntryGuard_five_of_sampleNttFamily
    {mpl : MultiPlacement} {EG : CliHooks → String → Option (State → State)} {s0 : State}
    (hFam : ∀ sym : String, sym ∈ mlkemSampleNttSyms →
      mlkemStubStateEntryGuard mpl EG sym (mlkemSampleNttTermOf sym) s0) :
    mlkemStubStateEntryGuard mpl EG lsKemEncapsSym KemEncapsStateTerminates s0 ∧
    mlkemStubStateEntryGuard mpl EG lsKemDecapsSym KemDecapsStateTerminates s0 ∧
    mlkemStubStateEntryGuard mpl EG lsMlkemFromSeedSym MlkemFromSeedStateTerminates s0 ∧
    mlkemStubStateEntryGuard mpl EG lsMlkemEncaps1Sym MlkemEncaps1StateTerminates s0 ∧
    mlkemStubStateEntryGuard mpl EG lsMlkemDecapsSym MlkemDecapsStateTerminates s0 :=
  ⟨fun W u hs hpc hr => (mlkemSampleNttTermOf_kemEncaps u) ▸
      hFam lsKemEncapsSym (by simp [mlkemSampleNttSyms]) W u hs hpc hr,
   fun W u hs hpc hr => (mlkemSampleNttTermOf_kemDecaps u) ▸
      hFam lsKemDecapsSym (by simp [mlkemSampleNttSyms]) W u hs hpc hr,
   fun W u hs hpc hr => (mlkemSampleNttTermOf_mlkemFromSeed u) ▸
      hFam lsMlkemFromSeedSym (by simp [mlkemSampleNttSyms]) W u hs hpc hr,
   fun W u hs hpc hr => (mlkemSampleNttTermOf_mlkemEncaps1 u) ▸
      hFam lsMlkemEncaps1Sym (by simp [mlkemSampleNttSyms]) W u hs hpc hr,
   fun W u hs hpc hr => (mlkemSampleNttTermOf_mlkemDecaps u) ▸
      hFam lsMlkemDecapsSym (by simp [mlkemSampleNttSyms]) W u hs hpc hr⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
