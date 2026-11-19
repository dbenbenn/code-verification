/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import ProofLib.ProgramReflection -- proof-setup: allow-public-import

/-!
# Placement-Generic `mlkemMultiLib` Ghost Hooks and Replay Bridges

Placement-generic ghost hooks and replay bridges for the 7 `libcrux_ml_kem` hooks (`CryptoMlKem`)
over any valid `mlkemMpl : MultiPlacement`:

1. `mlkemInvMem`, `mlkemActiveGuard`, and `mlkemBlockGhost`: package
   `mlkemMultiLib.Placeable mlkemMpl ∧ mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m`,
   prove preservation across `KeepsFrozen` and `stripExecOutside`, and define `mlkemBlockGhost`
   via `linkedCallHookG` over `emptyStdProg`.
2. Unconditional `HookOk` and `DalekLsRowTuple` without `*Terminates` premises: because
   `linkedCallHookG` evaluates its active real-code branch only when `ActiveRealRun` holds (which
   already witnesses a finite `StepsUntil emptyStdProg (SubroutineStop s0)` run to
   `SubroutineStop s0 sf`), `not_stepsUntil_subroutineStop_of_diverge_stripS` refutes the
   divergence branch of `mlkemSafeSubroutineOk`. All 7 ghost hooks (`kemEncapsGhost`,
   `kemDecapsGhost`, `mlkemFromSeedGhost`, `mlkemEncaps1Ghost`, `mlkemEncaps2Ghost`,
   `mlkemDecapsGhost`, `mlkemValidatePkGhost`) satisfy `DalekLsRowTuple`, `VmPreserved`,
   `HookFsTraced IsFsC`, `HookNoAllocFailed`, and `ExecFrozen` preservation unconditionally.
3. `GhostRowReplayOn` bridges:
   - Unconditional (`entryGuard := fun _ => True`) for `mlkemEncaps2` (`B20`) and
     `mlkemValidatePk` (`B21`).
   - State-level `SampleNTT` entry-guarded `GhostRowReplayOn` (with `entryGuard := fun _ => True`
     corollaries under universal termination) for `kemEncaps` (`B24`), `kemDecaps` (`B23`),
     `mlkemFromSeed` (`B10`), `mlkemEncaps1` (`B19`), and `mlkemDecaps` (`B22`), using
     `linkedCallHookG` equality on guarded call states without modifying the hook definitions.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (readVecN)
open CryptoVerification.E2E.Pqxdh (readVecN_eq_of_pointsToBytes)
open CryptoVerification.LibsignalSpqrV1 (
  MlkemDecapsCall MlkemEncaps1Call MlkemEncaps2Call MlkemFromSeedCall MlkemValidatePkCall
  mlkemDecapsName mlkemEncaps1Name mlkemEncaps2Name mlkemFromSeedName mlkemValidatePkName
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges (
  KemDecapsCall KemDecapsCallTerminates KemEncapsCall KemEncapsCallTerminates
  MlKemRoHoldsBytes MlkemDecapsCallTerminates MlkemEncaps1CallTerminates
  MlkemFromSeedCallTerminates
  kemDecaps_at_keepsFs_vm_premise_subroutineOk kemDecaps_at_keepsFs_vm_safeSubroutineOk
  kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk
  kemEncapsPreserved_at_keepsFs_vm_safeSubroutineOk
  mlkemDecaps_at_keepsFs_vm_premise_subroutineOk mlkemDecaps_at_keepsFs_vm_safeSubroutineOk
  mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk
  mlkemEncaps2_at_keepsFs_vm_safeSubroutineOk
  mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk
  mlkemValidatePk_at_keepsFs_vm_safeSubroutineOk
  withPremise
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  externAt?_mlkemBlockProgram_ext_none kemDecapsAtSpec kemDecapsName kemEncapsName
  kemEncapsPreservedAtSpec mlkemDecapsAtSpec mlkemEncaps1AtSpec mlkemEncaps2AtSpec
  mlkemEncaps2_at_keepsFs_vm_subroutineOk mlkemFromSeedAtSpec mlkemSafeSubroutineOk
  mlkemValidatePkAtSpec mlkemValidatePk_at_keepsFs_vm_subroutineOk withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_pc stripS_readReg64 stripS_sp
  stripS_spAligned stripS_status strip_codeLoaded_mlkem strip_readBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec kyber1024DecapsVec_toList kyber1024EncapsVec kyber1024EncapsVec_fst_toList
  kyber1024EncapsVec_snd_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  mlkem768Incremental_fromSeed_dk_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024DecapsTerminates Kyber1024EncapsTerminates Mlkem768DecapsTerminates
  Mlkem768Encaps1Terminates Mlkem768FromSeedTerminates mlkem768DecapsWith mlkem768Encaps2List
  mlkem768Incremental mlkem768ValidPk sampleNtt toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (PureFallbackPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace
  linkedCallHook satisfies_of_stripExecOutside satisfies_stripExecOutside standard_stripS
  stepsUntil_of_stripS_standard
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (
  HookNoAllocFailed hookNoAllocFailed_of_trace_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG linkedCallHookG_activeRealPre_of_noException linkedCallHookG_eq_of_guard
  linkedCallHookG_eq_of_not_guard linkedCallHookG_fs linkedCallHookG_fsT linkedCallHookG_visitedIn
  roDataAt_of_keepsFrozen withStateGuard
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_externAt_none emptyStdProg_svc
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  extract_withLsRet hookOk_withLsRet subroutine_ok_withLsRet withLsRet withLsRet_frameLeft
  withLsRet_outcome_setPC withLsRet_pre_setPC withLsRet_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs (
  DalekLsRowTuple rowTuple_of_keepsFs_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  KemDecapsRowSpec KemDecapsRowSpecAt KemEncapsRowSpec KemEncapsRowSpecAt MlkemDecapsRowSpec
  MlkemDecapsRowSpecAt MlkemEncaps1RowSpec MlkemEncaps1RowSpecAt MlkemEncaps2RowSpec
  MlkemEncaps2RowSpecAt MlkemFromSeedRowSpec MlkemFromSeedRowSpecAt MlkemValidatePkRowSpec
  MlkemValidatePkRowSpecAt kemDecapsFallback kemDecapsFallback_preserved kemDecapsFallback_rowSpecAt
  kemDecapsTightStack kemEncapsFallback kemEncapsFallback_preserved kemEncapsFallback_rowSpecAt
  kemEncapsTightStack kyber1024Prims₀ mlkemDecapsFallback mlkemDecapsFallback_preserved
  mlkemDecapsFallback_rowSpecAt mlkemDecapsTightStack mlkemEncaps1Fallback
  mlkemEncaps1Fallback_preserved mlkemEncaps1Fallback_rowSpecAt mlkemEncaps1TightStack
  mlkemEncaps2Fallback mlkemEncaps2Fallback_preserved mlkemEncaps2Fallback_rowSpecAt
  mlkemEncaps2TightStack mlkemFromSeedFallback mlkemFromSeedFallback_preserved
  mlkemFromSeedFallback_rowSpecAt mlkemFromSeedTightStack mlkemHookStack mlkemValidatePkFallback
  mlkemValidatePkFallback_preserved mlkemValidatePkFallback_rowSpecAt mlkemValidatePkTightStack
  kemDecapsHook_at_keepsFs_ok kemEncapsHook_preservedAt_keepsFs_ok mlkemDecapsHook_at_keepsFs_ok
  mlkemEncaps1Hook_at_keepsFs_ok mlkemEncaps2Hook_at_keepsFs_ok mlkemFromSeedHook_at_keepsFs_ok
  mlkemValidatePkHook_at_keepsFs_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_steps_lift_of_visitedIn_noExtern
)

private theorem mlkem768Incremental_encaps2_eq
    (es : List.Vector (BitVec 8) 2080) (ek : List.Vector (BitVec 8) 1152) :
    mlkem768Incremental.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList) := by
  rfl

private theorem mlkem768Incremental_decaps_eq
    (d : List.Vector (BitVec 8) 2400) (c1 : List.Vector (BitVec 8) 960)
    (c2 : List.Vector (BitVec 8) 128) :
    mlkem768Incremental.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList) := by
  rfl

private theorem mlkem768Incremental_validPk_eq
    (hdr ek : List (BitVec 8)) :
    mlkem768Incremental.validPk hdr ek = mlkem768ValidPk hdr ek := by
  rfl

attribute [local irreducible] kyber1024EncapsVec kyber1024DecapsVec mlkem768Incremental

/-! ## 1. `mlkemInvMem`, `mlkemActiveGuard`, & `stripExecOutside` / `KeepsFrozen` Preservation -/

/-- Memory-level invariant for `mlkemMultiLib` at placement `mpl`: valid placement, all 32 code
    blocks loaded, and all 11 `.rodata` tables intact (`MlKemRoOk`). -/
@[expose] def mlkemInvMem (mpl : MultiPlacement) (m : Memory) : Prop :=
  mlkemMultiLib.Placeable mpl ∧ mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m

/-- State-level active guard for `mlkemBlockGhost`. -/
@[expose] def mlkemActiveGuard (mpl : MultiPlacement) (s : State) : Prop :=
  mlkemInvMem mpl s.mem

theorem mlkemRoOk_of_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (hkf : m.KeepsFrozen m') (hro : MlKemRoOk mpl m) : MlKemRoOk mpl m' :=
  ⟨roDataAt_of_keepsFrozen hro.zetaTable hkf,
   roDataAt_of_keepsFrozen hro.keccakRc hkf,
   roDataAt_of_keepsFrozen hro.cst16_0 hkf,
   roDataAt_of_keepsFrozen hro.cst16_1 hkf,
   roDataAt_of_keepsFrozen hro.cst16_2 hkf,
   roDataAt_of_keepsFrozen hro.cst16_3 hkf,
   roDataAt_of_keepsFrozen hro.cst16_4 hkf,
   roDataAt_of_keepsFrozen hro.cst16_5 hkf,
   roDataAt_of_keepsFrozen hro.cst16_6 hkf,
   roDataAt_of_keepsFrozen hro.cst16_7 hkf,
   roDataAt_of_keepsFrozen hro.cst16_8 hkf⟩

theorem mlkemInvMem_of_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (hkf : m.KeepsFrozen m') (h : mlkemInvMem mpl m) : mlkemInvMem mpl m' :=
  ⟨h.1, fun k hk => (h.2.1 k hk).of_keepsFrozen hkf, mlkemRoOk_of_keepsFrozen hkf h.2.2⟩

theorem mlkemInvMem_of_holdsBytes_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (hpl : mlkemMultiLib.Placeable mpl) (hcl₀ : mlkemMultiLib.CodeLoaded mpl m₀)
    (hro₀ : MlKemRoHoldsBytes mpl m₀) (hkf : m₀.KeepsFrozen m) :
    mlkemInvMem mpl m :=
  ⟨hpl, fun k hk => (hcl₀ k hk).of_keepsFrozen hkf, hro₀.roOk hkf⟩

theorem codeLoaded_mlkem_stripExecOutside {mpl : MultiPlacement} {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded mpl m) :
    mlkemMultiLib.CodeLoaded mpl (stripExecOutside (mlkemKeep mpl) m) :=
  strip_codeLoaded_mlkem hcl

theorem mlkemInvMem_stripExecOutside {mpl : MultiPlacement} {m : Memory}
    (h : mlkemInvMem mpl m) :
    mlkemInvMem mpl (stripExecOutside (mlkemKeep mpl) m) :=
  ⟨h.1, strip_codeLoaded_mlkem h.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.2.2⟩

theorem mlkemActiveGuard_stripS_setPC (mpl : MultiPlacement) (pc : BitVec 64) (s0 : State)
    (hG : mlkemActiveGuard mpl s0) :
    mlkemActiveGuard mpl (stripS (mlkemKeep mpl) (s0.setPC pc)) := by
  dsimp only [mlkemActiveGuard]
  rw [stripS_mem]
  exact mlkemInvMem_stripExecOutside hG

/-! ## 2. `mlkemBlockGhost` & Refuting `stripS` Divergence on `ActiveRealRun` -/

@[expose] noncomputable def mlkemBlockGhost [LibsignalPlacement]
    (mlkemMpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) : State → State :=
  linkedCallHookG (mlkemActiveGuard mlkemMpl) (mlkemKeep mlkemMpl) emptyStdProg
    (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j) (withLsRet master) fallback

theorem mlkemBlockGhost_fs [LibsignalPlacement] (mlkemMpl : MultiPlacement) (j : Nat)
    {α : Type} (master : Spec α) (fallback : State → State) (s0 : State) :
    (mlkemBlockGhost mlkemMpl j master fallback s0).fs = s0.fs := by
  unfold mlkemBlockGhost
  exact linkedCallHookG_fs (mlkemActiveGuard mlkemMpl) (mlkemKeep mlkemMpl) emptyStdProg
    (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j) (withLsRet master) fallback s0

theorem mlkemBlockGhost_fsT [LibsignalPlacement] (mlkemMpl : MultiPlacement) (j : Nat)
    {α : Type} (master : Spec α) (fallback : State → State) :
    HookFsTraced IsFsC (mlkemBlockGhost mlkemMpl j master fallback) := by
  unfold mlkemBlockGhost
  exact linkedCallHookG_fsT (mlkemActiveGuard mlkemMpl) (mlkemKeep mlkemMpl) emptyStdProg
    (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j) (withLsRet master) fallback

private theorem keepFsTrace_eq_of_fs_trace {f : State → State}
    (hfs : ∀ s : State, (f s).fs = s.fs) (htr : ∀ s : State, (f s).trace = s.trace) :
    keepFsTrace f = f := by
  funext s; unfold keepFsTrace; rw [← hfs s, ← htr s]

theorem mlkemBlockGhost_preserves_execFrozen [LibsignalPlacement] (mlkemMpl : MultiPlacement)
    (j : Nat) {α : Type} (master : Spec α) {fallback : State → State}
    (hfb : PureFallbackPreserved fallback) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (mlkemBlockGhost mlkemMpl j master fallback u).mem := by
  classical
  unfold mlkemBlockGhost linkedCallHookG
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (hfb s).2.1) (fun s => (hfb s).2.2.1)
  split
  · unfold linkedCallHook; split
    · split
      · rename_i hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · rw [hkfb]; exact ExecFrozen.of_perm_eq hfr (hfb u).1.perm_eq
    · exact hfr
  · split
    · rw [hkfb]; exact ExecFrozen.of_perm_eq hfr (hfb u).1.perm_eq
    · exact hfr

theorem mlkemBlockGhost_keepLr_false_of_noException [LibsignalPlacement]
    {mlkemMpl : MultiPlacement} {j : Nat} {α : Type}
    {master : Spec α} {fallback : State → State} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hnoex : ∀ msg, (mlkemBlockGhost mlkemMpl j master fallback u).status ≠ .Exception msg) :
    mlkemKeep mlkemMpl (u.readReg64 .lr) = false := by
  obtain ⟨_, _, _, _, hpre⟩ := linkedCallHookG_activeRealPre_of_noException hnoex
  exact hKeep _ (extract_withLsRet hpre).1

private theorem mlkemBlockProgram_svc (mlkemMpl : MultiPlacement) (j : Nat) :
    (mlkemMultiLib.blockProgram mlkemMpl j).svc = Syscall.standard := rfl

private theorem realProg617_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard := rfl

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := fun a => by
  have hst := hstrip a; rw [ProofLib.strip_perm, ProofLib.strip_perm] at hst
  have hfr0_a := hfr0 a; have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a <;> cases hpf : mf.perm a
    · rfl
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rename_i p0 pf; rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
      rcases p0 with ⟨r0, w0, x0, _, _⟩; rcases pf with ⟨rf, wf, xf, _, _⟩
      unfold ProofLib.stripPerm at hst
      cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
        cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem canExec_stripExecOutside_false_of_keep_false {keep : BitVec 64 → Bool}
    (m : Memory) {pc : BitVec 64} (hk : keep pc = false) :
    (stripExecOutside keep m).canExec pc 4 = false := by
  have hpx : ((stripExecOutside keep m).perm pc).x = false := by
    rw [ProofLib.strip_perm]
    cases hp : m.perm pc with
    | none => rfl
    | some p =>
      rcases p with ⟨r, w, x, _, _⟩
      cases x <;> simp [Option.map, ProofLib.stripPerm, hk, Option.x]
  unfold Memory.canExec Memory.allPerm
  simp [hpx]

/-- Refutes the `stripS` divergence branch of `mlkemSafeSubroutineOk` whenever `ActiveRealRun`
    witnesses a finite `StepsUntil emptyStdProg (SubroutineStop s0)` trajectory with
    `mlkemKeep mpl (s0.readReg64 .lr) = false` and `ExecFrozen u.mem`. -/
private theorem not_stepsUntil_subroutineStop_of_diverge_stripS
    {mpl : MultiPlacement} {j : Nat} (hj : j < mlkemMultiLib.blocks.length)
    {s0 s1' : State} (hlr : mlkemKeep mpl (s0.readReg64 .lr) = false)
    (hdiv : ∀ u', Steps (mlkemMultiLib.blockProgram mpl j) s1' u' →
      u'.status = .Running ∧ ∃ v', Step (mlkemMultiLib.blockProgram mpl j) u' v') :
    ∀ {u sf : State},
      StepsUntil emptyStdProg (SubroutineStop s0) u sf →
      SubroutineStop s0 sf →
      Steps (mlkemMultiLib.blockProgram mpl j) s1' (stripS (mlkemKeep mpl) u) →
      ExecFrozen u.mem →
      False := by
  intro u sf huntil hstop_sf
  let P_sub := mlkemMultiLib.blockProgram mpl j
  have hsub_no : ∀ pc, P_sub.externAt? pc = none :=
    externAt?_mlkemBlockProgram_ext_none mpl hj (fun _ => none)
  induction huntil with
  | refl u =>
    intro hsteps_u _hfr
    obtain ⟨hrun_u', v', hstep_v'⟩ := hdiv (stripS (mlkemKeep mpl) u) hsteps_u
    obtain ⟨hrun_v', _⟩ := hdiv v' (hsteps_u.trans (Steps.step hstep_v' (Steps.refl v')))
    rcases hstop_sf with ⟨hpc_lr, _, _⟩ | hp | ⟨_, he⟩ | ho
    · cases hstep_v' with
      | halt_unmapped _ _ _ => cases hrun_v'
      | extern _ hext _ _ => rw [hsub_no] at hext; cases hext
      | extern_fault _ hext _ => rw [hsub_no] at hext; cases hext
      | @exec inst _ hfetch =>
        rw [stripS_pc, stripS_mem, hpc_lr] at hfetch
        unfold Program.fetchMem at hfetch
        rw [hsub_no, canExec_stripExecOutside_false_of_keep_false u.mem hlr] at hfetch
        simp at hfetch
    · rw [stripS_status, hp] at hrun_u'; cases hrun_u'
    · rw [stripS_status, he] at hrun_u'; cases hrun_u'
    · rw [stripS_status, ho] at hrun_u'; cases hrun_u'
  | @step u u2 sf _hnot_stop hstep_empty _hrest ih =>
    intro hsteps_u hfr
    obtain ⟨hrun_u', v', hstep_v'⟩ := hdiv (stripS (mlkemKeep mpl) u) hsteps_u
    obtain ⟨hrun_v', _⟩ := hdiv v' (hsteps_u.trans (Steps.step hstep_v' (Steps.refl v')))
    cases hstep_v' with
    | halt_unmapped _ _ _ => cases hrun_v'
    | extern _ hext _ _ => rw [hsub_no] at hext; cases hext
    | extern_fault _ hext _ => rw [hsub_no] at hext; cases hext
    | @exec inst _ hfetch' =>
      have hfetch_copy := hfetch'
      rw [stripS_pc, stripS_mem] at hfetch'
      unfold Program.fetchMem at hfetch'
      rw [hsub_no] at hfetch'
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfetch'
      by_cases hal_pc : u.pc.toNat % 4 = 0
      · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfetch'
        by_cases hce' : (stripExecOutside (mlkemKeep mpl) u.mem).canExec u.pc 4 = true
        · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfetch'
          have hx4 :
              ((stripExecOutside (mlkemKeep mpl) u.mem).perm u.pc).x = true ∧
              ((stripExecOutside (mlkemKeep mpl) u.mem).perm (u.pc + 1#64)).x = true ∧
              ((stripExecOutside (mlkemKeep mpl) u.mem).perm (u.pc + 2#64)).x = true ∧
              ((stripExecOutside (mlkemKeep mpl) u.mem).perm (u.pc + 3#64)).x = true := by
            simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
          obtain ⟨hx0, _⟩ := ProofLib.strip_perm_x_imp hx4.1
          obtain ⟨hx1, _⟩ := ProofLib.strip_perm_x_imp hx4.2.1
          obtain ⟨hx2, _⟩ := ProofLib.strip_perm_x_imp hx4.2.2.1
          obtain ⟨hx3, _⟩ := ProofLib.strip_perm_x_imp hx4.2.2.2
          have hce : u.mem.canExec u.pc 4 = true := by
            simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
          have hr32 : (stripExecOutside (mlkemKeep mpl) u.mem).read32 u.pc = u.mem.read32 u.pc := by
            simp [Memory.read32, ProofLib.strip_read8]
          rw [hr32] at hfetch'
          have hfm_emp : emptyStdProg.fetchMem u.mem u.pc = some inst := by
            unfold Program.fetchMem
            rw [emptyStdProg_externAt_none]
            simp [hal_pc, hce, hfetch']
          have hu2_eq : u2 = emptyStdProg.evalInst inst u := by
            cases hstep_empty with
            | halt_unmapped _ h_fetch _ => rw [hfm_emp] at h_fetch; cases h_fetch
            | extern _ hext _ _ => rw [emptyStdProg_externAt_none] at hext; cases hext
            | extern_fault _ hext _ => rw [emptyStdProg_externAt_none] at hext; cases hext
            | @exec inst_e _ hf_e =>
              rw [hfm_emp] at hf_e
              cases Option.some.inj hf_e
              rfl
          subst hu2_eq
          by_cases hsvc0 : inst.isSvc0 = true
          · have hinst : inst = .system false 0#16 := by
              cases inst <;> simp [Instr.isSvc0] at hsvc0
              rcases hsvc0 with ⟨rfl, rfl⟩; rfl
            subst hinst
            obtain ⟨hcomm, hfr2⟩ := standard_stripS (keep := mlkemKeep mpl) hfr
            have hsvc_sub : P_sub.svc = Syscall.standard := mlkemBlockProgram_svc mpl j
            have hev_sub :
                P_sub.evalInst (.system false 0#16) (stripS (mlkemKeep mpl) u) =
                  stripS (mlkemKeep mpl) (Syscall.standard u) := by
              simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
            have hev_emp : emptyStdProg.evalInst (.system false 0#16) u = Syscall.standard u := by
              simp [Program.evalInst, execInstWithSvc, emptyStdProg_svc]
            rw [hev_emp] at ih
            have hstep_sub : Step P_sub (stripS (mlkemKeep mpl) u)
                (stripS (mlkemKeep mpl) (Syscall.standard u)) :=
              hev_sub ▸ Step.exec hrun_u' hfetch_copy
            exact ih hstop_sf (hsteps_u.trans (Steps.step hstep_sub (Steps.refl _))) hfr2
          · have hns : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
            have hev_sub :
                P_sub.evalInst inst (stripS (mlkemKeep mpl) u) =
                  stripS (mlkemKeep mpl) (execInst inst u) := by
              rw [evalInst_eq_execInst_of_not_isSvc0 hns, execInst_stripS hns (mlkemKeep mpl) u]
            have hev_emp : emptyStdProg.evalInst inst u = execInst inst u :=
              evalInst_eq_execInst_of_not_isSvc0 hns u
            rw [hev_emp] at ih
            have hfr2 : ExecFrozen (execInst inst u).mem :=
              ExecFrozen.of_perm_eq hfr
                (congrFun (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns u).2.1)
            have hstep_sub : Step P_sub (stripS (mlkemKeep mpl) u)
                (stripS (mlkemKeep mpl) (execInst inst u)) :=
              hev_sub ▸ Step.exec hrun_u' hfetch_copy
            exact ih hstop_sf (hsteps_u.trans (Steps.step hstep_sub (Steps.refl _))) hfr2
        · simp [hce'] at hfetch'
      · simp [hal_pc] at hfetch'

/-! ## 3. Generic Partial-Correctness Bridge Structure & Unconditional `DalekLsRowTuple` -/

/-- Bundles a block `j` of `mlkemMultiLib` whose export `sym` has `lookupBlockSym = some (j, 0)` and
    satisfies `mlkemSafeSubroutineOk sym (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved master)))`
    together with a pure fallback `fallback` satisfying `HookOk fallback (keepsFs master)`. -/
structure MlKemSafeBridge (j : Nat) (sym : String) {α : Type}
    (master : Spec α) (fallback : State → State) : Prop where
  hj : j < mlkemMultiLib.blocks.length := by decide
  hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by rfl_kernel
  safe_ok : mlkemSafeSubroutineOk sym
    (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved master))) (fun _ => none)
  m_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl
  m_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl
  m_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl
  m_pre_mem : ∀ x (s : State) (m : Memory),
    master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl
  m_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
    master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
    intro _ s0 sf _ _; cases s0; cases sf; rfl
  m_pre_pc : ∀ x (s : State) (pc : BitVec 64),
    master.pre x (s.setPC pc) = master.pre x s := by intro _ s _; cases s; rfl
  m_post_pc : ∀ x (s0 sf : State) (pc : BitVec 64),
    master.post x (s0.setPC pc) sf = master.post x s0 sf := by intro _ s0 sf _; cases s0; rfl
  post_tr : ∀ x (R : SepProp) (s0 sf : State), sf.mem ⊨ master.post x s0 sf ∗ R → sf.trace = s0.trace
  fb_pres : PureFallbackPreserved fallback
  fb_keepsFs_ok : HookOk fallback (keepsFs master)

private theorem keepsFs_strip_inv {j : Nat} {sym : String} {α : Type}
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

private theorem keepsFs_post_fs_tr {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback)
    (x : α) (R : SepProp) (s0 sf : State)
    (hpost : sf.mem ⊨ (keepsFs master).post x s0 sf ∗ R) :
    sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  dsimp only [keepsFs] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact ⟨hpost.1, B.post_tr x R s0 sf hpost.2⟩

private theorem safe_run_on_activeRealRun {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback)
    {mlkemMpl : MultiPlacement} {x : α} {R : SepProp} {s0 : State}
    (hG : mlkemActiveGuard mlkemMpl s0)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (keepsFs master).pre x s0 ∗ R)
    (hReal : ActiveRealRun (mlkemKeep mlkemMpl) emptyStdProg
      (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j) s0) :
    let sf_ch := Classical.choose hReal.2.2.2
    s0.mem.KeepsFrozen sf_ch.mem ∧
    sf_ch.symtab = s0.symtab ∧
    SubroutineOutcome (keepsFs master) x R s0 sf_ch ∧
    VmPreserved s0 sf_ch ∧
    sf_ch.fs = s0.fs ∧ sf_ch.trace = s0.trace ∧
    sf_ch.tpidrEl0 = s0.tpidrEl0 ∧ sf_ch.oracle = s0.oracle := by
  dsimp only
  let keep := mlkemKeep mlkemMpl
  let s1 := s0.setPC (mlkemMpl.base j)
  let s1' := stripS keep s1
  obtain ⟨_, i, off, hsym', hsafe_all⟩ := B.safe_ok
  have hij : i = j ∧ off = 0 := by
    rw [B.hsym] at hsym'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsym'
    exact ⟨hsym'.1.symm, hsym'.2.symm⟩
  rcases hij with ⟨hi, hoff⟩
  subst i
  subst off
  have hsafe := hsafe_all mlkemMpl hG.1
  have hfn : mlkemMultiLib.fnAddr mlkemMpl sym = mlkemMpl.base j := by
    simp [MultiPlacedLib.fnAddr, B.hsym]
  rw [hfn] at hsafe
  have hG1' : mlkemActiveGuard mlkemMpl s1' := mlkemActiveGuard_stripS_setPC mlkemMpl _ s0 hG
  have hs1_pre : s1.mem ⊨ (keepsFs master).pre x s1 ∗ R := by
    dsimp only [s1, keepsFs] at hpre ⊢
    have hmem_s1 : (s0.setPC (mlkemMpl.base j)).mem = s0.mem := by cases s0; rfl
    rw [hmem_s1, B.m_pre_pc]
    exact hpre
  have hs1'_pre : s1'.mem ⊨ (keepsFs master).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← (keepsFs_strip_inv B keep).pre_eq x s1] at hsat
  have hpre_full : s1'.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (withMlKemRoOk mlkemMpl (keepsFs (withVmPreserved master)))).pre x s1' ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, keepsFs, withVmPreserved] at hs1'_pre ⊢
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hG1'.2.1,
      sepConj_assoc, pure_sepConj_of_true hG1'.2.2]
    exact hs1'_pre
  have hentry' : AapcsEntry s1' (mlkemMpl.base j) := ⟨rfl, hrun, hsp⟩
  have hchoose := Classical.choose_spec hReal.2.2.2
  rcases hsafe x R s1' hentry' hpre_full (hG1'.2.1 j B.hj) with ⟨sf', hsteps', hout'⟩ | hdiv
  · have hsub_no := externAt?_mlkemBlockProgram_ext_none mlkemMpl B.hj (fun _ => none)
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
        stepsUntil_of_stripS_standard (s0 := s0) emptyStdProg_svc
          (mlkemBlockProgram_svc mlkemMpl j) (fun pc _ => emptyStdProg_externAt_none pc)
          (fun pc f he => nomatch hsub_no pc ▸ he)
          hReal.2.1 hsteps' (Or.inl hret') (by rw [hret'.2.2]; decide) s1 rfl hReal.1
      have hdet : Classical.choose hReal.2.2.2 = sf :=
        StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
      rw [hdet]
      have horc' := Steps.oracle_eq_of_standard (mlkemBlockProgram_svc mlkemMpl j) hsub_no hsteps'
      rw [hsf_eq] at horc'
      dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, keepsFs, withVmPreserved] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
      obtain ⟨hfs', hpost_vm⟩ := hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_vm
      obtain ⟨hvm', hpostM'⟩ := hpost_vm
      have htr' : sf'.trace = s1'.trace := B.post_tr x R s1' sf' hpostM'
      rw [hsf_eq] at hfs' hvm' htr'
      have hfs : sf.fs = s0.fs := by dsimp only [s1', s1] at hfs'; cases s0; cases sf; exact hfs'
      have htr : sf.trace = s0.trace := by dsimp only [s1', s1] at htr'; cases s0; cases sf; exact htr'
      have horc : sf.oracle = s0.oracle := by dsimp only [s1', s1] at horc'; cases s0; cases sf; exact horc'
      have hperm := perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf
        huntil.toSteps.keepsFrozen hvm'.2.2.1
      have hpool : PoolPreserved s0 sf := by
        rcases hvm'.1 with ⟨h1, h2, h3⟩; dsimp only [s1', s1] at h1 h2 h3
        exact ⟨by cases s0; cases sf; exact h1, by cases s0; cases sf; exact h2,
          by cases s0; cases sf; exact h3⟩
      have hphys : sf.physMemAvail = s0.physMemAvail := by
        have hp := hvm'.2.1; dsimp only [s1', s1] at hp; cases s0; cases sf; exact hp
      have hvm : VmPreserved s0 sf := ⟨hpool, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩
      have hpost_strip : (stripS keep sf).mem ⊨ (keepsFs master).post x s1' (stripS keep sf) ∗ R := by
        rw [← hsf_eq]
        dsimp only [keepsFs]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨by rw [hsf_eq]; dsimp only [s1', s1]; cases s0; cases sf; exact hfs, hpostM'⟩
      rw [(keepsFs_strip_inv B keep).post_eq x s1 sf] at hpost_strip
      have hpost_s1 : sf.mem ⊨ (keepsFs master).post x s1 sf ∗ R :=
        satisfies_of_stripExecOutside hfr_sf hpost_strip
      have hpost_s0 : sf.mem ⊨ (keepsFs master).post x s0 sf ∗ R := by
        dsimp only [s1, keepsFs] at hpost_s1 ⊢
        have hfs_s1 : (s0.setPC (mlkemMpl.base j)).fs = s0.fs := by cases s0; rfl
        rw [hfs_s1, B.m_post_pc] at hpost_s1
        exact hpost_s1
      have hret_sf : Returned s0 sf := by
        rw [hsf_eq] at hret'
        exact ⟨hret'.1, hret'.2.1, hret'.2.2⟩
      have hcc_sf : CallingConventionPreserved s0 sf := by
        rw [hsf_eq] at hcc'
        cases s0; cases sf; exact hcc'
      exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq,
        Or.inl ⟨hret_sf, hcc_sf, hpost_s0⟩, hvm, hfs, htr, hpool.2.2, horc⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, keepsFs, withVmPreserved] at hp
      rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, keepsFs, withVmPreserved] at he
      rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, keepsFs, withVmPreserved] at ho
      rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim
  · exact False.elim
      (not_stepsUntil_subroutineStop_of_diverge_stripS B.hj hReal.2.1 hdiv
        hchoose.1 hchoose.2.1 (Steps.refl s1') (by cases s0; exact hReal.1))

/-- Unconditional `HookOk` for `mlkemBlockGhost` at `withLsRet (keepsFs master)` (no termination premises). -/
theorem mlkemBlockGhost_keepsFs_ok [LibsignalPlacement] {mlkemMpl : MultiPlacement}
    {j : Nat} {sym : String} {α : Type} {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) :
    HookOk (mlkemBlockGhost mlkemMpl j (keepsFs master) fallback)
      (withLsRet (keepsFs master)) := by
  classical
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (B.fb_pres s).2.1) (fun s => (B.fb_pres s).2.2.1)
  have hfb_ls : HookOk (keepFsTrace fallback) (withLsRet (keepsFs master)) := by
    rw [hkfb]; exact hookOk_withLsRet B.fb_keepsFs_ok
  intro x R s0 hrun hpreLs hsp
  have hActPre : ActiveRealPre (withLsRet (keepsFs master)) s0 := ⟨hrun, hsp, x, R, hpreLs⟩
  unfold mlkemBlockGhost
  by_cases hG : mlkemActiveGuard mlkemMpl s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    simp only [hActPre, ↓reduceDIte]
    by_cases hReal : ActiveRealRun (mlkemKeep mlkemMpl) emptyStdProg
        (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j) s0
    · simp only [hReal, ↓reduceDIte]
      obtain ⟨_, hpre⟩ := extract_withLsRet hpreLs
      obtain ⟨hkf, hsym, hout, _, _, _, _, _⟩ :=
        safe_run_on_activeRealRun B hG hrun hsp hpre hReal
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | hrest
      · exact Or.inl ⟨hret, hcc, hpost⟩
      · exact Or.inr hrest
    · simp only [hReal, ↓reduceDIte]
      exact hfb_ls x R s0 hrun hpreLs hsp
  · rw [linkedCallHookG_eq_of_not_guard hG]
    simp only [hActPre, ↓reduceDIte]
    exact hfb_ls x R s0 hrun hpreLs hsp

/-- Unconditional `VmPreserved` and non-syscall field preservation for `mlkemBlockGhost`. -/
theorem mlkemBlockGhost_vmPreserved_and_nonSyscall [LibsignalPlacement] {mlkemMpl : MultiPlacement}
    {j : Nat} {sym : String} {α : Type} {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) (s0 : State) :
    let sf := mlkemBlockGhost mlkemMpl j (keepsFs master) fallback s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle := by
  classical
  dsimp only; unfold mlkemBlockGhost
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (B.fb_pres s).2.1) (fun s => (B.fb_pres s).2.2.1)
  by_cases hG : mlkemActiveGuard mlkemMpl s0
  · rw [linkedCallHookG_eq_of_guard hG]; unfold linkedCallHook; split
    · rename_i hActPre; split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpreLs⟩
        obtain ⟨_, hpre⟩ := extract_withLsRet hpreLs
        obtain ⟨_, _, _, hvm, hfs, htr, htp, horc⟩ :=
          safe_run_on_activeRealRun B hG hrun hsp hpre hReal
        exact ⟨hvm, hfs, htr, htp, horc⟩
      · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩, rfl, rfl, rfl, rfl⟩
  · rw [linkedCallHookG_eq_of_not_guard hG]; split
    · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩, rfl, rfl, rfl, rfl⟩

/-- Unconditional `HookNoAllocFailed` for `mlkemBlockGhost`. -/
theorem mlkemBlockGhost_noAllocFailed [LibsignalPlacement] {mlkemMpl : MultiPlacement}
    {j : Nat} {sym : String} {α : Type} {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) :
    HookNoAllocFailed (mlkemBlockGhost mlkemMpl j (keepsFs master) fallback) :=
  hookNoAllocFailed_of_trace_eq _ fun s0 => (mlkemBlockGhost_vmPreserved_and_nonSyscall B s0).2.2.1

/-- Unconditional `DalekLsRowTuple` for `mlkemBlockGhost` (no `*Terminates` premises). -/
theorem mlkemBlockGhost_rowTuple [LibsignalPlacement] {mlkemMpl : MultiPlacement}
    {j : Nat} {sym : String} {α : Type} {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) :
    DalekLsRowTuple
      (mlkemBlockGhost mlkemMpl j (keepsFs master) fallback) master := by
  refine rowTuple_of_keepsFs_vm ?_
  rw [withLsRet_withVmPreserved]
  exact hookOk_withVmPreserved (mlkemBlockGhost_keepsFs_ok B)
    (fun s0 => (mlkemBlockGhost_vmPreserved_and_nonSyscall B s0).1)

/-! ## 4. Concrete Ghost Hooks & Unconditional `RowSpecAt` / `RowSpec` for All 7 ML-KEM Hooks -/

theorem kemEncapsSafeBridge (stk : Nat) (hstk : kemEncapsTightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 24 kemEncapsName (kemEncapsPreservedAtSpec stk kyber1024Prims₀)
      kemEncapsFallback where
  safe_ok := kemEncapsPreserved_at_keepsFs_vm_safeSubroutineOk kyber1024Prims₀
    (fun pk rand => ⟨kyber1024EncapsVec_fst_toList pk rand, kyber1024EncapsVec_snd_toList pk rand⟩)
    stk hstk hfit (fun _ => none)
  post_tr := fun ⟨_, _, _, _, _⟩ _ _ sf hpost => by
    dsimp only [kemEncapsPreservedAtSpec, withStack] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := kemEncapsFallback_preserved
  fb_keepsFs_ok := kemEncapsHook_preservedAt_keepsFs_ok kyber1024Prims₀ stk

theorem kemDecapsSafeBridge (stk : Nat) (hstk : kemDecapsTightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 23 kemDecapsName (kemDecapsAtSpec stk kyber1024Prims₀)
      kemDecapsFallback where
  safe_ok := kemDecaps_at_keepsFs_vm_safeSubroutineOk kyber1024Prims₀
    kyber1024DecapsVec_toList stk hstk hfit (fun _ => none)
  post_tr := fun ⟨_, _, _, _, _⟩ _ _ sf hpost => by
    dsimp only [kemDecapsAtSpec, withStack] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := kemDecapsFallback_preserved
  fb_keepsFs_ok := kemDecapsHook_at_keepsFs_ok kyber1024Prims₀ stk

theorem mlkemFromSeedSafeBridge (stk : Nat) (hstk : mlkemFromSeedTightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 10 mlkemFromSeedName (mlkemFromSeedAtSpec stk mlkem768Incremental)
      mlkemFromSeedFallback where
  safe_ok := mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList stk hstk hfit (fun _ => none)
  post_tr := fun _ _ _ sf hpost => by
    dsimp only [mlkemFromSeedAtSpec] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := mlkemFromSeedFallback_preserved
  fb_keepsFs_ok := mlkemFromSeedHook_at_keepsFs_ok mlkem768Incremental stk

theorem mlkemEncaps1SafeBridge (stk : Nat) (hstk : mlkemEncaps1TightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 19 mlkemEncaps1Name (mlkemEncaps1AtSpec stk mlkem768Incremental)
      mlkemEncaps1Fallback where
  safe_ok := mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk mlkem768Incremental
    (fun _ _ => rfl) stk hstk hfit (fun _ => none)
  post_tr := fun _ _ _ sf hpost => by
    dsimp only [mlkemEncaps1AtSpec] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := mlkemEncaps1Fallback_preserved
  fb_keepsFs_ok := mlkemEncaps1Hook_at_keepsFs_ok mlkem768Incremental stk

theorem mlkemEncaps2SafeBridge (stk : Nat) (hstk : mlkemEncaps2TightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 20 mlkemEncaps2Name (mlkemEncaps2AtSpec stk mlkem768Incremental)
      mlkemEncaps2Fallback where
  safe_ok := mlkemEncaps2_at_keepsFs_vm_safeSubroutineOk mlkem768Incremental
    mlkem768Incremental_encaps2_eq stk hstk hfit (fun _ => none)
  post_tr := fun _ _ _ sf hpost => by
    dsimp only [mlkemEncaps2AtSpec] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := mlkemEncaps2Fallback_preserved
  fb_keepsFs_ok := mlkemEncaps2Hook_at_keepsFs_ok mlkem768Incremental stk

theorem mlkemDecapsSafeBridge (stk : Nat) (hstk : mlkemDecapsTightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 22 mlkemDecapsName (mlkemDecapsAtSpec stk mlkem768Incremental)
      mlkemDecapsFallback where
  safe_ok := mlkemDecaps_at_keepsFs_vm_safeSubroutineOk mlkem768Incremental
    mlkem768Incremental_decaps_eq stk hstk hfit (fun _ => none)
  post_tr := fun _ _ _ sf hpost => by
    dsimp only [mlkemDecapsAtSpec] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1
  fb_pres := mlkemDecapsFallback_preserved
  fb_keepsFs_ok := mlkemDecapsHook_at_keepsFs_ok mlkem768Incremental stk

theorem mlkemValidatePkSafeBridge (stk : Nat) (hstk : mlkemValidatePkTightStack ≤ stk)
    (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlKemSafeBridge 21 mlkemValidatePkName (mlkemValidatePkAtSpec stk mlkem768Incremental)
      mlkemValidatePkFallback where
  safe_ok := mlkemValidatePk_at_keepsFs_vm_safeSubroutineOk mlkem768Incremental
    mlkem768Incremental_validPk_eq stk hstk hfit (fun _ => none)
  post_tr := fun _ _ _ sf hpost => by
    dsimp only [mlkemValidatePkAtSpec] at hpost
    simp only [sepConj_assoc] at hpost
    exact (satisfies_pure_sepConj _ _ sf.mem |>.mp hpost).1.2
  fb_pres := mlkemValidatePkFallback_preserved
  fb_keepsFs_ok := mlkemValidatePkHook_at_keepsFs_ok mlkem768Incremental stk

section ConcreteGhosts

variable [LibsignalPlacement]

/-- Hook #1 (`kemEncapsName`, `B24`) ghost hook at stack `stk`. -/
@[expose] noncomputable def kemEncapsGhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 24 (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀))
    kemEncapsFallback

/-- Hook #1 (`kemEncapsName`, `B24`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def kemEncapsGhost (mlkemMpl : MultiPlacement) : State → State :=
  kemEncapsGhostAt mlkemMpl mlkemHookStack

/-- Hook #2 (`kemDecapsName`, `B23`) ghost hook at stack `stk`. -/
@[expose] noncomputable def kemDecapsGhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 23 (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀))
    kemDecapsFallback

/-- Hook #2 (`kemDecapsName`, `B23`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def kemDecapsGhost (mlkemMpl : MultiPlacement) : State → State :=
  kemDecapsGhostAt mlkemMpl mlkemHookStack

/-- Hook #3 (`mlkemFromSeedName`, `B10`) ghost hook at stack `stk`. -/
@[expose] noncomputable def mlkemFromSeedGhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 10 (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental))
    mlkemFromSeedFallback

/-- Hook #3 (`mlkemFromSeedName`, `B10`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def mlkemFromSeedGhost (mlkemMpl : MultiPlacement) : State → State :=
  mlkemFromSeedGhostAt mlkemMpl mlkemHookStack

/-- Hook #4 (`mlkemEncaps1Name`, `B19`) ghost hook at stack `stk`. -/
@[expose] noncomputable def mlkemEncaps1GhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 19 (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental))
    mlkemEncaps1Fallback

/-- Hook #4 (`mlkemEncaps1Name`, `B19`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def mlkemEncaps1Ghost (mlkemMpl : MultiPlacement) : State → State :=
  mlkemEncaps1GhostAt mlkemMpl mlkemHookStack

/-- Hook #5 (`mlkemEncaps2Name`, `B20`) ghost hook at stack `stk`. -/
@[expose] noncomputable def mlkemEncaps2GhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 20 (keepsFs (mlkemEncaps2AtSpec stk mlkem768Incremental))
    mlkemEncaps2Fallback

/-- Hook #5 (`mlkemEncaps2Name`, `B20`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def mlkemEncaps2Ghost (mlkemMpl : MultiPlacement) : State → State :=
  mlkemEncaps2GhostAt mlkemMpl mlkemHookStack

/-- Hook #6 (`mlkemDecapsName`, `B22`) ghost hook at stack `stk`. -/
@[expose] noncomputable def mlkemDecapsGhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 22 (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental))
    mlkemDecapsFallback

/-- Hook #6 (`mlkemDecapsName`, `B22`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def mlkemDecapsGhost (mlkemMpl : MultiPlacement) : State → State :=
  mlkemDecapsGhostAt mlkemMpl mlkemHookStack

/-- Hook #7 (`mlkemValidatePkName`, `B21`) ghost hook at stack `stk`. -/
@[expose] noncomputable def mlkemValidatePkGhostAt (mlkemMpl : MultiPlacement) (stk : Nat) :
    State → State :=
  mlkemBlockGhost mlkemMpl 21 (keepsFs (mlkemValidatePkAtSpec stk mlkem768Incremental))
    mlkemValidatePkFallback

/-- Hook #7 (`mlkemValidatePkName`, `B21`) default `65,536`-B ghost hook. -/
@[expose] noncomputable def mlkemValidatePkGhost (mlkemMpl : MultiPlacement) : State → State :=
  mlkemValidatePkGhostAt mlkemMpl mlkemHookStack

/-- Unconditional `KemEncapsRowSpecAt` for `kemEncapsGhostAt` (`34,240 ≤ stk`). -/
theorem kemEncapsGhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    KemEncapsRowSpecAt stk (kemEncapsGhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (kemEncapsSafeBridge stk hstk hfit)

theorem kemEncapsGhost_rowSpec (mlkemMpl : MultiPlacement) :
    KemEncapsRowSpec (kemEncapsGhost mlkemMpl) :=
  kemEncapsGhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `KemDecapsRowSpecAt` for `kemDecapsGhostAt` (`35,968 ≤ stk`). -/
theorem kemDecapsGhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    KemDecapsRowSpecAt stk (kemDecapsGhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (kemDecapsSafeBridge stk hstk hfit)

theorem kemDecapsGhost_rowSpec (mlkemMpl : MultiPlacement) :
    KemDecapsRowSpec (kemDecapsGhost mlkemMpl) :=
  kemDecapsGhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `MlkemFromSeedRowSpecAt` for `mlkemFromSeedGhostAt` (`33,664 ≤ stk`). -/
theorem mlkemFromSeedGhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlkemFromSeedRowSpecAt stk (mlkemFromSeedGhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (mlkemFromSeedSafeBridge stk hstk hfit)

theorem mlkemFromSeedGhost_rowSpec (mlkemMpl : MultiPlacement) :
    MlkemFromSeedRowSpec (mlkemFromSeedGhost mlkemMpl) :=
  mlkemFromSeedGhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `MlkemEncaps1RowSpecAt` for `mlkemEncaps1GhostAt` (`18,304 ≤ stk`). -/
theorem mlkemEncaps1GhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlkemEncaps1RowSpecAt stk (mlkemEncaps1GhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (mlkemEncaps1SafeBridge stk hstk hfit)

theorem mlkemEncaps1Ghost_rowSpec (mlkemMpl : MultiPlacement) :
    MlkemEncaps1RowSpec (mlkemEncaps1Ghost mlkemMpl) :=
  mlkemEncaps1GhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `MlkemEncaps2RowSpecAt` for `mlkemEncaps2GhostAt` (`6,128 ≤ stk`). -/
theorem mlkemEncaps2GhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : mlkemEncaps2TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlkemEncaps2RowSpecAt stk (mlkemEncaps2GhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (mlkemEncaps2SafeBridge stk hstk hfit)

theorem mlkemEncaps2Ghost_rowSpec (mlkemMpl : MultiPlacement) :
    MlkemEncaps2RowSpec (mlkemEncaps2Ghost mlkemMpl) :=
  mlkemEncaps2GhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `MlkemDecapsRowSpecAt` for `mlkemDecapsGhostAt` (`26,960 ≤ stk`). -/
theorem mlkemDecapsGhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlkemDecapsRowSpecAt stk (mlkemDecapsGhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (mlkemDecapsSafeBridge stk hstk hfit)

theorem mlkemDecapsGhost_rowSpec (mlkemMpl : MultiPlacement) :
    MlkemDecapsRowSpec (mlkemDecapsGhost mlkemMpl) :=
  mlkemDecapsGhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

/-- Unconditional `MlkemValidatePkRowSpecAt` for `mlkemValidatePkGhostAt` (`5,824 ≤ stk`). -/
theorem mlkemValidatePkGhostAt_rowSpec (mlkemMpl : MultiPlacement) (stk : Nat)
    (hstk : mlkemValidatePkTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide) :
    MlkemValidatePkRowSpecAt stk (mlkemValidatePkGhostAt mlkemMpl stk) :=
  mlkemBlockGhost_rowTuple (mlkemMpl := mlkemMpl) (mlkemValidatePkSafeBridge stk hstk hfit)

theorem mlkemValidatePkGhost_rowSpec (mlkemMpl : MultiPlacement) :
    MlkemValidatePkRowSpec (mlkemValidatePkGhost mlkemMpl) :=
  mlkemValidatePkGhostAt_rowSpec mlkemMpl mlkemHookStack (by decide) (by decide)

end ConcreteGhosts

/-! ## 5. `GhostRowReplayOn` Bridges (Unconditional #5/#7 & Per-Call Guarded #1/#2/#3/#4/#6) -/

private theorem stripS_setPC_readBytes (keep : BitVec 64 → Bool) (s : State) (pc a : BitVec 64)
    (n : Nat) :
    (stripS keep (s.setPC pc)).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem]
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [hmem]
  exact strip_readBytes keep s.mem a n

private theorem stripS_setPC_readVecN (keep : BitVec 64 → Bool) (s : State) (pc a : BitVec 64)
    (n : Nat) :
    readVecN (stripS keep (s.setPC pc)).mem a n = readVecN s.mem a n :=
  Subtype.ext (stripS_setPC_readBytes keep s pc a n)

private theorem keepsFs_fsT {α : Type} {master : Spec α} {j : Nat} {sym : String}
    {fallback : State → State} (B : MlKemSafeBridge j sym master fallback) :
    SpecPreservesFsTrace (keepsFs master) := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨hfs, htr⟩ := keepsFs_post_fs_tr B x R s0 sf hpost
    exact ⟨hfs, FsTraced.of_eq htr (congrArg (·.files) hfs)⟩
  · dsimp only [keepsFs] at hp; rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
  · dsimp only [keepsFs] at he; rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
  · dsimp only [keepsFs] at ho; rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

section Replay

variable [LibsignalPlacement]

private theorem specStripSInvariant_withLsRet {keep : BitVec 64 → Bool} {α : Type}
    {spec : Spec α} (h : SpecStripSInvariant keep spec) :
    SpecStripSInvariant keep (withLsRet spec) where
  pre_eq := fun x s => by dsimp only [withLsRet]; rw [stripS_readReg64, h.pre_eq x s]
  post_eq := h.post_eq
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq

private theorem specPreservesFsTrace_withLsRet {α : Type} {spec : Spec α}
    (h : SpecPreservesFsTrace spec) :
    SpecPreservesFsTrace (withLsRet spec) := h

/-- State-level `SampleNTT` termination predicates reading the call input directly from `u.mem` at
    the AAPCS register pointer (`x0` / `(x0, x1)`), invariant under `setPC` and `stripS`. -/
@[expose] def KemEncapsStateTerminates (u : State) : Prop :=
  Kyber1024EncapsTerminates (u.mem.readBytes (u.readReg64 .x0) 1568)

@[expose] def KemDecapsStateTerminates (u : State) : Prop :=
  Kyber1024DecapsTerminates (u.mem.readBytes (u.readReg64 .x0) 3168)

@[expose] def MlkemFromSeedStateTerminates (u : State) : Prop :=
  Mlkem768FromSeedTerminates (readVecN u.mem (u.readReg64 .x0) 64)

@[expose] def MlkemEncaps1StateTerminates (u : State) : Prop :=
  Mlkem768Encaps1Terminates (u.mem.readBytes (u.readReg64 .x0) (u.readReg64 .x1).toNat)

@[expose] def MlkemDecapsStateTerminates (u : State) : Prop :=
  Mlkem768DecapsTerminates (readVecN u.mem (u.readReg64 .x0) 2400)

/-- Trajectory-level entry guard requiring `StateTerm u` at every non-exception stub entry of `sym`
    along the ghost trajectory `s0 →* sf` (matching `ExtraGhostReplay.GhostRowReplayOn`). -/
@[expose] def mlkemStubStateEntryGuard (mpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (StateTerm : State → Prop) (s0 : State) : Prop :=
  ∀ (W : CliHooks) (u : State),
    Steps (cliProgExtPlacedAt mpl EG 617 W) s0 u →
    u.pc = libsignalSessionLib.resolve mpl sym →
    u.status = .Running →
    StateTerm u

/-- Generic `GhostRowReplayOn` builder for a `mlkemBlockGhost` whose block `j` satisfies
    `subroutine_ok` under `withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)`. -/
theorem mlkemBlockGhost_rowReplayOn_guarded
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
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
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base j)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym StateTerm)
      (mlkemBlockGhost mlkemMpl j (keepsFs master) fallback) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨mlkemBlockGhost_preserves_execFrozen mlkemMpl j (keepsFs master) hfb hfr,
     mlkemBlockGhost_fs mlkemMpl j (keepsFs master) fallback u⟩
  replay_at_stub := by
    intro W s0 _sf _stubPc _P_ghost _P_real hEntry _hret_pc _hnoex_sf _hnhalt_sf
    right
    refine ⟨hRealStubNone W, fun u hsteps_u _ hpc hrun hnoex hkf hfr hInvU => ?_⟩
    have hInvM : mlkemInvMem mlkemMpl u.mem := hInvMlkem u hInvU
    have hGu : mlkemActiveGuard mlkemMpl u := hInvM
    have hTu : StateTerm u := hEntry W u hsteps_u hpc hrun
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
        (fallback := fallback) emptyStdProg_svc (mlkemBlockProgram_svc mlkemMpl j)
        (fun pc _ => emptyStdProg_externAt_none pc)
        (externAt?_mlkemBlockProgram_ext_none mlkemMpl hj (fun _ => none))
        (fun v _ ⟨hg, ht⟩ => ⟨mlkemActiveGuard_stripS_setPC mlkemMpl _ v hg, hTermStrip v ht⟩)
        hSubOk (specStripSInvariant_withLsRet hStripInv) (specPreservesFsTrace_withLsRet hFsT)
        (withLsRet_pre_setPC hPrePC) (withLsRet_outcome_setPC hOutPC)
        ⟨hGu, hTu⟩ hActPre hfr hlr hCodeSub
    rw [← hEqG] at hvis hfr_out
    have hStubSteps := hStub W u hpc hrun hfr hInvM
    have hBodySteps := h2fsgen_steps_lift_of_visitedIn_noExtern
      (D := mlkemKeep mlkemMpl) (P1 := emptyStdProg)
      (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
      (fun pc _ => emptyStdProg_externAt_none pc) (fun _ hk => hRealMlkemNoExt W hk) hvis
    exact ⟨hStubSteps.trans hBodySteps, hfr_out,
      hInvKeep u _ hInvU hkf (mlkemBlockGhost_fs mlkemMpl j (keepsFs master) fallback u)⟩

private theorem subroutineOk_guarded_from_multi {j : Nat} {sym : String} {α : Type}
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

/-- Hook #5 (`mlkemEncaps2GhostAt`, `B20`): unconditional `GhostRowReplayOn` (`entryGuard := fun _ => True`). -/
theorem mlkemEncaps2GhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : mlkemEncaps2TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 20)) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True) (mlkemEncaps2GhostAt mlkemMpl stk) := by
  let B := mlkemEncaps2SafeBridge stk hstk hfit
  have hSub := mlkemEncaps2_at_keepsFs_vm_subroutineOk mlkem768Incremental
    mlkem768Incremental_encaps2_eq stk hstk hfit (fun _ => none)
  have hSubPrem : mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun m => withMlKemRoOk m (withPremise (fun _ => True)
        (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk mlkem768Incremental))))) (fun _ => none) :=
    SpecSimulates.multiSubroutineOk
      (fun _ => SpecSimulates.of_map fun x R _ hpre => by
        dsimp only [withMlKemRoOk, withPremise] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨hro, hp⟩ := hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        refine ⟨x, R, ?_, fun _ _ _ hq => hq⟩
        dsimp only [withMlKemRoOk]
        rw [sepConj_assoc, pure_sepConj_of_true hro]
        exact hp.2)
      hSub
  have hRep := mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    (fun _ => True) (fun _ _ => trivial)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSubPrem (fun _ _ _ _ _ => trivial))
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact ⟨hRep.preserves_execFrozen, fun W s0 sf _ hret hnoex hnhalt =>
    hRep.replay_at_stub W s0 sf (fun _ _ _ _ _ => trivial) hret hnoex hnhalt⟩

/-- Hook #7 (`mlkemValidatePkGhostAt`, `B21`): unconditional `GhostRowReplayOn` (`entryGuard := fun _ => True`). -/
theorem mlkemValidatePkGhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : mlkemValidatePkTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 21)) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True)
      (mlkemValidatePkGhostAt mlkemMpl stk) := by
  let B := mlkemValidatePkSafeBridge stk hstk hfit
  have hSub := mlkemValidatePk_at_keepsFs_vm_subroutineOk mlkem768Incremental
    mlkem768Incremental_validPk_eq stk hstk hfit (fun _ => none)
  have hSubPrem : mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun m => withMlKemRoOk m (withPremise (fun _ => True)
        (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk mlkem768Incremental))))) (fun _ => none) :=
    SpecSimulates.multiSubroutineOk
      (fun _ => SpecSimulates.of_map fun x R _ hpre => by
        dsimp only [withMlKemRoOk, withPremise] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨hro, hp⟩ := hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        refine ⟨x, R, ?_, fun _ _ _ hq => hq⟩
        dsimp only [withMlKemRoOk]
        rw [sepConj_assoc, pure_sepConj_of_true hro]
        exact hp.2)
      hSub
  have hRep := mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    (fun _ => True) (fun _ _ => trivial)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSubPrem (fun _ _ _ _ _ => trivial))
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub
  exact ⟨hRep.preserves_execFrozen, fun W s0 sf _ hret hnoex hnhalt =>
    hRep.replay_at_stub W s0 sf (fun _ _ _ _ _ => trivial) hret hnoex hnhalt⟩

/-- Hook #1 (`kemEncapsGhostAt`, `B24`): trajectory-guarded `GhostRowReplayOn`. -/
theorem kemEncapsGhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 24)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym KemEncapsStateTerminates)
      (kemEncapsGhostAt mlkemMpl stk) := by
  let B := kemEncapsSafeBridge stk hstk hfit
  have hSub := kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
    (fun pk rand => ⟨kyber1024EncapsVec_fst_toList pk rand, kyber1024EncapsVec_snd_toList pk rand⟩)
    stk hstk hfit (fun _ => none)
  refine mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    KemEncapsStateTerminates
    (fun s0 hT => by
      unfold KemEncapsStateTerminates at hT ⊢
      rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 24)).readReg64 .x0 = s0.readReg64 .x0
        by cases s0; rfl, stripS_setPC_readBytes]
      exact hT)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSub fun ⟨pkA, pk, rA, rnd, ret⟩ R s hT hpre => by
      dsimp only [kemEncapsPreservedAtSpec, withStack] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨⟨hx0, _, _⟩, hmem⟩ := hpre
      obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes pkA pk.toList).read hmem
      rw [pk.toList_length] at hread
      unfold KemEncapsCallTerminates
      unfold KemEncapsStateTerminates at hT
      rwa [hx0, hread] at hT)
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Hook #2 (`kemDecapsGhostAt`, `B23`): trajectory-guarded `GhostRowReplayOn`. -/
theorem kemDecapsGhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 23)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym KemDecapsStateTerminates)
      (kemDecapsGhostAt mlkemMpl stk) := by
  let B := kemDecapsSafeBridge stk hstk hfit
  have hSub := kemDecaps_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
    kyber1024DecapsVec_toList stk hstk hfit (fun _ => none)
  refine mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    KemDecapsStateTerminates
    (fun s0 hT => by
      unfold KemDecapsStateTerminates at hT ⊢
      rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 23)).readReg64 .x0 = s0.readReg64 .x0
        by cases s0; rfl, stripS_setPC_readBytes]
      exact hT)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSub fun ⟨skA, sk, ctA, ct, ret⟩ R s hT hpre => by
      dsimp only [kemDecapsAtSpec, withStack] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨⟨hx0, _, _⟩, hmem⟩ := hpre
      obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes skA sk.toList).read hmem
      rw [sk.toList_length] at hread
      unfold KemDecapsCallTerminates
      unfold KemDecapsStateTerminates at hT
      rwa [hx0, hread] at hT)
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Hook #3 (`mlkemFromSeedGhostAt`, `B10`): trajectory-guarded `GhostRowReplayOn`. -/
theorem mlkemFromSeedGhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 10)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym MlkemFromSeedStateTerminates)
      (mlkemFromSeedGhostAt mlkemMpl stk) := by
  let B := mlkemFromSeedSafeBridge stk hstk hfit
  have hSub := mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList stk hstk hfit (fun _ => none)
  refine mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    MlkemFromSeedStateTerminates
    (fun s0 hT => by
      unfold MlkemFromSeedStateTerminates at hT ⊢
      rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 10)).readReg64 .x0 = s0.readReg64 .x0
        by cases s0; rfl, stripS_setPC_readVecN]
      exact hT)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSub fun x R s hT hpre => by
      dsimp only [mlkemFromSeedAtSpec] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨⟨hx0, _⟩, hmem⟩ := hpre
      have hread : readVecN s.mem x.seedA 64 = x.seed := readVecN_eq_of_pointsToBytes hmem
      unfold MlkemFromSeedCallTerminates
      unfold MlkemFromSeedStateTerminates at hT
      rwa [hx0, hread] at hT)
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Hook #4 (`mlkemEncaps1GhostAt`, `B19`): trajectory-guarded `GhostRowReplayOn`. -/
theorem mlkemEncaps1GhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 19)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym MlkemEncaps1StateTerminates)
      (mlkemEncaps1GhostAt mlkemMpl stk) := by
  let B := mlkemEncaps1SafeBridge stk hstk hfit
  have hSub := mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    (fun _ _ => rfl) stk hstk hfit (fun _ => none)
  refine mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    MlkemEncaps1StateTerminates
    (fun s0 hT => by
      unfold MlkemEncaps1StateTerminates at hT ⊢
      rw [stripS_readReg64, stripS_readReg64,
        show (s0.setPC (mlkemMpl.base 19)).readReg64 .x0 = s0.readReg64 .x0 by cases s0; rfl,
        show (s0.setPC (mlkemMpl.base 19)).readReg64 .x1 = s0.readReg64 .x1 by cases s0; rfl,
        stripS_setPC_readBytes]
      exact hT)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSub fun x R s hT hpre => by
      dsimp only [mlkemEncaps1AtSpec] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨⟨_, hx0, hx1, _, _, _, _, _⟩, hmem⟩ := hpre
      obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
      unfold MlkemEncaps1CallTerminates
      unfold MlkemEncaps1StateTerminates at hT
      rwa [hx0, hx1, hread] at hT)
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

/-- Hook #6 (`mlkemDecapsGhostAt`, `B22`): trajectory-guarded `GhostRowReplayOn`. -/
theorem mlkemDecapsGhostAt_rowReplayOn
    (mpl mmpl mlkemMpl : MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State)) (sym : String)
    (stk : Nat) (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    (hInvMlkem : ∀ u : State, InvS u → mlkemInvMem mlkemMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep mlkemMpl lr = false)
    (hRealMlkemNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, mlkemKeep mlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (mlkemInvMem mlkemMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) (mlkemMpl.base 22)) :
    GhostRowReplayOn mpl mmpl InvS EG sym
      (mlkemStubStateEntryGuard mpl EG sym MlkemDecapsStateTerminates)
      (mlkemDecapsGhostAt mlkemMpl stk) := by
  let B := mlkemDecapsSafeBridge stk hstk hfit
  have hSub := mlkemDecaps_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_decaps_eq stk hstk hfit (fun _ => none)
  refine mlkemBlockGhost_rowReplayOn_guarded mpl mmpl mlkemMpl InvS EG sym B.hj
    MlkemDecapsStateTerminates
    (fun s0 hT => by
      unfold MlkemDecapsStateTerminates at hT ⊢
      rw [stripS_readReg64, show (s0.setPC (mlkemMpl.base 22)).readReg64 .x0 = s0.readReg64 .x0
        by cases s0; rfl, stripS_setPC_readVecN]
      exact hT)
    (subroutineOk_guarded_from_multi mlkemMpl B.hsym hSub fun x R s hT hpre => by
      dsimp only [mlkemDecapsAtSpec] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨⟨_, hx0, _, _⟩, hmem⟩ := hpre
      have hread : readVecN s.mem x.dkA 2400 = x.dk := readVecN_eq_of_pointsToBytes hmem
      unfold MlkemDecapsCallTerminates
      unfold MlkemDecapsStateTerminates at hT
      rwa [hx0, hread] at hT)
    (keepsFs_strip_inv B (mlkemKeep mlkemMpl)) (keepsFs_fsT B)
    (fun _ s _ => by cases s; rfl) (fun _ _ s0 sf _ h => by cases s0; cases sf; exact h)
    B.fb_pres hInvMlkem hInvKeep hKeep hRealMlkemNoExt hRealStubNone hStub

end Replay

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
