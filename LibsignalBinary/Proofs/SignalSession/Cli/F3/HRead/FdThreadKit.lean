/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Per-Call `FdsGe3Closed` and Return-Address Threading Kit

Combinators for threading `FdsGe3Closed` and `LsRetAddr624` / `keepSet` return-address guards
across `HookOk`, `HookSat`, and `subroutine_ok` boundaries.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit

open Arm64 (FsState HookOk HookSat Memory Program Reg SepProp Spec State subroutine_ok
  subroutine_ok_mono)
open ProofLib (Entails Satisfies satisfies_pure_sepConj sepConj_assoc sepConj_comm
  sepConj_left_comm)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
  libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles extract_withLsCodeRoLoaded
  extract_withLsRoCl subroutine_ok_rocl_of_plain subroutine_ok_rocl_of_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain subroutine_ok_withLsCodeRoLoaded_of_rocl
  withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName withStack)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SignalSession
  (lsReadFileSym lsRustDeallocSymCli lsRustNoAllocShimSymCli readStdinHook writeFileHook
   writeStdoutHook)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits
  RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr LsRetAddr624 lsRetAddr624_of_lsRetAddr)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed fdsGe3Closed_readStdinHook fdsGe3Closed_writeFileHook
   fdsGe3Closed_writeStdoutHook hRead_of_hookSat hookOk_withFdsGe3Closed
   hookOk_withFdsGe3Closed_of_fs_eq hookOk_withFdsGe3Closed_readStdinHook
   hookOk_withFdsGe3Closed_writeFileHook hookOk_withFdsGe3Closed_writeStdoutHook
   subroutine_ok_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced ReadFileRuleEnv readFileSpecPlaced)

/-- Narrow `spec.pre` by conjoining `⌜P s⌝` while keeping `post`, `onPanic`, `onExit`, and `onOom`
    definitionally unchanged. -/
@[expose]
def withPreGuard {α : Type} (P : State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜P s⌝ ∗ spec.pre x s }

/-- Narrow `spec.pre` by `⌜keepSet (s.readReg64 .lr) = false⌝`. -/
abbrev withKeepLrFalse {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  withPreGuard (fun s => keepSet (s.readReg64 .lr) = false) spec

/-- Narrow `spec.pre` by `⌜keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs⌝`. -/
abbrev withKeepLrAndFds {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  withPreGuard (fun s => keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs) spec

/-- Thread `LsRetAddr624 (s.readReg64 .lr)` in `pre` and `FdsGe3Closed` in both `pre` and `post`. -/
@[expose]
def withLsRetAddr624AndFds [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  withPreGuard (fun s => LsRetAddr624 (s.readReg64 .lr)) (withFdsGe3Closed spec)

/-- Contravariant precondition strengthening for `HookOk`: if `Q s → P s`, a hook meeting
    `withPreGuard P spec` also meets `withPreGuard Q spec`. -/
theorem hookOk_withPreGuard_mono {α : Type} {f : State → State} {P Q : State → Prop}
    {spec : Spec α} (himp : ∀ s, Q s → P s)
    (hok : HookOk f (withPreGuard P spec)) :
    HookOk f (withPreGuard Q spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withPreGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine hok x R s0 hrun ?_ hsp
  dsimp only [withPreGuard]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨himp s0 hpre.1, hpre.2⟩

theorem hookSat_withPreGuard_mono {α : Type} {H : LibsignalHooks} {sym : String}
    {P Q : State → Prop} {spec : Spec α} (himp : ∀ s, Q s → P s)
    (hsat : HookSat H sym (withPreGuard P spec)) :
    HookSat H sym (withPreGuard Q spec) := by
  rcases hsat with ⟨f, hsym, hok⟩
  exact ⟨f, hsym, hookOk_withPreGuard_mono himp hok⟩

theorem subroutine_ok_withPreGuard_mono {α : Type} {prog : Program} {entry : BitVec 64}
    {P Q : State → Prop} {spec : Spec α} (himp : ∀ s, Q s → P s)
    (h : subroutine_ok prog entry (withPreGuard P spec)) :
    subroutine_ok prog entry (withPreGuard Q spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      dsimp only [withPreGuard] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨himp s0 hp.1, hp.2⟩)
    (fun _ _ _ _ hq => hq)

/-- Reassociate `HookOk f (withFdsGe3Closed (withKeepLrAndFds keepSet spec))` to
`HookOk f (withKeepLrFalse keepSet (withFdsGe3Closed spec))`. -/
theorem hookOk_keepLr_withFds_of_withFds_keepLrAndFds {α : Type} {f : State → State}
    {keepSet : BitVec 64 → Bool} {spec : Spec α}
    (hok : HookOk f (withFdsGe3Closed (withKeepLrAndFds keepSet spec))) :
    HookOk f (withKeepLrFalse keepSet (withFdsGe3Closed spec)) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withKeepLrFalse, withPreGuard, withFdsGe3Closed] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hlr, hfds, hpre0⟩
  have hpreK : s0.mem ⊨ (withFdsGe3Closed (withKeepLrAndFds keepSet spec)).pre x s0 ∗ R := by
    dsimp only [withFdsGe3Closed, withKeepLrAndFds, withPreGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds, ⟨hlr, hfds⟩, hpre0⟩
  exact hok x R s0 hrun hpreK hsp

theorem hookSat_keepLr_withFds_of_withFds_keepLrAndFds {α : Type} {H : LibsignalHooks}
    {sym : String} {keepSet : BitVec 64 → Bool} {spec : Spec α}
    (hsat : HookSat H sym (withFdsGe3Closed (withKeepLrAndFds keepSet spec))) :
    HookSat H sym (withKeepLrFalse keepSet (withFdsGe3Closed spec)) := by
  rcases hsat with ⟨f, hsym, hok⟩
  exact ⟨f, hsym, hookOk_keepLr_withFds_of_withFds_keepLrAndFds hok⟩

/-- Bridge `HookSat H sym (withFdsGe3Closed (withKeepLrAndFds keepSet spec))` to
`HookSat H sym (withLsRetAddr624AndFds spec)` given `∀ lr, LsRetAddr624 lr → keepSet lr = false`. -/
theorem hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {keepSet : BitVec 64 → Bool} {spec : Spec α}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepSet lr = false)
    (hsat : HookSat H sym (withFdsGe3Closed (withKeepLrAndFds keepSet spec))) :
    HookSat H sym (withLsRetAddr624AndFds spec) :=
  hookSat_withPreGuard_mono (fun _ hlr => hKeep _ hlr)
    (hookSat_keepLr_withFds_of_withFds_keepLrAndFds hsat)

/-- Frame `FdsGe3Closed` across any `subroutine_ok` whose postcondition implies `sf.fs = s0.fs`. -/
theorem subroutine_ok_withFdsGe3Closed_of_fs_eq {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok P entry spec)
    (hfs : ∀ x R s0 sf, (sf.mem ⊨ spec.post x s0 sf ∗ R) → sf.fs = s0.fs) :
    subroutine_ok P entry (withFdsGe3Closed spec) :=
  subroutine_ok_withFdsGe3Closed h (fun x R s0 sf h0 hpost => (hfs x R s0 sf hpost) ▸ h0)

theorem subroutine_ok_withFdsGe3Closed_of_keepsFs {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok P entry spec.keepsFs) :
    subroutine_ok P entry (withFdsGe3Closed spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre0 hsp _
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpre0
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost.1 ▸ hClosed0, hpost.2⟩
  · exact Or.inr hrest

theorem subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs {α : Type}
    {pl : Arm64.Obj.MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCodeRoLoaded pl spec).keepsFs) :
    subroutine_ok P entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec)) :=
  subroutine_ok_mono (subroutine_ok_withFdsGe3Closed_of_keepsFs h)
    (fun _ _ _ hp => by
      dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hp ⊢
      exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed {α : Type}
    {pl : Arm64.Obj.MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withFdsGe3Closed (withLsCodeRoLoaded pl spec))) :
    subroutine_ok P entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hp ⊢
      exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

/-- Lift `HookSat ext lsReadFileSym spec` to `subroutine_ok callerProg (lsρ lsReadFileSym) spec`
on an unmutated block `i`. -/
theorem lsReadFile_subroutine_ok_of_hookSat [LibsignalPlacement] {α : Type}
    {spec : Spec α} {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym spec)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym) spec :=
  ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i) hsat (by decide) hi hunmut

theorem lsReadFile_withLsCodeRoLoaded_of_hookSat [LibsignalPlacement] {α : Type}
    {spec : Spec α} {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym spec)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym) (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (lsReadFile_subroutine_ok_of_hookSat hsat hi hunmut)

theorem lsReadFile_rocl_of_hookSat [LibsignalPlacement] {α : Type}
    {spec : Spec α} {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym spec)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain (lsReadFile_subroutine_ok_of_hookSat hsat hi hunmut)

theorem subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded {α : Type}
    {pl : Arm64.Obj.MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec))) :
    subroutine_ok P entry (withFdsGe3Closed (withLsCodeRoLoaded pl spec)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hp ⊢
      exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

theorem ls_transfer_withFdsGe3Closed_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withFdsGe3Closed (withLsCodeRoLoaded lsmpl spec)))
    (hi : i < 619 := by decide)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withFdsGe3Closed (withLsCodeRoLoaded lsmpl spec)) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded
    (ls_transfer_lscro (callerProg := callerProg) (calleeProg := calleeProg) (i := i) (j := j)
      (subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed h) hi hj hj_unmut)

theorem dealloc_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hFs.dealloc hi

theorem shim_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hFs.shim stk h1 h2) hi

theorem session_memcpy_region_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hFs.session_memcpy_region stk h1 h2) hi

theorem session_memcpy_region_ro_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hFs.session_memcpy_region_ro stk h1 h2) hi

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
