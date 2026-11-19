/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook -- proof-setup: allow-public-import

/-!
# Concrete `GhostRowOk` and `HookNoAllocFailed` Glue for ML-KEM

Instantiates `GhostRowSpecOk`, `GhostRowReplayOn`, `GhostRowOk` (both natural entry-guard and
`guardOf` forms), and `HookNoAllocFailed` at `c2MlkemMpl` (`*TightStack`, matching
`ExtraGhostSpecs.ExtraRowSpec`) for all 7 `libcrux_ml_kem` exports:
1. `lsKyber1024EncapsSym` (`kemEncapsGhostAt c2MlkemMpl kemEncapsTightStack`, block `24`)
2. `lsKyber1024DecapsSym` (`kemDecapsGhostAt c2MlkemMpl kemDecapsTightStack`, block `23`)
3. `lsMlkem768FromSeedSym` (`mlkemFromSeedGhostAt c2MlkemMpl mlkemFromSeedTightStack`, block `10`)
4. `lsMlkem768Encaps1Sym` (`mlkemEncaps1GhostAt c2MlkemMpl mlkemEncaps1TightStack`, block `19`)
5. `lsMlkem768Encaps2Sym` (`mlkemEncaps2GhostAt c2MlkemMpl mlkemEncaps2TightStack`, block `20`, unconditional)
6. `lsMlkem768DecapsSym` (`mlkemDecapsGhostAt c2MlkemMpl mlkemDecapsTightStack`, block `22`)
7. `lsMlkem768ValidatePkSym` (`mlkemValidatePkGhostAt c2MlkemMpl mlkemValidatePkTightStack`, block `21`, unconditional)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRow

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (mlkemKeep)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (HookNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem
  (c2_mlkem_invMem_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemKeep c2MlkemMpl c2_mlkemKeep_lr_false c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg
   c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
   c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq
   c2_resolve_mlkem768Encaps2_eq c2_resolve_mlkem768FromSeed_eq
   c2_resolve_mlkem768ValidatePk_eq lsKyber1024DecapsSym lsKyber1024EncapsSym
   lsMlkem768DecapsSym lsMlkem768Encaps1Sym lsMlkem768Encaps2Sym
   lsMlkem768FromSeedSym lsMlkem768ValidatePkSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
  (KemDecapsStateTerminates KemEncapsStateTerminates MlkemDecapsStateTerminates
   MlkemEncaps1StateTerminates MlkemFromSeedStateTerminates
   kemDecapsGhost kemDecapsGhostAt kemDecapsGhostAt_rowReplayOn kemDecapsGhostAt_rowSpec
   kemDecapsSafeBridge
   kemEncapsGhost kemEncapsGhostAt kemEncapsGhostAt_rowReplayOn kemEncapsGhostAt_rowSpec
   kemEncapsSafeBridge
   mlkemBlockGhost_fs mlkemBlockGhost_fsT mlkemBlockGhost_noAllocFailed
   mlkemDecapsGhost mlkemDecapsGhostAt mlkemDecapsGhostAt_rowReplayOn mlkemDecapsGhostAt_rowSpec
   mlkemDecapsSafeBridge
   mlkemEncaps1Ghost mlkemEncaps1GhostAt mlkemEncaps1GhostAt_rowReplayOn mlkemEncaps1GhostAt_rowSpec
   mlkemEncaps1SafeBridge
   mlkemEncaps2Ghost mlkemEncaps2GhostAt mlkemEncaps2GhostAt_rowReplayOn mlkemEncaps2GhostAt_rowSpec
   mlkemEncaps2SafeBridge
   mlkemFromSeedGhost mlkemFromSeedGhostAt mlkemFromSeedGhostAt_rowReplayOn
   mlkemFromSeedGhostAt_rowSpec mlkemFromSeedSafeBridge mlkemInvMem mlkemStubStateEntryGuard
   mlkemValidatePkGhost mlkemValidatePkGhostAt mlkemValidatePkGhostAt_rowReplayOn
   mlkemValidatePkGhostAt_rowSpec mlkemValidatePkSafeBridge)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (KemDecapsRowSpecAt KemEncapsRowSpecAt MlkemDecapsRowSpecAt MlkemEncaps1RowSpecAt
   MlkemEncaps2RowSpecAt MlkemFromSeedRowSpecAt MlkemValidatePkRowSpecAt
   kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemHookStack mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3RxSeg_realProg617_externAt_none isLinkedPanicAddr keepLib2Text
   keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

/-! ## 1. Shared Premise Dischargers at `c2MlkemMpl` -/

private theorem stubReachesTargetOn_of_eq {InvMem : Memory → Prop} {P_real : Program}
    {stubPc entryTarget : BitVec 64} (h : stubPc = entryTarget) :
    StubReachesTargetOn InvMem P_real stubPc entryTarget :=
  fun u hpc _ _ _ => by
    have heq : u.setPC entryTarget = u := by
      rw [← h, ← hpc]
      cases u
      rfl
    rw [heq]
    exact Steps.refl u

private theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {g1 g2 : State → Prop} {f : State → State}
    (h : GhostRowReplayOn mpl mmpl InvS EG sym g1 f)
    (himp : ∀ s0, g2 s0 → g1 s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym g2 f :=
  ⟨h.preserves_execFrozen, fun W s0 sf hg2 => h.replay_at_stub W s0 sf (himp s0 hg2)⟩

private theorem c2_mlkem_entry_in_lib2 :
    ∀ j ∈ ([10, 19, 20, 21, 22, 23, 24] : List Nat),
      keepLib2Text (c2MlkemMpl.base j) = true := by
  decide

private theorem c2_mlkem_entry_noPanic :
    ∀ j ∈ ([10, 19, 20, 21, 22, 23, 24] : List Nat),
      isLinkedPanicAddr (c2MlkemMpl.base j) = false := by
  decide

private theorem c2_mlkem_realStubNone {mpl mmpl : Obj.MultiPlacement} {sym : String} {j : Nat}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl sym = c2MlkemMpl.base j)
    (hj : j ∈ ([10, 19, 20, 21, 22, 23, 24] : List Nat) := by decide) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none :=
  fun W => by
    rw [hRes]
    exact f3RxSeg_realProg617_externAt_none hExt W
      (keepLib2Text_sub_rxProg (c2_mlkem_entry_in_lib2 j hj))
      (c2_mlkem_entry_noPanic j hj)

private theorem c2_mlkem_invMem_of_inv {mpl mmpl : Obj.MultiPlacement} {PredFs : FsState → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ∀ u : State, (F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) → mlkemInvMem c2MlkemMpl u.mem :=
  fun _ hu => c2_mlkem_invMem_of_f3CodeInv hLs hu.1

private theorem c2_mlkem_keep_lr [LibsignalPlacement]
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep c2MlkemMpl lr = false := by
  intro lr hlr
  rw [hKeepEq]
  exact c2_mlkemKeep_lr_false hLs hlr

private theorem c2_mlkem_realNoExt {mpl mmpl : Obj.MultiPlacement}
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      mlkemKeep c2MlkemMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  intro W pc hk
  rw [hKeepEq] at hk
  exact f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg hk)
    (c2_mlkemKeep_noPanic hk)

/-! ## 2. `ExtraRowSpec` Arm Injections (`*TightStack` Arms) -/

theorem kemEncaps_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : KemEncapsRowSpecAt kemEncapsTightStack f) : ExtraRowSpec lsKyber1024EncapsSym f := by
  unfold ExtraRowSpec
  iterate 24 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem kemDecaps_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : KemDecapsRowSpecAt kemDecapsTightStack f) : ExtraRowSpec lsKyber1024DecapsSym f := by
  unfold ExtraRowSpec
  iterate 25 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem mlkemFromSeed_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : MlkemFromSeedRowSpecAt mlkemFromSeedTightStack f) :
    ExtraRowSpec lsMlkem768FromSeedSym f := by
  unfold ExtraRowSpec
  iterate 26 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem mlkemEncaps1_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : MlkemEncaps1RowSpecAt mlkemEncaps1TightStack f) :
    ExtraRowSpec lsMlkem768Encaps1Sym f := by
  unfold ExtraRowSpec
  iterate 27 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem mlkemEncaps2_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : MlkemEncaps2RowSpecAt mlkemEncaps2TightStack f) :
    ExtraRowSpec lsMlkem768Encaps2Sym f := by
  unfold ExtraRowSpec
  iterate 28 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem mlkemDecaps_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : MlkemDecapsRowSpecAt mlkemDecapsTightStack f) :
    ExtraRowSpec lsMlkem768DecapsSym f := by
  unfold ExtraRowSpec
  iterate 29 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem mlkemValidatePk_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : MlkemValidatePkRowSpecAt mlkemValidatePkTightStack f) :
    ExtraRowSpec lsMlkem768ValidatePkSym f := by
  unfold ExtraRowSpec
  iterate 30 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

/-! ## 3. Unconditional `HookNoAllocFailed` (Tight and Default Stacks at `c2MlkemMpl`) -/

theorem c2_kemEncapsGhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := kemEncapsTightStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (kemEncapsGhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (kemEncapsSafeBridge stk hlo hhi)

theorem c2_kemEncapsGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (kemEncapsGhost c2MlkemMpl) :=
  c2_kemEncapsGhostAt_noAllocFailed mlkemHookStack

theorem c2_kemDecapsGhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := kemDecapsTightStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (kemDecapsGhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (kemDecapsSafeBridge stk hlo hhi)

theorem c2_kemDecapsGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (kemDecapsGhost c2MlkemMpl) :=
  c2_kemDecapsGhostAt_noAllocFailed mlkemHookStack

theorem c2_mlkemFromSeedGhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := mlkemFromSeedTightStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (mlkemFromSeedGhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (mlkemFromSeedSafeBridge stk hlo hhi)

theorem c2_mlkemFromSeedGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (mlkemFromSeedGhost c2MlkemMpl) :=
  c2_mlkemFromSeedGhostAt_noAllocFailed mlkemHookStack

theorem c2_mlkemEncaps1GhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := mlkemEncaps1TightStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (mlkemEncaps1GhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (mlkemEncaps1SafeBridge stk hlo hhi)

theorem c2_mlkemEncaps1Ghost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (mlkemEncaps1Ghost c2MlkemMpl) :=
  c2_mlkemEncaps1GhostAt_noAllocFailed mlkemHookStack

theorem c2_mlkemEncaps2GhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := mlkemEncaps2TightStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (mlkemEncaps2GhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (mlkemEncaps2SafeBridge stk hlo hhi)

theorem c2_mlkemEncaps2Ghost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (mlkemEncaps2Ghost c2MlkemMpl) :=
  c2_mlkemEncaps2GhostAt_noAllocFailed mlkemHookStack

theorem c2_mlkemDecapsGhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := mlkemDecapsTightStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (mlkemDecapsGhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (mlkemDecapsSafeBridge stk hlo hhi)

theorem c2_mlkemDecapsGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (mlkemDecapsGhost c2MlkemMpl) :=
  c2_mlkemDecapsGhostAt_noAllocFailed mlkemHookStack

theorem c2_mlkemValidatePkGhostAt_noAllocFailed [LibsignalPlacement]
    (stk : Nat := mlkemValidatePkTightStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookNoAllocFailed (mlkemValidatePkGhostAt c2MlkemMpl stk) :=
  mlkemBlockGhost_noAllocFailed (mlkemMpl := c2MlkemMpl) (mlkemValidatePkSafeBridge stk hlo hhi)

theorem c2_mlkemValidatePkGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (mlkemValidatePkGhost c2MlkemMpl) :=
  c2_mlkemValidatePkGhostAt_noAllocFailed mlkemHookStack

/-! ## 4. Unconditional `GhostRowSpecOk` (`*TightStack`, no `hArm` binders) -/

theorem c2_kemEncapsGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsKyber1024EncapsSym (kemEncapsGhostAt c2MlkemMpl kemEncapsTightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 24 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 24 _ _
  rowSpec := kemEncaps_extraRowSpec
    (kemEncapsGhostAt_rowSpec c2MlkemMpl kemEncapsTightStack (Nat.le_refl _) (by decide))

theorem c2_kemDecapsGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsKyber1024DecapsSym (kemDecapsGhostAt c2MlkemMpl kemDecapsTightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 23 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 23 _ _
  rowSpec := kemDecaps_extraRowSpec
    (kemDecapsGhostAt_rowSpec c2MlkemMpl kemDecapsTightStack (Nat.le_refl _) (by decide))

theorem c2_mlkemFromSeedGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkem768FromSeedSym
      (mlkemFromSeedGhostAt c2MlkemMpl mlkemFromSeedTightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 10 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 10 _ _
  rowSpec := mlkemFromSeed_extraRowSpec
    (mlkemFromSeedGhostAt_rowSpec c2MlkemMpl mlkemFromSeedTightStack (Nat.le_refl _) (by decide))

theorem c2_mlkemEncaps1Ghost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkem768Encaps1Sym
      (mlkemEncaps1GhostAt c2MlkemMpl mlkemEncaps1TightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 19 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 19 _ _
  rowSpec := mlkemEncaps1_extraRowSpec
    (mlkemEncaps1GhostAt_rowSpec c2MlkemMpl mlkemEncaps1TightStack (Nat.le_refl _) (by decide))

theorem c2_mlkemEncaps2Ghost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkem768Encaps2Sym
      (mlkemEncaps2GhostAt c2MlkemMpl mlkemEncaps2TightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 20 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 20 _ _
  rowSpec := mlkemEncaps2_extraRowSpec
    (mlkemEncaps2GhostAt_rowSpec c2MlkemMpl mlkemEncaps2TightStack (Nat.le_refl _) (by decide))

theorem c2_mlkemDecapsGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkem768DecapsSym
      (mlkemDecapsGhostAt c2MlkemMpl mlkemDecapsTightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 22 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 22 _ _
  rowSpec := mlkemDecaps_extraRowSpec
    (mlkemDecapsGhostAt_rowSpec c2MlkemMpl mlkemDecapsTightStack (Nat.le_refl _) (by decide))

theorem c2_mlkemValidatePkGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkem768ValidatePkSym
      (mlkemValidatePkGhostAt c2MlkemMpl mlkemValidatePkTightStack) where
  fs_eq := mlkemBlockGhost_fs c2MlkemMpl 21 _ _
  fsT := mlkemBlockGhost_fsT c2MlkemMpl 21 _ _
  rowSpec := mlkemValidatePk_extraRowSpec
    (mlkemValidatePkGhostAt_rowSpec c2MlkemMpl mlkemValidatePkTightStack (Nat.le_refl _) (by decide))

/-! ## 5. Concrete `GhostRowOk` and `guardOf` Variants (`*TightStack` at `c2MlkemMpl`) -/

/-- Natural entry-guard `GhostRowOk` for Hook #1 (`lsKyber1024EncapsSym`, `B24`). -/
theorem c2_kemEncapsGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsKyber1024EncapsSym
      (mlkemStubStateEntryGuard lsmpl EG lsKyber1024EncapsSym KemEncapsStateTerminates)
      (kemEncapsGhostAt c2MlkemMpl kemEncapsTightStack) :=
  ⟨c2_kemEncapsGhost_rowSpecOk,
   kemEncapsGhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
     (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsKyber1024EncapsSym
     kemEncapsTightStack (Nat.le_refl _) (by decide)
     (c2_mlkem_invMem_of_inv hLs)
     (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
     (c2_mlkem_keep_lr hKeepEq hLs)
     (c2_mlkem_realNoExt hKeepEq hExt)
     (c2_mlkem_realStubNone hExt (c2_resolve_kyber1024Encaps_eq hLs))
     (fun _ => stubReachesTargetOn_of_eq (c2_resolve_kyber1024Encaps_eq hLs))⟩

/-- `guardOf`-parameterized `GhostRowOk` for Hook #1 (`lsKyber1024EncapsSym`, `B24`). -/
theorem c2_kemEncapsGhost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hGuard : ∀ s0 : State,
      guardOf lsKyber1024EncapsSym s0 →
        mlkemStubStateEntryGuard lsmpl EG lsKyber1024EncapsSym KemEncapsStateTerminates s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsKyber1024EncapsSym (guardOf lsKyber1024EncapsSym)
      (kemEncapsGhostAt c2MlkemMpl kemEncapsTightStack) :=
  let h := c2_kemEncapsGhost_rowOk_c2 mmpl PredFs EG hExt hLs hKeepEq
  ⟨h.1, ghostRowReplayOn_of_guard_imp h.2 hGuard⟩

/-- Natural entry-guard `GhostRowOk` for Hook #2 (`lsKyber1024DecapsSym`, `B23`). -/
theorem c2_kemDecapsGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsKyber1024DecapsSym
      (mlkemStubStateEntryGuard lsmpl EG lsKyber1024DecapsSym KemDecapsStateTerminates)
      (kemDecapsGhostAt c2MlkemMpl kemDecapsTightStack) :=
  ⟨c2_kemDecapsGhost_rowSpecOk,
   kemDecapsGhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
     (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsKyber1024DecapsSym
     kemDecapsTightStack (Nat.le_refl _) (by decide)
     (c2_mlkem_invMem_of_inv hLs)
     (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
     (c2_mlkem_keep_lr hKeepEq hLs)
     (c2_mlkem_realNoExt hKeepEq hExt)
     (c2_mlkem_realStubNone hExt (c2_resolve_kyber1024Decaps_eq hLs))
     (fun _ => stubReachesTargetOn_of_eq (c2_resolve_kyber1024Decaps_eq hLs))⟩

/-- `guardOf`-parameterized `GhostRowOk` for Hook #2 (`lsKyber1024DecapsSym`, `B23`). -/
theorem c2_kemDecapsGhost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hGuard : ∀ s0 : State,
      guardOf lsKyber1024DecapsSym s0 →
        mlkemStubStateEntryGuard lsmpl EG lsKyber1024DecapsSym KemDecapsStateTerminates s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsKyber1024DecapsSym (guardOf lsKyber1024DecapsSym)
      (kemDecapsGhostAt c2MlkemMpl kemDecapsTightStack) :=
  let h := c2_kemDecapsGhost_rowOk_c2 mmpl PredFs EG hExt hLs hKeepEq
  ⟨h.1, ghostRowReplayOn_of_guard_imp h.2 hGuard⟩

/-- Natural entry-guard `GhostRowOk` for Hook #3 (`lsMlkem768FromSeedSym`, `B10`). -/
theorem c2_mlkemFromSeedGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768FromSeedSym
      (mlkemStubStateEntryGuard lsmpl EG lsMlkem768FromSeedSym MlkemFromSeedStateTerminates)
      (mlkemFromSeedGhostAt c2MlkemMpl mlkemFromSeedTightStack) :=
  ⟨c2_mlkemFromSeedGhost_rowSpecOk,
   mlkemFromSeedGhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
     (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsMlkem768FromSeedSym
     mlkemFromSeedTightStack (Nat.le_refl _) (by decide)
     (c2_mlkem_invMem_of_inv hLs)
     (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
     (c2_mlkem_keep_lr hKeepEq hLs)
     (c2_mlkem_realNoExt hKeepEq hExt)
     (c2_mlkem_realStubNone hExt (c2_resolve_mlkem768FromSeed_eq hLs))
     (fun _ => stubReachesTargetOn_of_eq (c2_resolve_mlkem768FromSeed_eq hLs))⟩

/-- `guardOf`-parameterized `GhostRowOk` for Hook #3 (`lsMlkem768FromSeedSym`, `B10`). -/
theorem c2_mlkemFromSeedGhost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hGuard : ∀ s0 : State,
      guardOf lsMlkem768FromSeedSym s0 →
        mlkemStubStateEntryGuard lsmpl EG lsMlkem768FromSeedSym MlkemFromSeedStateTerminates s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768FromSeedSym (guardOf lsMlkem768FromSeedSym)
      (mlkemFromSeedGhostAt c2MlkemMpl mlkemFromSeedTightStack) :=
  let h := c2_mlkemFromSeedGhost_rowOk_c2 mmpl PredFs EG hExt hLs hKeepEq
  ⟨h.1, ghostRowReplayOn_of_guard_imp h.2 hGuard⟩

/-- Natural entry-guard `GhostRowOk` for Hook #4 (`lsMlkem768Encaps1Sym`, `B19`). -/
theorem c2_mlkemEncaps1Ghost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768Encaps1Sym
      (mlkemStubStateEntryGuard lsmpl EG lsMlkem768Encaps1Sym MlkemEncaps1StateTerminates)
      (mlkemEncaps1GhostAt c2MlkemMpl mlkemEncaps1TightStack) :=
  ⟨c2_mlkemEncaps1Ghost_rowSpecOk,
   mlkemEncaps1GhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
     (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsMlkem768Encaps1Sym
     mlkemEncaps1TightStack (Nat.le_refl _) (by decide)
     (c2_mlkem_invMem_of_inv hLs)
     (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
     (c2_mlkem_keep_lr hKeepEq hLs)
     (c2_mlkem_realNoExt hKeepEq hExt)
     (c2_mlkem_realStubNone hExt (c2_resolve_mlkem768Encaps1_eq hLs))
     (fun _ => stubReachesTargetOn_of_eq (c2_resolve_mlkem768Encaps1_eq hLs))⟩

/-- `guardOf`-parameterized `GhostRowOk` for Hook #4 (`lsMlkem768Encaps1Sym`, `B19`). -/
theorem c2_mlkemEncaps1Ghost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hGuard : ∀ s0 : State,
      guardOf lsMlkem768Encaps1Sym s0 →
        mlkemStubStateEntryGuard lsmpl EG lsMlkem768Encaps1Sym MlkemEncaps1StateTerminates s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768Encaps1Sym (guardOf lsMlkem768Encaps1Sym)
      (mlkemEncaps1GhostAt c2MlkemMpl mlkemEncaps1TightStack) :=
  let h := c2_mlkemEncaps1Ghost_rowOk_c2 mmpl PredFs EG hExt hLs hKeepEq
  ⟨h.1, ghostRowReplayOn_of_guard_imp h.2 hGuard⟩

/-- Unconditional (`guardOf` arbitrary, no guard premises) `GhostRowOk` for Hook #5
    (`lsMlkem768Encaps2Sym`, `B20`). -/
theorem c2_mlkemEncaps2Ghost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768Encaps2Sym (guardOf lsMlkem768Encaps2Sym)
      (mlkemEncaps2GhostAt c2MlkemMpl mlkemEncaps2TightStack) :=
  ⟨c2_mlkemEncaps2Ghost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (mlkemEncaps2GhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
       (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsMlkem768Encaps2Sym
       mlkemEncaps2TightStack (Nat.le_refl _) (by decide)
       (c2_mlkem_invMem_of_inv hLs)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2_mlkem_keep_lr hKeepEq hLs)
       (c2_mlkem_realNoExt hKeepEq hExt)
       (c2_mlkem_realStubNone hExt (c2_resolve_mlkem768Encaps2_eq hLs))
       (fun _ => stubReachesTargetOn_of_eq (c2_resolve_mlkem768Encaps2_eq hLs)))
     (fun _ _ => trivial)⟩

theorem c2_mlkemEncaps2Ghost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768Encaps2Sym (fun _ => True)
      (mlkemEncaps2GhostAt c2MlkemMpl mlkemEncaps2TightStack) :=
  c2_mlkemEncaps2Ghost_rowOk_guardOf_c2 mmpl PredFs EG (fun _ _ => True) hExt hLs hKeepEq

/-- Natural entry-guard `GhostRowOk` for Hook #6 (`lsMlkem768DecapsSym`, `B22`). -/
theorem c2_mlkemDecapsGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768DecapsSym
      (mlkemStubStateEntryGuard lsmpl EG lsMlkem768DecapsSym MlkemDecapsStateTerminates)
      (mlkemDecapsGhostAt c2MlkemMpl mlkemDecapsTightStack) :=
  ⟨c2_mlkemDecapsGhost_rowSpecOk,
   mlkemDecapsGhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
     (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsMlkem768DecapsSym
     mlkemDecapsTightStack (Nat.le_refl _) (by decide)
     (c2_mlkem_invMem_of_inv hLs)
     (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
     (c2_mlkem_keep_lr hKeepEq hLs)
     (c2_mlkem_realNoExt hKeepEq hExt)
     (c2_mlkem_realStubNone hExt (c2_resolve_mlkem768Decaps_eq hLs))
     (fun _ => stubReachesTargetOn_of_eq (c2_resolve_mlkem768Decaps_eq hLs))⟩

/-- `guardOf`-parameterized `GhostRowOk` for Hook #6 (`lsMlkem768DecapsSym`, `B22`). -/
theorem c2_mlkemDecapsGhost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hGuard : ∀ s0 : State,
      guardOf lsMlkem768DecapsSym s0 →
        mlkemStubStateEntryGuard lsmpl EG lsMlkem768DecapsSym MlkemDecapsStateTerminates s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768DecapsSym (guardOf lsMlkem768DecapsSym)
      (mlkemDecapsGhostAt c2MlkemMpl mlkemDecapsTightStack) :=
  let h := c2_mlkemDecapsGhost_rowOk_c2 mmpl PredFs EG hExt hLs hKeepEq
  ⟨h.1, ghostRowReplayOn_of_guard_imp h.2 hGuard⟩

/-- Unconditional (`guardOf` arbitrary, no guard premises) `GhostRowOk` for Hook #7
    (`lsMlkem768ValidatePkSym`, `B21`). -/
theorem c2_mlkemValidatePkGhost_rowOk_guardOf_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768ValidatePkSym (guardOf lsMlkem768ValidatePkSym)
      (mlkemValidatePkGhostAt c2MlkemMpl mlkemValidatePkTightStack) :=
  ⟨c2_mlkemValidatePkGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (mlkemValidatePkGhostAt_rowReplayOn lsmpl mmpl c2MlkemMpl
       (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsMlkem768ValidatePkSym
       mlkemValidatePkTightStack (Nat.le_refl _) (by decide)
       (c2_mlkem_invMem_of_inv hLs)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2_mlkem_keep_lr hKeepEq hLs)
       (c2_mlkem_realNoExt hKeepEq hExt)
       (c2_mlkem_realStubNone hExt (c2_resolve_mlkem768ValidatePk_eq hLs))
       (fun _ => stubReachesTargetOn_of_eq (c2_resolve_mlkem768ValidatePk_eq hLs)))
     (fun _ _ => trivial)⟩

theorem c2_mlkemValidatePkGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hKeepEq : mlkemKeep c2MlkemMpl = c2MlkemKeep c2MlkemMpl := by rfl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsMlkem768ValidatePkSym (fun _ => True)
      (mlkemValidatePkGhostAt c2MlkemMpl mlkemValidatePkTightStack) :=
  c2_mlkemValidatePkGhost_rowOk_guardOf_c2 mmpl PredFs EG (fun _ _ => True) hExt hLs hKeepEq

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRow
