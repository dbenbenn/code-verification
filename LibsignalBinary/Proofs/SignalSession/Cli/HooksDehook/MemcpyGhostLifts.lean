/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsDeserialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# File-Local Consumer `HookOk` Ghost Lifts for `memcpy` (`HooksDehook.MemcpyGhostLifts`)

`HookOk` consequence lifts from `masterMemcpySpec` / `memcpySpecK` to the file-local and
namespace-distinct `memcpy` consumer specifications:

1. `CryptoVerification.E2E.Bin.openMemcpySpec` (`OpenSegsDeserialize.lean:159`) and
   `CryptoVerification.E2E.Bin.openMemcpyRoSpec` (`OpenSegsPartyRoData.lean:125`).
2. `CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity.hashbrownMemcpyRegionSpec`
   (`FallibleWithCapacity.lean:122`).
3. `CryptoVerification.E2E.Pqxdh.Initiator.pqxdhMemcpyRegionSpec` (`HandshakeDerive.lean:915`) and
   its `withVmPreserved` (`pqxdhMemcpyRegionBudgetSpec`) counterpart.
4. `CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec`
   (`ChainClone3/ChainCloneEpilogue.lean:526`), its `ChainCloneEpilogueBudget` alias (`:504`), and
   `CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec`
   (`Record/Serialization/SessionCloneAux/ChainCloneEpilogue.lean:716`).
5. `LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec`
   (`RustStdAllocBudgetBridge.lean:811`, consumed by `Initiate/HooksPlacedBudget.lean:174`).
6. `CryptoVerification.LibsignalTripleRatchet.sessionMemcpyROXSpec`
   (`SessionRecordAt/TripleRatchet/HooksX.lean:47`) and its `withVmPreserved` counterpart.

Fixed-320 mixed-`↦₆₄` `pcs` contracts (`memcpyRecvPcsSpec[S]`, `memcpyPcs[Budget]Spec`) live in the
companion leaf module `HooksDehook.MemcpyGhostLiftsPcs`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords memcpySrc)
open CryptoVerification.E2E.Bin (openMemcpySpec openMemcpyRoSpec)
open CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity (hashbrownMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (pqxdhMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpyROXSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec memcpySpecK
  hookOk_map_frame_pureAbort hookOk_memcpySpecK_map_frame_pureAbort
  hookOk_framelessMemcpyBudgetFlat_of_master hookOk_framelessMemcpyBudgetFlatK_of_master
  memcpySpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK
  memcpyGhostHook_master_ok memcpyGhostHookK_masterK_ok
  memcpyGhostHook_vmPreserved memcpyGhostHookK_vmPreserved
  memcpyGhostHook_oracle memcpyGhostHookK_oracle
)

/-! ## 1. Generic `HookOk` Consequence Lifts from `masterMemcpySpec` & `memcpySpecK` -/

/-- Lift `HookOk f masterMemcpySpec` to `openMemcpySpec` (`ro = false`). -/
theorem hookOk_openMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f openMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, openMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `openMemcpyRoSpec` (`ro = true`). -/
theorem hookOk_openMemcpyRo_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f openMemcpyRoSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpyRoSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, openMemcpyRoSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `hashbrownMemcpyRegionSpec` (`ro = false`). -/
theorem hookOk_hashbrownMemcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f hashbrownMemcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [hashbrownMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, hashbrownMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `pqxdhMemcpyRegionSpec` (`ro = false`). -/
theorem hookOk_pqxdhMemcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f pqxdhMemcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [pqxdhMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, pqxdhMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `ChainClone3.sessionMemcpySpec` (`ro = false`). -/
theorem hookOk_chainClone3SessionMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Budget alias: `ChainCloneEpilogueBudget.sessionMemcpySpec` (`= framelessMemcpyBudgetSpec`). -/
theorem hookOk_chainClone3SessionMemcpyBudget_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec :=
  hookOk_framelessMemcpyBudgetFlat_of_master hh hvm

/-- Lift `HookOk f masterMemcpySpec` to `ChainCloneLocal1.sessionMemcpySpec` (`ro = false`). -/
theorem hookOk_recordSessionCloneMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` + `oracle` preservation to
    `RustStdAllocBudgetBridge.allocMemcpyVmSpec` (`ro = false`). -/
theorem hookOk_rustStdAllocMemcpyVm_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, hlt⟩ =>
      have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
        rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      Entails.pure_right ⟨hx0, hx1, hx2_nat⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HooksX.sessionMemcpyROXSpec` (`ro = true`). -/
theorem hookOk_sessionMemcpyROX_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f sessionMemcpyROXSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpyROXSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, sessionMemcpyROXSpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-! ## 2. Instantiations for `memcpyGhostHook` & `memcpyGhostHookK` -/

section GhostHookLifts

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memcpySymWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

end GhostHookLifts

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts
