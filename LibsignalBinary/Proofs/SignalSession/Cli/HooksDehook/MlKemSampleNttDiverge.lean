/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768FromSeed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Encaps1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Decaps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Kyber1024Encaps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Kyber1024Decaps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs

/-!
# Operational Divergence of Stuck `libcrux_ml_kem` `SampleNTT` Calls (`MlKemSampleNttDiverge`)

Untrusted (`Role::Proof`, `CliElfLib`) barrel and unified 5-row dispatcher proving that a real
0-hook execution entering any of the 5 matrix-generating `libcrux_ml_kem` entry points with a
non-terminating `SampleNTT` seed never leaves `.Running` (never returns, never reaches
`.OutOfMemory`, never panics, exits, or halts):

1. **Per-entry Layer 1 operational divergence** (for both
   `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `Placed.cliProgPlacedSig mpl mmpl W`):
   - `B24` `lsKyber1024EncapsSym`: `kemEncaps_diverge_of_not_stateTerminates[_step]` and
     `kemEncapsAtSpec_diverge_of_not_stateTerminates[_step]` (`MlKemSampleNttDiverge.Kyber1024Encaps`).
   - `B23` `lsKyber1024DecapsSym`: `kemDecaps_diverge_of_not_stateTerminates[_step]`
     (`MlKemSampleNttDiverge.Kyber1024Decaps`).
   - `B10` `lsMlkem768FromSeedSym`: `mlkemFromSeed_diverge_of_not_stateTerminates[_step]`
     (`MlKemSampleNttDiverge.Mlkem768FromSeed`).
   - `B19` `lsMlkem768Encaps1Sym`: `mlkemEncaps1_diverge_of_not_stateTerminates[_step]`
     (`MlKemSampleNttDiverge.Mlkem768Encaps1`).
   - `B22` `lsMlkem768DecapsSym`: `mlkemDecaps_diverge_of_not_stateTerminates[_step]`
     (`MlKemSampleNttDiverge.Mlkem768Decaps`).
2. **Unified 5-row `MlKemSampleNttStuckAtU` dispatchers**:
   `mlkemSampleNttStuckAtU_diverge_of_activeRealPre[_step]` and
   `mlkemSampleNttStuckAtU_diverge_of_activeRealPre_withLsRet[_step]`.
3. **Run-level corollaries** (`MlKemSampleNttDiverge.Common`):
   `cliRunPlacedSig_eq_none_of_reaches_diverge`, `not_cliReachesOOMPlaced_of_reaches_diverge`,
   `cliRunPlacedSig_none_and_not_oom_of_reaches_diverge`, `all_running_of_reaches_diverge`, and
   `no_oom_after_diverge`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PqxdhPrims)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec kemEncapsPreservedAtSpec mlkemDecapsAtSpec mlkemEncaps1AtSpec mlkemFromSeedAtSpec
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  lsKyber1024DecapsSym lsKyber1024EncapsSym lsMlkem768DecapsSym lsMlkem768Encaps1Sym
  lsMlkem768FromSeedSym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  MlKemSampleNttStuckAtU
  lsKyber1024DecapsSym_resolve_eq_rho lsKyber1024EncapsSym_resolve_eq_rho
  lsMlkem768DecapsSym_resolve_eq_rho lsMlkem768Encaps1Sym_resolve_eq_rho
  lsMlkem768FromSeedSym_resolve_eq_rho
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (extract_withLsRet withLsRet)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

export Common (
  all_running_of_reaches_diverge
  no_oom_after_diverge
  cliRunPlacedSig_eq_none_of_reaches_diverge
  not_cliReachesOOMPlaced_of_reaches_diverge
  cliRunPlacedSig_none_and_not_oom_of_reaches_diverge
)

export Kyber1024Encaps (
  kemEncaps_diverge_of_not_stateTerminates_step
  kemEncaps_diverge_of_not_stateTerminates
  kemEncapsAtSpec_diverge_of_not_stateTerminates_step
  kemEncapsAtSpec_diverge_of_not_stateTerminates
)

export Kyber1024Decaps (
  kemDecaps_diverge_of_not_stateTerminates_step
  kemDecaps_diverge_of_not_stateTerminates
)

export Mlkem768FromSeed (
  mlkemFromSeed_diverge_of_not_stateTerminates_step
  mlkemFromSeed_diverge_of_not_stateTerminates
)

export Mlkem768Encaps1 (
  mlkemEncaps1_diverge_of_not_stateTerminates_step
  mlkemEncaps1_diverge_of_not_stateTerminates
)

export Mlkem768Decaps (
  mlkemDecaps_diverge_of_not_stateTerminates_step
  mlkemDecaps_diverge_of_not_stateTerminates
)

/-! ## Unified 5-Row `MlKemSampleNttStuckAtU` Operational Divergence Dispatchers -/

/-- Strip the pure `withLsRet` caller return-address conjunct from `ActiveRealPre`. -/
theorem activeRealPre_of_withLsRet [LibsignalPlacement] {α : Type} {spec : Spec α} {u : State}
    (h : ActiveRealPre (withLsRet spec) u) :
    ActiveRealPre spec u := by
  obtain ⟨hrun, hsp, x, R, hpre⟩ := h
  exact ⟨hrun, hsp, x, R, (extract_withLsRet hpre).2⟩

/-- Step-witnessed unified 5-row operational divergence from `MlKemSampleNttStuckAtU mpl u` and
    per-row `ActiveRealPre (keepsFs (<rowAtSpec> stk …)) u`. -/
theorem mlkemSampleNttStuckAtU_diverge_of_activeRealPre_step
    {stk : Nat} (hstk : 35968 ≤ stk := by decide) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {K : MlKem}
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {u : State}
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hStuck : MlKemSampleNttStuckAtU mpl u)
    (hActEnc : u.pc = mpl.ρ lsKyber1024EncapsSym →
      ActiveRealPre (keepsFs (kemEncapsPreservedAtSpec stk Q)) u)
    (hActDec : u.pc = mpl.ρ lsKyber1024DecapsSym →
      ActiveRealPre (keepsFs (kemDecapsAtSpec stk Q)) u)
    (hActSeed : u.pc = mpl.ρ lsMlkem768FromSeedSym →
      ActiveRealPre (keepsFs (mlkemFromSeedAtSpec stk K)) u)
    (hActEnc1 : u.pc = mpl.ρ lsMlkem768Encaps1Sym →
      ActiveRealPre (keepsFs (mlkemEncaps1AtSpec stk K)) u)
    (hActDec768 : u.pc = mpl.ρ lsMlkem768DecapsSym →
      ActiveRealPre (keepsFs (mlkemDecapsAtSpec stk K)) u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  rcases hStuck with
    ⟨hpc, hNot⟩ | ⟨hpc, hNot⟩ | ⟨hpc, hNot⟩ | ⟨hpc, hNot⟩ | ⟨hpc, hNot⟩
  · obtain ⟨hrun, hsp, x, R, hpre⟩ := hActEnc hpc
    have hpc' : u.pc = libsignalSessionLib.resolve mpl lsKyber1024EncapsSym :=
      hpc.trans (lsKyber1024EncapsSym_resolve_eq_rho mpl).symm
    exact kemEncaps_diverge_of_not_stateTerminates_step (Q := Q)
      (Nat.le_trans (by decide) hstk) hfit hLs hExt W hpc' hrun hsp hInv hFr hpre hNot
  · obtain ⟨hrun, hsp, x, R, hpre⟩ := hActDec hpc
    have hpc' : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym :=
      hpc.trans (lsKyber1024DecapsSym_resolve_eq_rho mpl).symm
    exact kemDecaps_diverge_of_not_stateTerminates_step (Q := Q)
      hstk hfit hLs hExt W hpc' hrun hsp hInv hFr hpre hNot
  · obtain ⟨hrun, hsp, x, R, hpre⟩ := hActSeed hpc
    have hpc' : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym :=
      hpc.trans (lsMlkem768FromSeedSym_resolve_eq_rho mpl).symm
    exact mlkemFromSeed_diverge_of_not_stateTerminates_step (K := K)
      (Nat.le_trans (by decide) hstk) hfit hLs hExt W hpc' hrun hsp hInv hFr hpre hNot
  · obtain ⟨hrun, hsp, x, R, hpre⟩ := hActEnc1 hpc
    have hpc' : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym :=
      hpc.trans (lsMlkem768Encaps1Sym_resolve_eq_rho mpl).symm
    exact mlkemEncaps1_diverge_of_not_stateTerminates_step (K := K)
      (Nat.le_trans (by decide) hstk) hfit hLs hExt W hpc' hrun hsp hInv hFr hpre hNot
  · obtain ⟨hrun, hsp, x, R, hpre⟩ := hActDec768 hpc
    have hpc' : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym :=
      hpc.trans (lsMlkem768DecapsSym_resolve_eq_rho mpl).symm
    exact mlkemDecaps_diverge_of_not_stateTerminates_step (K := K)
      (Nat.le_trans (by decide) hstk) hfit hLs hExt W hpc' hrun hsp hInv hFr hpre hNot

/-- Unified 5-row operational divergence from `MlKemSampleNttStuckAtU mpl u` and per-row
    `ActiveRealPre (keepsFs (<rowAtSpec> stk …)) u`. -/
theorem mlkemSampleNttStuckAtU_diverge_of_activeRealPre
    {stk : Nat} (hstk : 35968 ≤ stk := by decide) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {K : MlKem}
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {u : State}
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hStuck : MlKemSampleNttStuckAtU mpl u)
    (hActEnc : u.pc = mpl.ρ lsKyber1024EncapsSym →
      ActiveRealPre (keepsFs (kemEncapsPreservedAtSpec stk Q)) u)
    (hActDec : u.pc = mpl.ρ lsKyber1024DecapsSym →
      ActiveRealPre (keepsFs (kemDecapsAtSpec stk Q)) u)
    (hActSeed : u.pc = mpl.ρ lsMlkem768FromSeedSym →
      ActiveRealPre (keepsFs (mlkemFromSeedAtSpec stk K)) u)
    (hActEnc1 : u.pc = mpl.ρ lsMlkem768Encaps1Sym →
      ActiveRealPre (keepsFs (mlkemEncaps1AtSpec stk K)) u)
    (hActDec768 : u.pc = mpl.ρ lsMlkem768DecapsSym →
      ActiveRealPre (keepsFs (mlkemDecapsAtSpec stk K)) u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) := by
  have ⟨h1, h2⟩ := mlkemSampleNttStuckAtU_diverge_of_activeRealPre_step (Q := Q) (K := K)
    hstk hfit hLs hExt W hInv hFr hStuck hActEnc hActDec hActSeed hActEnc1 hActDec768
  exact ⟨fun v hv => (h1 v hv).1, fun v hv => (h2 v hv).1⟩

/-- Step-witnessed unified 5-row operational divergence from `MlKemSampleNttStuckAtU mpl u` and
    per-row `ActiveRealPre (withLsRet (keepsFs …)) u`. -/
theorem mlkemSampleNttStuckAtU_diverge_of_activeRealPre_withLsRet_step [LibsignalPlacement]
    {stk : Nat} (hstk : 35968 ≤ stk := by decide) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {K : MlKem}
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {u : State}
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hStuck : MlKemSampleNttStuckAtU mpl u)
    (hActEnc : u.pc = mpl.ρ lsKyber1024EncapsSym →
      ActiveRealPre (withLsRet (keepsFs (kemEncapsPreservedAtSpec stk Q))) u)
    (hActDec : u.pc = mpl.ρ lsKyber1024DecapsSym →
      ActiveRealPre (withLsRet (keepsFs (kemDecapsAtSpec stk Q))) u)
    (hActSeed : u.pc = mpl.ρ lsMlkem768FromSeedSym →
      ActiveRealPre (withLsRet (keepsFs (mlkemFromSeedAtSpec stk K))) u)
    (hActEnc1 : u.pc = mpl.ρ lsMlkem768Encaps1Sym →
      ActiveRealPre (withLsRet (keepsFs (mlkemEncaps1AtSpec stk K))) u)
    (hActDec768 : u.pc = mpl.ρ lsMlkem768DecapsSym →
      ActiveRealPre (withLsRet (keepsFs (mlkemDecapsAtSpec stk K))) u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) :=
  mlkemSampleNttStuckAtU_diverge_of_activeRealPre_step (Q := Q) (K := K)
    hstk hfit hLs hExt W hInv hFr hStuck
    (fun hpc => activeRealPre_of_withLsRet (hActEnc hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActDec hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActSeed hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActEnc1 hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActDec768 hpc))

/-- Unified 5-row operational divergence from `MlKemSampleNttStuckAtU mpl u` and per-row
    `ActiveRealPre (withLsRet (keepsFs ...)) u` (e.g. at `stk := mlkemHookStack`,
    `Q := kyber1024Prims₀`, `K := mlkem768Incremental`, fed by
    `MlKemFirstStopTransfer.mlkemBlockGhost_activeRealPre_of_noException`).
    Note: `MlKemSampleNttStuckAtU mpl u` (`C2RowLayoutFacts.MlKemSampleNttHelpers`) is
    `rfl`-identical to `CliBinaryPq.MlKemSampleNttStuckAt mpl u` (`readVecN` = `⟨readBytes, _⟩`). -/
theorem mlkemSampleNttStuckAtU_diverge_of_activeRealPre_withLsRet [LibsignalPlacement]
    {stk : Nat} (hstk : 35968 ≤ stk := by decide) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {K : MlKem}
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {u : State}
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hStuck : MlKemSampleNttStuckAtU mpl u)
    (hActEnc : u.pc = mpl.ρ lsKyber1024EncapsSym →
      ActiveRealPre (withLsRet (keepsFs (kemEncapsPreservedAtSpec stk Q))) u)
    (hActDec : u.pc = mpl.ρ lsKyber1024DecapsSym →
      ActiveRealPre (withLsRet (keepsFs (kemDecapsAtSpec stk Q))) u)
    (hActSeed : u.pc = mpl.ρ lsMlkem768FromSeedSym →
      ActiveRealPre (withLsRet (keepsFs (mlkemFromSeedAtSpec stk K))) u)
    (hActEnc1 : u.pc = mpl.ρ lsMlkem768Encaps1Sym →
      ActiveRealPre (withLsRet (keepsFs (mlkemEncaps1AtSpec stk K))) u)
    (hActDec768 : u.pc = mpl.ρ lsMlkem768DecapsSym →
      ActiveRealPre (withLsRet (keepsFs (mlkemDecapsAtSpec stk K))) u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) :=
  mlkemSampleNttStuckAtU_diverge_of_activeRealPre (Q := Q) (K := K)
    hstk hfit hLs hExt W hInv hFr hStuck
    (fun hpc => activeRealPre_of_withLsRet (hActEnc hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActDec hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActSeed hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActEnc1 hpc))
    (fun hpc => activeRealPre_of_withLsRet (hActDec768 hpc))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge
