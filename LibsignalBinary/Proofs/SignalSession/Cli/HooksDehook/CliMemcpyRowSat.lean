/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsDeserialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.ResponderWireCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Ghost-`memcpy` / `memset` `BaseHelperRowsSat` and `HookSat` Discharge Bundle (`CliMemcpyRowSat`)

Contract-level row-satisfaction adapters replacing hook-identity equalities
(`baseExt memcpyName = cliExternsPlaced mmpl W memcpyName`,
`baseExt memsetName = cliExternsPlaced mmpl W memsetName`) with `GhostMemcpyRow`,
`GhostMemsetRow`, and `BaseHelperRowsSat`, while leaving `memmove_eq` untouched:

1. `MemcpyStripKeepsFrozen` bridges (`memcpyStripKeepsFrozen_linkedCallHook`,
   `memcpyStripKeepsFrozen_memcpyGhostHook`, `memcpyStripKeepsFrozen_memcpyGhostHookK`) for
   `CodecCalleesFsTransferPlacedBudgetFd.codec_pure_fs_transfer_at_579_mc`.
2. `GhostMemcpyRow`, `GhostMemsetRow`, and `BaseHelperRowsSat`: row predicates, constructors from
   both `hookMemcpy` / `hookMemset` (`BaseHelperRows.toSat`) and `memcpyGhostHook` /
   `memsetGhostHook`, and `cliGhostExterns` preservation.
3. `HookSat` dischargers for shared CLI/Stage2/Codec `memcpy` and `memset` contracts and for the
   file-local `memcpy` contracts in `MemcpyGhostLifts` and `MemcpyGhostLiftsPcs`.
4. Bundle and pure-`fs` codec adapters (`allocContractsXCliPlaced_of_ghost_sat`,
   `allocContractsFsPlaced_of_ghost_sat`, `stage2ContractsMinPlaced_of_ghost_sat`,
   `codecHooksPlaced_of_ghost_sat`, `publicApiDecHooksPlaced_of_ghost_sat`, and the `_of_sat`
   Block `85` (`tryFrom`) / Block `111` (`pksmSlot`) transfer corollaries).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords memsetWordsSym)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPl_111 lsHandleErrorSym lsmpl
)
open CryptoVerification.E2E.Bin (openMemcpyRoSpec openMemcpySpec)
open CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity (hashbrownMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (pqxdhMemcpyRegionSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsExpectFailedSym)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack framelessMemcpySpec memcpyName memcpyROExtSpec memsetName
  sessionMemcpyROXSpec sessionMemcpyRegionSpec sessionMemcpySpec
  sessionMemsetRegionSpec sessionMemsetSpec withStack
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty (
  memcpyRecvPcsSpec memcpyRecvPcsSpecS
)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty (memcpyPcsSpec)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFromUtf8Sym lsMemrchrSym lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliExternsPlaced_memcpy_none cliExternsPlaced_memset_none
  hookMemcpy_fs hookMemset_fs hookNoop_fs hookOk_withStack
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks IsFsC cliGhostExterns cliGhostExterns_alloc
  cliGhostExterns_dealloc cliGhostExterns_memcpy_none cliGhostExterns_memcpy_some
  cliGhostExterns_memset_none cliGhostExterns_memset_some
  cliGhostExterns_realloc cliGhostExterns_shim hookMemcpy_fsT hookMemset_fsT
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.CliExt (memcpyROSpec memcpySpec memsetSpec)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits MallocngCostModelIface MallocngCostModelSound
  RustCliAllocBudget VmPreserved allocMemcpyVmSpec
)
open LibsignalBinary.Heap.Fine (
  fineCostModel hookMemcpy_vmPreserved hookMemset_vmPreserved
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun BaseHelperRows CliGhostAllocHooks cliGhostExterns_panics
  keepFsTrace linkedCallHook linkedCallHook_fs linkedCallHook_fsT
  noAllocShim_budget_sat_of_eq shim_budget_sat_of_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  hookMemcpy_masterMemcpy_ok hookOk_allocMemcpyVm_of_master hookOk_cliMemcpyRO_of_master
  hookOk_cliMemcpy_of_master hookOk_framelessMemcpy_of_master hookOk_libcMemcpy_of_master
  hookOk_memcpyROExt_of_master hookOk_memcpyRegion_of_master hookOk_sessionMemcpyRO4K_of_master
  hookOk_sessionMemcpyRegionRO_of_master hookOk_sessionMemcpyRegion_of_master
  hookOk_sessionMemcpy_of_master masterMemcpySpec memcpySpecK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK memcpyGhostHook_master_ok memcpyGhostHook_oracle
  memcpyGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts (
  hookOk_chainClone3SessionMemcpyBudget_of_master hookOk_chainClone3SessionMemcpy_of_master
  hookOk_hashbrownMemcpyRegion_of_master hookOk_openMemcpyRo_of_master hookOk_openMemcpy_of_master
  hookOk_pqxdhMemcpyRegion_of_master hookOk_recordSessionCloneMemcpy_of_master
  hookOk_rustStdAllocMemcpyVm_of_master hookOk_sessionMemcpyROX_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs (
  hookOk_memcpyPcsBudget_of_master hookOk_memcpyPcs_of_master
  hookOk_memcpyRecvPcsS_of_master hookOk_memcpyRecvPcs_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  hookMemset_masterMemset_ok hookOk_cliMemset_of_master hookOk_libcMemset_of_master
  hookOk_memsetRegion_of_master hookOk_session2MemsetExtern_of_master
  hookOk_sessionMemsetRegion_of_master hookOk_sessionMemset_of_master masterMemsetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  memsetGhostHook memsetGhostHook_master_ok memsetGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd (
  pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd (
  stripCodec_keepsFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd (
  MemcpyStripKeepsFrozen memcpyStripKeepsFrozen_hookMemcpy not_badKf_of_memcpy
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd (
  pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_mc
  tryFrom_okFs_mallocng_cli_placed_at_579_mc
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget (
  subsetA4PksmTryFromPlaced_of_codecHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  SubsetA4PksmTryFromPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  allocContractsFsPlaced_of_hookSat allocContractsXCliPlaced_of_hookSat
  codecHooksPlaced_of_hookSat publicApiDecHooksPlaced_of_hookSat stage2ContractsMinPlaced_of_hookSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced AllocContractsXCliPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec
  sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget (memcpyPcsBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

/-! ## 1. `MemcpyStripKeepsFrozen` Ghost Bridges (`linkedCallHook`, `memcpyGhostHook`, `memcpyGhostHookK`) -/

/-- Any `linkedCallHook` with fallback `ProofLib.hookMemcpy` satisfies `MemcpyStripKeepsFrozen`:
on active real runs `ExecFrozen u.mem` transports `KeepsFrozen` across `stripCodecMem`, on
non-`ActiveRealRun` calls `keepFsTrace hookMemcpy` has the same memory as `hookMemcpy`, and outside
`ActiveRealPre` memory is unchanged. -/
theorem memcpyStripKeepsFrozen_linkedCallHook {α : Type}
    (keep_g : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) :
    MemcpyStripKeepsFrozen
      (linkedCallHook keep_g P_real P_sub entryTarget spec ProofLib.hookMemcpy) := by
  intro keep u hact hkf
  classical
  by_cases hPre : ActiveRealPre spec u
  · by_cases hReal : ActiveRealRun keep_g P_real P_sub entryTarget u
    · simp only [linkedCallHook, hPre, hReal, ↓reduceDIte] at hkf ⊢
      exact stripCodec_keepsFrozen keep
        (fun a p hp hx => by have hfr := hReal.1 a; rw [hp] at hfr; exact (hfr hx).2) hkf
    · simp only [linkedCallHook, hPre, hReal, ↓reduceDIte]
      have hmem : (keepFsTrace ProofLib.hookMemcpy u).mem = (ProofLib.hookMemcpy u).mem := rfl
      rw [hmem]
      exact not_badKf_of_memcpy keep hact
  · simp only [linkedCallHook, hPre, ↓reduceDIte]
    exact fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- `MemcpyStripKeepsFrozen` for plain `memcpyGhostHook`. -/
theorem memcpyStripKeepsFrozen_memcpyGhostHook
    (keep_g : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    MemcpyStripKeepsFrozen (memcpyGhostHook keep_g P_real P_sub entryTarget) :=
  memcpyStripKeepsFrozen_linkedCallHook keep_g P_real P_sub entryTarget masterMemcpySpec

/-! ## 2. `GhostMemcpyRow`, `GhostMemsetRow`, & `BaseHelperRowsSat` (`memmove_eq` Preserved) -/

/-- Contract-level `memcpy` row bundle on an extern map `ext`, bundling `masterMemcpySpec`,
`VmPreserved`, `State.fs` preservation, `HookFsTraced IsFsC`, `MemcpyStripKeepsFrozen`, and
`State.oracle` preservation. -/
@[expose] def GhostMemcpyRow (ext : LibsignalHooks) : Prop :=
  ∃ f : State → State,
    ext memcpyName = some f ∧
    HookOk f masterMemcpySpec ∧
    (∀ s, VmPreserved s (f s)) ∧
    (∀ s, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f ∧
    MemcpyStripKeepsFrozen f ∧
    (∀ s, (f s).oracle = s.oracle)

/-- Contract-level `memset` row bundle on an extern map `ext`, bundling `masterMemsetSpec`,
`VmPreserved`, `State.fs` preservation, and `HookFsTraced IsFsC`. -/
@[expose] def GhostMemsetRow (ext : LibsignalHooks) : Prop :=
  ∃ f : State → State,
    ext memsetName = some f ∧
    HookOk f masterMemsetSpec ∧
    (∀ s, VmPreserved s (f s)) ∧
    (∀ s, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f

/-- Ghost-compatible `BaseHelperRows` counterpart: replaces `memcpy_eq` and `memset_eq` with
`GhostMemcpyRow` and `GhostMemsetRow` while keeping `bcmp_eq`, `utf8_eq`,
`memrchr_eq`, and `panics` unchanged. -/
structure BaseHelperRowsSat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (baseExt : LibsignalHooks) : Prop where
  memcpy_sat : GhostMemcpyRow baseExt
  memset_sat : GhostMemsetRow baseExt
  bcmp_eq : baseExt "bcmp" = cliExternsPlaced mmpl W "bcmp"
  utf8_eq : baseExt lsFromUtf8Sym = cliExternsPlaced mmpl W lsFromUtf8Sym
  memrchr_eq : baseExt lsMemrchrSym = cliExternsPlaced mmpl W lsMemrchrSym
  panics : CliPanicHooksPlaced baseExt

/-- Combine `GhostMemcpyRow`, `GhostMemsetRow`, and a `BaseHelperRows` witness into
`BaseHelperRowsSat`. -/
theorem BaseHelperRows.toSat {mmpl : Obj.MultiPlacement} {W : CliHooks}
    {baseExt : LibsignalHooks}
    (hMc : GhostMemcpyRow baseExt) (hMs : GhostMemsetRow baseExt)
    (hBase : BaseHelperRows mmpl W baseExt) :
    BaseHelperRowsSat mmpl W baseExt where
  memcpy_sat := hMc
  memset_sat := hMs
  bcmp_eq := hBase.bcmp_eq
  utf8_eq := hBase.utf8_eq
  memrchr_eq := hBase.memrchr_eq
  panics := hBase.panics

theorem GhostMemcpyRow.of_eq {ext₁ ext₂ : LibsignalHooks}
    (heq : ext₂ memcpyName = ext₁ memcpyName) (h : GhostMemcpyRow ext₁) :
    GhostMemcpyRow ext₂ := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, hfst, hskf, horc⟩
  exact ⟨f, heq.trans hrow, hok, hvm, hfs, hfst, hskf, horc⟩

theorem GhostMemsetRow.of_eq {ext₁ ext₂ : LibsignalHooks}
    (heq : ext₂ memsetName = ext₁ memsetName) (h : GhostMemsetRow ext₁) :
    GhostMemsetRow ext₂ := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, hfst⟩
  exact ⟨f, heq.trans hrow, hok, hvm, hfs, hfst⟩

/-- `none`-slot pass-through only (`g.memcpy = none`); not usable on the K or Narrow routes. -/
theorem GhostMemcpyRow.cliGhostExterns {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hNone : g.memcpy = none) (h : GhostMemcpyRow baseExt) :
    GhostMemcpyRow (cliGhostExterns g baseExt) :=
  h.of_eq (cliGhostExterns_memcpy_none g baseExt hNone)

/-- `none`-slot pass-through only (`g.memset = none`); not usable on the K or Narrow routes. -/
theorem GhostMemsetRow.cliGhostExterns {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hNone : g.memset = none) (h : GhostMemsetRow baseExt) :
    GhostMemsetRow (cliGhostExterns g baseExt) :=
  h.of_eq (cliGhostExterns_memset_none g baseExt hNone)

/-! ## 3. Generic & Contract-Specific `HookSat` Dischargers (`GhostMemcpyRow` & `GhostMemsetRow`) -/

theorem GhostMemcpyRow.hookSat_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName spec := by
  rcases h with ⟨f, hrow, hok, _, _, _, _, _⟩
  exact ⟨f, hrow, hlift hok⟩

theorem GhostMemcpyRow.hookSat_keepsFs_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName spec.keepsFs := by
  rcases h with ⟨f, hrow, hok, _, hfs, _, _, _⟩
  exact ⟨f, hrow, (hlift hok).keepsFs hfs⟩

theorem GhostMemcpyRow.hookSat_budget_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName (withVmPreserved spec) := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, _⟩
  exact ⟨f, hrow, hookOk_withVmPreserved (hlift hok) hvm⟩

theorem GhostMemcpyRow.hookSat_budget_keepsFs_of_master {α : Type} {ext : LibsignalHooks}
    {spec : Spec α} (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName (withVmPreserved spec).keepsFs := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, _, _, _⟩
  exact ⟨f, hrow, (hookOk_withVmPreserved (hlift hok) hvm).keepsFs hfs⟩

theorem GhostMemsetRow.hookSat_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName spec := by
  rcases h with ⟨f, hrow, hok, _, _, _⟩
  exact ⟨f, hrow, hlift hok⟩

theorem GhostMemsetRow.hookSat_keepsFs_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName spec.keepsFs := by
  rcases h with ⟨f, hrow, hok, _, hfs, _⟩
  exact ⟨f, hrow, (hlift hok).keepsFs hfs⟩

theorem GhostMemsetRow.hookSat_budget_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName (withVmPreserved spec) := by
  rcases h with ⟨f, hrow, hok, hvm, _, _⟩
  exact ⟨f, hrow, hookOk_withVmPreserved (hlift hok) hvm⟩

theorem GhostMemsetRow.hookSat_budget_keepsFs_of_master {α : Type} {ext : LibsignalHooks}
    {spec : Spec α} (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName (withVmPreserved spec).keepsFs := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, _⟩
  exact ⟨f, hrow, (hookOk_withVmPreserved (hlift hok) hvm).keepsFs hfs⟩

-- 3.1 Shared CLI / Stage2 / Codec `memcpy` `HookSat` dischargers:

theorem GhostMemcpyRow.framelessMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName framelessMemcpyBudgetSpec :=
  h.hookSat_budget_of_master hookOk_framelessMemcpy_of_master

-- 3.2 File-local `memcpy` `HookSat` dischargers (`MemcpyGhostLifts` & `MemcpyGhostLiftsPcs`):

-- 3.3 Shared CLI `memset` `HookSat` dischargers:

/-! ## 4. Bundle & Pure-`fs` Codec Adapter Theorems over `BaseHelperRowsSat` -/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat
