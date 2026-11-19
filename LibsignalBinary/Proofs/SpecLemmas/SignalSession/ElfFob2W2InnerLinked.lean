/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# `decryptSignal` (`W2`, Block `463`) Linked and State-Guarded Inner Producers

**Checked by Lean.** Refutes the unconditional protobuf-to-tight allocation inclusion
`∀ pb evs, StatesFromPbEnv pb evs → StatesFromPbTightEnv evs` via a constructive counterexample
(`fob2_not_statesFromPbEnv_sub_tight`), discharges fine-budget extern and binary-store-kit
obligations on `cliGhostExterns`, and derives `InnerDecryptFrozenPlacedOk` producers for
`decryptSignal` (block `463`) at `TryDecryptCliLinkedEnv` and under per-state `StateGuard`
hypotheses on `spqr::recv`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (ExternsDistinctOnHooked LibsignalFullPlacement LibsignalPlacement
   libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (region_ok_restrictPre_true)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E
  (libcruxHmacHookMallocng pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre)
open CryptoVerification.LibsignalSpqrV1 (V1State sha256Compress spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced
   libsignalSessionLib lsAesDecSym lsReadFileSym)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (cliSessionKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (cliDecModelRecOkAt_opened
   scopeIn scopeKit scopeKit_pqrState_lt scopeKit_recordInScopeP
   trTrapExternsPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecBudgetSpecErrRo)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineCostModelSound fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFmtWriteEnv CliFormatInnerEnv cliFmtWriteEnv_nil cliFormatInnerEnv_nil)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (withStoresDecPlacedSpecVX)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
  (recordDecryptPlacedSpecTPTight withStoresDecPlacedSpecVTPF)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
  (cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
  (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliEnvOfPure TryDecryptCliLinkedEnv
   spqrRecvC07C09aBytesEnv_nonempty)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
  (spqr_recv_placed_disp_ok_blockProgram_ext_of_contracts_c07c09aTightLinked)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (spqrRecvPlacedInnerDispSpecXOfEnv spqrRecvPlacedInnerDispSpecXTOfEnv
   spqrRecvPlacedInnerSpecXOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (spqrRecvPlacedDispSpecXOfEnv spqrRecvPlacedDispSpecXTOfEnv spqrRecvPlacedRawDispSpecXOfEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv sessDeserEvents_mem_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdKitOkIE_placed_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessKitOkSE_seqFree_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget
  (w2IdKitBudgetEnv w2SessKitBudgetEnv w2_inner_full_placed_ok_ofEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv sessDeserialize_cli_dcan_byBytes_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonSeqFree_cli_placed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Counterexample to Unconditional `StatesFromPbEnv ⊆ StatesFromPbTightEnv` -/

def fob2_statesFromPbEnv_witnessPb : V1State :=
  { innerState := some (.keysUnsampled default) }

/-- Single-allocation trace (`3000` B aligned at `8` B) inside `StatesFromPbEnv`
(`maxReq ≤ 4 * encodeRaw.length + 4096`) and outside `StatesFromPbTightEnv` (`maxReq ≤ 2560`). -/
def fob2_statesFromPbEnv_witnessEvs : List AllocEvent :=
  [AllocEvent.aligned 8 3000]

theorem fob2_statesFromPbEnv_witness_mem :
    StatesFromPbEnv fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs := by
  unfold StatesFromPbEnv fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs
  refine ⟨by decide, fun ev hev => ?_⟩
  rcases List.mem_singleton.mp hev with rfl
  refine ⟨by decide, Nat.le_trans (by decide : 3000 ≤ 4096) (Nat.le_add_left 4096 _), ?_, ?_⟩
  · intro al _ h
    cases h
    decide
  · intro _ _ _ h
    cases h

theorem fob2_statesFromPbEnv_witness_not_tight :
    ¬ StatesFromPbTightEnv fob2_statesFromPbEnv_witnessEvs := by
  intro h
  have hreq := (h.2.2.2 (AllocEvent.aligned 8 3000) List.mem_cons_self).1
  exact absurd hreq (by decide)

/-- Constructive witness `(pb, evs)` satisfying `StatesFromPbEnv pb evs` and
`¬ StatesFromPbTightEnv evs`. -/
theorem fob2_statesFromPbEnv_counterexample :
    ∃ (pb : V1State) (evs : List AllocEvent),
      StatesFromPbEnv pb evs ∧ ¬ StatesFromPbTightEnv evs :=
  ⟨fob2_statesFromPbEnv_witnessPb, fob2_statesFromPbEnv_witnessEvs,
   fob2_statesFromPbEnv_witness_mem, fob2_statesFromPbEnv_witness_not_tight⟩

theorem fob2_not_statesFromPbEnv_sub_tight :
    ¬ (∀ (pb : V1State) (evs : List AllocEvent),
        StatesFromPbEnv pb evs → StatesFromPbTightEnv evs) := fun hAll =>
  fob2_statesFromPbEnv_witness_not_tight
    (hAll fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs
      fob2_statesFromPbEnv_witness_mem)

/-! ## Fine-Budget Extern Hook Dischargers -/

theorem fob2_libcruxHmac_hookSat [LibsignalPlacement] {mmpl : MultiPlacement}
    (gh : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F))
    (γ : GhostName) (tp : BitVec 64) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)) :=
  hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp cliElfImage.brkStart cliBudgetLimits gh W
    hPl_mng hHmac

/-! ## Binary Store-Kit (`decBinarySessKitPlacedBudgetFixed` / `decBinaryIdKitPlacedBudgetFixed`) Producers -/

theorem fob2_decBinarySessKitPlacedFixed_okSE [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (deserProg := lsProg_46 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 46)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    (sessDeserialize_cli_dcan_byBytes_placed_ok mmpl gh W hG (fun _ h => h))
    (serializeCanonSeqFree_cli_placed mmpl gh W hG)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem fob2_decBinaryIdKitPlacedFixed_okIE [LibsignalPlacement]
    {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    IdentityStoreKitPlacedOkI A lim
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed_sat
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (vtSym := cliIdentityVtRoSym)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    hh.blackBox
    (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)

/-! ## `InnerDecryptFrozenPlacedOk` Producers for `decryptSignal` -/


private theorem tryDecryptCliEnvOf_eq_linked (C : CryptoGames.LibsignalSession.Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) :
    TryDecryptCliEnvOf C (spqrV1 C.F K) CliFmtWriteEnv (SpqrRecvC07C09aBytesEnv C.F K) CliFormatInnerEnv =
      TryDecryptCliLinkedEnv C K :=
  rfl

private theorem fob2_spqrRecvPlacedInnerDispSpecXTOfEnv_of_placedDispSpecXT [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {R : CryptoVerification.LibsignalSpqrV1.SpqrRecvModel}
    {Env : VecArg → VecArg → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (spqrRecvPlacedDispSpecXTOfEnv A lim R Env)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim R Env)) := by
  refine subroutine_ok_mono hok
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.lsLogOff,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff] at hpre ⊢
      let H_sp : SepProp :=
        tokenInitPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
          (CryptoVerification.lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim stB s0 ∗
          stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.spqrRecvStack ∗ Fr
      have hpre' : s0.mem ⊨
          ⌜CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧
              CryptoVerification.LibsignalTripleRatchet.spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜LibsignalBinary.Heap.FitsEnv M lim stB (Env st msg)⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
            H_sp))) := by
        dsimp only [H_sp]
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcro, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hbds, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfit, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hx8⟩, hsp⟩ := hpre'
      have hcro' : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem :=
        ⟨hcro.1, hcro.2⟩
      have hgoal : s0.mem ⊨
          ⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧
            CryptoVerification.LibsignalTripleRatchet.spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret ∧
            LibsignalBinary.Heap.FitsEnv M lim stB (Env st msg)⌝ ∗ H_sp)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hbds, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcro', ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx8, hfit⟩, hsp⟩
      dsimp only [H_sp] at hgoal
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal)
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.lsLogOff,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff] at hpost ⊢
      refine Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_mono fun evs => ?_))) hpost
      apply Entails.pure_left
      rintro ⟨htr, hevs, hnp⟩
      exact Entails.pure_right hevs (Entails.pure_right ⟨htr, hnp⟩ (Entails.refl _)))
    (fun _ _ _ _ hpanic => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv] at hpanic ⊢
      exact hpanic)

private theorem spqrV1PlacedSeamsOfEnv_of_c07c09aLinked [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hBase : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv PrevRecvEnv SendEnv)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv W.C.F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv where
  spqrInitialState := hBase.spqrInitialState
  spqrRecv := fob2_spqrRecvPlacedInnerDispSpecXTOfEnv_of_placedDispSpecXT
    (spqr_recv_placed_disp_ok_blockProgram_ext_of_contracts_c07c09aTightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W) hRecvC)
  spqrSendCoins := hBase.spqrSendCoins

/-- Instantiates `w2_inner_full_placed_ok_ofEnv` at `TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_full_placed_ok_linked_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (w2SessKitBudgetEnv A.repAlloc B
        (ofBytesEnv RecordDeserializeCancelEnv) (ReadFileRuleEnvFixed cliIo.rd))
      (w2IdKitBudgetEnv A.repAlloc B (ReadFileRuleEnvFixed cliIo.rd)) := by
  rw [← tryDecryptCliEnvOf_eq_linked W.C W.Q.K]
  exact w2_inner_full_placed_ok_ofEnv mmpl gh W A lim hDropNz hG hF hX hPub hFs hh hReadHook
    (fun _ hr => sessDeserEvents_mem_recordDeserializeCancelEnv hr)
    hAesDec hSpqrLinked
    hh.fmtWrite
    hh.formatInner
    (spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K)
    ⟨[], cliFmtWriteEnv_nil⟩
    ⟨[], cliFormatInnerEnv_nil⟩

/-- Binary-store-kit counterpart of `w2_inner_frozen_placed_ok_of_region_ofEnv`. -/
theorem fob2_w2_inner_binaryKitFixed_frozen_placed_ok_of_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) := by
  intro F0 peer hPeer
  have hSess := fob2_decBinarySessKitPlacedFixed_okSE mmpl gh W A lim B F0 peer
    hDropNz hG hh hReadHook
  have hId := fob2_decBinaryIdKitPlacedFixed_okIE mmpl gh W A lim B F0 peer
    hDropNz hh hReadHook
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw :=
    cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl gh W
      (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
      (kit := decSessKitPlaced A.repAlloc F0 peer B)
      (kitEnv := decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (ikit := decIdKitPlaced A.repAlloc F0 peer B)
      (ikitEnv := decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (Scope := scopeKit) (Q := fun _ => True)
      hh hSess hId hq
      (fun _ hr => scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        cliDecModelRecOkAt_opened
          (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
      hrec
      (fun _ _ ses hsc hcur => ⟨scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
      (by rintro _ rfl; exact hPeer.nameLe40)
  refine Arm64.subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpost ⊢
    exact hpost

/-- Envelope-parametric `[LibsignalFullPlacement]` `InnerDecryptFrozenPlacedOk` producer at
`decBinarySessKitPlacedBudgetFixed` and `decBinaryIdKitPlacedBudgetFixed`. -/
theorem fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) CliFmtWriteEnv RecvBytesEnv CliFormatInnerEnv a evs →
      tdEnv a evs) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  fob2_w2_inner_binaryKitFixed_frozen_placed_ok_of_region mmpl gh W A lim
    hDropNz hG hFs hh hReadHook
    (region_ok_restrictPre_true
      (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
        mmpl gh W 0#64 hG hF hX hPub hAesDec hSpqr
        hh.fmtWrite
        hh.formatInner
        hRecv_ne ⟨[], cliFmtWriteEnv_nil⟩ ⟨[], cliFormatInnerEnv_nil⟩ htd))

/-- Specialization of `fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv` to
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_binaryKitFixed_placed_ok_linked_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv mmpl gh W hF hX hPub A lim
    hDropNz hG hFs hh hReadHook hAesDec hSpqrLinked
    (spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K)
    (fun _ _ h => h)

/-- Two-placement `InnerDecryptFrozenPlacedOk` producer on `cliElfBytes` at
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_linked_ok_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (_hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (γ : GhostName) (tp : BitVec 64)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrLinked : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact fob2_w2_inner_binaryKitFixed_placed_ok_linked_of_spqr mmpl ghFixed W hF hX hPub
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    h547 hGSpqr.toCliGhostAllocHooks hFs hHooks.runHooks hsat
    hAesDec hSpqrLinked

/-- State-guarded `InnerDecryptFrozenPlacedOk` producer: lifts `SpqrV1PlacedSeamsOfEnv` at
`StateGuard st.bytes → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes evs` into
`TryDecryptCliEnvOfPure`. -/
theorem fob2_w2_inner_stateGuarded_ok_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (_hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (γ : GhostName) (tp : BitVec 64)
    (StateGuard : List (BitVec 8) → Prop)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrGuarded : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg evs =>
        StateGuard st.bytes → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes evs)
      SendEnv) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) CliFmtWriteEnv
        (fun stBs msgBs evs => StateGuard stBs → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K stBs msgBs evs)
        CliFormatInnerEnv)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  refine fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv mmpl ghFixed W hF hX hPub
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    h547 hGSpqr.toCliGhostAllocHooks hFs hHooks.runHooks hsat
    hAesDec hSpqrGuarded
    (fun stBs msgBs =>
      let ⟨evs, hevs⟩ := spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K stBs msgBs
      ⟨evs, fun _ => hevs⟩)
    (fun _ _ h => h)

/-- Variant of `fob2_w2_inner_linked_ok_of_spqr` taking `SpqrRecvPlacedContractsOfEnv` at the tight
`C07 + C09a` leaves. -/
theorem fob2_w2_inner_linked_ok_of_recvContracts
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (γ : GhostName) (tp : BitVec 64)
    {H_inner : V1InnerHeapPred}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (h547 : mpl.base 547 ≠ 0#64)
    (hBase : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv PrevRecvEnv SendEnv)
    (hRecvC : @SpqrRecvPlacedContractsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel H_inner
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F W.Q.K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv W.C.F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact fob2_w2_inner_linked_ok_of_spqr hLs hblk hext_nodup ghFixed hPl_mng W hF hX hPub γ tp
    hGSpqr hFs hsat hHooks hAesDec h547 (spqrV1PlacedSeamsOfEnv_of_c07c09aLinked hBase hRecvC)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked
