/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserAssemblyW -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainKeyFieldGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainSenderRatchetKeyGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserCalleesX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenIdentityRootKeysExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenPendingPreKeyExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenPreviousCounterExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenReceiverChainsExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSenderChainExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSessionVersionExt
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# Root `SessionRecord::deserialize` Assembly

Instantiates `DeserLeavesPlacedW`, `ChainLeavesPlacedW`, and `MergeFieldLeavesPlacedW` from their
leaf proofs and combines `DeserAssemblyW` with `DeserTransportX` to establish
`recordDeserializeOpenSpec` under `[LibsignalPlacement]` (Block `46`).
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin

theorem L1_RecordDeserializeX : True := trivial

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

/-- Anchor declaration for incremental close checking of the `Placed` section. -/
theorem L1_RecordDeserializeX_Placed : True := trivial

/-- Instantiate `DeserLeavesPlacedW H` from a `memcpy` contract at `extHookStack` and
`DeserializeCalleesPlacedW H`. -/
theorem deserLeavesPlacedW_of_memcpy [LibsignalPlacement] (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hCallees : DeserializeCalleesPlacedW H) :
    DeserLeavesPlacedW H :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      DeserLoopEntryGExt.deserLoopEntryG_placed_okW H hCallees x R s0 hpc hrun hpre hal
    iter := fun hMF x R s0 k s hr hlt hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG.deserLoopIterG_placed_okW
        H hMF x R s0 k s hr hlt hs
    exit := fun x R s0 s hr hs =>
      deserLoopExitG_placed_ok_of_memcpy H (memcpy_placed_ok_of_extHookStack hmc) x R s0 s hr hs }

/-- Instantiate `DeserLeavesPlacedW H` from `Stage2ContractsA0Placed H` and
`DeserializeCalleesPlacedW H`. -/
theorem deserLeavesPlacedW_of_stage2 [LibsignalPlacement] (H : LibsignalHooks)
    (hStage2 : Stage2ContractsA0Placed H)
    (hCallees : DeserializeCalleesPlacedW H) :
    DeserLeavesPlacedW H :=
  deserLeavesPlacedW_of_memcpy H hStage2.memcpy hCallees

/-- Instantiate `ChainLeavesPlacedW H` from `DeserializeCalleesPlacedW H`. -/
theorem chainLeavesPlacedW_of_callees [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H) :
    ChainLeavesPlacedW H :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG.chainEntryG_placed_okW
        H hCallees x R s0 hpc hrun hpre hal
    srk := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG.chainSenderRatchetKeyG_placed_okW
        hCallees x R s0 k s hk htag hs
    ck := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG.chainKeyFieldG_placed_okW
        hCallees x R s0 k s hk htag hs
    keys := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG.chainMessageKeysG_placed_okW
        hCallees x R s0 k s hk htag hs
    exit := fun x R s0 s hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG.chainExitG_placed_okW
        H x R s0 s hs }

/-- Instantiate `MergeFieldLeavesPlacedW H` from `DeserializeCalleesPlacedW H` and an explicit
`tag9` hypothesis. -/
theorem mergeFieldLeavesPlacedW_of_tag9 [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H)
    (htag9 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 9)) :
    MergeFieldLeavesPlacedW H :=
  { tag1 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSessionVersion.mergeFieldGenSessionVersion_placed_okW
        H hCallees
    tag234 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys.mergeFieldGenIdentityRootKeys_placed_okW
        H hCallees
    tag5 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter.mergeFieldGenPreviousCounter_placed_okW
        H hCallees
    tag6 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain.mergeFieldGenSenderChain_placed_okW
        H hCallees hCh
    tag7 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains.mergeFieldGenReceiverChains_placed_okW
        H hCallees hCh
    tag9 := htag9 }

/-- Instantiate `MergeFieldLeavesPlacedW H` from `DeserializeCalleesPlacedW H`. -/
theorem mergeFieldLeavesPlacedW_of_callees [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H) :
    MergeFieldLeavesPlacedW H :=
  mergeFieldLeavesPlacedW_of_tag9 H hCallees
    (CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey.mergeFieldGenPendingPreKey_placed_okW
      H hCallees)

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from leaf bundles. -/
theorem deserializeExactPlacedX_ok_of_leaves [LibsignalPlacement] {H : LibsignalHooks}
    (hChain : ChainLeavesPlacedW H)
    (hMF : MergeFieldLeavesPlacedW H)
    (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedW_ok_of_leaves H hChain hMF hD

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from leaf bundles. -/
theorem recordDeserialize_placed_ok_of_leaves [LibsignalPlacement] {H : LibsignalHooks}
    (hChain : ChainLeavesPlacedW H)
    (hMF : MergeFieldLeavesPlacedW H)
    (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserializeOpen_placed_of_exactX lsmpl (deserializeExactPlacedX_ok_of_leaves hChain hMF hD)

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from minimal
allocator + `memcpy` contracts (`Stage1X.AllocContractsPlaced A0 H` + `memcpy`). -/
theorem deserializeExactPlacedX_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeExactPlacedX_ok_of_leaves
    (chainLeavesPlacedW_of_callees H hCallees)
    (mergeFieldLeavesPlacedW_of_callees H hCallees)
    (deserLeavesPlacedW_of_memcpy H hMemcpy hCallees)

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from minimal allocator + `memcpy`
contracts (`Stage1X.AllocContractsPlaced A0 H` + `memcpy`). -/
theorem recordDeserialize_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserializeOpen_placed_of_exactX lsmpl (deserializeExactPlacedX_ok_of_alloc hA hMemcpy)

/-- Relocatable general `SessionRecord::deserialize` contract (`deserializeGenPlacedSpec`) on
`lsProg_46 H` from minimal allocator + `memcpy` contracts. -/
theorem deserializeGen_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeBodyGPlacedW_ok H
    (deserLeavesPlacedW_of_memcpy H hMemcpy hCallees)
    (mergeFieldGenPlacedW_ok H (mergeFieldLeavesPlacedW_of_callees H hCallees)
      (chainMergeGenPlacedW_ok H (chainLeavesPlacedW_of_callees H hCallees)))
    deserReprG_ok

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from
`Stage2ContractsA0Placed H`. -/
theorem deserializeExactPlacedX_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedX_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem recordDeserialize_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserialize_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable general `SessionRecord::deserialize` contract (`deserializeGenPlacedSpec`) on
`lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem deserializeGen_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec :=
  deserializeGen_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

end Placed

end Proofs.libsignal.Hooks2
