/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded `PreKeySignalMessage::new` Composition

Relocatable `[LibsignalPlacement]` proofs that `<libsignal_protocol::protocol::PreKeySignalMessage>::new`
(block `41`) satisfies `preKeyMsgNewSpec M A lim` under `RustCliAllocBudget M`, instantiated for both
frameless and session-scoped shim/`memcpy` hook contracts.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_10 blkPl_10 blkPl_205 extract_withLsCodeLoaded
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl lsρ withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalPublicApi.Placed (blkPl_41 lsProg_41)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (preKeyMsgNewSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenBudget (
  encodedLen_placed_ok'
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsBudget (
  fields_placed_ok fields_placed_ok_of_ok fields_placed_ok_sessionHooks
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget (
  encodeVarintNoGrowPlacedSpec
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueBudget (
  prologue_placed_ok prologue_placed_ok_of_ok prologue_placed_ok_sessionHooks
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget (
  PreKeyMsgEncodedLenPlacedOk preKeyMsgSegExit_placed_chain
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

/-- Relocatable `PreKeySignalMessage::new` (block `41`) satisfies
`withLsCodeLoaded lsmpl (preKeyMsgNewSpec M A lim)` under `noAllocShimBudgetSpec` and
`framelessMemcpyBudgetSpec` hooks. -/
theorem preKeyMsgNew_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok (lsProg_41 H) (blkPl_41).base
      (withLsCodeLoaded lsmpl (preKeyMsgNewSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hs hpre hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  exact (preKeyMsgSegExit_placed_chain
    (prologue_placed_ok hshim halloc hmemcpy encodedLen_placed_ok' x st R s0 hcl hs hpc hsp hpre)
    (fun s' ⟨g, hA⟩ =>
      fields_placed_ok hshim halloc hdealloc hrealloc hmemcpy x st g R s0 s' hA)).mono_outcome
      fun _ hout => hout

theorem preKeySignalMessageNew_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok (lsProg_41 H) (blkPl_41).base
      (withLsCodeLoaded lsmpl (preKeyMsgNewSpec M A lim)) :=
  preKeyMsgNew_placed_ok hshim halloc hdealloc hrealloc hmemcpy

/-- Relocatable `PreKeySignalMessage::new` (block `41`) satisfies
`withLsCodeLoaded lsmpl (preKeyMsgNewSpec M A lim)` under `sessionShimBudgetSpec` and
`sessionMemcpyRegionBudgetSpec` hooks. -/
theorem preKeyMsgNew_placed_ok_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_41 H) (blkPl_41).base
      (withLsCodeLoaded lsmpl (preKeyMsgNewSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hs hpre hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  exact (preKeyMsgSegExit_placed_chain
    (prologue_placed_ok_sessionHooks hshim halloc hmemcpy encodedLen_placed_ok' x st R s0
      hcl hs hpc hsp hpre)
    (fun s' ⟨g, hA⟩ =>
      fields_placed_ok_sessionHooks hshim halloc hdealloc hrealloc hmemcpy x st g R s0 s' hA)).mono_outcome
      fun _ hout => hout

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget
