/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserD0X
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserDExitX
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserDIterX
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.ProstSSGXRepr
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# PQXDH-Scope `SessionRecord::deserialize` Composition

Composes the entry (`DeserD0X`), field-loop iteration (`DeserDIterX`), loop exit (`DeserDExitX`),
and representation (`ProstSSGXRepr`) leaves to establish both `deserializeXExactSpec` (raw
`prostSSGXAt` postcondition) and `deserializeXSpec` (canonical `sessionRecordAt` postcondition) for
`SessionRecord::deserialize` (`0x16ed4`, block `46`) on records in `DeserializeScopeP`, along with
relocatable `[LibsignalPlacement]` corollaries.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.E2E.RecordX (DeserializeScopeP)

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_L1GX_Body_Placed : True := trivial

theorem deserializeXExact_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_alloc hA hMemcpy

theorem deserializeX_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_alloc hA hMemcpy

theorem deserializeXExact_placed_ok_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_stage2 hStage2

theorem deserializeX_placed_ok_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_stage2 hStage2

set_option maxRecDepth 200000 in
/-- Relocatable `SessionRecord::deserialize` (block `46`) satisfies `deserializeQExactPlacedSpecW` on
`lsProg_46 H` under allocator, `memcpy`, shim, and panic hook contracts. -/
theorem deserializeXExact_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy" (sessionMemcpySpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

set_option maxRecDepth 200000 in
/-- Relocatable `SessionRecord::deserialize` (block `46`) satisfies `deserializeQPlacedSpecW` on
`lsProg_46 H` under allocator, `memcpy`, shim, and panic hook contracts. -/
theorem deserializeX_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy" (sessionMemcpySpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

end Placed

end CryptoVerification.E2E.Record.L1GX
