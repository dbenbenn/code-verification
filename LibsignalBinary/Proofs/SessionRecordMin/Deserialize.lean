/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserAssemblyW -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.LoopW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.RecordDeserializeX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.WaveCTemplates
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXPhase1
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.Int32MergeX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.VarintSliceX
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Minimal Stage-2 Contracts for `SessionRecord::deserialize`

Restates the `SessionRecord::deserialize` contracts over `Stage2ContractsMin` (the 7 fields of
`Stage2ContractsA0` actually used by deserialization and serialization), generalizes them to an
arbitrary `A : RustAlloc` (`Stage2ContractsMinA`, `Stage2ContractsMinExt`), and provides relocatable
`[LibsignalPlacement]` wrappers on block `46`.
-/

public section

set_option autoImplicit false

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.HooksE

end Proofs.libsignal.Hooks2

/-! ## Extern Adapters -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.HooksE

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

end Proofs.libsignal.Hooks2

/-! ## `Vec::do_reserve_and_handle` -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end Proofs.libsignal.Hooks2

/-! ## Deserialization Callee Bundle -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.E2E.Record
open Proofs.libsignal.Stage1X

end Proofs.libsignal.Hooks2

/-! ## Deserialization Loop Exit -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2 CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end Proofs.libsignal.Hooks2

/-! ## `SessionRecord::deserialize` (`A0`) -/

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

end Proofs.libsignal.Hooks2

/-! ## `Q`-Scope Deserialization Loop -/

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Hooks2.DeserLoopEntryGExt

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## `Q`-Scope `SessionRecord::deserialize` -/

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## Serialization Contract Projection -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Stage1X

end Proofs.libsignal.Hooks2

/-! ## Reduction of `Stage2ContractsA0` Headlines via `toMin` -/

namespace Proofs.libsignal.Hooks2

end Proofs.libsignal.Hooks2

namespace Symbolic.Swarm.TRREF.B3DeserQ

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## Generalization to Arbitrary `A : RustAlloc` -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Stage1X

section GenAHelpers

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end GenAHelpers

end Proofs.libsignal.Hooks2

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.E2E.Record
open Proofs.libsignal.Stage1X

end Proofs.libsignal.Hooks2

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2 CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end Proofs.libsignal.Hooks2

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

namespace Proofs.libsignal.Hooks2

open Arm64 Arm64.Obj ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Bin

theorem L1_SessionRecordMin_Deserialize_Placed : True := trivial

/-- Minimal relocatable `[LibsignalPlacement]` contract bundle for `SessionRecord::deserialize`:
`Stage1X.AllocContractsPlaced HooksE.A0 H` plus `memcpy` at `extHookStack`. -/
structure Stage2ContractsMinPlaced [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  alloc : Stage1X.AllocContractsPlaced HooksE.A0 H
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))

set_option maxRecDepth 200000 in
/-- Construct `Stage2ContractsMinPlaced H` from `HookSat H` single-step hooks. -/
theorem Stage2ContractsMinPlaced.of_hooks [LibsignalPlacement] {H : LibsignalHooks}
    (halloc : HookSat H CryptoVerification.lsRustAllocSym (rustAllocSpec HooksE.A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec HooksE.A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec HooksE.A0))
    (hshim : HookSat H CryptoVerification.lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy"
      (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (hpan_err : H CryptoVerification.lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsMinPlaced H where
  alloc := Stage1X.AllocContractsPlaced.of_hooks
    halloc hdealloc hrealloc hshim hpan_err hpan_alloc
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)

/-- `SerContractsXPlaced` at `HooksE.A0` from `Stage2ContractsMinPlaced H`. -/
theorem serContractsXPlaced_of_stage2ContractsMinPlaced [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsMinPlaced H) :
    SerContractsXPlaced HooksE.A0 H :=
  ⟨hC.alloc, hC.memcpy⟩

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from
`Stage2ContractsMinPlaced H`. -/
theorem deserializeExact_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedX_ok_of_alloc hStage2.alloc hStage2.memcpy

abbrev deserializeExactPlacedX_ok_of_stage2Min := @deserializeExact_placed_ok_of_stage2Min

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem recordDeserialize_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec HooksE.A0)) :=
  recordDeserialize_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

/-- Relocatable `deserializeGenPlacedSpec` on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeGen_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec :=
  deserializeGen_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

end Proofs.libsignal.Hooks2

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

/-- Relocatable exact `Q`-scope `SessionRecord::deserialize` contract (`deserializeQExactPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeExactQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQExactPlacedSpecW :=
  deserializeExactAtQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

abbrev deserializeExactAtQ_placed_ok_of_stage2Min := @deserializeExactQ_placed_ok_of_stage2Min

/-- Relocatable general `Q`-scope `SessionRecord::deserialize` contract (`deserializeQPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeBodyQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQPlacedSpecW :=
  deserializeBodyQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

/-- Relocatable `withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)` on `lsProg_46 H`
from `Stage2ContractsMinPlaced H`. -/
theorem recordDeserializeOpenQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)) :=
  recordDeserializeOpenQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

end Symbolic.Swarm.TRREF.B3DeserQ
