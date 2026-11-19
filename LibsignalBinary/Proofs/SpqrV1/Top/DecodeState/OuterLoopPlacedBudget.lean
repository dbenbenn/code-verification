/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DefsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget -- proof-setup: allow-public-import

/-!
# Budget-Threaded Relocatable Top Theorems for `spqr::decode_state` (Block `325`)

Delegates `decodeState_entry_5349c_placed*` and `decodeState_placed_ok*` to the code-loaded
proofs in `OuterLoopClPlacedBudget` by lifting `DecodeStateCalleeContractsPlacedX` to
`DecodeStateCalleeContractsClPlacedX`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement ls_subroutine_ok_cl_of_block subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg decodeStateStackX)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX
   DecodeStatePlacedOk DecodeStatePlacedOkOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv
   decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
  (decodeState_cl_placed_ok decodeState_cl_placed_ok_ofEnv
   decodeState_entry_5349c_cl_placed decodeState_entry_5349c_cl_placed_ofEnv)

private theorem toClPlaced [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext) :
    DecodeStateCalleeContractsClPlaced H_inner A lim ext where
  of_drop_inner := hc.of_drop_inner
  of_cap_inner := hc.of_cap_inner
  dealloc := hc.dealloc
  memcpy := hc.memcpy
  session_memcpy := hc.session_memcpy
  decodeErrorFrom := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorFrom
  decodeErrorPush := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorPush
  decodeVarint2 := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeVarint2
  skipField3 := subroutine_ok_withLsCodeLoaded_of_plain hc.skipField3
  chainParamsMerge := subroutine_ok_withLsCodeLoaded_of_plain hc.chainParamsMerge
  growOneChainEpoch := subroutine_ok_withLsCodeLoaded_of_plain hc.growOneChainEpoch
  dropOptProtoInnerState :=
    ls_subroutine_ok_cl_of_block (subroutine_ok_withLsCodeLoaded_of_plain hc.dropOptProtoInnerState)
  dropProtoPqRatchetState :=
    ls_subroutine_ok_cl_of_block (subroutine_ok_withLsCodeLoaded_of_plain hc.dropProtoPqRatchetState)

private theorem toClPlacedX [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    DecodeStateCalleeContractsClPlacedX H_inner A lim ext where
  toDecodeStateCalleeContractsClPlaced := toClPlaced hc.toDecodeStateCalleeContractsPlaced
  bytesMerge3 := hc.bytesMerge3
  epochDirectionMerge := hc.epochDirectionMerge
  v1StateMerge := hc.v1StateMerge

theorem decodeState_entry_5349c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (s0 : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st0 (DecodeStateEnv x))
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st0 s0 ∗
      stackAt s0.sp decodeStateStackX) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) :=
  decodeState_entry_5349c_cl_placed_ofEnv (toClPlacedX hc) x st0 s0 P R post hpost hpost_env
    hs0A hpc hrun hx8 hx0 hlen_bound hFit hP

theorem decodeState_entry_5349c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (s0 : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st0 (DecodeStateEnv x))
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st0 s0 ∗
      stackAt s0.sp decodeStateStackX) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_entry_5349c_cl_placed (toClPlacedX hc) x st0 s0 P R post hpost hs0A hpc hrun hx8 hx0
    hlen_bound hFit hP

theorem decodeState_placed_ok_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hpre_imp : ∀ x evs, DecodeStateEnv x evs → PreEnv x evs)
    (hpost_imp : ∀ x evs, DecodeStateEnv x evs → PostEnv x evs)
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim PreEnv PostEnv ext :=
  decodeState_cl_placed_ok_ofEnv hpre_imp hpost_imp (toClPlacedX hc)

theorem decodeState_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    DecodeStatePlacedOk H_inner A lim ext :=
  decodeState_cl_placed_ok (toClPlacedX hc)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudget
