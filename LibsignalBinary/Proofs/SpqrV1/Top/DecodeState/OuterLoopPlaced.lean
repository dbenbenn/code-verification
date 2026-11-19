/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlaced

/-!
# Relocatable Verification of `spqr::decode_state` (Block `325`) — Top Theorems

Delegates `decodeState_entry_5349c_placed` and `decodeState_placed_ok` to the code-loaded
proofs in `OuterLoopClPlaced` by lifting `DecodeStateCalleeContractsPlacedX` to
`DecodeStateCalleeContractsClPlacedX`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement ls_subroutine_ok_cl_of_block subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)

private theorem toClPlaced_unb [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext) :
    DecodeStateCalleeContractsClPlaced H_inner A ext where
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

private theorem toClPlacedX_unb [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext) :
    DecodeStateCalleeContractsClPlacedX H_inner A ext where
  toDecodeStateCalleeContractsClPlaced := toClPlaced_unb hc.toDecodeStateCalleeContractsPlaced
  bytesMerge3 := hc.bytesMerge3
  epochDirectionMerge := hc.epochDirectionMerge
  v1StateMerge := hc.v1StateMerge

/-- Full execution of `spqr::decode_state` from entry `+0`. -/
theorem decodeState_entry_5349c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt s0.sp decodeStateStackX) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) :=
  decodeState_entry_5349c_cl_placed (toClPlacedX_unb hc) x s0 P R post hpost hs0A hpc hrun hx8 hx0
    hlen_bound hP

/-- `spqr::decode_state` (Block `325`) satisfies `DecodeStatePlacedOkX H_inner A ext`
    given `DecodeStateCalleeContractsPlacedX H_inner A ext`. -/
theorem decodeState_placed_ok [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext) :
    DecodeStatePlacedOkX H_inner A ext :=
  decodeState_cl_placed_ok (toClPlacedX_unb hc)

end CryptoVerification.SpqrV1.Top.DecodeState
