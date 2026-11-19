/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat

/-!
# `HookSat` Sibling of `LeavesTopPlacedBudget` (`LeavesTopPlacedBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in Section 8 (`:997..1204`, the 10
Block `350` `<EkSentCt1Received>::recv_ct2_chunk` theorems) of
`LeavesTopPlacedBudget.lean` with `[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPl_338 lsProg_338 ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem mlkemDecapsSpec mlkemEncaps2Spec mlkemValidatePkSpec
)
open CryptoVerification.LibsignalTripleRatchet (
  keys_ls_subroutine_ok_of_block_cro memsetName
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedSpec)
open CryptoVerification.SpqrV1.Alloc (
  growOneStack spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym
  spqrPanicConstAddOverflowSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (OnceCallHookOk)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedCt1SentRecvEkGhost)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost spqrAssertFailedU64Sym spqrLibcruxHmacSym' spqrMlkemDecapsSym
  spqrPanicBoundsCheckSym spqrRustDeallocSym' spqrSliceIndexFailSym spqrUnwrapFailedSym
)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsStep FreeOnlyEvs
  RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  zeroBudgetLimits
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (mlkemDecapsAtSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  framelessMemcpyAcpSpec sessionMemcpyRegionROSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget (
  add_chunk_cl_placed_ok add_chunk_cl_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  Ct1AcknowledgedRecvEkChunkPlacedOkX EkReceivedCt1SampledRecvCt1AckPlacedOkX
  unchunkedCt1SentRecvEkSpec unchunkedCt1SentRecvEkSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget (
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget (
  polyDecodedMessagePlacedOkX_of_hooks polyDecoderDecodedMessage_cro_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget (
  hookSat_noAllocShim_of_rustAllocShimVm
  hookSat_sessionMemcpyRegionBudget_of_framelessAcp
  hookSat_sessionShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget (
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget (
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_withLsRet
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget (
  send_ct2_encoder_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget (
  unchunked_ct1_sent_recv_ek_placed_ok_x_withLsRet
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2ChunkEnv RecvCt2ChunkPlacedOkExt RecvCt2ChunkPlacedOkExtOfEnv
  RecvCt2ChunkPlacedOkExtOfPrePostEnv RecvCt2PlacedAlloc
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat (
  recv_ct2_chunk_placed_ok_ext_ofEnv_sat
  recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat
  recv_ct2_chunk_placed_ok_ext_of_hooks_sat
  recv_ct2_chunk_placed_ok_ext_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec 36864 K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat hsub_pre hsub_post hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset hOnce)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec 36864 K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_ext_ofEnv_sat hsub hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset hOnce)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec 36864 K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recv_ct2_chunk_placed_ok_ext_sat hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset hOnce)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_alloc_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec 36864 K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_sat hA
    (hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy) hmemmove hmemset hdecaps hhmac hOnce

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_hooks_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec 36864 K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked)
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recv_ct2_chunk_placed_ok_ext_of_hooks_sat
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset hOnce)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

/-! ## `withLsRet` Leaf Bridges for Blocks `338`, `343`, `349` -/

private abbrev zeroOverheadModel (M : AllocCostModel) : AllocCostModel where
  σ := M.σ
  init := M.init
  step := M.step
  footprint := fun _ => 0
  maxDynIvs := fun _ => 0
  stepReserve := fun ev _ => ev.reqBytes
  liveBytes := M.liveBytes
  footprint_mono := fun _ _ => Nat.le_refl 0
  maxDynIvs_mono := fun _ _ => Nat.le_refl 0
  stepReserve_mono := fun _ _ _ => Nat.le_refl _
  req_le_stepReserve := fun _ _ => Nat.le_refl _
  liveBytes_free_le := M.liveBytes_free_le

private abbrev freeOnlyLim : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := true }

private abbrev rebindBudgetAlloc (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : RustCliAllocBudget (zeroOverheadModel M) where
  pool := fun l st s => if l.enforced then A.pool lim st s else A.pool zeroBudgetLimits st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := fun l st s s' hvm => by
    cases l.enforced <;> exact A.pool_transport _ st s s' hvm
  pool_zero_transport := fun st s s' hpp => A.pool_zero_transport st s s' hpp

private theorem fitsStep_freeOnlyLim_zero : FitsStep freeOnlyLim 0 0 0 :=
  ⟨rfl, by decide, by decide⟩

private theorem fitsEvents_zeroOverhead_of_freeOnly (M : AllocCostModel) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      FreeOnlyEvs evs → FitsEvents (zeroOverheadModel M) freeOnlyLim st evs
  | [], _, _ => trivial
  | ev :: evs, st, hfree => by
    obtain ⟨al, sz, rfl⟩ := hfree ev List.mem_cons_self
    exact ⟨⟨trivial, fitsStep_freeOnlyLim_zero⟩,
      fitsEvents_zeroOverhead_of_freeOnly M evs (M.step (.free al sz) st)
        (fun e he => hfree e (List.mem_cons_of_mem _ he))⟩

private theorem fitsEnv_zeroOverhead_freeOnly (M : AllocCostModel) (st : M.σ) :
    FitsEnv (zeroOverheadModel M) freeOnlyLim st FreeOnlyEvs :=
  fun evs hfree => fitsEvents_zeroOverhead_of_freeOnly M evs st hfree

theorem unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_ofPrePostEnv_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPost : ∀ x evs, FreeOnlyEvs evs → PostEnv x evs)
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withLsRet (withVmPreserved (mlkemValidatePkSpec K)))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) := by
  have hok := unchunked_ct1_sent_recv_ek_placed_ok_x_withLsRet
    (M := zeroOverheadModel M) (A := rebindBudgetAlloc M A lim) (lim := freeOnlyLim)
    (F := F) (K := K) hdealloc hval_pk
  refine subroutine_ok_withLsCodeLoaded_of_plain
    (subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_))
  · dsimp only [unchunkedCt1SentRecvEkSpecOfPrePostEnv] at hp
    dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpec,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpecOfEnv,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedCt1SentRecvEkEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx1, hx2, hx3, hres, _hfit, hlr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hres, fitsEnv_zeroOverhead_freeOnly M st, hlr⟩, hmem⟩
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpec,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpecOfEnv,
      unchunkedCt1SentRecvEkSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hPost x evs hq.1.2⟩, hq.2⟩

theorem unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withLsRet (withVmPreserved (mlkemValidatePkSpec K)))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)) :=
  unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_ofPrePostEnv_sat (fun _ _ h => h) hdealloc hval_pk

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withLsRet (withVmPreserved (mlkemEncaps2Spec K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (withLsRet (libcruxHmacBudgetSpec F M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX M A lim F K ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext hdealloc
    (ls_subroutine_ok_of_block (i := 343) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_withLsRet
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 343) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

theorem ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withLsRet (withVmPreserved (mlkemValidatePkSpec K))))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withLsRet (withVmPreserved (mlkemEncaps2Spec K))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (withLsRet (libcruxHmacBudgetSpec F M A lim)))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX M A lim F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 349) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 349) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset hOnce))
    (ls_subroutine_ok_of_block (i := 349) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_sat (F := F) hdealloc hval_pk))
    (ls_subroutine_ok_of_block (i := 349) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_withLsRet
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 349) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat
