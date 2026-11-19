/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlaced
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (Block `370`, `RustCliAllocBudget` Lifts)

Re-exports the Block `370` `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` from
`KeysSampledRecvCt1ChunkBudgetAux`, and provides envelope-monotonicity lifts,
`sessionShimBudgetSpec` hook variants, and `libsignalSessionLib.blockProgram` / cross-block
`IsLsBlockProg` seam bridges.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPl_370 extract_withLsCodeLoaded
   libsignalSessionLib lsProg_370 ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (SortedSetPt)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.States.Leaves
  (KeysSampledRecvCt1ChunkGhost ls_subroutine_ok_to_blockProgram)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (drop_glue_poly16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkPlacedOkExt AddChunkSlotsEnv addChunkSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkEnv KeysSampledRecvCt1ChunkPlacedOkX
   KeysSampledRecvCt1ChunkPlacedOkXOfEnv KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv
   KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv
   keysSampledRecvCt1ChunkSpec keysSampledRecvCt1ChunkSpecOfEnv
   keysSampledRecvCt1ChunkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
   keysSampledRecvCt1ChunkPostEnv_of_parts keysSampledRecvCt1ChunkPreEnv_of_parts)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (hookSat_sessionMemcpyBudget_of_region)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

/-! ## 1. Re-Exports from `Batch2DefsPlacedBudget` & `KeysSampledRecvCt1ChunkBudgetAux` -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkPostEnv
   KeysSampledRecvCt1ChunkEnv keysSampledRecvCt1ChunkPreEnv_nonempty
   keysSampledRecvCt1ChunkEnv_nonempty)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (keysSampledRecvCt1ChunkSpecOfPrePostEnv keysSampledRecvCt1ChunkSpecOfEnv
   keysSampledRecvCt1ChunkSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv KeysSampledRecvCt1ChunkPlacedOkXOfEnv
   KeysSampledRecvCt1ChunkPlacedOkX)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (emptyPolyDecoder_pts keysSampledRecvCt1ChunkPreEnv_of_parts
   keysSampledRecvCt1ChunkPostEnv_of_parts)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_ofEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_ok_x_ofEnv
   keys_sampled_recv_ct1_chunk_placed_ok_x)

/-! ## 2. Envelope-Monotonicity Lifts for Block `370` -/

/-! ## 3. `sessionShimBudgetSpec` Hook Variants for Block `370` -/

/-- Two-envelope `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    taking `sessionShimBudgetSpec` directly on `spqrRustNoAllocShimSym`. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
    hPre hPost hdealloc hmemcpy hadd
    (ls_subroutine_ok_of_block (i := 370) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext hshim halloc
          (hookSat_sessionMemcpyBudget_of_region hmemcpy))))
    (ls_subroutine_ok_of_block (i := 370) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

/-- Canonical `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    taking `sessionShimBudgetSpec` directly on `spqrRustNoAllocShimSym`. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv
    keysSampledRecvCt1ChunkPreEnv_of_parts
    keysSampledRecvCt1ChunkPostEnv_of_parts
    hshim halloc hdealloc hmemcpy hadd

/-! ## 4. `libsignalSessionLib.blockProgram` & Cross-Block Seam Bridges -/

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget
