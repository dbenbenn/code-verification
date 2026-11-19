/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.SubsetA4cBudget
import LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochBudget
import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyBudget
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyBudget
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Placed `spqr::send::<Coins>` & SPQR-V1 Peer Leaves

Proves placed budget contracts for `signal_session_coins_fill` (Block 618), SPQR-V1 allocator and
crypto hook bundles, chain/authenticator/varint/polynomial/KDF/codec leaves (Blocks 320, 326, 341,
342, 351, 352, 362, 366..368, 378, 417, 424), and `spqr::send::<Coins>` (Block 427).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement
   blkPC_320 blkPl_320 blkPC_341 blkPl_341 blkPC_342 blkPl_342
   blkPC_361 blkPl_361 blkPC_362 blkPl_362 blkPC_366 blkPl_366
   blkPC_367 blkPl_367 blkPC_368 blkPl_368
   instIsLsBlockProg_417 libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_of_mem ls_subroutine_ok_of_block lscall_blk lsmpl lsρ sepWP_seq_lscl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (instIsLsBlockProg_427)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (MlKem spqrAuthApi spqrHkdfWith spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall SendCall SpqrModel extHookStack
   keys_ls_subroutine_ok_of_block_cro lsMemcpySym lsMemsetSym reserveCap
   sessionMemcpyRegionSpec sessionMemcpySpec sessionMemmoveSpec
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsReadFileSym lsReadStdinSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
   lsStringCloneSym)
open CryptoVerification.SignalSession.Coins.Placed (instIsLsBlockProg_618)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliExtraGhostSyms cliGhostExterns cliGhostExterns_other
   hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliExternsPlaced_panic_add_overflow cliExternsPlaced_panic_assert_jj
   cliExternsPlaced_panic_assert_yy cliExternsPlaced_panic_bounds_check
   cliExternsPlaced_panic_panic cliExternsPlaced_panic_result_unwrap_failed
   cliExternsPlaced_panic_slice_index_fail cliExternsPlaced_panic_sub_overflow
   cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
   lsMlkemEncaps1SymCli lsMlkemFromSeedSymCli lsMlkemPk1SymCli lsMlkemPk2SymCli
   lsMlkemValidatePkSymCli)
open CryptoVerification.SpqrV1.Alloc
  (DoReserveStrideCall adds_cs_eq_false growOneStack reserveCapStride reserveCapStride_one
   reserveMinCap reserve_new_cap_stride_eq spqrHandleErrorSym spqrMemmoveSym
   spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_externAt?_of_mem spqr_hook_ok_of_mem stackAt_doReserve_gen)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.ChainProofs
  (NextKeyInternalPanicPlacedOkX hkdfToSliceSpqrSpec nextKeyInternalPanicSpecX
   nextKeyInternal_panic_placed_ok)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (ls_subroutine_ok_callInv_of_block subroutine_ok_withLsCallInv_of_plain
   subroutine_ok_withLsCallInv_of_withLsCodeLoaded withLsCallInv)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (spqrMlkemDecapsSym)
open CryptoVerification.SpqrV1.Top.DecodeState
  (V1InnerHeapPred canonicalV1InnerHeap optProtoInnerStateAt_canonical_eq_drop)
open CryptoVerification.SpqrV1.Top.MessageDeserialize (spqrFormatInnerSym)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_351 blkPl_351 instIsLsBlockProg_351)
open CryptoVerification.SpqrV1.Top.Send (spqrSendCalleeStack)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk VmPreserved
   rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   rustReallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (subroutine_ok_allocNoOom_withStack_of_hookSat subroutine_ok_reallocNoOom_withStack_of_hookSat)
open LibsignalBinary.Heap.IfaceSimp (allocCallPreserved_self)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
  (ls_subroutine_ok_cro_of_plain ls_subroutine_ok_of_blockProgram_plain
   spqrSendPlacedContractsTight_of_okX spqrSendPlacedContracts_of_okX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX EncodeBytesPlacedOkX PolyNextChunkPlacedOkX
   SpqrSendPlacedContracts SpqrSendPlacedContractsTight spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (CliSpqrSendPeerSeams MessageSerializeEnv SpqrSendCoinsEnv decodeStatePlacedSpecX
   messageSerializeSpecX spqrCoinsFillSpecPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (AuthMacHdrPinnedPlacedOkX doReserve2_placed_ok_ext_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
  (SpqrSendCoinsExactEnv SpqrSendExtraContractsPlaced
   spqrSendCoins_disp_placed_ok_at_prog_ext_of_contracts
   spqrSend_dropChainEpochSlice_raw_ok_of_dealloc spqrSend_dropChunkedStates_ok_of_dealloc)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux
  (coinsFillBudgetSpecPlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
  (cliCoinsFillBudgetPlaced_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
  (mlkemDecapsAtSpec mlkemEncaps1AtSpec mlkemFromSeedAtSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.Placed.SubsetA4cBudget (statesPlacedSeams_of_hooks)
open LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat (statesPlacedSeams_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookSat_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (ExtraSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliChainFromVn_placed_ok cliDeallocBudget_at_block cliExternsPlaced_sessionMemmoveAcp_sat
   cliSpqrSend_chainFromPb_ok cliSpqrSend_chainFromVn_ok cliSpqrSend_chainIntoPb_ok
   cliVecDequeGrow_placed_ok hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliAllocWithStack_at_block cliAllocZeroedWithStack_at_block
   cliDeallocWithStack_at_block cliExternsPlaced_allocZeroed_budget_sat
   cliExternsPlaced_framelessMemcpyAcp_sat cliExternsPlaced_noAllocShimBudget_sat
   cliExternsPlaced_rustAllocShimVm_sat cliExternsPlaced_sessionMemcpyRegionRO_sat
   cliShimBudgetWithStack_at_block)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (sliceConcat2Spec sliceConcat3Spec slice_concat_2_placed_ok slice_concat_3_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
  (acp_chain_acp session2ShimAcpWithStack_of_rustAllocShimVm)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (DoReserveStrideEnv doReserveRawSpecWithStack doReserveSpecX doReserveSpecWithStack
   doReserveStrideEvents doReserveStrideRawSpecWithStack do_reserve_7_placed_ok
   do_reserve_7_placed_ok_x fitsEnv_doReserveStride_iff)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
  (finishGrow8NeCellsAcpSpecG finishGrow8ZeroCellsAcpSpecG
   finish_grow_8_ne_cells_acp_placed_ok_of_hooks finish_grow_8_zero_cells_acp_placed_ok_of_hooks
   sessionMemmoveAcpSpec sessionMemmoveBoundedAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
  (authMacHdrPinned_placed_ok authMacHdrSpec authMacHdr_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget (authUpdateSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (authUpdate_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochBudget
  (chainAddEpoch_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalSpecX vecDequeGrowSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
  (nextKeyInternal_placed_ok withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget (withAllocCallPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyBudget
  (chainRecvKey_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyBudget
  (chainSendKey_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget
  (hkdf_to_slice_spqr_placed_ok_of_other_block hkdf_to_vec_spqr_placed_ok_of_other_block)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
  (hkdf_to_slice_spqr_placed_ok_of_other_block_sat hkdf_to_vec_spqr_placed_ok_of_other_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget (poly_next_chunk_block_ok_x_ext)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (RecvCt2PlacedAlloc)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv StatesPlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget (SpqrEncodeVarintPlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlacedBudget
  (spqrEncodeVarint_placed_ok_of_hookSat_x)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs statesIntoPbPlacedSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlacedBudget
  (messageDeserialize_spqrPolyApi_placed_ok_x)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (formatInnerCallCliLsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (mlkemDecapsTightStack mlkemEncaps1TightStack mlkemFromSeedTightStack)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (messageSerializeEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
  (messageSerialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents doReserveSpec fitsEnv_doReserve_iff noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (subroutine_ok_withStack_of_subroutine_ok withStack)

/-! ## 1. `signal_session_coins_fill` (`Block 618`) & External Crypto/Memmove Hook Lemmas -/

private theorem r1sc_cliGhostExterns_eq_of_base
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {sym : String} {v : Option (State → State)}
    (h : cliExternsPlaced mmpl W sym = v)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : cliExtraGhostSyms.contains sym = false ∨ gh.extra.lookup sym = none :=
      by left; decide) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym = v :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hExtra).trans h

private theorem r1sc_hExt_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun _ _ => rfl

private theorem r1sc_hExt_withPanics
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem r1sc_hExt_withPanics_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  r1sc_hExt_withPanics mmpl gh W (r1sc_hExt_id mmpl gh W)

theorem spqrCoinsFillSpecPlaced_eq_coinsFillBudgetSpecPlaced [LibsignalPlacement] :
    spqrCoinsFillSpecPlaced = coinsFillBudgetSpecPlaced :=
  rfl

theorem cliSpqrSend_coinsFill_ok_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 618
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 618)
      (spqrCoinsFillSpecPlaced spqrSendCalleeStack) := by
  rw [withPanics_cliGhostExterns mmpl gh W,
    (instIsLsBlockProg_618 (cliGhostExterns gh (cliExternsPlaced mmpl W))).eq_blockProgram.symm,
    spqrCoinsFillSpecPlaced_eq_coinsFillBudgetSpecPlaced]
  exact cliCoinsFillBudgetPlaced_ok mmpl gh W hA spqrSendCalleeStack (by decide) (by decide)

theorem cliExternsPlaced_sessionMemmove_allocVm_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hOk : ExtraSpecOk gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveBoundedSpec 0)) := by
  refine HookSat.mono (cliExternsPlaced_sessionMemmoveAcp_sat mmpl gh W hOk 0) fun x R s0 hpre =>
    ⟨x, R, hpre, fun sf hpost => ?_⟩
  rcases x with ⟨base, buf, dst, src, len⟩
  dsimp only [sessionMemmoveBoundedAcpSpec, sessionMemmoveAcpSpec, withAllocVmPreserved,
    sessionMemmoveBoundedSpec, sessionMemmoveSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨⟨hx0, hacp, hvm⟩, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hacp, hvm⟩, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hacp.2.1⟩, hm⟩

private theorem hookSat_sessionMemcpyBudget_of_region_any {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat)
    (h : HookSat H sym sessionMemcpyRegionBudgetSpec) :
    HookSat H sym (sessionMemcpyBudgetSpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, libcMemcpySpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem cliGhostExterns_mlkemValidatePk_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hOk : ExtraSpecOk gh) (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMlkemValidatePkSymCli
      (withLsRet (withVmPreserved (CryptoVerification.LibsignalSpqrV1.mlkemValidatePkSpec W.Q.K))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemValidatePk_budget_sat
    gh (cliExternsPlaced mmpl W) hOk hK

theorem cliGhostExterns_mlkemEncaps2_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hOk : ExtraSpecOk gh) (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrMlkemEncaps2Sym
      (withLsRet (withVmPreserved (CryptoVerification.LibsignalSpqrV1.mlkemEncaps2Spec W.Q.K))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemEncaps2_budget_sat
    gh (cliExternsPlaced mmpl W) hOk hK

theorem cliGhostExterns_mlkemFromSeedAt_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hOk : ExtraSpecOk gh) (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMlkemFromSeedSymCli
      (withLsRet (withVmPreserved (mlkemFromSeedAtSpec stk W.Q.K))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemFromSeed_budget_sat
    gh (cliExternsPlaced mmpl W) hOk stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps1At_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hOk : ExtraSpecOk gh) (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMlkemEncaps1SymCli
      (withLsRet (withVmPreserved (mlkemEncaps1AtSpec stk W.Q.K))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemEncaps1_budget_sat
    gh (cliExternsPlaced mmpl W) hOk stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hOk : ExtraSpecOk gh) (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrMlkemDecapsSym
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec stk W.Q.K))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemDecapsAt_budget_sat
    gh (cliExternsPlaced mmpl W) hOk stk hlo hhi hK

/-! ## 2. `RecvCt2PlacedAlloc`, `StatesPlacedSeamsOfEnv`, and `AllocContractsPlaced` -/

theorem cliRecvCt2PlacedAlloc [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    RecvCt2PlacedAlloc M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  handleError := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_panic_handle_error mmpl gh W
  assertFailedU64 := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_assert_yy mmpl W)
  sliceIndexFail := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_slice_index_fail mmpl W)
  unwrapFailed := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_result_unwrap_failed mmpl W)
  panicBoundsCheck := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_bounds_check mmpl W)
  panicConstAddOverflow := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W)
  shim := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq
  alloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  allocZeroed := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_allocZeroed_budget_sat mmpl gh W hA
  dealloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_dealloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  realloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  memcpy := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA.toCliGhostAllocHooks
  memcpyRO := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_sessionMemcpyRegionRO_sat mmpl gh W hA.toCliGhostAllocHooks

theorem cliRecvCt2PlacedAllocExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    RecvCt2PlacedAlloc M A lim ext where
  handleError := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (cliGhostExterns_panic_handle_error mmpl gh W)
  assertFailedU64 := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_assert_yy mmpl W))
  sliceIndexFail := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_slice_index_fail mmpl W))
  unwrapFailed := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_result_unwrap_failed mmpl W))
  panicBoundsCheck := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_bounds_check mmpl W))
  panicConstAddOverflow := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))
  shim := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq)
  alloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  allocZeroed := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_allocZeroed_budget_sat mmpl gh W hA)
  dealloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  realloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  memcpy := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA.toCliGhostAllocHooks)
  memcpyRO := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_sessionMemcpyRegionRO_sat mmpl gh W hA.toCliGhostAllocHooks)

theorem cliStatesPlacedSeamsExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      StatesFromPbEnv (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      ext := by
  let _ : HkdfPlacedHooksExactSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactSat.of_allocHooks_ext (mmpl := mmpl) (W := W)
      hA.toCliGhostAllocHooks hF (r1sc_hExt_withPanics mmpl gh W hExt)
  have hmemset_wp :=
    hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  let _ : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (F := W.C.F) hmemset_wp
  exact statesPlacedSeams_of_hooks_sat
    (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W hA.extraOk))
    hmemset_wp
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliGhostExterns_mlkemValidatePk_budget_sat mmpl gh W hA.extraOk hK))
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliGhostExterns_mlkemEncaps2_budget_sat mmpl gh W hA.extraOk hK))
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliGhostExterns_mlkemDecapsAt_budget_sat mmpl gh W 36864 hA.extraOk hK))
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)) hHmac)
    (hA.onceCallHookOk_ext mmpl W hExt)

theorem cliStatesPlacedSeams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      StatesFromPbEnv (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliStatesPlacedSeamsExt mmpl gh W hA hF hK hHmac (r1sc_hExt_id mmpl gh W)

theorem cliSpqrSendAllocContractsPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    AllocContractsPlaced M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  handle_error := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_panic_handle_error mmpl gh W
  shim := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq
  alloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  dealloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_dealloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  realloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  session_memcpy stk := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact hookSat_sessionMemcpyBudget_of_region_any stk
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  session_memset_region := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks
  once_ok := hA.onceCallHookOk_withPanics mmpl W

theorem cliSpqrSendAllocContractsPlacedExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    AllocContractsPlaced M A lim ext where
  handle_error := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (cliGhostExterns_panic_handle_error mmpl gh W)
  shim := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq)
  alloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  dealloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  realloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  session_memcpy stk := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (hookSat_sessionMemcpyBudget_of_region_any stk
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks))
  session_memset_region := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  once_ok := hA.onceCallHookOk_ext mmpl W hExt

theorem cliFormatInnerCliLs_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hFmt : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrFormatInnerSym
      (formatInnerCallCliLsSpec M A lim)) :
    subroutine_ok prog (lsρ spqrFormatInnerSym) (formatInnerCallCliLsSpec M A lim) :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt _ (by decide)) hFmt)
    (by decide) hi hunmut

private theorem r1sc_cliRustAllocShimVmWithStack_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hShim : gh.shim = hookNoop := by rfl)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (stk : Nat)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli) (withStack rustAllocShimVmSpec stk) :=
  subroutine_ok_withStack_of_subroutine_ok
    (spqr_hook_ok_of_mem
      (hookSat_of_eq (hExt _ (by decide)) (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hShim))
      (by decide) hi hunmut)
    stk

/-!
## 3. Closed Budget Leaves (`Blocks 320, 326, 341, 342, 351, 352, 362, 366, 367, 368, 378, 417, 424`)
-/

section DoReserveAcp

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

private theorem do_reserve_7_stride_raw_acp_placed_ok_of_fg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsAcpSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsAcpSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveStrideRawSpecWithStack M A lim hookStack))) := by
  unfold withLsCodeLoaded withAllocCallPreserved doReserveStrideRawSpecWithStack
  simp only [stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hrlay : RustLayoutOk
      (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat) align.toNat := by
    assumption
  have hfits_env : FitsEnv M lim st
      (DoReserveStrideEnv ⟨v, cap, ptr, bs, len, additional, align, stride⟩) := by
    assumption
  have hlay := hrlay.1
  have hal_le := hrlay.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hlay.2.1 with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤
        2 ^ 63 := hlay.2.2
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_rlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hrlay
  have hmul_pos : 0 < new.toNat * stride.toNat := hnew_rlay.1.1
  have hpow_al : ∃ k, align.toNat = 2 ^ k := hnew_rlay.1.2.1
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      simpa only [doReserveStrideEvents, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
      doReserveStrideEvents, ↓reduceIte, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H) hfg0_blk hcl_m
    wp_call hfg0
      (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    have ⟨hfs_sf, htr_sf, hsig_sf, htpidr_sf, hbrk_sf, horacle_sf, hsym_sf⟩ := hacp
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st
        (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      simpa only [doReserveStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveStrideEvents, ↓reduceIte, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H) hfg1_blk hcl_m
    wp_call hfg1
      (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    have ⟨hfs_sf, htr_sf, hsig_sf, htpidr_sf, hbrk_sf, horacle_sf, hsym_sf⟩ := hacp
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

private theorem do_reserve_raw_acp_placed_of_stride [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveStrideRawSpecWithStack M A lim hookStack)))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveRawSpecWithStack M A lim hookStack))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [withAllocCallPreserved, doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, hmem⟩
  let xs : DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hevs : doReserveStrideEvents xs = doReserveEvents x := by
    simp only [doReserveStrideEvents, doReserveEvents, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one]
  have hrlay : RustLayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, hbound⟩, by decide⟩
  have hfits_s : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserveStride_iff, hevs, ← fitsEnv_doReserve_iff]
    exact hfits
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveStrideRawSpecWithStack M A lim hookStack))).pre
          (xs, st) s0 ∗ R := by
    simp only [withAllocCallPreserved, doReserveStrideRawSpecWithStack, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hrlay, hfits_s⟩, hmem⟩
  refine hs.mono_outcome (xs, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [withAllocCallPreserved, doReserveStrideRawSpecWithStack,
      doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack, xs,
      hevs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one,
      and_true] using hq
  · exact Or.inr hfail

private theorem vecU8At_eq_local (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

private theorem do_reserve_vec_acp_placed_of_raw [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveRawSpecWithStack M A lim hookStack)))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveSpecWithStack M A lim hookStack))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [withAllocCallPreserved, doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq_local, RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl
        (withAllocCallPreserved (doReserveRawSpecWithStack M A lim hookStack))).pre (x, st) s0 ∗
        (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [withAllocCallPreserved, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    have heq :
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          ((if x.cap = 0#64 then emp
            else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
              memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
            A.pool lim st s0 ∗ stackAt s0.sp (hookStack + 48 + 64) ∗
            ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ R) =
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((if x.cap = 0#64 then emp
            else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
              memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
            A.pool lim st s0 ∗ stackAt s0.sp (hookStack + 48 + 64) ∗
            ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
            ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by sep_ac_rfl
    simpa only [sepConj_assoc] using heq ▸ hmem
  refine hraw.mono_outcome (x, st) (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 at hbound
    simp only [withAllocCallPreserved, doReserveRawSpecWithStack,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap,
      vecU8At_eq_local, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hacp, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem_f⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hacp, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    simp only [sepConj_assoc] at hmem_f ⊢
    have hpost_eq :
        (x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) ∗
          ((x.v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
          stackAt s0.sp (hookStack + 48 + 64) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R =
        (x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) ∗
          ((x.v + 8#64) ↦₆₄ p') ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
          stackAt s0.sp (hookStack + 48 + 64) ∗ R := by sep_ac_rfl
    exact hpost_eq ▸ hmem_f
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem cliDoReserve7_acp_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (withAllocCallPreserved (doReserveSpec M A lim))) := by
  have hpanic : H spqrHandleErrorSym = some Rust.panicked :=
    (hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W)
  have hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec :=
    hookSat_of_eq (hExt _ (by decide)) (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq)
  have halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false) :=
    hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  have hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim) :=
    hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  exact do_reserve_vec_acp_placed_of_raw (hookStack := allocHookStack)
    (do_reserve_raw_acp_placed_of_stride
      (do_reserve_7_stride_raw_acp_placed_ok_of_fg (hookStack := allocHookStack) (by decide) hpanic
        (finish_grow_8_zero_cells_acp_placed_ok_of_hooks (by decide)
          (session2ShimAcpWithStack_of_rustAllocShimVm allocHookStack (spqr_hook_ok_of_mem hshim))
          (subroutine_ok_allocNoOom_withStack_of_hookSat halloc spqr_externAt?_of_mem))
        (finish_grow_8_ne_cells_acp_placed_ok_of_hooks (by decide)
          (subroutine_ok_reallocNoOom_withStack_of_hookSat hrealloc spqr_externAt?_of_mem))))

end DoReserveAcp

theorem cliDoReserve7_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_7_placed_ok
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_eq (hExt _ (by decide)) (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks))
    (hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks))

theorem cliDoReserve7_placed_ok_x [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_7_placed_ok_x
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_eq (hExt _ (by decide)) (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks))
    (hookSat_of_eq (hExt _ (by decide))
      (cliExternsPlaced_realloc_budget_sat mmpl gh W hA.toCliGhostAllocHooks))

private theorem cliExternsPlaced_sessionMemsetRegion_allocVm_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget.withAllocVmPreserved
        CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec) := by
  obtain ⟨f, hf, _, _, _, hok, hvm, hfs, _⟩ := hA.memset
  have hacp := hA.memset_acp f hf
  refine ⟨f,
    CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memset_some gh _ hf,
    fun x R s0 hrun hpre hsp_al => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp_al
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have htr : (f s0).trace = s0.trace := by
      rcases x with ⟨ptr, c, len⟩
      dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact hpost.1.2
    dsimp only [withAllocVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs s0, htr, (hacp s0).1, (hvm s0).1.2.2, (hvm s0).1.1, (hacp s0).2, hsym⟩, hvm s0⟩, hpost⟩
  · exact Or.inr hrest

private theorem r1sc_hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat_priv
    [LibsignalPlacement] (C : Crypto) {callerProg : Program} {i : Nat}
    {H : CryptoVerification.LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemset : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat
    C hMemset hi

theorem cliNextKeyInternal_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (blkPl_362).base
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  let _ : HkdfPlacedHooksExactSat W.C.F H :=
    HkdfPlacedHooksExactSat.of_allocHooks_ext (mmpl := mmpl) (W := W) hA hF hExt
  have hMemsetH : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec) :=
    hookSat_of_eq (hExt lsMemsetSym (by decide))
      (cliExternsPlaced_sessionMemsetRegion_allocVm_sat mmpl gh W hA)
  have hconcat_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 362) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_2_placed_ok
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_sessionMemcpyRegionRO_sat mmpl gh W hA)))))
  have hhkdf_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (r1sc_hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat_priv W.C hMemsetH)
  exact nextKeyInternal_placed_ok hconcat_362 hhkdf_362 (cliDeallocWithStack_at_block mmpl gh W hA hExt)

theorem cliNextKeyInternal_panic_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    NextKeyInternalPanicPlacedOkX H :=
  nextKeyInternal_panic_placed_ok
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_assert_jj mmpl W))))

theorem cliChainRecvKey_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (blkPl_366).base
      (withLsCallInv lsmpl (chainRecvKeySpecX M A lim (spqrHkdfWith W.C.F))) := by
  have hnext_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_placed_ok mmpl gh W hA.toCliGhostAllocHooks hF hExt)
  have hpanic_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_panic_placed_ok mmpl gh W hExt)
  have hdoRes_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 366) (j := 320)
        (cliDoReserve7_acp_placed_ok mmpl gh W hA hExt))
  exact chainRecvKey_placed_ok_of_contracts
    hnext_366 hpanic_366
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks hExt)
    hdoRes_366
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_assert_jj mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W
          (cliExternsPlaced_panic_slice_index_fail mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W))))

theorem cliChainSendKey_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (blkPl_367).base
      (withLsCallInv lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnext_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_placed_ok mmpl gh W hA hF hExt)
  have hpanic_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_panic_placed_ok mmpl gh W hExt)
  exact chainSendKey_placed_ok_of_contracts
    hnext_367 hpanic_367
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA hExt)
    (cliDeallocWithStack_at_block mmpl gh W hA hExt)

theorem cliChainAddEpoch_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  let _ : HkdfPlacedHooksExactSat W.C.F H :=
    HkdfPlacedHooksExactSat.of_allocHooks_ext (mmpl := mmpl) (W := W) hA hF hExt
  have hMemsetH : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec) :=
    hookSat_of_eq (hExt lsMemsetSym (by decide))
      (cliExternsPlaced_sessionMemsetRegion_allocVm_sat mmpl gh W hA)
  have hhkdf_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (r1sc_hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat_priv W.C hMemsetH)
  have hgrow_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 368) (j := 353)
        (cliVecDequeGrow_placed_ok mmpl gh W hA hExt))
  exact chainAddEpoch_placed_ok_of_contracts_x
    hhkdf_368 hgrow_368
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA hExt)
    (cliDeallocWithStack_at_block mmpl gh W hA hExt)
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W))))

theorem cliEncodeVarintPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    SpqrEncodeVarintPlacedOkX A lim ext := by
  have hc := cliSpqrSendAllocContractsPlacedExt mmpl gh W hA hExt
  exact spqrEncodeVarint_placed_ok_of_hookSat_x A lim ext
    hc.handle_error
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc

theorem cliEncodeVarint_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (cliEncodeVarintPlacedOkX mmpl gh W hA hExt)

private theorem messageSerializeEvents_spqrBoundedEvs
    {P_api : CryptoVerification.LibsignalSpqrV1.PolyApi} (x : MessageSerializeGhost P_api) :
    SpqrBoundedEvs 8 256 (messageSerializeEvents P_api x) := by
  have halloc : SpqrBoundedEvs 8 256 (rustAllocEvents 40 1) := by
    have hr : rustAllocEvents 40 1 = [.alloc 40] := rfl
    rw [hr]
    refine ⟨by decide, fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨by decide, by decide, fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  have hboth : SpqrBoundedEvs 8 256 (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) := by
    have hr : rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 = [.alloc 40, .realloc 1 40 80] :=
      rfl
    rw [hr]
    refine ⟨by decide, fun ev hev => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · exact ⟨by decide, by decide, fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
    · refine ⟨by decide, by decide, fun _ _ h => (by cases h), fun al _ _ h => ?_⟩
      cases h; decide
  unfold messageSerializeEvents
  cases x.msg.payload <;> dsimp only <;> first | exact halloc | (split <;> [exact halloc; exact hboth])

theorem cliMessageSerialize_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)) := by
  have hc := cliSpqrSendAllocContractsPlacedExt mmpl gh W hA hExt
  have hraw := messageSerialize_placed_ok_of_hooks spqrPolyApi A lim ext
    hc.handle_error
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc (cliEncodeVarintPlacedOkX mmpl gh W hA hExt)
  have hcro := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hraw
  exact subroutine_ok_mono hcro
    (fun (x, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecX,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, hfit⟩ =>
        ⟨h1, h2, h3, hfit.mono fun evs hevs => by
          rw [hevs]; exact messageSerializeEvents_spqrBoundedEvs x⟩)
    (fun (x, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecX,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
          (⌜LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.MessageSerializeEnv spqrPolyApi x evs⌝ ∗
            ((messageAt spqrPolyApi x.msgA x.msg ∗
                vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
                A.pool lim (M.stepEvents evs stB) sf ∗
                stackAt s0.sp messageSerializeStackX) ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨htr, hevs, hrest⟩
      have hgoal : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ MessageSerializeEnv x evs⌝ ∗
          ((messageAt spqrPolyApi x.msgA x.msg ∗
              vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
              A.pool lim (M.stepEvents evs stB) sf ∗
              stackAt s0.sp messageSerializeStackX) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, by rw [hevs]; exact messageSerializeEvents_spqrBoundedEvs x⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

theorem cliMessageDeserialize_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hFmt : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrFormatInnerSym
      (formatInnerCallCliLsSpec M A lim)) :
    MessageDeserializePlacedOkX spqrPolyApi M A lim ext :=
  let _ := instIsLsBlockProg_351 (Rust.withPanics ext)
  messageDeserialize_spqrPolyApi_placed_ok_x A lim ext
    (cliFormatInnerCliLs_at_block mmpl gh W A lim (r1sc_hExt_withPanics mmpl gh W hExt)
      (i := 351) (hFmt := hFmt))
    (cliDeallocBudget_at_block mmpl gh W hA (r1sc_hExt_withPanics mmpl gh W hExt) (i := 351))

theorem cliPolyNextChunkPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    PolyNextChunkPlacedOkX M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (poly_next_chunk_block_ok_x_ext (cliSpqrSendAllocContractsPlaced mmpl gh W hA))

theorem cliEncodeBytesPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    EncodeBytesPlacedOkX A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hraw := encode_bytes_placed_ok_x
    (by
      rw [withPanics_cliGhostExterns mmpl gh W]
      exact cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq)
    (by
      rw [withPanics_cliGhostExterns mmpl gh W]
      exact cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    (by
      rw [withPanics_cliGhostExterns mmpl gh W]
      exact hookSat_sessionMemcpyBudget_of_region_any allocHookStack
        (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
  exact @ls_subroutine_ok_cro_of_plain _ _
    (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) _ 427 417
    (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (instIsLsBlockProg_427 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (instIsLsBlockProg_417 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (lsmpl.base 417) (encodeBytesSpecX A lim)
    hraw (by decide) (by decide) (by decide)

theorem cliHkdfToVec_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith W.C.F))) := by
  let _ : HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    HkdfPlacedHooksExactSat.of_allocHooks_withPanics (mmpl := mmpl) (W := W)
      hA.toCliGhostAllocHooks hF
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  exact hkdf_to_vec_spqr_placed_ok_of_other_block_sat
    (i := 427) W.C M A lim
    (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks))
    (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    hc.allocZeroed

theorem cliAuthUpdate_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec W.C.F M A lim)) := by
  let _ : HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    HkdfPlacedHooksExactSat.of_allocHooks_withPanics (mmpl := mmpl) (W := W)
      hA.toCliGhostAllocHooks hF
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  have hconcat_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 341) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_2_placed_ok hc.shim hc.alloc hc.memcpy hc.memcpyRO)))
  have hhkdf_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_placed_ok_of_other_block_sat W.C
        (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
          (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)))
  have hupd_341 :=
    authUpdate_placed_ok hconcat_341 hhkdf_341
      (cliShimBudgetWithStack_at_block mmpl gh W hA.shim_eq (r1sc_hExt_withPanics_id mmpl gh W)
        extHookStack (i := 341))
      (cliAllocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
      (cliAllocZeroedWithStack_at_block mmpl gh W hA
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
      (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 341)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hupd_341)

theorem cliAuthMacHdr_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec W.C.F M A lim)) := by
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  have hconcat_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat3Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 342) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_3_placed_ok hc.shim hc.alloc hc.memcpy hc.memcpyRO)))
  have hhmac_sat : HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      spqrLibcruxHmacSym (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)) := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact hHmac
  have hhmac_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ spqrLibcruxHmacSym)
      (withLsCallInv lsmpl (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (spqr_hook_ok_of_mem hhmac_sat (by decide) (by decide) (by decide)))
  have hmac_342 :=
    authMacHdr_placed_ok hconcat_342 hhmac_342
      (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 342))
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 342)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hmac_342)

theorem cliAuthMacHdrPinnedPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :
    AuthMacHdrPinnedPlacedOkX W.C.F M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  have hconcat_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat3Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 342) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_3_placed_ok hc.shim hc.alloc hc.memcpy hc.memcpyRO)))
  have hhmac_sat : HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      spqrLibcruxHmacSym (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)) := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact hHmac
  have hhmac_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ spqrLibcruxHmacSym)
      (withLsCallInv lsmpl (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (spqr_hook_ok_of_mem hhmac_sat (by decide) (by decide) (by decide)))
  have hmac_342 :=
    authMacHdrPinned_placed_ok hconcat_342 hhmac_342
      (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 342))
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 342)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hmac_342)

/-! ## 4. Top-Level `Block 427` (`spqr::send::<Coins>`) Budget Seams -/

theorem spqrSendExtraContractsPlaced_of_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim))) :
    SpqrSendExtraContractsPlaced M A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  panic_hook := r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W)
  panicSubOverflow_hook :=
    r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_sub_overflow mmpl W)
  unwrapFailed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W
      (cliExternsPlaced_panic_result_unwrap_failed mmpl W)
  allocZeroed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_allocZeroed_budget_sat mmpl gh W hA
  mlkemFromSeed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_mlkemFromSeedAt_budget_sat mmpl gh W 36864 hA.extraOk hK
  mlkemPk1_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemPk1_budget_sat
      gh (cliExternsPlaced mmpl W) hA.extraOk
  mlkemPk2_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliGhostExterns_mlkemPk2_budget_sat
      gh (cliExternsPlaced mmpl W) hA.extraOk
  mlkemEncaps1_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_mlkemEncaps1At_budget_sat mmpl gh W 36864 hA.extraOk hK
  fromSeed_pk1_slice := W.Q.K.fromSeed_pk1
  fromSeed_pk2_slice := W.Q.K.fromSeed_pk2
  macHdrPinned_ok := cliAuthMacHdrPinnedPlacedOkX mmpl gh W hA hHmac
  doReserve2_ok :=
    doReserve2_placed_ok_ext_x
      (cliSpqrSendAllocContractsPlaced mmpl gh W hA)
  dropChainEpochSlice_raw_ok :=
    spqrSend_dropChainEpochSlice_raw_ok_of_dealloc
      (cliSpqrSendAllocContractsPlaced mmpl gh W hA)
  dropChunkedStates_ok :=
    spqrSend_dropChunkedStates_ok_of_dealloc
      (cliSpqrSendAllocContractsPlaced mmpl gh W hA)

private theorem r1sc_cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Bridge from `SeamSpecsPlacedBudget.spqrSendCoinsDispPlacedSpecTOfEnv` (under
    `LibsignalTripleRatchet.withLsCodeRoLoaded` and `SpqrSendCoinsExactEnv W.C.F W.Q.K`) to
    `SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv` (under `StoreKit.withLsCodeRoLoaded`
    and any `SendEnv` containing `SpqrSendCoinsExactEnv W.C.F W.Q.K`). -/
theorem spqrSendCoins_placed_seam_of_contracts_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hSub : ∀ sc evs, SpqrSendCoinsExactEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)))
    (hC : SpqrSendPlacedContracts M H_inner A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have hok := spqrSendCoins_disp_placed_ok_at_prog_ext_of_contracts
    (callerProg := (blkPC_427).rebase (blkPl_427).base
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 427) (by decide)
    (r1sc_cliGhostExterns_isPanic mmpl gh W)
    (cliSpqrSendAllocContractsPlaced mmpl gh W hA)
    hC
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hA hK hHmac)
  have heq_cro (m : Memory) :
      LibsignalCodeRoLoaded lsmpl m =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hmod : pqxdhSpqrModel ⟨W.C, W.Q⟩ = spqrV1 W.C.F W.Q.K := rfl
  rw [hmod]
  have hcoinsAt : spqrCoinsAtPlaced = cliTapeAt := rfl
  have hcoinsAfter : spqrCoinsAfterPlaced = cliTapeAfter := rfl
  exact subroutine_ok_mono hok
    (fun (sc, stB) _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsDispPlacedSpec,
        withLsCodeRoLoaded,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsDispPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsDispPlacedSpecOfEnv]
        at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => ⟨h1, h2, hfit.mono (hSub sc)⟩)
    (fun (sc, stB) _ s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsDispPlacedSpec,
        withLsCodeRoLoaded,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsDispPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsDispPlacedSpecOfEnv]
        at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ => ⟨hSub sc evs hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hpanic => hpanic)

private theorem r1sc_cliSpqrSend_chainAddEpoch_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainAddEpoch_placed_ok mmpl gh W hA hF (r1sc_hExt_withPanics_id mmpl gh W)))

private theorem r1sc_cliSpqrSend_chainSendKey_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainSendKey_placed_ok mmpl gh W hA hF (r1sc_hExt_withPanics_id mmpl gh W)))

private theorem r1sc_cliSpqrSend_coinsFill_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    CoinsFillPlacedOkX (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_plain (cliSpqrSend_coinsFill_ok_cli mmpl gh W hA)

private theorem r1sc_cliSpqrSend_messageSerialize_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliMessageSerialize_placed_ok mmpl gh W hA (r1sc_hExt_id mmpl gh W))

private theorem r1sc_cliSpqrSend_encodeVarint_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliEncodeVarint_placed_ok mmpl gh W hA (r1sc_hExt_id mmpl gh W))

/-- Block `427` (`spqr::send::<Coins>`) at `SpqrSendCoinsExactEnv W.C.F W.Q.K` from
    `CliSpqrSendPeerSeams M A lim W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))`, with all
    intra-SPQR KDF/chain/auth/poly leaves discharged. -/
theorem cliSpqrSendCoins_placed_ok_of_peerSeams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)))
    (hPeers : CliSpqrSendPeerSeams M A lim W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) (SpqrSendCoinsExactEnv W.C.F W.Q.K))) :=
  spqrSendCoins_placed_seam_of_contracts_ofEnv (fun _ _ h => h) hA hK hHmac
    (spqrSendPlacedContracts_of_okX
      (cliSpqrSendAllocContractsPlaced mmpl gh W hA)
      (cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks)
      (r1sc_cliSpqrSend_chainAddEpoch_on mmpl gh W hA.toCliGhostAllocHooks hF)
      (r1sc_cliSpqrSend_chainSendKey_on mmpl gh W hA.toCliGhostAllocHooks hF)
      (cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks)
      (cliAuthMacHdr_placed_ok mmpl gh W hA hHmac)
      (cliAuthUpdate_placed_ok mmpl gh W hA hF)
      (cliHkdfToVec_placed_ok mmpl gh W hA hF)
      (cliEncodeBytesPlacedOkX mmpl gh W hA.toCliGhostAllocHooks)
      (cliPolyNextChunkPlacedOkX mmpl gh W hA)
      hPeers)

set_option maxHeartbeats 1600000 in
/-- Tight `SpqrSendPlacedContractsTight` assembly on
    `cliGhostExterns gh (cliExternsPlaced mmpl W)` from the exact proved peer leaves
    (`SpqrChunkedMergePlacedInstBudget.cliSpqrSend_decodeState_closed_ok`,
    `cliStatesPlacedSeams`, `SpqrStatesIntoPbPlacedInstBudget`, `SpqrChainPlacedInstBudget`,
    `cliMessageSerialize_placed_ok`, `cliEncodeVarint_placed_ok`, `cliSpqrSend_coinsFill_ok_cli`). -/
theorem spqrSendPlacedContractsTight_of_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (libcruxHmacBudgetSpec W.C.F M A lim)))
    (hStatesIntoPb : subroutine_ok
      (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim W.C.F))) :
    SpqrSendPlacedContractsTight M canonicalV1InnerHeap A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hS := cliStatesPlacedSeams mmpl gh W hA hF hK hHmac
  exact spqrSendPlacedContractsTight_of_okX
    (cliSpqrSendAllocContractsPlaced mmpl gh W hA)
    (r1sc_cliSpqrSend_coinsFill_on mmpl gh W hA.toCliGhostAllocHooks)
    (SpqrChunkedMergePlacedInstBudget.cliSpqrSend_decodeState_closed_ok mmpl gh W
      hA.toCliGhostAllocHooks (r1sc_hExt_id mmpl gh W))
    (hS.statesFromPb_on)
    hStatesIntoPb
    (cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks)
    (cliSpqrSend_chainFromVn_ok mmpl gh W hA.toCliGhostAllocHooks hF)
    (r1sc_cliSpqrSend_chainAddEpoch_on mmpl gh W hA.toCliGhostAllocHooks hF)
    (r1sc_cliSpqrSend_chainSendKey_on mmpl gh W hA.toCliGhostAllocHooks hF)
    (cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks)
    (r1sc_cliSpqrSend_messageSerialize_on mmpl gh W hA)
    (r1sc_cliSpqrSend_encodeVarint_on mmpl gh W hA)
    (cliAuthMacHdr_placed_ok mmpl gh W hA hHmac)
    (cliAuthUpdate_placed_ok mmpl gh W hA hF)
    (cliHkdfToVec_placed_ok mmpl gh W hA hF)
    (cliEncodeBytesPlacedOkX mmpl gh W hA.toCliGhostAllocHooks)
    (cliPolyNextChunkPlacedOkX mmpl gh W hA)
    (hS.headerSentSendEkChunk_on)
    (hS.ct1ReceivedSendEkChunk_on)
    (hS.ct1SampledSendCt1Chunk_on)
    (hS.ekReceivedCt1SampledSendCt1Chunk_on)
    (hS.ct2SampledSendCt2Chunk_on)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
