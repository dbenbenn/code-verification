/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Send
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat
import LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget
import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget

/-!
# `{A}`-Generic Slot-`464` (`encrypt`) Callee and `w1Inner` Assembly (`ElfSlicesPqOomH2KSlot464Cal`)

**Checked by Lean.**

Generalizes the Block-`427` (`spqr::send::<Coins>`), Block-`428` (`otr::encrypt`), and Block-`464`
(`w1Inner` / `encSlotSpecPlaced`) assemblies to an arbitrary `A : RustCliAllocBudget M` (such as
`AllocWithFds.withFds A0`), taking `SessionOnlyKitPlacedOkSE A`, `IdentityStoreKitPlacedOkI A`,
`hHmac`, and `hAesEnc` directly without raw `lsReadFileSym` `HookSat` premises.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Cal

open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Send
  (spqrSendCoins_placed_ok_guarded_of_decodeState_at)



/-! ## `{M} {A}`-Generic Block-`428` and Block-`464` Slot Assembly -/

section SlotAt

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession
  (OutgoingTripleRatchet SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi
  (Session SessionRecord execOk)
open CryptoVerification
  (ExternsDistinctOnHooked IsLsBlockProg LibsignalFullPlacement
   LibsignalHooks LibsignalPlacement blkLib_eq_114 blkPC_114 blkPC_38 blkPC_39 blkPC_60 blkPC_61
   blkPC_69 blkPl_114 blkPl_38 blkPl_39 blkPl_60 blkPl_61 blkPl_69 libsignalMutatedBlocks
   libsignalSessionLib lsProg_114 lsRustNoAllocShimSym ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.Cli.LibsignalTripleRatchet (otrEncryptName)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428 instIsLsBlockProg_428)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427 instIsLsBlockProg_427)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles NoFsEv ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl withLsRoCl)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (CallingConventionPreserved_of_calleeSaved Frame disjointRegions_of_ro_rw
   hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook lsCompress256Sym lsMemcpySym lsMemsetSym
   lsSha256IVAddr rodata_placed_sha256IV)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress spqrV1_emptyOk)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks SendCall blkPC_63 blkPl_63 extract_withLsCodeRoLoaded
   keys_ls_hook_ok_of_mem lsPanicConstAddOverflowSym newFromSliceSpec newFromSliceStack
   noAllocShimSpec subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsAesEncSym)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.Slots
  (cliEncRecOk_opened cliGhostExterns_panic_handle_alloc_error
   cliGhostExterns_panic_handle_error cliGhostExterns_panic_option_expect_failed
   encodeInjOn_deserializeScopeP_Q scopeIn scopeKit
   scopeKit_pqrState_lt scopeKit_recordInScopeEnc)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget
  (aesEncBudgetSpec libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (formatInnerCallCliLsSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (PublicApiEncHooksPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget
  (withStores_placed_okVT_fs_cli)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
  (otrEncryptEmpty_coins_placed_ok otrEncryptV1_coins_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges (tlb_DecodeStateGuardedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 SpqrStateTight640)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (OtrEncryptCoreEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
  (OtrRoCalleesPlacedOk nextChainKey_39_vm_cro_ok transfer_tr_cro_of_block uuidTryParse_252_vm_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (cliExternsPlaced_rustAllocShimVm_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
  (W1InnerPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
  (cliEncrypt_slot_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (hookSatCompress256_cliGhostExterns_of_extraOk_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks
   cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_exactMemcpy_sat
   cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat
   cliGhostExterns_compress256_roBudget_sat
   cliGhostExterns_durationSinceBounded_budget_sat cliGhostExterns_timeAdd_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (spqrSendCoinsPlacedSpecTOfEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
  (w1t_SendGuardedBytesEnv w1t_SendGuardedEnv w1t_SendTightBytesEnv
   w1t_cliEncryptBinaryKitSlotEnvExact w1t_encTailsVTPlaced w1t_libsignalFullPlacementOf
   w1t_s427_not_fitsEnv_of_univ w1t_sendBytesEnvOf w1t_sendGuardedBytes_empty)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStatePlacedOkOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
  (message_keys_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
  (hmac_placed_cro_ok_at_block_sat new_from_slice_placed_cro_budget_ok_at_block_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (newFromSliceSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
  (parseSid_placed_ok_of_code)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (generateKeysSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat
  (generateKeys_placed_ok_of_contracts_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
  (serialize_addresses_placed_ok_of_rustAllocShimVm)
open LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudgetSat (computeMac_placed_cro_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (encode_varint_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget (encoded_len_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget (signalMessageNew_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (signalMessageNewSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cal_subroutine_ok_storeKitCro_of_trCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ :=
        CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem cal_subroutine_ok_trCro_of_storeKitCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem cal_hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem cal_new_from_slice_cro_budget_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (newFromSliceSpecSat W.C.F))) :=
  new_from_slice_placed_cro_budget_ok_at_block_sat (callerProg := callerProg) (i := i) W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (hookSatCompress256_cliGhostExterns_of_extraOk_eq g (cliExternsPlaced mmpl W) hG.extraOk hF) hi

private theorem cal_hmac_vm_cro_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec W.C.F))) :=
  hmac_placed_cro_ok_at_block_sat (callerProg := callerProg) (i := i) W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    (hookSatCompress256_cliGhostExterns_of_extraOk_eq g (cliExternsPlaced mmpl W) hG.extraOk hF) hi

private theorem publicApiEncHooks_of_ghost [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    PublicApiEncHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG
  stringClone := hh.stringClone
  timeAdd := cliGhostExterns_timeAdd_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
  durationSince :=
    cliGhostExterns_durationSinceBounded_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  handleAllocError := cliGhostExterns_panic_handle_alloc_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

private theorem generateKeys_428_placed_ok_of_ghost [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim W.C.F)) := by
  haveI : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    ⟨cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG,
     cliExternsPlaced_exactMemcpy_sat mmpl g W hG,
     hookSatCompress256_cliGhostExterns_of_extraOk_eq g (cliExternsPlaced mmpl W) hG.extraOk hF⟩
  have hext69 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hexp69 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hdealloc69 := keys_ls_hook_ok_of_mem
    (prog := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 69)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
  have hgk69 := generateKeys_placed_ok_of_contracts_budget_sat (C := W.C) hext69 hexp69 hdealloc69
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    hgk69

private theorem signalMessageNew_428_placed_cro_ok_of_ghost [LibsignalPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 63)
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim W.C.F uuidTryParse)) := by
  have hNoAlloc := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq
  have hshim_b := cal_hookSat_noAllocShimBudget_of_withVmPreserved hNoAlloc
  have hAlloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  have hDealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  have hRealloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  have hpks205 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (public_key_serialize_placed_ok hshim_b hAlloc)
  have hparse206 := parseSid_placed_ok_of_code (cliGhostExterns g (cliExternsPlaced mmpl W))
    (uuidTryParse_252_vm_placed_ok (cliGhostExterns g (cliExternsPlaced mmpl W)))
  have hparse61 := ls_subroutine_ok_of_block
    (callerProg := (blkPC_61).rebase (blkPl_61).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hparse206
  have hser61 := serialize_addresses_placed_ok_of_rustAllocShimVm hparse61
    (cliExternsPlaced_rustAllocShimVm_sat mmpl g W hG.shim_eq)
    hAlloc
  have hmac60 := computeMac_placed_cro_ok_sat W.C M A lim
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (cal_new_from_slice_cro_budget_ok_at_block mmpl g W hF hG
      (callerProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_60).rebase (blkPl_60).base
          (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205))
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (hF ▸ cliGhostExterns_compress256_roBudget_sat g (cliExternsPlaced mmpl W) hG.extraOk (stk := 176))
    hDealloc
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  have hnew63 := signalMessageNew_placed_cro_ok (C := W.C)
    hNoAlloc
    hAlloc
    hDealloc
    (cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
        (encoded_len_placed_ok A.repAlloc (cliGhostExterns g (cliExternsPlaced mmpl W)))))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (encode_varint_placed_ok hshim_b hAlloc hRealloc))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hser61)
    (transfer_tr_cro_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (calleeProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hmac60)
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_63).rebase (blkPl_63).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hnew63

private theorem otrRoCalleesPlacedOk_of_ghost [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    OtrRoCalleesPlacedOk mmpl g W A lim := by
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact
    { messageKeys := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_38).rebase (blkPl_38).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (message_keys_placed_cro_ok
          (cal_hmac_vm_cro_ok_at_block mmpl g W hF hG
            (callerProg := (blkPC_38).rebase (blkPl_38).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq)
          (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
      signalMessageNew := signalMessageNew_428_placed_cro_ok_of_ghost mmpl g W hF A lim hG
      nextChainKey := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_39).rebase (blkPl_39).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (nextChainKey_39_vm_cro_ok
          (cal_hmac_vm_cro_ok_at_block mmpl g W hF hG
            (callerProg := (blkPC_39).rebase (blkPl_39).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (hh.panics lsPanicConstAddOverflowSym (by decide))) }

/-- `{M} {A}`-generic Block-`464` `W1InnerPlacedOk` taking `SessionOnlyKitPlacedOkSE A` and
`IdentityStoreKitPlacedOkI A` directly. -/
theorem w1Inner_of_sendCoins_at [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    {mmpl : MultiPlacement}
    (ghFixed : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (SendEnv : SendCall → List AllocEvent → Prop)
    (hSend427 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A cliBudgetLimits 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)))
    (hSendEmpty : ∀ rest, w1t_sendBytesEnvOf SendEnv [] rest [])
    (hSend_ptr_congr : ∀ (sc : SendCall) (evs : List AllocEvent),
      SendEnv sc evs ↔ w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs)
    (hGSpqr : CliGhostSpqrAllocHooks M A cliBudgetLimits ghFixed)
    (hh : RunHooksPlaced A cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hAesEnc : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesEncSym
      (withLsRet (aesEncBudgetSpec W.C.E M A cliBudgetLimits)))
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost),
      SessionOnlyKitPlacedOkSE A cliBudgetLimits
        (w1SessKitPlaced A.repAlloc cliRunBudgets F peer)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
        scopeKit encodeRecord (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost),
      IdentityStoreKitPlacedOkI A cliBudgetLimits
        (w1IdKitPlaced A.repAlloc cliRunBudgets F peer)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (h547 : lsmpl.base 547 ≠ 0#64) :
    W1InnerPlacedOk mmpl ghFixed W A cliBudgetLimits
      cliRunBudgets scopeIn (w1t_sendBytesEnvOf SendEnv)
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) := by
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  have hG := hGSpqr.toCliGhostAllocHooks
  have hhooks := publicApiEncHooks_of_ghost mmpl ghFixed W A cliBudgetLimits hG hh
  have hFmtEnv : HookSat H CryptoVerification.LibsignalTripleRatchet.Encrypt.lsFormatInnerSym
      (formatInnerCallCliLsSpec M A cliBudgetLimits) :=
    hh.formatInner
  have hOtrRo := otrRoCalleesPlacedOk_of_ghost mmpl ghFixed W hF A cliBudgetLimits hG hh
  have _ := instIsLsBlockProg_427 H
  have _ := instIsLsBlockProg_464 H
  have _ := instIsLsBlockProg_428 H
  have hSend_eq : SendEnv = fun sc evs => w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs := by
    funext sc evs; exact propext (hSend_ptr_congr sc evs)
  have hSend427_bytes :
      subroutine_ok ((blkPC_427).rebase (blkPl_427).base H) (lsmpl.base 427)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrSendCoinsPlacedSpecTOfEnv M A cliBudgetLimits 0#64
            (pqxdhSpqrModel ⟨W.C, W.Q⟩)
            (fun sc evs => w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs))) :=
    hSend_eq ▸ hSend427
  have hSend428 := cal_subroutine_ok_trCro_of_storeKitCro
    (subroutine_ok_withLsCodeRoLoaded_of_rocl (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base H)
      hSend427_bytes (by decide) (by decide) (by decide)))
  have hOtrT :
      subroutine_ok (lsProg_464 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
        (withLsRoCl lsmpl
          (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
            tokenInitPlacedAt W.C A cliBudgetLimits 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv))) := by
    have h428 := otrEncryptV1_coins_placed_ok tokenInitPlacedAt W.C A cliBudgetLimits 0#64
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv) H
      hAesEnc hFmtEnv (cliExternsPlaced_dealloc_budget_sat mmpl ghFixed W hG)
      hSend428 hOtrRo.messageKeys
      (generateKeys_428_placed_ok_of_ghost mmpl ghFixed W hF A cliBudgetLimits hG)
      hOtrRo.signalMessageNew hOtrRo.nextChainKey
    have h428' := cal_subroutine_ok_storeKitCro_of_trCro h428
    change subroutine_ok _ (lsmpl.base 428 + 0#64) _
    rw [BitVec.add_zero]
    exact ls_subroutine_ok_rocl_of_block
      (callerProg := lsProg_464 H) (j := 428) h428' (by decide) (by decide) (by decide)
  have hOtrEmpty :
      subroutine_ok (lsProg_464 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
        (withLsRoCl lsmpl
          (otrEncryptPlacedSpecQ (· = []) W.C A cliBudgetLimits 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv))) := by
    have h428 := otrEncryptEmpty_coins_placed_ok W.C A cliBudgetLimits 0#64
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv) H
      (spqrV1_emptyOk W.C.F W.Q.K) hSendEmpty
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl ghFixed W hG)
      hAesEnc hFmtEnv (cliExternsPlaced_dealloc_budget_sat mmpl ghFixed W hG)
      hOtrRo.messageKeys
      (generateKeys_428_placed_ok_of_ghost mmpl ghFixed W hF A cliBudgetLimits hG)
      hOtrRo.signalMessageNew hOtrRo.nextChainKey
    have h428' := cal_subroutine_ok_storeKitCro_of_trCro h428
    change subroutine_ok _ (lsmpl.base 428 + 0#64) _
    rw [BitVec.add_zero]
    exact ls_subroutine_ok_rocl_of_block
      (callerProg := lsProg_464 H) (j := 428) h428' (by decide) (by decide) (by decide)
  have hTails := @w1t_encTailsVTPlaced _ M A cliBudgetLimits
  intro F peer hok
  exact withStores_placed_okVT_fs_cli hhooks
    (hSessKit F peer)
    (hIdKit F peer)
    hOtrT hOtrEmpty
    (w2SessVt_placed_ok A.repAlloc cliRunBudgets h547 F peer)
    (w2IdVt_placed_ok A.repAlloc cliRunBudgets h547 F peer)
    (Or.inr ⟨⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
      ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩,
      hh.fs (lsProg_464 H) 464⟩)
    (fun r ⟨hsc, _⟩ => scopeKit_recordInScopeEnc hsc)
    (fun r s ⟨hsc, _⟩ hsess => scopeKit_pqrState_lt hsc s hsess)
    (fun {x r sess otr taken k m otr'} haddr h15 =>
      cliEncRecOk_opened (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
        (Scope₀ := scopeIn) (F0 := F) (peer := peer) (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
        (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
        (fun _ h => h) hok haddr h15)
    (hTails hhooks)

/-- `{M} {A}`-generic outer Block-`579` `encrypt` slot (`lsmpl.base 464`) parametric in `SendEnv`. -/
theorem hole3_w1_inner_of_sendCoins_at [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    {mmpl : MultiPlacement}
    (ghFixed : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (SendEnv : SendCall → List AllocEvent → Prop)
    (hSend427 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A cliBudgetLimits 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)))
    (hSendEmpty : ∀ rest, w1t_sendBytesEnvOf SendEnv [] rest [])
    (hSend_ptr_congr : ∀ (sc : SendCall) (evs : List AllocEvent),
      SendEnv sc evs ↔ w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs)
    (hGSpqr : CliGhostSpqrAllocHooks M A cliBudgetLimits ghFixed)
    (hh : RunHooksPlaced A cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hAesEnc : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesEncSym
      (withLsRet (aesEncBudgetSpec W.C.E M A cliBudgetLimits)))
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost),
      SessionOnlyKitPlacedOkSE A cliBudgetLimits
        (w1SessKitPlaced A.repAlloc cliRunBudgets F peer)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
        scopeKit encodeRecord (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost),
      IdentityStoreKitPlacedOkI A cliBudgetLimits
        (w1IdKitPlaced A.repAlloc cliRunBudgets F peer)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (h547 : lsmpl.base 547 ≠ 0#64) :
    (mkSlot
      (encSlotSpecPlaced A cliBudgetLimits
        (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
          (w1t_sendBytesEnvOf SendEnv)
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (lsmpl.base 464) := by
  intro stk h1 h2
  exact cliEncrypt_slot_placed (i := 579) mmpl ghFixed W
    A cliBudgetLimits
    cliRunBudgets (cliRunSemD2c_placed X W) scopeIn (w1t_sendBytesEnvOf SendEnv)
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
    hh
    (w1Inner_of_sendCoins_at A ghFixed W hF SendEnv hSend427 hSendEmpty
      hSend_ptr_congr hGSpqr hh hAesEnc hSessKit hIdKit h547)
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
    (fun _ _ _ _ hf he => ⟨hf.1, he⟩) stk h1 h2

private theorem seqEnv_congr {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂) : SeqEnv P₁ Q₁ = SeqEnv P₂ Q₂ :=
  hP ▸ hQ ▸ rfl

/-- Under `hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`, the inner
`w1t_SendGuardedBytesEnv`-instantiated `CliEncryptSlotEnv` coincides pointwise with
`w1t_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets x`. -/
theorem slotEnv_eq_of_peer [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (x : EncGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
        (w1t_SendGuardedBytesEnv W.C.F W.Q.K)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x =
      w1t_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets x := by
  funext evs
  have hsend_eq_on (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState) :
      w1t_SendGuardedBytesEnv W.C.F W.Q.K otr.pqrState =
        w1t_SendTightBytesEnv W.C.F W.Q.K otr.pqrState := by
    funext rest evs0
    exact propext ⟨fun h => h hSt, fun h _ => h⟩
  have hotr_core (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState)
      (ptext : List (BitVec 8)) (loc : Option AddrGhost) (rem : AddrGhost)
      (rest : List (BitVec 8)) :
      OtrEncryptCoreEnv W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (w1t_SendGuardedBytesEnv W.C.F W.Q.K) uuidTryParse otr ptext loc rem rest =
        OtrEncryptCoreEnv W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (w1t_SendTightBytesEnv W.C.F W.Q.K) uuidTryParse otr ptext loc rem rest := by
    unfold OtrEncryptCoreEnv
    exact seqEnv_congr (congrFun (hsend_eq_on otr hSt) rest) rfl
  have hfrom_otr (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8)))
      (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8)))
      (hScAt : (w1SessKitPlaced A.repAlloc cliRunBudgets x.F x.peer).ScopeAt
        scopeKit StoresGhost.opened.sessions (w1EncGhost x).rem.val r)
      (hcur : r.currentSession = some sess)
      (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendGuardedBytesEnv W.C.F W.Q.K)
          uuidTryParse
          (w1SessKitPlaced A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
            (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
            (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendTightBytesEnv W.C.F W.Q.K)
          uuidTryParse
          (w1SessKitPlaced A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
            (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
            (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken := by
    have hrem : (w1EncGhost x).rem.val = x.peer.val := rfl
    have hTop :=
      LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas.topStateTight_of_cliSessionStoreSpecPlaced_fromSessionState
        (A := A.repAlloc) (F := W.C.F) (K := W.Q.K) (files := x.F)
        (pathOk := cliWrOk) (peer := x.peer)
        (s1 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed)
        (s2 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed cliRunBudgets.readFile)
        (s3 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed)
        (s4 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX)
        hScAt hcur hotr (hrem.symm ▸ hPeer)
    have hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState := Or.inr hTop
    funext evs1
    unfold
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
    rw [hotr_core otr hSt, hotr_core otr hSt]
  unfold w1t_cliEncryptBinaryKitSlotEnvExact CliEncryptSlotEnv
    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.WithStoresEncEnv
  dsimp only
  refine propext ⟨fun h _ => ?_, fun h => ?_⟩
  · rcases h with h0 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl h0
    · refine SeqEnv.append h1 ?_
      rcases h2 with hf | hstr | hseq
      · exact Or.inl hf
      · exact Or.inr (Or.inl hstr)
      · refine Or.inr (Or.inr ?_)
        rcases hseq with hf | ⟨ea, eb, rfl, ha, hb⟩
        · exact Or.inl hf
        · refine SeqEnv.append ha ?_
          rcases hb with hf | ⟨r, sess, otr, taken, hScAt, hcur, hotr, hfo⟩
          · exact Or.inl hf
          · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcur, hotr, ?_⟩
            rwa [← hfrom_otr r sess otr taken hScAt hcur hotr]
  · have h' := h hPeer
    rcases h' with h0 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl h0
    · refine SeqEnv.append h1 ?_
      rcases h2 with hf | hstr | hseq
      · exact Or.inl hf
      · exact Or.inr (Or.inl hstr)
      · refine Or.inr (Or.inr ?_)
        rcases hseq with hf | ⟨ea, eb, rfl, ha, hb⟩
        · exact Or.inl hf
        · refine SeqEnv.append ha ?_
          rcases hb with hf | ⟨r, sess, otr, taken, hScAt, hcur, hotr, hfo⟩
          · exact Or.inl hf
          · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcur, hotr, ?_⟩
            rwa [hfrom_otr r sess otr taken hScAt hcur hotr]

/-- `{M} {A}`-generic `encrypt` slot producer parameterized by Block `325`'s
`DecodeStatePlacedOkOfEnv`, `SessionOnlyKitPlacedOkSE A`, and `IdentityStoreKitPlacedOkI A`. -/
theorem hole3_w1_inner_of_decodeState_at
    {elfBytes : List (BitVec 8)}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ghFixed : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks M A cliBudgetLimits ghFixed)
    (hh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunHooksPlaced A cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hAesEnc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesEncSym
        (withLsRet (aesEncBudgetSpec W.C.E M A cliBudgetLimits)))
    (hHmac :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
        (withLsRet (libcruxHmacBudgetSpec W.C.F M A cliBudgetLimits)))
    (hSessKit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (F : FsFiles) (peer : AddrGhost),
        SessionOnlyKitPlacedOkSE A cliBudgetLimits
          (w1SessKitPlaced A.repAlloc cliRunBudgets F peer)
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
          scopeKit encodeRecord (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hIdKit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (F : FsFiles) (peer : AddrGhost),
        IdentityStoreKitPlacedOkI A cliBudgetLimits
          (w1IdKitPlaced A.repAlloc cliRunBudgets F peer)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets F peer)
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (h547 : mpl.base 547 ≠ 0#64)
    (h325 : @DecodeStatePlacedOkOfEnv (libsignalPlacementOf mpl hblk hext_nodup) M
      canonicalV1InnerHeap A cliBudgetLimits
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) :
    letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (encSlotSpecPlaced A cliBudgetLimits
        (w1t_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
  letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
  have hSend427 := spqrSendCoins_placed_ok_guarded_of_decodeState_at
    A cliBudgetLimits mmpl ghFixed W hF hK hGSpqr hHmac h325
  have hSlot := hole3_w1_inner_of_sendCoins_at A ghFixed X W hF
    (w1t_SendGuardedEnv W.C.F W.Q.K) hSend427
    (w1t_sendGuardedBytes_empty W.C.F W.Q.K)
    (fun _ _ => Iff.rfl)
    hGSpqr hh hAesEnc hSessKit hIdKit h547
  intro stk h1 h2
  have hok := hSlot stk h1 h2
  exact subroutine_ok_mono hok
    (fun (x, st) _ _ hpre => by
      dsimp only [mkSlot, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        encSlotSpecPlaced] at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hfit⟩ => by
        by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
        · have heq : w1t_sendBytesEnvOf (w1t_SendGuardedEnv W.C.F W.Q.K) =
              w1t_SendGuardedBytesEnv W.C.F W.Q.K := rfl
          rw [heq, slotEnv_eq_of_peer W A x hPeer]
          exact ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hfit⟩
        · exact False.elim
            (w1t_s427_not_fitsEnv_of_univ (fun _ hp => False.elim (hPeer hp)) hfit))
    (fun (x, st) _ _ _ hpost => by
      dsimp only [mkSlot, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        encSlotSpecPlaced] at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine Entails.sepExists_mono fun g' => ?_
      refine Entails.sepExists_mono fun e => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hevs, htr, hout, hser⟩ => by
        by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
        · have heq : w1t_sendBytesEnvOf (w1t_SendGuardedEnv W.C.F W.Q.K) =
              w1t_SendGuardedBytesEnv W.C.F W.Q.K := rfl
          rw [heq, slotEnv_eq_of_peer W A x hPeer] at hevs
          exact ⟨hevs, htr, hout, hser⟩
        · exact ⟨fun hp => False.elim (hPeer hp), htr, hout, hser⟩)
    (fun _ _ _ _ hp => hp)

end SlotAt

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Cal
