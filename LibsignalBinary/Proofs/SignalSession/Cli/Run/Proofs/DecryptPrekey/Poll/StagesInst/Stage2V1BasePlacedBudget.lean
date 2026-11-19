/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOkPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Base Callees and Bounds

Generalizes placed Stage P2 `FsAt` lifts, `ResponderPqxdhPlacedHookContracts`, and Stage P2 callee
projections (`drop_spe2`, `drop_session_structure`, `<PublicKey>::serialize`,
`<PrivateKey>::calculate_agreement`, `hkdfExtract`, and `hkdfExpandMultiInfo`) to
`RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement
  lsBlackBoxU8Sym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
  ls_subroutine_ok_of_block
  subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP2EnvOk stageP2Quiet stageP2V1CallStack
)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives blockLevelPrims modelPrims u8Vec vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Primitives StructuralPrims fitBv8 kyberDecapsOutBytes
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  PrimitivesMatchCrypto lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym
  ofSignalPqxdhPrimitives toSignalPqxdhPrimitives toSignalPqxdhPrimitives_isCanonicalRef_eq
  u8Vec_toList_of_length
)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec TraceFsSound speErrAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (IdentitySelfStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks diffieHellmanSpec lsMemsetSym withLsCodeRoLoaded zeroizeSecretSpec
)
open CryptoVerification.LibsignalTripleRatchet.Getters (withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys (
  lsDhSym lsRustAllocSym lsSharedDropSym lsStaticDropSym
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsBlackBoxSym)
open CryptoVerification.SignalSession.Cli.RunCompose (decResAt)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_extra_some
  cliGhostExterns_memcpy_some cliGhostExterns_memset_some cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  DpKitStk cliKitStk cliModelPrims_matchCrypto cliModelPrims_structural cliPollIdKitPlaced
  cliPollKpkKitPlaced cliPollKpkPlaced_quiet cliPollPkKitPlaced cliPollPkPlaced_quiet
  cliPollSelfKitPlaced cliPollSelfPlaced_quiet cliPollSpkKitPlaced cliPollSpkPlaced_quiet
  dpClosSubStack dpPollProgPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.Variant SepProp
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_cl_ok_at drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (
  PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
  handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (
  drop_spe2_placed_ok_at
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  kyberDecapsPlacedStack kyberDecapsStubSpecAt
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget (
  PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk
  pqxdhCalculateAgreement_placed_frozen_ok_of_block pqxdhCalculateAgreement_placed_ok_of_block
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  createChain_placed_ok_of_block createChain_placed_ok_x_of_block
  handshakeKeysDerive_placed_ok_of_block handshakeKeysDerive_placed_vm_ok_of_block
  kyberDecapsStubBudgetSpec pqxdhHkdfExpandMultiInfo_placed_ok pqxdhHkdfExtract_placed_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (kemDecapsAtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202 (
  IsCanonicalCurveSound dalekHookStack dalekMontToEdExtSpec dalekTorsionFreeExtSpec
  isCanonicalCurveSound_modelPrims_dalekPrimsRef modelPrims_isCanonicalEC_eq_isCanonicalRef
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  extract_withLsRet intro_withLsRet withLsRet
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_sessionMemsetRegion_budget_sat cliGhostExterns_blackBoxSat_budget_sat
  cliGhostExterns_sharedSecretDrop_budget_sat cliGhostExterns_staticSecretDrop_budget_sat
  cliGhostExterns_toEdwards_budget_sat cliGhostExterns_torsionFree_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  hookSat_cliGhostExterns_of_extraOk
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec noAllocShim_hookOk publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok public_key_serialize_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)

/-! ## 1. Placed Call-Stack Bound & `FsAt` Lift -/

/-- Placed `stageP2V1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits. -/
theorem stageP2V1CallStack_le_subStack_placed {A : RustAlloc} [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2V1CallStack_le_subStack_placed
    F0 peer spkId kpkId opkIdWord kbk B

/-- Generic `TraceFsSound` lift from `FsAt (fun f => f = F0) True` to placed
`FsAt (stageP2EnvOk...) (stageP2Quiet...)` at any representation allocator `A_r : RustAlloc`. -/
theorem cliPollStageP2_fsAt_of_hook_placed {A_r : RustAlloc}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} [LibsignalPlacement]
    (hfsHook : TraceFsSound (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A_r F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A_r F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A_r F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A_r F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A_r F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A_r F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s := by
  rcases hfs with hall | ⟨_, _, hf⟩
  · exact .inl fun f => ⟨hall f, hall f, hall f, hall f⟩
  · exact .inr
      ⟨⟨cliPollSpkPlaced_quiet F0 spkId (cliKitStk B),
        cliPollKpkPlaced_quiet F0 kpkId spkId kbk (cliKitStk B),
        cliPollPkPlaced_quiet F0 opkIdWord (cliKitStk B),
        cliPollSelfPlaced_quiet F0 peer (cliKitStk B)⟩,
       hfsHook, ⟨hf, hf, hf, hf⟩⟩

/-- Lift `FsAt (fun f => f = F0) True` + `hh.fs` (`SkeletonPlacedBudget.RunHooksPlaced`) to placed
`FsAt (stageP2EnvOk...) (stageP2Quiet...)` at `A.repAlloc`. -/
theorem cliPollStageP2_fsAt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  cliPollStageP2_fsAt_of_hook_placed
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518)
    F0 peer spkId kpkId opkIdWord kbk B hfs

/-- Variant of `cliPollStageP2_fsAt_placed` accepting `ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem cliPollStageP2_fsAt_stages_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  cliPollStageP2_fsAt_of_hook_placed
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518)
    F0 peer spkId kpkId opkIdWord kbk B hfs

/-! ## 2. Placed Error-Payload Entailments (`b := 0#64`) -/

/-- Placed `get_signed_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollSpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (spkId : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSpkKitPlaced A F0 spkId σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSpkKitPlaced A F0 spkId σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSpk_getErr_entails_decResAt_anyHeap_placed
    A F0 spkId σ outPtr e err

/-- Placed `get_kyber_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollKpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollKpk_getErr_entails_decResAt_anyHeap_placed
    A F0 kpkId spkId kbk σ outPtr e err

/-- Placed `get_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollPk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (opkIdWord : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollPkKitPlaced A F0 opkIdWord σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollPkKitPlaced A F0 opkIdWord σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollPk_getErr_entails_decResAt_anyHeap_placed
    A F0 opkIdWord σ outPtr e err

/-- Placed `get_identity_key_pair` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_kpErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).KpErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).kpErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_kpErr_entails_decResAt_err_placed
    A F0 peer σ outPtr e err

/-- Placed `get_local_registration_id` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_regIdErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).RegIdErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).regIdErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_regIdErr_entails_decResAt_err_placed
    A F0 peer σ outPtr e err

/-! ## 3. Budget-Threaded `PqxdhPlacedHookContracts` at `cliGhostExterns` -/

/-- `HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`g.memset = some memsetHook`, `g.memcpy = some memcpyHook`, and `g.extra.lookup lsCompress256Sym`. -/
theorem instHkdfPlacedHooks_cli_poll (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    (hMs : g.memset = some memsetHook)
    (hMc : g.memcpy = some memcpyHook)
    (hCp : g.extra.lookup CryptoVerification.SignalSession.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook W.C.F)) :
    HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  memset := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hMs
  memcpy := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hMc
  compress256 := cliGhostExterns_extra_some g (cliExternsPlaced mmpl W) hCp

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- `noAllocShimBudgetSpec` `HookSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliExternsPlaced_noAllocShimBudget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
    noAllocShim_hookOk⟩

/-- `withLsRet` + `VmPreserved` + `1808`-B `HookSat` for `x25519_dalek::diffie_hellman` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `ExtraSpecOk g` and `W.C.X = x25519Ref`. -/
theorem cliGhostExterns_dh1808_budget_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsDhSym
      (withLsRet (withVmPreserved
        (CryptoVerification.LibsignalTripleRatchet.withStack (diffieHellmanSpec W.C.X) 1808))) :=
  hookSat_cliGhostExterns_of_extraOk g (cliExternsPlaced mmpl W) hG.extraOk
    fun _ _ hRow => by rw [hX]; exact hRow.diffieHellmanWithStack_budget_ok 1808

/-- `withLsRet` + `VmPreserved` + `36864`-B `HookSat` for `kyber::decapsulate` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `ExtraSpecOk g` and
`W.Q.decaps = kyber1024DecapsVec`. -/
theorem cliGhostExterns_kemDecaps_budget_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (X : UnreachedPqxdhPrimitives) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsKyberDecapsSym
      (kyberDecapsStubBudgetSpec (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) := by
  have hsat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsKyberDecapsSym
      (withLsRet (withVmPreserved (kemDecapsAtSpec kyberDecapsPlacedStack W.Q))) :=
    hookSat_cliGhostExterns_of_extraOk g (cliExternsPlaced mmpl W) hG.extraOk
      fun _ _ hRow =>
        hRow.kemDecaps_budget_ok kyberDecapsPlacedStack (by decide) (by decide) hDecaps
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun call R s0 hrun hpre hsp => ?_⟩
  obtain ⟨hlr, hpre0⟩ := extract_withLsRet hpre
  dsimp only [withVmPreserved, kyberDecapsStubSpecAt] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx8, hsk_len, hct_len, _⟩, hmem⟩
  let skVec := u8Vec 3168 call.sk3168
  let ctVec := u8Vec 1568 call.ct1568
  have hsk_list : skVec.toList = CryptoVerification.E2E.Pqxdh.Initiator.bytesToBv8 call.sk3168 :=
    u8Vec_toList_of_length hsk_len
  have hct_list : ctVec.toList = CryptoVerification.E2E.Pqxdh.Initiator.bytesToBv8 call.ct1568 :=
    u8Vec_toList_of_length hct_len
  have hpre_x : s0.mem ⊨
      (withLsRet (withVmPreserved (kemDecapsAtSpec kyberDecapsPlacedStack W.Q))).pre
        (call.skPtr, skVec, call.ctPtr, ctVec, call.outPtr) s0 ∗ R := by
    refine intro_withLsRet hlr ?_
    dsimp only [withVmPreserved, kemDecapsAtSpec,
      LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack]
    rw [hsk_list, hct_list, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl⟩
  rcases hok (call.skPtr, skVec, call.ctPtr, ctVec, call.outPtr) R s0 hrun hpre_x hsp with
    ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩⟩
  · refine ⟨hkeep, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsRet, withVmPreserved, kemDecapsAtSpec,
      LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
      kyberDecapsStubBudgetSpec,
      E2E.Pqxdh.ResponderCore.AcceptBudget.kyberDecapsStubBudgetSpec,
      E2E.Pqxdh.ResponderCore.AcceptBudget.kyberDecapsStubSpecAt] at hpost ⊢
    have hdec : (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)).kemDecaps
        call.sk3168 call.ct1568 = some (vecU8 (W.Q.decaps skVec ctVec)) := by
      simp only [ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
        SignalPqxdh.kyberCtLen, hct_len, beq_self_eq_true, ↓reduceIte]
      rfl
    have hout : fitBv8 32
        (kyberDecapsOutBytes (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          call.sk3168 call.ct1568) = (W.Q.decaps skVec ctVec).toList := by
      unfold kyberDecapsOutBytes fitBv8
      rw [hdec, Option.getD_some, CryptoVerification.E2E.Pqxdh.Initiator.e2e_bytesToBv8_vecU8]
      have hlen32 : (W.Q.decaps skVec ctVec).toList.length = 32 :=
        (W.Q.decaps skVec ctVec).toList_length
      rw [hlen32, List.take_of_length_le (by rw [hlen32]), Nat.sub_self, List.replicate_zero,
        List.append_nil]
    rw [hsk_list, hct_list] at hpost
    rw [hout]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `IsCanonicalCurveSound` for `toSignalPqxdhPrimitives (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))`
using the reference Curve25519/Dalek primitives (`dalekPrimsRef`). -/
theorem cliModelPrims_curveSound (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    IsCanonicalCurveSound
      (toSignalPqxdhPrimitives (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) := by
  intro keyBytes hlen hb31 hsc
  have h1 := (cliModelPrims_structural X W).isCanonical_eq_isCanonicalRef keyBytes
  have h2 := toSignalPqxdhPrimitives_isCanonicalRef_eq
    (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
    (cliModelPrims_structural X W).montToEd_len keyBytes
  have h3 : (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)).isCanonical keyBytes =
      SignalPqxdh.isCanonicalRef (modelPrims X ⟨W.C, W.Q⟩) keyBytes :=
    modelPrims_isCanonicalEC_eq_isCanonicalRef X ⟨W.C, W.Q⟩ keyBytes
  exact h2.trans (h1.symm.trans (h3.trans
    (isCanonicalCurveSound_modelPrims_dalekPrimsRef X W.C W.Q keyBytes hlen hb31 hsc)))

/-- Combined budget-threaded external-hook contract bundle for `ResponderCore` using the in-image
extended-Edwards contracts (`dalekMontToEdExtSpec` / `dalekTorsionFreeExtSpec`) at `dalekHookStack`. -/
structure ResponderPqxdhPlacedHookContracts [LibsignalPlacement] (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooks C.F H
  dh               : HookSat H lsDhSym
    (withLsRet (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.withStack (diffieHellmanSpec C.X) 1808)))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  curveSound       : IsCanonicalCurveSound (toSignalPqxdhPrimitives P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym
    (withLsRet (withVmPreserved (dalekMontToEdExtSpec dalekHookStack)))
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym
    (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec dalekHookStack)))

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok hP hi

/-- `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok hP hi

/-- `<HandshakeKeys>::derive` (`VmPreserved`, Block `59`) on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_vm_ok_of_block hWF hP hi

/-- `<HandshakeKeys>::derive` (`RustCliAllocBudget`, Block `59`) on any caller
block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_ok_of_block hWF hP hi

/-- `<RootKey>::create_chain` (Block `40`) on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- `<RootKey>::create_chain` at `createChainStackX` (Block `40`) on any caller
block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_x_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- `HkdfPlacedHooksExactSat`-widened external-hook contract bundle for `ResponderCore`, replacing
`HkdfPlacedHooks C.F H` with `HkdfPlacedHooksExactSat C.F H` plus
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec` (derivable from `CliGhostAllocHooks`). -/
structure ResponderPqxdhPlacedHookContractsExactSat [LibsignalPlacement]
    (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat C.F H
  memsetBudget     : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  dh               : HookSat H lsDhSym
    (withLsRet (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.withStack (diffieHellmanSpec C.X) 1808)))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : HookSat H lsBlackBoxSym blackBoxSpecSat
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  curveSound       : IsCanonicalCurveSound (toSignalPqxdhPrimitives P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym
    (withLsRet (withVmPreserved (dalekMontToEdExtSpec dalekHookStack)))
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym
    (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec dalekHookStack)))

/-- Bundle projection: `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat.pqxdhCalculateAgreement_placed_ok_of_block_sat
    hP hH.dh hH.sharedDrop hH.blackBox hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat.pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat
    hP hH.dh hH.sharedDrop hH.blackBox hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ := hH.hkdf
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    hH.memsetBudget (F := C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExtract_placed_ok_sat
    hP hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ := hH.hkdf
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    hH.memsetBudget (F := C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExpandMultiInfo_placed_ok_sat
    hP hi

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `W.C.F = sha256Compress`, and `HookSat` contracts for `alloc`,
`dealloc`, and `noAllocShim`. -/
theorem cliResponderPqxdhHookContractsPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  refine
    { hkdf :=
        LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks
          (mmpl := mmpl) hG hF
      memsetBudget :=
        cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG
      dh := cliGhostExterns_dh1808_budget_sat mmpl g W hG hX
      sharedDrop := cliGhostExterns_sharedSecretDrop_budget_sat g (cliExternsPlaced mmpl W)
        hG.extraOk
      staticDrop := cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W)
        hG.extraOk
      blackBox := cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
      noAllocShim := hnoAllocShim
      alloc := halloc
      dealloc := hdealloc
      kyberDecaps := cliGhostExterns_kemDecaps_budget_sat mmpl g W hG hDecaps X
      curveSound := cliModelPrims_curveSound X W
      dalekMontToEd := cliGhostExterns_toEdwards_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
      dalekTorsionFree := cliGhostExterns_torsionFree_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk }

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `W.C.F = sha256Compress`, `hX`, and `hDecaps`. -/
theorem cliResponderPqxdhHookContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat X mmpl g W hG hF hX hDecaps
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `W.C.F = sha256Compress`, `hX`, `hDecaps`, and
`SkeletonPlacedBudget.RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))`. -/
theorem cliResponderPqxdhHookContractsPlaced_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat X mmpl g W hG hF hX hDecaps
    hh.codecHooks.alloc hh.codecHooks.dealloc
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)

/-! ## 4. Placed Budget Stage P2 Callee Projections at `cliGhostExterns` -/

/-- `drop_spe2` (`dropSpeSpec M A lim`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `hdealloc`. -/
theorem cliDropSpe2_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :=
  drop_spe2_placed_ok_at hdealloc hi

/-- `drop_spe2` (`dropSpeSpec M A lim`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliDropSpe2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :=
  cliDropSpe2_placed_ok_of_dealloc mmpl g W (cliExternsPlaced_dealloc_budget_sat mmpl g W hG) hi

/-- `drop_session_structure` (`dropSessionStructureLocal2Spec M A lim`) on any caller block
`i < 619` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `hdealloc`. -/
theorem cliDropSessionStructure_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at hdealloc hi

/-- `withLsCl` variant of `cliDropSessionStructure_placed_ok_of_dealloc`. -/
theorem cliDropSessionStructure_placed_cl_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCl lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_cl_ok_at hdealloc hi

/-- `drop_session_structure` (`dropSessionStructureLocal2Spec M A lim`) on any caller block
`i < 619` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliDropSessionStructure_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  cliDropSessionStructure_placed_ok_of_dealloc mmpl g W
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG) hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc`. -/
theorem cliPublicKeySerialize_placed_ok_at_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        hnoAllocShim
        halloc))
    hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpecX M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc`. -/
theorem cliPublicKeySerialize_placed_ok_x_at_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok_x
        hnoAllocShim
        halloc))
    hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliPublicKeySerialize_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  cliPublicKeySerialize_placed_ok_at_of_alloc mmpl g W
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) hi

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks`, `hX`, `halloc`, and `hdealloc`. -/
theorem cliPqxdhCalculateAgreement_placed_ok_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (_hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat.pqxdhCalculateAgreement_placed_ok_of_block_sat
    (cliModelPrims_matchCrypto X W)
    (cliGhostExterns_dh1808_budget_sat mmpl g W hG hX)
    (cliGhostExterns_sharedSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    hnoAllocShim
    halloc
    (cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    hi

/-- `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks`, `hX`, `halloc`, and `hdealloc`. -/
theorem cliPqxdhCalculateAgreement_frozen_placed_ok_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (_hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat.pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat
    (cliModelPrims_matchCrypto X W)
    (cliGhostExterns_dh1808_budget_sat mmpl g W hG hX)
    (cliGhostExterns_sharedSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    hnoAllocShim
    halloc
    (cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    hi

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g` and `hX`. -/
theorem cliPqxdhCalculateAgreement_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  cliPqxdhCalculateAgreement_placed_ok_of_hookSat X mmpl g W hG hX
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)
    hi

/-- `PqxdhHkdfExtractPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g` and
`W.C.F = sha256Compress`. -/
theorem cliPqxdhHkdfExtract_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks
    (mmpl := mmpl) hG hF
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG) (F := W.C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExtract_placed_ok_sat
    (cliModelPrims_matchCrypto X W) hi

/-- `PqxdhHkdfExpandMultiInfoPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g` and
`W.C.F = sha256Compress`. -/
theorem cliPqxdhHkdfExpandMultiInfo_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks
    (mmpl := mmpl) hG hF
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG) (F := W.C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExpandMultiInfo_placed_ok_sat
    (cliModelPrims_matchCrypto X W) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
