/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Tight `fineCostModel` Credit and Group Specifications for SPQR `spqr::send::<Coins>`

Combines the tight `spqr::send` sub-phase credit bounds (`SpqrSendPeakSpec`), `spqr::recv` credit
and group instances (`SpqrRecvC09aWire`), and `FineScale` slot-group accounting (`spqrSendTightGroupS =
281,542,656` = `4,296` groups across `≤ 1,432` non-free operations) into closed `fineCostModel`
credit, group, and `1 GiB` `FitsEnv` specs for `spqr::send::<Coins>` and `StoresGhost.opened`
encrypt.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB PqRatchetState States V1State VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainSendKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (otrEncryptStepEnv_groupSpec spqrNonFreeCount_eq withStoresEncTightEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec (w1CliOpenedCustomSendCum w1CliOpenedCustomSendLive w1CliOpenedCustomSendMaxReq w1CliOpenedCustomSendPeak w1CliOpenedCustomSend_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSmallStorePollEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (c09aStatesRecvTightCreditSpec_inst c09aStatesRecvTightGroupSpec_inst
   spqrRecvParts_c07_128_c09a_phaseGroupSpec_tight
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
   spqrRecvParts_c07_c09a_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendC07TightEnv SpqrSendTightCapEnv SpqrSendTightLargeEnv
   spqrSendLarge_nonFreeCount_le_tight spqrSendParts_c07_fineCredit_le_tight
   spqrSendParts_c07_nonFreeCount_le spqrSendParts_c07_phaseCreditSpec_tight
   spqrSendParts_c07_phaseCreditSpec_tight_largeEncode spqrSendTight79236DeltaCum
   spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightFineCreditCap spqrSendTightLargeDeltaCum spqrSendTightMaxReq
   spqrSend_evalLog_footprint_le_tight spqrSend_fineCredit_le_tight
   spqrSend_nonFreeCount_le_tight spqrSend_phaseCreditSpec_tight
   spqrSend_phaseCreditSpec_tight_largeEncode)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
  (SpqrSendTightDomain SpqrSendTightDomain707)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec (OtrEncryptStepEnv WithStoresEncTightEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak (otrAfterNone otrAfterSome)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

/-! ## `spqr::send` and `spqr::recv` Tight Re-Exports -/

export SpqrSendPeakSpec
  (SpqrSendTightCapEnv SpqrSendTightLargeEnv SpqrSendC07TightEnv spqrSendTightDeltaCum)
export SpqrSendPeakSpec
  (spqrSendTightLargeDeltaCum spqrSendTight79236DeltaCum spqrSendTightDeltaLive
   spqrSendTightDeltaPeak)
export SpqrSendPeakSpec
  (spqrSendTightMaxReq spqrSendTightFineCreditCap spqrSend_phaseCreditSpec_tight
   spqrSend_phaseCreditSpec_tight_largeEncode)
export SpqrSendPeakSpec
  (spqrSendParts_c07_phaseCreditSpec_tight spqrSendParts_c07_phaseCreditSpec_tight_largeEncode
   spqrSend_fineCredit_le_tight spqrSend_evalLog_footprint_le_tight)
export SpqrSendPeakSpec
  (spqrSendParts_c07_fineCredit_le_tight)
export SpqrSendRodataCaps
  (SpqrSendTightDomain SpqrSendTightDomain707)

export SpqrRecvC09aWire
  (c09aStatesRecvTightCreditSpec_inst c09aStatesRecvTightGroupSpec_inst
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight spqrRecvParts_c07_c09a_phaseGroupSpec_tight)
export SpqrRecvC09aWire
  (spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
   spqrRecvParts_c07_128_c09a_phaseGroupSpec_tight)

/-! ## `PhaseGroupSpec` and `1 GiB` `FitsEnv` Bounds for `spqr::send` -/

/-- Upper bound on non-`.free` allocator operations across all 10 `spqr::send` sub-phases (`1,432`).
-/
@[expose] def spqrSendTightMaxNonFree : Nat := 1432

/-- `FineScale`-scaled slot-group bound (`3 * FineScale * 1432 = 281,542,656` = `4,296` groups) for tight `spqr::send` envelopes.
-/
@[expose] def spqrSendTightGroupS : Nat := 3 * FineScale * spqrSendTightMaxNonFree

theorem spqrSendTightGroupS_val :
    spqrSendTightGroupS = 281542656 ∧
    (spqrSendTightGroupS + FineScale - 1) / FineScale = 4296 := by
  decide

theorem spqrSendTightCap_nonFreeBound (stBytes ptext : Bytes) :
    NonFreeBound (SpqrSendTightCapEnv stBytes ptext) spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSend_nonFreeCount_le_tight h

theorem spqrSendTightCap_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (stBytes ptext : Bytes) :
    PhaseGroupSpec M (SpqrSendTightCapEnv stBytes ptext) spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendTightCap_nonFreeBound stBytes ptext)

theorem spqrSendTightLarge_nonFreeBound (stBytes ptext : Bytes) :
    NonFreeBound (SpqrSendTightLargeEnv stBytes ptext) spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSendLarge_nonFreeCount_le_tight h

theorem spqrSendTightLarge_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (stBytes ptext : Bytes) :
    PhaseGroupSpec M (SpqrSendTightLargeEnv stBytes ptext) spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendTightLarge_nonFreeBound stBytes ptext)

theorem spqrSendParts_c07_nonFreeBound (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt) :
    NonFreeBound
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSendParts_c07_nonFreeCount_le F dom h

theorem spqrSendParts_c07_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt) :
    PhaseGroupSpec M
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendParts_c07_nonFreeBound F dom)

/-- `FitsEnv fineCostModel` bound for `SpqrSendTightCapEnv` under a `1 GiB` (`< 2 ^ 30`) budget. -/
theorem spqrSendTightCap_fitsEnv_1GiB
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes)
    (hChain : ValidChainParams stBytes) :
    FitsEnv fineCostModel lim fineCostModel.init (SpqrSendTightCapEnv stBytes ptext) := by
  have hram0 :
      cliDecoupledRamNeed cliDefaultStaticBytes
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ cliOneGiB := by
    decide
  have hva0 :
      cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ 2 ^ 48 := by
    decide
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (spqrSend_phaseCreditSpec_tight (ptext := ptext) hPts hChain)
    (spqrSendTightCap_groupSpec fineCostModel stBytes ptext)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (by decide)
    henf hram hva

theorem spqrSendTightCap_fitsEnv_cliBudgetLimits
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes)
    (hChain : ValidChainParams stBytes) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (SpqrSendTightCapEnv stBytes ptext) :=
  spqrSendTightCap_fitsEnv_1GiB rfl (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hPts hChain

/-! ## `StoresGhost.opened` Encrypt Tight Credit and Group Corollaries -/

@[expose] def w1CliOpenedTightSendCum
    (ptextLen nameCum fileCap deserCum c_sig c_pk c_st : Nat) : Nat :=
  w1CliOpenedCustomSendCum fineCostModel spqrSendTightDeltaCum
    ptextLen nameCum fileCap deserCum c_sig c_pk c_st

@[expose] def w1CliOpenedTightSendLive
    (ptextLen fileCap deserLive l_sig l_pk l_st : Nat) : Nat :=
  w1CliOpenedCustomSendLive fineCostModel spqrSendTightDeltaLive
    ptextLen fileCap deserLive l_sig l_pk l_st

@[expose] def w1CliOpenedTightSendPeak
    (ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st : Nat) : Nat :=
  w1CliOpenedCustomSendPeak fineCostModel
    spqrSendTightDeltaLive spqrSendTightDeltaPeak
    ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st

@[expose] def w1CliOpenedTightSendMaxReq
    (ptextLen fileCap deserMaxReq r_sig r_pk r_st : Nat) : Nat :=
  w1CliOpenedCustomSendMaxReq spqrSendTightMaxReq
    ptextLen fileCap deserMaxReq r_sig r_pk r_st

theorem w1CliOpenedTightSend_live_le_peak
    {ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk l_st p_st : Nat}
    (hSig : l_sig ≤ p_sig)
    (hPk : l_pk ≤ p_pk)
    (hSt : l_st ≤ p_st) :
    w1CliOpenedTightSendLive ptextLen fileCap deserLive l_sig l_pk l_st ≤
      w1CliOpenedTightSendPeak ptextLen fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st :=
  w1CliOpenedCustomSend_live_le_peak fineCostModel hSig hPk hSt

private theorem fineSmallAlloc_le_of_le_40 {nameCum : Nat} (hNameCum : 9619 ≤ nameCum) :
    ∀ n, 0 < n → n ≤ 40 →
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallAllocCost
        fineCostModel n ≤ nameCum := by
  intro n _ hn40
  have hsm :
      n ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
        fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    omega
  have haff := fineCostModel_modelHyps.smallAlloc_le hsm
  omega

end LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
