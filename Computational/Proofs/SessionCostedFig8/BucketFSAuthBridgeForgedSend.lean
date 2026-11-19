/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedInr
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSendRec
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShort
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSend

public section

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.PRFPRNG (prngSMCodec)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (MakesAtMostQueries RatchetSenderState RatchetReceiverState
  ReceiveResult withPub transmitQuery deliverQuery injectQuery corruptSenderQuery fromAEADPRG)
open _root_.CryptoGames.FSAEAD.Thm5 (hp hInit HSt DG SpecialOps transmitHWith deliverH injectH
  corruptSenderH)
open _root_.CryptoGames.SM (GameState Pos Record RecvResult authLosingConditionsAvoided healedBy
  lastLeakGuessAdmissible ltOpt maxOpt)
open _root_.CryptoGames.SM.Engine (Ctx Hooks EState VP vSend vSendStep1 vSend_eq_bind vRecv
  vRecvStep1 vRecv_eq_bind deliverE injectE commitE abortE liftH run_liftH_bind HooksVRInv
  SMEngineInv SMVRInv Policy transmitE challE corrE coinsE implE implE_inv implE_vrInv)
open _root_.CryptoGames.SM.Construction (Header PartyState mkParties realParty SchemeAdversary
  healEpoch sampleT fsaeadMultiHeaderAdIface fsClamp FSMultiSpec FSMultiBook)
open _root_.CryptoGames.SM.Construction.AuthL11 (nilSpec lImpl)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart
  LibsignalCiphertextWithSalt32 dummyKey lChainPRG lAeadR lIdeal lFS lPubOf GuardedFSInjectShort
  lAead)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps rustLenBound)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit sessOffRange
  multiSessSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionWire (sessQueryAt)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsCostedRedsInst fsAuthCompBoundMix
  fsAuthPrgMix fsAuthSWMix fsAuthCompBoundWith macForgeryTerm ratchetCostBudget GRedBounded
  signalRoundTripShort_proto)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv multiSessPubToAD
  MultiSessPubFsAdv TwoModeMultiSessBounds RouterAdvCompat)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_isQueryBoundP_sessQueryAt)
open _root_.ReductionDsl (CostedReduction fsaeadHeaderIface fig8SmCodec atomicFig8Ops bits
  reductionSizeBudget isGameQuery)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos bits_succ_le)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (compSizeW ckaOpS ckaSampS)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiAtomic
  compileFsMultiAtomic_gRedBounded compileFsMultiAtomic_routerAdvCompat
  compileFsMultiAtomic_isQueryBoundP compileFsMultiAtomic_makesAtMostQueries
  compileFsMultiAtomic_encMsgsOk compileFsMultiAtomic_guardedFSInjectShort fsMultiQueryC
  fsMultiQueryS)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb multiSessEndWinProb
  bucket_four_branch_fs_le)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg
  LocalBucketAuthState isHonestHdrLocalBucket hooksLocalBucketAuth hooksLocalBucketAuthForgedHdr
  implLocalBucketAuthGen)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (redFSAuthMultiBucketProg
  redFSAuthMultiBucketProg_totalQueries localAuthBucketMain localAuthBucketForgedHdr
  localAuthBucketMainPar localAuthBucketForgedHdrPar localAuthBucketMain_le_par_false_add_true
  localAuthBucketForgedHdr_le_par_false_add_true)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  FSMultiBucketAuthEState liftFSMultiBucket lookupMultiBucketF regSessMultiBucket
  regSessOptMultiBucket validGuessBucketParAuth rootFSMultiBucketAuth isHonestHdrMultiBucket
  hooksFSMultiBucketAuth initFSMultiBucketAuth implFSMultiBucketAuth redFSAuthMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (redFSAuthMultiBucketShallow
  redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow (redFSAuthMultiBucketShallow_eval_eq)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (mSessMain
  healedBy_imp_healEpoch_le healedBy_of_not_postLeak LeAdd LeOne leAdd_of_lhs_zero
  leAdd_of_le_main leAdd_of_la_one leAdd_bind leAdd_bind_dummy_loc leOne_bind sampleVec
  multiFsEager_le_real keySlotSpec keySlotImpl keySlot_lazy_eq_eager
  isQueryBoundP_sessOffRange_of_ge_zero pubFsMultiImpl
  simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl lFS_receive_eq pubFsMultiImpl_inl_run
  pubFsMultiImpl_transmit_run pubFsMultiImpl_corruptSender_run pubFsMultiImpl_deliver_some_run
  pubFsMultiImpl_inject_none_run pubFsMultiImpl_inject_some_run)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux (sIdxForged
  sIdxForged_lt_mSessMain sIdxForged_inj not_isSome_and_eq_healEpoch_of_validGuess CompUnhealed
  compUnhealed_init compUnhealed_epMgmt compUnhealed_record compUnhealed_accept
  compUnhealed_afterCorr trivial_eq_false_of_healed forgedParOut LocEpochInv locEpochInv_init
  vSend_support_id_tcur locEpochInv_send vRecv_support_id_tcur locEpochInv_accept LocDeadForged
  locDeadForged_of_postLeak leak_postLeak_witness evalDist_locForged_eq_zero_of_dead SessHSt
  ForgedSessInv forgedSessInv_init forgedSessInv_transmit forgedSessInv_deliver
  forgedSessInv_inject)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed (forgedOut
  LocalForgedSlotState ForgedSlotHM sampleOrSlotF lookupLocalForgedSlotF rootLocalForgedSlot
  hooksLocalForgedSlot initLocalForgedSlot LocalForgedSlotEState implLocalForgedSlot
  localAuthBucketForgedSlot keySlotFixedImplF forged_halted_leOne forged_lfWin_aborted_eq_one
  localAuthBucketForgedHdrPar_eq_eager_ks forgedSlot_fixed_eq_localGen_of_halted_or_postLeak)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (badSendMsg_chall_false
  badSendMsg_query_bind_step badSendMsg_transmit_false)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (query_eq_liftM)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow (isTargetEp
  isTargetEp_zero isTargetEp_imp sendsIn_succ_false_imp sendsIn_exclusive sendsIn_false_unique
  sim_sampleT_fixedF run_sampleT_fixedF sim_sampleT_inl_gen run_sampleT_inl_gen eraseCtxSt
  eraseCtxSt_postLeak eraseCtxSt_safeCh eraseCtxSt_safeInj eraseCtxSt_inTransit eraseCtxSt_trivial
  eraseCtxSt_corrAllowed eraseCtxSt_epMgmt eraseCtxSt_record eraseCtxSt_accept eraseCtxSt_afterCorr
  VSAlign VRAlign VPAlign Fig8Γ Fig8Sig Fig8K Fig8SS Fig8RS Fig8E SlotES MultiES HookTableInv
  stateT_lift_run modify_run liftH_run hookTableInv_empty hookTableInv_mono_rem ForgedPhase1Inv
  isHonestHdr_eq_of_inv forgedPhase1_exit_halted forgedPhase1_exit_lfWin forgedPhase1_exit_postLeak
  sampleOrSlotF_false_run sampleOrSlotF_true_run lookup_off_step hmTargetM lookup_target_step
  forgedPhase1Inv_mono_rem makesAtMostQueries_inl makesAtMostQueries_inr sendMsgsOk_query_bind
  runLocForged runSideForged epMgmt_align epMgmt_leaks_tL mkParties_forgedPhase1Inv)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedInr (
  redFSAuthMultiBucket_atomic_eq_lFS hℓ_rust run_lift_transmit run_lift_deliver_some
  run_lift_inject_none run_lift_inject_some fsSend_inr_step fsRecv_inr_step
  liftFSMultiBucket_transmit_run liftFSMultiBucket_deliver_some_run
  liftFSMultiBucket_inject_none_run liftFSMultiBucket_inject_some_run)

open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSendRec (
  locFsOf hkLocOf hkMOf pubImplOf fsSendStepSlot fsSendStepM
  fsSend_record_coupled vSend_start_coins_forged)

theorem step_corrupt_forged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party)
    (k : Option (PartyState (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (ih : ∀ u {ssMap' rsMap' esLoc' esM' tblM' tblL'},
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap' rsMap' esLoc' esM' tblM' tblL' →
      LeAdd (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par true (k u) esM' none tblL')) :
    LeAdd
      (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inr P))) >>= k) esLoc none)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inr P))) >>= k) esM none tblM)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inr P))) >>= k) esM none tblL) := by
  have hwinM : esM.g.win = false :=
    (congrArg GameState.win hinv.ctx_eq).trans hinv.not_win
  have hcorrM : esM.g.corrAllowed P = esLoc.g.corrAllowed P :=
    eraseCtxSt_corrAllowed hinv.ctx_eq
  have hepM : esM.g.epoch = esLoc.g.epoch := congrArg GameState.epoch hinv.ctx_eq
  have hvp := hinv.vp_align P
  dsimp only [runLocForged, runSideForged]
  rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
    simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    map_bind, map_bind]
  have habL : esLoc.abort = false := hinv.not_abort.1
  have habM : esM.abort = false := hinv.not_abort.2
  have hwinL : esLoc.g.win = false := hinv.not_win
  have hS_step : (implLocalForgedSlot
      (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par)
      1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL (.inr (.inr P))).run (esLoc, none) =
      (if !(esLoc.g.corrAllowed P) then pure (none, (esLoc, none))
       else
         (((hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
           (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
           (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par).reveal esLoc.g P (esLoc.g.st P)).run esLoc.h) >>=
           fun ⟨res, h'⟩ =>
             match res with
             | none => pure (none, ({ esLoc with h := h', abort := true }, none))
             | some stOut => pure (some stOut, ({ esLoc with g := esLoc.g.afterCorr P, h := h' }, none))) := by
    simp only [implLocalForgedSlot, HAdd.hAdd, Add.add, QueryImpl.add, habL, hwinL, Bool.or_self,
      Bool.false_or, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hca'
    · simp only [StateT.run_pure]
    · simp only [StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
      congr 1; funext ⟨res, h'⟩; cases res <;> rfl
  have hM_step : ∀ la : Bool, (implFSMultiBucketAuth
      (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
      1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL (.inr (.inr P))).run (esM, none) =
      (if !(esLoc.g.corrAllowed P) then pure (none, (esM, none))
       else
         (((hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
           (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la).reveal esM.g P (esM.g.st P)).run esM.h) >>=
           fun ⟨res, h'⟩ =>
             match res with
             | none => pure (none, ({ esM with h := h', abort := true }, none))
             | some stOut => pure (some stOut, ({ esM with g := esM.g.afterCorr P, h := h' }, none))) := fun la => by
    simp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add, habM, hwinM, Bool.or_self,
      Bool.false_or, hcorrM, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hca'
    · simp only [StateT.run_pure]
    · simp only [StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
      congr 1; funext ⟨res, h'⟩; cases res <;> rfl
  rw [hS_step, hM_step false, hM_step true]
  cases hca : esLoc.g.corrAllowed P with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
    exact ih none (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hguard : (!(esLoc.g.st P).tcur < healEpoch tL ||
        !(max (esLoc.g.epoch .A) (esLoc.g.epoch .B) < healEpoch tL)) = true
    · have hguardM : (!(esM.g.st P).tcur < healEpoch tL ||
          !(max (esM.g.epoch .A) (esM.g.epoch .B) < healEpoch tL)) = true := by
        simpa [hvp.tcur_eq, hepM] using hguard
      have hrevL : ((hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par).reveal esLoc.g P (esLoc.g.st P)).run esLoc.h =
          pure (none, esLoc.h) := by
        dsimp only [hooksLocalForgedSlot]
        simp only [hguard, ↓reduceIte, StateT.run_pure]
      have hrevM : ∀ la : Bool, ((hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la).reveal esM.g P (esM.g.st P)).run esM.h =
          pure (none, esM.h) := fun la => by
        dsimp only [hooksFSMultiBucketAuth]
        simp only [Bool.not_false, Bool.true_and, hguardM, ↓reduceIte, StateT.run_pure]
      rw [hrevL, hrevM false, hrevM true]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      exact forgedPhase1_exit_halted ℓ Pt C Dh encPt encT idOf q qep tL par ks (k none)
        { esLoc with abort := true } { esM with abort := true } { esM with abort := true }
        none none tblM tblL (by simp) rfl hinv.ctx_eq
    · have hguardF : (!(esLoc.g.st P).tcur < healEpoch tL ||
          !(max (esLoc.g.epoch .A) (esLoc.g.epoch .B) < healEpoch tL)) = false :=
        Bool.eq_false_iff.mpr hguard
      have htcur_lt : (esLoc.g.st P).tcur < healEpoch tL := by
        have h1 : (!(esLoc.g.st P).tcur < healEpoch tL) = false := (Bool.or_eq_false_iff.mp hguardF).1
        simpa using h1
      have hguardMF : (!(esM.g.st P).tcur < healEpoch tL ||
          !(max (esM.g.epoch .A) (esM.g.epoch .B) < healEpoch tL)) = false := by
        simpa [hvp.tcur_eq, hepM] using hguardF
      have hrp_eq :
          realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root (esLoc.g.st P).vS (esLoc.g.st P).vR =
          realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root (esLoc.g.st P).vS (esLoc.g.st P).vR := by
        unfold realParty
        simp [hvp.id_loc, hvp.id_m, hvp.γ_eq, hvp.root_eq, hvp.cka_eq, hvp.tcur_eq]
      let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root
        (esLoc.g.st P).vS (esLoc.g.st P).vR
      have hrevL : ((hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par).reveal esLoc.g P (esLoc.g.st P)).run esLoc.h =
          pure (some stOut, esLoc.h) := by
        dsimp only [hooksLocalForgedSlot]
        simp only [hguardF, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, stOut]
      have hrevM : ∀ la : Bool, ((hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la).reveal esM.g P (esM.g.st P)).run esM.h =
          pure (some stOut, esM.h) := fun la => by
        dsimp only [hooksFSMultiBucketAuth]
        simp only [Bool.not_false, Bool.true_and, hguardMF, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind]
        refine Eq.trans (congrArg (· >>= _) (show _ = pure (some (esLoc.g.st P).vS, esM.h) from by
          rcases hvp.vS_align with ⟨h1, h2⟩ | ⟨ss, h1, h2⟩ | ⟨_, _, _, _, hhe_le, _⟩
          · simp [h1, h2]
          · simp [h1, h2]
          · omega)) ?_
        simp only [pure_bind]
        rw [ite_eq_right (by
          rw [Bool.not_eq_true, List.any_eq_false]
          intro t _
          by_cases hgt : (esLoc.g.st P).tcur < t
          · simp [(hvp.vR_gt t hgt).2]
          · rcases hvp.vR_align t with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, hhe_le, _⟩
            · simp [h2]
            · simp [h2]
            · omega)]
        simp only [StateT.run_pure, stOut, ← hrp_eq]
        refine congrArg (fun vR' =>
          pure (some (realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root (esLoc.g.st P).vS vR'), esM.h)) ?_
        funext t
        by_cases hlt : t < q + 1
        · simp only [hlt, ↓reduceIte]
          by_cases hgt : (esLoc.g.st P).tcur < t
          · simp [(hvp.vR_gt t hgt).1, (hvp.vR_gt t hgt).2]
          · rcases hvp.vR_align t with ⟨h1, h2⟩ | ⟨rs, h1, h2⟩ | ⟨_, _, hhe_le, _⟩
            · simp [h1, h2]
            · simp [h1, h2]
            · omega
        · simp only [hlt, ↓reduceIte]
          have hgt : (esLoc.g.st P).tcur < t := by have := hvp.tcur_rem; omega
          exact ((hvp.vR_gt t hgt).1).symm
      rw [hrevL, hrevM false, hrevM true]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      have hloc_ep' : LocEpochInv (esLoc.g.afterCorr P) :=
        ⟨fun Q => hinv.loc_epoch.1 Q, fun r hr => hinv.loc_epoch.2 r hr⟩
      have htL_wit : ∀ cur, (esLoc.g.afterCorr P).tL = some cur →
          ∃ lk ∈ (esLoc.g.afterCorr P).leaks, cur = lk := by
        intro cur hcur
        simp only [GameState.afterCorr, GameState.leak, Option.some.injEq] at hcur ⊢
        exact ⟨cur, List.mem_cons.mpr (Or.inl hcur.symm), rfl⟩
      cases hpl' : postLeak tL (esLoc.g.afterCorr P) with
      | true =>
        exact forgedPhase1_exit_postLeak ℓ Pt C Dh encPt encT idOf q qep tL par ks
          (k (some stOut)) (g₀ := esLoc.g)
          { esLoc with g := esLoc.g.afterCorr P }
          { esM with g := esM.g.afterCorr P }
          { esM with g := esM.g.afterCorr P }
          none none tblM tblL hloc_ep' hinv.not_pl hpl'
          (fun cur hcur => Or.inr (htL_wit cur hcur))
      | false =>
        refine ih (some stOut) (ssMap' := ssMap) (rsMap' := rsMap) ?_
        exact
          { not_abort := hinv.not_abort
            not_win := hinv.not_win
            not_pl := hpl'
            ctx_eq := eraseCtxSt_afterCorr hinv.ctx_eq
            loc_epoch := hloc_ep'
            comp_unhealed := compUnhealed_afterCorr hinv.comp_unhealed
            leaks_tL := htL_wit
            vp_align := fun Q =>
              let hv := hinv.vp_align Q
              { hv with tcur_rem := by have := hv.tcur_rem; dsimp only [GameState.afterCorr, GameState.leak]; omega }
            htbl := hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl
            ss_fresh := hinv.ss_fresh
            rs_fresh := hinv.rs_fresh
            sess_inv := hinv.sess_inv }

set_option maxHeartbeats 400000 in
theorem step_vSend_forged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : m.1.shortB = true)
    (k : Option (Fig8C Pt) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (ih : ∀ u {ssMap' rsMap' esLoc' esM' tblM' tblL'},
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap' rsMap' esLoc' esM' tblM' tblL' →
      LeAdd (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par true (k u) esM' none tblL')) :
    LeAdd
      (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esLoc none)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esM none tblM)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esM none tblL) := by
  have _ := hD
  let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let hkLoc := hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
    (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par
  let hkM := fun (la : Bool) =>
    hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
  let pubImpl := fun (la : Bool) =>
    pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
  have hwinM : esM.g.win = false := (congrArg GameState.win hinv.ctx_eq).trans hinv.not_win
  dsimp only [runLocForged, runSideForged]
  rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
    simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    map_bind, map_bind]
  rcases epMgmt_align (Δ := 3) (qep := qep) (P := P) (bad := r.isSome) hinv.ctx_eq with
    ⟨hepM_none, hepLoc_none⟩ | ⟨s₁M, s₁Loc, hepM, hepLoc, hctx₁, hstM1, hstLoc1, hep1_eq⟩
  · have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esLoc, none) =
        pure (none, (esLoc, none)) := by
      simp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        hinv.not_abort.1, hinv.not_win, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hepLoc_none,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esM, none) =
        pure (none, (esM, none)) := fun la => by
      simp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        hinv.not_abort.2, hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hepM_none,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
    rw [hS, hM false, hM true]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact ih none (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv)
  · have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esLoc, none) =
        (((vSend hkLoc s₁Loc P (s₁Loc.st P) m none r).run esLoc.h) >>= fun p =>
          match p.1 with
          | none => pure (none, ({ esLoc with h := p.2, abort := true }, none))
          | some (st', ct) =>
            let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
            pure (some ct, ({ esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 }, none))) := by
      simp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        hinv.not_abort.1, hinv.not_win, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        hepLoc, StateT.run_bind, StateT.run_get,
        stateT_lift_run, pure_bind, bind_assoc]
      congr 1; funext ⟨res, h'⟩; cases res <;> rfl
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esM, none) =
        (((vSend (hkM la) s₁M P (s₁M.st P) m none r).run esM.h) >>= fun p =>
          match p.1 with
          | none => pure (none, ({ esM with h := p.2, abort := true }, none))
          | some (st', ct) =>
            let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
            pure (some ct, ({ esM with g := s₁M.record 3 P st' recE false, h := p.2 }, none))) := fun la => by
      simp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        hinv.not_abort.2, hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        hepM, StateT.run_bind, StateT.run_get,
        stateT_lift_run, pure_bind, bind_assoc]
      congr 1; funext ⟨res, h'⟩; cases res <;> rfl
    rw [hS, hM false, hM true]
    cases hpl₁ : postLeak tL s₁Loc with
    | true =>
      apply leAdd_of_lhs_zero
      rw [simulateQ_bind, bind_assoc]
      refine _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun ⟨res, h'⟩ hz => ?_
      cases res with
      | none =>
        simp only [simulateQ_pure, pure_bind]
        erw [forgedSlot_fixed_eq_localGen_of_halted_or_postLeak (dhScheme Dh) (rootPRNG C.F encPt)
          locFs (sIdxForged q tL) ks 1 qep (mSessMain q qep tL) tL par (k none)
          { esLoc with h := h', abort := true } none (Or.inl (by simp))]
        exact evalDist_locForged_eq_zero_of_dead
          (hooksLocalBucketAuthForgedHdr (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep tL)
          (fun _ _ _ new => rfl) qep locFs.maxSkip tL par (k none)
          { g := esLoc.g, h := h'.loc, abort := true } none (Or.inl rfl)
      | some sc =>
        rcases sc with ⟨st', ct⟩
        simp only [simulateQ_pure, pure_bind]
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
          ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
        have hid1 : (s₁Loc.st P).id = P := by rw [hstLoc1]; exact (hinv.loc_epoch.1 P).1
        rcases vSend_support_id_tcur (keySlotFixedImplF ks) hkLoc s₁Loc P m r esLoc.h h' st' ct hid1 hz with
          ⟨hid', htcur', hct'⟩
        have hloc_ep' : LocEpochInv (s₁Loc.record 3 P st' recE false) :=
          locEpochInv_send m hinv.loc_epoch hepLoc hid' htcur' hct'
        have hpl_rec : postLeak tL (s₁Loc.record 3 P st' recE false) = true := by
          simpa [GameState.record, postLeak] using hpl₁
        have htL_rec : ∀ cur, (s₁Loc.record 3 P st' recE false).tL = some cur →
            esLoc.g.tL = some cur ∨ ∃ lk ∈ (s₁Loc.record 3 P st' recE false).leaks, cur = lk := by
          intro cur hcur
          exact Or.inr (by
            simpa [GameState.record] using epMgmt_leaks_tL hinv.leaks_tL hepLoc cur
              (by simpa [GameState.record] using hcur))
        erw [forgedSlot_fixed_eq_localGen_of_halted_or_postLeak (dhScheme Dh) (rootPRNG C.F encPt)
          locFs (sIdxForged q tL) ks 1 qep (mSessMain q qep tL) tL par (k (some ct))
          { esLoc with g := s₁Loc.record 3 P st' recE false, h := h' } none (Or.inr hpl_rec)]
        exact evalDist_locForged_eq_zero_of_dead
          (hooksLocalBucketAuthForgedHdr (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep tL)
          (fun _ _ _ new => rfl) qep locFs.maxSkip tL par (k (some ct))
          { g := s₁Loc.record 3 P st' recE false, h := h'.loc, abort := esLoc.abort } none
          (locDeadForged_of_postLeak hloc_ep' hinv.not_pl hpl_rec htL_rec)
    | false =>
      have hplM : postLeak tL s₁M = false := (eraseCtxSt_postLeak hctx₁).trans hpl₁
      let vpLoc := esLoc.g.st P
      let vpM := esM.g.st P
      have hvp := hinv.vp_align P
      have htcur_ep0 : vpLoc.tcur = esLoc.g.epoch P := (hinv.loc_epoch.1 P).2
      have hS_post : ∀ (p : Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × Fig8C Pt) ×
          LocalForgedSlotState Pt Fig8Sig Fig8K Pt),
          (simulateQ (keySlotFixedImplF ks)
            (match p.1 with
             | none => pure (none, ({ esLoc with h := p.2, abort := true }, none))
             | some (st', ct) =>
               let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                 ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
               pure (some ct, ({ esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 }, none))) >>=
            fun y =>
              simulateQ (keySlotFixedImplF ks) (do
                let x ← (simulateQ (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL) (k y.1)).run y.2
                pure (forgedOut 3 tL par x.2.1 x.2.2))) =
          match p.1 with
          | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
              { esLoc with h := p.2, abort := true } none
          | some (st', ct) =>
            let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
            runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
              { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none := by
        intro ⟨res, h'⟩; rcases res with _ | ⟨st', ct⟩ <;>
          (dsimp only [runLocForged]; simp only [simulateQ_pure, pure_bind]; rfl)
      have hM_post : ∀ (la : Bool)
          (q0 : (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × Fig8C Pt) ×
            FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))),
          ((simulateQ (pubImpl la)
            (match q0.1.1 with
             | none => pure (none, ({ esM with h := q0.1.2, abort := true }, none))
             | some (st', ct) =>
               let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                 ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
               pure (some ct, ({ esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)))).run q0.2 >>=
            fun a =>
              Prod.fst <$> (simulateQ (pubImpl la) (do
                let x ← (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k a.1.1)).run a.1.2
                if la then return x.2.1.h.lfWin else return forgedOut 3 tL par x.2.1 x.2.2)).run a.2) =
          Prod.fst <$> (simulateQ (pubImpl la) do
            let (u, es1, we1) := match q0.1.1 with
              | none => (none, { esM with h := q0.1.2, abort := true }, none)
              | some (st', ct) =>
                let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                  ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
            if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2 := by
        intro la ⟨⟨res, h'⟩, pSt⟩; rcases res with _ | ⟨st', ct⟩ <;>
          simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      rw [simulateQ_bind, bind_assoc,
        simulateQ_bind, StateT.run_bind, bind_assoc,
        simulateQ_bind, StateT.run_bind, bind_assoc]
      have hleAdd_congr0 : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
          a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a2 b2 c2 → LeAdd a1 b1 c1 := by
        rintro _ _ _ _ _ _ rfl rfl rfl h; exact h
      refine hleAdd_congr0
        (congrArg (Bind.bind _) (funext hS_post))
        (congrArg (Bind.bind _) (funext (hM_post false)))
        (congrArg (Bind.bind _) (funext (hM_post true)))
        ?_
      have hstLoc1_P : s₁Loc.st P = vpLoc := by rw [hstLoc1]
      have hstM1_P : s₁M.st P = vpM := by rw [hstM1]
      rw [hstLoc1_P, hstM1_P]
      unfold vSend
      have hcond_loc : vpLoc.id.sendsIn (vpLoc.tcur + 1) = P.sendsIn (vpLoc.tcur + 1) := by
        rw [hvp.id_loc]
      have hcond_m : vpM.id.sendsIn (vpM.tcur + 1) = P.sendsIn (vpLoc.tcur + 1) := by
        rw [hvp.id_m, hvp.tcur_eq]
      by_cases hsends : P.sendsIn (vpLoc.tcur + 1) = true
      · have hsendsL : vpLoc.id.sendsIn (vpLoc.tcur + 1) = true := hcond_loc.trans hsends
        have hsendsM : vpM.id.sendsIn (vpM.tcur + 1) = true := hcond_m.trans hsends
        rw [ite_eq_left hsendsL, ite_eq_left hsendsM, ite_eq_left hsendsM]
        let t0 := vpLoc.tcur + 1
        have hep_t0 : s₁Loc.epoch P = t0 := by
          rw [hep1_eq, ← htcur_ep0, hsends]; simp [t0]
        have hrun_sim_bind : ∀ {α β : Type} (la : Bool)
            (m1 : OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) α)
            (m2 : α → OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) β)
            (st : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            (simulateQ (pubImpl la) (m1 >>= m2)).run st =
              ((simulateQ (pubImpl la) m1).run st >>= fun p => (simulateQ (pubImpl la) (m2 p.1)).run p.2) := by
          intros; rw [simulateQ_bind, StateT.run_bind]
        have hstart_coins : ∀ (c0 : BitVec 256), _ := fun c0 =>
          vSend_start_coins_forged C Dh encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv
            P m r hshort hepLoc hctx₁ hstLoc1 hstM1 hpl₁ hsends hep_t0 k ih c0
        have hstartL : (hkLoc.startSend s₁Loc P t0 vpLoc.γ vpLoc.root r).run esLoc.h =
            ((r.elim
              (StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec Fig8K)) (BitVec 256)))
              pure : ForgedSlotHM Pt Fig8Sig Fig8K Pt (BitVec 256)).run esLoc.h >>=
              fun cPair =>
                ((rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
                    (mSessMain q qep tL) tL par t0 false ((dhScheme Dh).send vpLoc.γ cPair.1).2.2 vpLoc.root).run cPair.2 >>=
                  fun r0 =>
                    pure (some (((dhScheme Dh).send vpLoc.γ cPair.1).1, ((dhScheme Dh).send vpLoc.γ cPair.1).2.1,
                                r0.1.1, locFs.initSender r0.1.2),
                      { r0.2 with loc := { r0.2.loc with
                          cache := Function.update r0.2.loc.cache t0
                            (some (((dhScheme Dh).send vpLoc.γ cPair.1).2.1, r0.1.1, r0.1.2)) } }))) := by
          dsimp only [hkLoc, hooksLocalForgedSlot]
          cases r <;>
            simp only [Option.elim, hpl₁, StateT.run_bind, modify_run,
              StateT.run_pure, pure_bind]
        have hstartM : ∀ la : Bool, ((hkM la).startSend s₁M P t0 vpM.γ vpM.root r).run esM.h =
            ((r.elim
              (StateT.lift (sampleT (tspec := FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) (BitVec 256)))
              pure :
                _root_.CryptoGames.SM.Engine.HM
                  (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
                  (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) (BitVec 256)).run esM.h >>=
              fun cPair =>
                StateT.run (do
                  let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false
                    ((dhScheme Dh).send vpLoc.γ cPair.1).2.2 vpLoc.root
                  let s1 ← get
                  let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
                  set ({ s2 with cache := Function.update s2.cache t0 (some (((dhScheme Dh).send vpLoc.γ cPair.1).2.1, σ', kVal, optIdx)) })
                  let ssv : Fig8SS ⊕ ℕ := match optIdx with
                    | none => .inl (locFs.initSender kVal)
                    | some sIdx => .inr sIdx
                  return (some (((dhScheme Dh).send vpLoc.γ cPair.1).1, ((dhScheme Dh).send vpLoc.γ cPair.1).2.1, σ', ssv) :
                    Option (Fig8Γ Pt × Pt × Fig8Sig × (Fig8SS ⊕ ℕ)))) cPair.2) := fun la => by
          have hγ_eq : vpM.γ = vpLoc.γ := hvp.γ_eq
          have hrt_eq : vpM.root = vpLoc.root := hvp.root_eq
          dsimp only [hkM, hooksFSMultiBucketAuth]
          rw [hplM, hγ_eq, hrt_eq, StateT.run_bind]
          refine congrArg₂ Bind.bind (by cases r <;> rfl) (funext fun cPair => ?_)
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
          refine congrArg (Bind.bind _) (funext fun ⟨⟨σ', kVal, sid⟩, s1⟩ => ?_)
          rcases regSessOptMultiBucket (q + 1) false tL t0 sid s1 with ⟨_ | sIdx, s2⟩ <;> rfl
        let postContM (la : Bool)
            (q0 : Option (Fig8Γ Pt × Pt × Fig8Sig × (Fig8SS ⊕ ℕ)) ×
              FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) :
            OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
              (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × Fig8C Pt) ×
                FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) :=
          match q0.1 with
          | none => pure (none, q0.2)
          | some (γ', T', σ', ss) =>
            (fsSendStepM C Dh encPt encT idOf ℓ q qep tL par la s₁M P m
              { vpM with tcur := t0, γ := γ', curCkaMsg := some T', root := σ',
                         vS := some ss }).run q0.2
        have hpostM : ∀ (la : Bool) (c0 : BitVec 256)
            (h0 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E),
            (StateT.run (do
              let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false
                ((dhScheme Dh).send vpLoc.γ c0).2.2 vpLoc.root
              let s1 ← get
              let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
              set ({ s2 with cache := Function.update s2.cache t0 (some (((dhScheme Dh).send vpLoc.γ c0).2.1, σ', kVal, optIdx)) })
              let ssv : Fig8SS ⊕ ℕ := match optIdx with
                | none => .inl (locFs.initSender kVal)
                | some sIdx => .inr sIdx
              return (some (((dhScheme Dh).send vpLoc.γ c0).1, ((dhScheme Dh).send vpLoc.γ c0).2.1, σ', ssv) :
                Option (Fig8Γ Pt × Pt × Fig8Sig × (Fig8SS ⊕ ℕ)))) h0 >>= postContM la) =
            (StateT.run (do
              let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false
                ((dhScheme Dh).send vpLoc.γ c0).2.2 vpLoc.root
              let s1 ← get
              let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
              set ({ s2 with cache := Function.update s2.cache t0 (some (((dhScheme Dh).send vpLoc.γ c0).2.1, σ', kVal, optIdx)) })
              let ssv : Fig8SS ⊕ ℕ := match optIdx with
                | none => .inl (locFs.initSender kVal)
                | some sIdx => .inr sIdx
              return ({ vpM with tcur := t0, γ := ((dhScheme Dh).send vpLoc.γ c0).1,
                                 curCkaMsg := some ((dhScheme Dh).send vpLoc.γ c0).2.1, root := σ',
                                 vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) h0 >>= fun p1 =>
              (fsSendStepM C Dh encPt encT idOf ℓ q qep tL par la s₁M P m p1.1).run p1.2) := fun la c0 h0 => by
          dsimp only [postContM]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            bind_assoc, pure_bind]
        refine hleAdd_congr0
          (congrArg (· >>= _) (congrArg (simulateQ _)
            (show _ = ((hkLoc.startSend s₁Loc P t0 vpLoc.γ vpLoc.root r).run esLoc.h >>= fun q0 =>
              match q0.1 with
              | none => pure (none, q0.2)
              | some (γ', T', σ', ss) =>
                (fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m
                  { vpLoc with tcur := t0, γ := γ', curCkaMsg := some T', root := σ',
                               vS := some ss }).run q0.2) from by
              dsimp only [t0, fsSendStepSlot, hkLocOf, locFsOf, hkLoc, locFs]
              simp only [StateT.run_bind, pure_bind]
              refine congrArg (Bind.bind _) (funext fun ⟨res, h0⟩ => ?_)
              rcases res with _ | ⟨γ', T', σ', ss⟩
              · simp only [StateT.run_pure]
              · simp only [StateT.run_bind]
                refine congrArg (Bind.bind _) (funext fun p => ?_)
                rcases p.1 with _ | ⟨v', e⟩ <;> rfl)))
          (congrArg (· >>= _) (congrFun (congrArg StateT.run (congrArg (simulateQ _)
            (show _ = (((hkM false).startSend s₁M P t0 vpM.γ vpM.root r).run esM.h >>= postContM false) from by
              have htcur_m : vpM.tcur + 1 = t0 := by dsimp only [t0]; rw [hvp.tcur_eq]
              rw [htcur_m]
              dsimp only [postContM, fsSendStepM, hkMOf, locFsOf, hkM, locFs]
              simp only [StateT.run_bind, pure_bind]
              refine congrArg (Bind.bind _) (funext fun ⟨res, h0⟩ => ?_)
              rcases res with _ | ⟨γ', T', σ', ss⟩
              · simp only [StateT.run_pure]
              · simp only [StateT.run_bind]
                refine congrArg (Bind.bind _) (funext fun p => ?_)
                rcases p.1 with _ | ⟨v', e⟩ <;> rfl))) _))
          (congrArg (· >>= _) (congrFun (congrArg StateT.run (congrArg (simulateQ _)
            (show _ = (((hkM true).startSend s₁M P t0 vpM.γ vpM.root r).run esM.h >>= postContM true) from by
              have htcur_m : vpM.tcur + 1 = t0 := by dsimp only [t0]; rw [hvp.tcur_eq]
              rw [htcur_m]
              dsimp only [postContM, fsSendStepM, hkMOf, locFsOf, hkM, locFs]
              simp only [StateT.run_bind, pure_bind]
              refine congrArg (Bind.bind _) (funext fun ⟨res, h0⟩ => ?_)
              rcases res with _ | ⟨γ', T', σ', ss⟩
              · simp only [StateT.run_pure]
              · simp only [StateT.run_bind]
                refine congrArg (Bind.bind _) (funext fun p => ?_)
                rcases p.1 with _ | ⟨v', e⟩ <;> rfl))) _))
          ?_
        have hleAdd_of_eq : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
            LeAdd a2 b2 c2 → a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a1 b1 c1 := by
          rintro _ _ _ _ _ _ h rfl rfl rfl; exact h
        have helim_some : ∀ {α β : Sort _} (x : α) (d : β) (f : α → β), Option.elim (some x) d f = f x :=
          fun _ _ _ => rfl
        have helim_none : ∀ {α β : Sort _} (d : β) (f : α → β), Option.elim (none : Option α) d f = d :=
          fun _ _ => rfl
        rw [hstartL, hstartM false, hstartM true]
        cases r with
        | some c0 =>
          rw [helim_some, helim_some, StateT.run_pure, StateT.run_pure,
            pure_bind (m := OracleComp _), pure_bind (m := OracleComp _)]
          rw [hpostM false, hpostM true, hrun_sim_bind false, hrun_sim_bind true]
          rw [bind_assoc (m := OracleComp _), simulateQ_bind]
          simp only [bind_assoc, pure_bind]
          refine hleAdd_of_eq (hstart_coins c0)
            (congrArg (Bind.bind _) (funext fun r0 =>
              congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl)))
            (congrArg₂ Bind.bind
              (congrFun (congrArg StateT.run (congrArg (simulateQ _) (by
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                refine congrArg (Bind.bind _) (funext fun ⟨⟨σ', kVal, sid⟩, s1⟩ => ?_)
                rcases regSessOptMultiBucket (q + 1) false tL t0 sid s1 with ⟨_ | sIdx, s2⟩ <;> rfl))) _)
              (funext fun p1 =>
                congrArg (Bind.bind _) (funext fun q0 => by
                  rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                    exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                      (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
            (congrArg₂ Bind.bind
              (congrFun (congrArg StateT.run (congrArg (simulateQ _) (by
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                refine congrArg (Bind.bind _) (funext fun ⟨⟨σ', kVal, sid⟩, s1⟩ => ?_)
                rcases regSessOptMultiBucket (q + 1) false tL t0 sid s1 with ⟨_ | sIdx, s2⟩ <;> rfl))) _)
              (funext fun p1 =>
                congrArg (Bind.bind _) (funext fun q0 => by
                  rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                    exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                      (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
        | none =>
          rw [helim_none, helim_none]
          rw [bind_assoc (m := OracleComp (unifSpec + multiSessSpec (keySlotSpec Fig8K))),
            simulateQ_bind, run_sampleT_fixedF]
          rw [bind_assoc (m := OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)),
            bind_assoc (m := OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)),
            hrun_sim_bind false, hrun_sim_bind true,
            run_sampleT_inl_gen (pubImpl false) (pubFsMultiImpl_inl_run _),
            run_sampleT_inl_gen (pubImpl true) (pubFsMultiImpl_inl_run _)]
          simp (config := { zeta := false, iota := false, proj := false }) only
            [bind_assoc (m := ProbComp), pure_bind (m := ProbComp)]
          refine leAdd_bind ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) fun c0 _ => ?_
          rw [hpostM false, hpostM true, hrun_sim_bind false, hrun_sim_bind true]
          rw [bind_assoc (m := OracleComp (unifSpec + multiSessSpec (keySlotSpec Fig8K))), simulateQ_bind]
          simp only [bind_assoc, pure_bind]
          refine hleAdd_of_eq (hstart_coins c0)
            (congrArg (Bind.bind _) (funext fun r0 =>
              congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl)))
            (congrArg₂ Bind.bind
              (congrFun (congrArg StateT.run (congrArg (simulateQ _) (by
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                refine congrArg (Bind.bind _) (funext fun ⟨⟨σ', kVal, sid⟩, s1⟩ => ?_)
                rcases regSessOptMultiBucket (q + 1) false tL t0 sid s1 with ⟨_ | sIdx, s2⟩ <;> rfl))) _)
              (funext fun p1 =>
                congrArg (Bind.bind _) (funext fun q0 => by
                  rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                    exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                      (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
            (congrArg₂ Bind.bind
              (congrFun (congrArg StateT.run (congrArg (simulateQ _) (by
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                refine congrArg (Bind.bind _) (funext fun ⟨⟨σ', kVal, sid⟩, s1⟩ => ?_)
                rcases regSessOptMultiBucket (q + 1) false tL t0 sid s1 with ⟨_ | sIdx, s2⟩ <;> rfl))) _)
              (funext fun p1 =>
                congrArg (Bind.bind _) (funext fun q0 => by
                  rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                    exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                      (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
      · have hsendsF : P.sendsIn (vpLoc.tcur + 1) = false := Bool.eq_false_iff.mpr hsends
        have hnsendsL : ¬(vpLoc.id.sendsIn (vpLoc.tcur + 1) = true) := by
          rw [hcond_loc]; exact hsends
        have hnsendsM : ¬(vpM.id.sendsIn (vpM.tcur + 1) = true) := by
          rw [hcond_m]; exact hsends
        rw [ite_eq_right hnsendsL, ite_eq_right hnsendsM, ite_eq_right hnsendsM]
        have hsends_cur : P.sendsIn vpLoc.tcur = true := sendsIn_succ_false_imp P hsendsF
        have hep_cur : vpLoc.tcur = s₁Loc.epoch P := by
          rw [hep1_eq, ← htcur_ep0, hsendsF]; simp
        simp only [pure_bind]
        have hleAdd_of_eq : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
            LeAdd a2 b2 c2 → a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a1 b1 c1 := by
          rintro _ _ _ _ _ _ h rfl rfl rfl; exact h
        refine hleAdd_of_eq
          (fsSend_record_coupled C Dh encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P m r hshort
            hepLoc hctx₁ hstLoc1 hstM1 hpl₁ vpLoc vpM esLoc.h esM.h
            { hvp with tcur_rem := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem') _) hvp.tcur_rem }
            hep_cur hsends_cur le_rfl
            (by
              dsimp only [vpLoc] at hsendsF ⊢
              rw [hstLoc1]
              simp only [hsendsF, Bool.false_eq_true, ↓reduceIte])
            (hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl) rfl k ih)
          (by
            refine (congrArg (· >>= _) (congrArg (simulateQ _)
              (show _ = (fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m vpLoc).run esLoc.h from by
                dsimp only [fsSendStepSlot, hkLocOf, locFsOf, hkLoc, locFs]
                cases vpLoc.vS with
                | none => rfl
                | some v =>
                  simp only [StateT.run_bind]
                  refine congrArg (Bind.bind _) (funext fun p => ?_)
                  rcases p.1 with _ | ⟨v', e⟩ <;> rfl))).trans ?_
            refine congrArg (Bind.bind _) (funext fun x => ?_)
            rcases x.1 with _ | ⟨st', ct⟩ <;> rfl)
          (by
            refine (congrArg (· >>= _) (congrFun (congrArg StateT.run (congrArg (simulateQ _)
              (show _ = (fsSendStepM C Dh encPt encT idOf ℓ q qep tL par false s₁M P m vpM).run esM.h from by
                dsimp only [fsSendStepM, hkMOf, locFsOf, hkM, locFs]
                cases vpM.vS with
                | none => rfl
                | some v =>
                  simp only [StateT.run_bind]
                  refine congrArg (Bind.bind _) (funext fun p => ?_)
                  rcases p.1 with _ | ⟨v', e⟩ <;> rfl))) _)).trans ?_
            refine congrArg (Bind.bind _) (funext fun q0 => ?_)
            rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
              exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => by simp)))) q0.2))
          (by
            refine (congrArg (· >>= _) (congrFun (congrArg StateT.run (congrArg (simulateQ _)
              (show _ = (fsSendStepM C Dh encPt encT idOf ℓ q qep tL par true s₁M P m vpM).run esM.h from by
                dsimp only [fsSendStepM, hkMOf, locFsOf, hkM, locFs]
                cases vpM.vS with
                | none => rfl
                | some v =>
                  simp only [StateT.run_bind]
                  refine congrArg (Bind.bind _) (funext fun p => ?_)
                  rcases p.1 with _ | ⟨v', e⟩ <;> rfl))) _)).trans ?_
            refine congrArg (Bind.bind _) (funext fun q0 => ?_)
            rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
              exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => by simp)))) q0.2))

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSend
