/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShort
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedInr
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSend
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedRecv
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedHop

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
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSend (step_corrupt_forged
  step_vSend_forged)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedRecv (
  accept_st_update_self_forged accept_forgedPhase1Inv vRecv_forged_coupled)

private theorem step_deliver_forged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) →
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
          (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esLoc none)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM none tblM)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM none tblL) := by
  let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let hkLoc := hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
    (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par
  let hkM := fun (la : Bool) =>
    hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
  let pubImpl := fun (la : Bool) =>
    pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
  have hwinM : esM.g.win = false := (congrArg GameState.win hinv.ctx_eq).trans hinv.not_win
  have hinTr_eq : esM.g.inTransit P.other c = esLoc.g.inTransit P.other c :=
    eraseCtxSt_inTransit hinv.ctx_eq
  have hchall_eq : esM.g.chall = esLoc.g.chall := congrArg GameState.chall hinv.ctx_eq
  unfold runLocForged runSideForged
  rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
    simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    map_bind, map_bind]
  cases hinLoc : esLoc.g.inTransit P.other c with
  | none =>
    have hinM : esM.g.inTransit P.other c = none := hinTr_eq.trans hinLoc
    have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inl (.inr (P, c)))))).run (esLoc, none) =
        pure (none, (esLoc, none)) := by
      dsimp only [implLocalForgedSlot, HAdd.hAdd, Add.add, QueryImpl.add, deliverE]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, pure_bind, hinv.not_abort.1, hinv.not_win, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, hinLoc]
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inl (.inr (P, c)))))).run (esM, none) =
        pure (none, (esM, none)) := fun la => by
      dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add, deliverE]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, pure_bind, hinv.not_abort.2, hwinM, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, hinM]
    rw [hS, hM false, hM true]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact ih none (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv)
  | some r =>
    have hinM : esM.g.inTransit P.other c = some r := hinTr_eq.trans hinLoc
    have hr_mem : r ∈ esLoc.g.trans := List.mem_of_find?_eq_some hinLoc
    have hr_ct : r.ct = c := by
      have hf := List.find?_some hinLoc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      exact hf.2
    have hr_ep : r.pos.epoch = c.1.1 :=
      (hinv.loc_epoch.2 r hr_mem).trans (congrArg (·.1.1) hr_ct)
    let postLoc (p : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) × LocalForgedSlotState Pt Fig8Sig Fig8K Pt) :
        Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × (SlotES Pt ℓ × Option ℕ) :=
      match p.1 with
      | none => (none, ({ esLoc with h := p.2, abort := true }, none))
      | some none => (some RecvResult.rejected, ({ esLoc with h := p.2 }, none))
      | some (some (st', t', i', m')) =>
        let outMsg := if esLoc.g.chall.contains r.pos then none else some m'
        (some (RecvResult.accepted t' i' outMsg),
          ({ esLoc with g := esLoc.g.accept P st' r.pos, h := p.2 }, none))
    let postM (p : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) :
        Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × (MultiES Pt ℓ × Option ℕ) :=
      match p.1 with
      | none => (none, ({ esM with h := p.2, abort := true }, none))
      | some none => (some RecvResult.rejected, ({ esM with h := p.2 }, none))
      | some (some (st', t', i', m')) =>
        let outMsg := if esLoc.g.chall.contains r.pos then none else some m'
        (some (RecvResult.accepted t' i' outMsg),
          ({ esM with g := esM.g.accept P st' r.pos, h := p.2 }, none))
    have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inl (.inr (P, c)))))).run (esLoc, none) =
        (((vRecv hkLoc esLoc.g P (esLoc.g.st P) c (some r)).run esLoc.h) >>= fun p =>
          pure (postLoc p)) := by
      dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        deliverE, abortE, commitE, bucketAuthCfg]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, liftH_run, pure_bind, bind_assoc, hinv.not_abort.1, hinv.not_win, hinLoc,
        Bool.or_self, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext ⟨res, h'⟩
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · dsimp only [postLoc]
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      · dsimp only [postLoc]
        simp [StateT.run_pure, hinv.not_abort.1]
      · dsimp only [hkLoc, hooksLocalForgedSlot, postLoc]
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, liftH_run, pure_bind,
          accept_st_update_self_forged]
        simp [hinv.not_abort.1]
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inl (.inr (P, c)))))).run (esM, none) =
        (((vRecv (hkM la) esM.g P (esM.g.st P) c (some r)).run esM.h) >>= fun p =>
          pure (postM p)) := fun la => by
      dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        deliverE, abortE, commitE, bucketAuthCfg]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, liftH_run, pure_bind, bind_assoc, hinv.not_abort.2, hwinM, hinM, hchall_eq,
        Bool.or_self, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext ⟨res, h'⟩
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · dsimp only [postM]
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      · dsimp only [postM]
        simp [StateT.run_pure, hinv.not_abort.2]
      · dsimp only [hkM, hooksFSMultiBucketAuth, postM]
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, liftH_run, pure_bind,
          accept_st_update_self_forged]
        simp [hinv.not_abort.2]
    rw [hS, hM false, hM true, simulateQ_bind, bind_assoc,
      simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_bind, StateT.run_bind, bind_assoc]
    let kLoc := fun p =>
      let q1 := postLoc p
      runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k q1.1) q1.2.1 q1.2.2
    let kSide := fun (la : Bool)
        (x : (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
            (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
          ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
      let q1 := postM x.1
      Prod.fst <$> (simulateQ (pubImpl la) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k q1.1)).run q1.2
        if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run x.2
    change LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((vRecv hkLoc esLoc.g P (esLoc.g.st P) c (some r)).run esLoc.h) >>= kLoc)
      (((simulateQ (pubImpl false)
        ((vRecv (hkM false) esM.g P (esM.g.st P) c (some r)).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
      (((simulateQ (pubImpl true)
        ((vRecv (hkM true) esM.g P (esM.g.st P) c (some r)).run esM.h)).run (fun _ => false, tblL)) >>= kSide true)
    refine vRecv_forged_coupled C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c (some r)
      kLoc kSide
      (fun hLoc' hM' tblM' tblL' =>
        forgedPhase1_exit_halted ℓ Pt C Dh encPt encT idOf q qep tL par ks (k none)
          { esLoc with h := hLoc', abort := true }
          { esM with h := hM', abort := true }
          { esM with h := hM', abort := true }
          none none tblM' tblL' rfl rfl hinv.ctx_eq)
      (fun lhs rhsF hL' tblL' hlf => by
        apply leAdd_of_la_one
        exact forged_lfWin_aborted_eq_one
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par true)
          1 qep locFs.maxSkip tL (pubImpl true)
          (pubFsMultiImpl_inl_run _) (k none) { esM with h := hL', abort := true } none
          (fun _ => false, tblL') rfl hlf)
      (fun rsMap' hLoc' hM' tblM' tblL' hinv' =>
        ih (some .rejected) hinv')
      (fun stLoc' stM' idxOut pmOut rsMap' hLoc' hM' tblM' tblL' hacc _ =>
        ih (some (.accepted c.1.1 idxOut (if esLoc.g.chall.contains r.pos then none else some pmOut)))
          (hacc r.pos hr_ep))

private theorem step_inject_forged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) →
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
          (.inr (.inl (.inr (P, c))))) >>= k) esLoc none)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inr (P, c))))) >>= k) esM none tblM)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (.inr (.inl (.inr (P, c))))) >>= k) esM none tblL) := by
  let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let hkLoc := hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
    (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par
  let hkM := fun (la : Bool) =>
    hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
  let pubImpl := fun (la : Bool) =>
    pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
  have hwinM : esM.g.win = false := (congrArg GameState.win hinv.ctx_eq).trans hinv.not_win
  have hinTr_eq : esM.g.inTransit P.other c = esLoc.g.inTransit P.other c :=
    eraseCtxSt_inTransit hinv.ctx_eq
  have hsafe_eq : esM.g.safeInj 3 = esLoc.g.safeInj 3 :=
    eraseCtxSt_safeInj hinv.ctx_eq
  have htcur_eq := (hinv.vp_align P).tcur_eq
  have hhon_eq := isHonestHdr_eq_of_inv hinv.htbl c.1
  let isNF : Bool := decide (c.1.1 = (esLoc.g.st P).tcur + 1) && !isHonestHdrLocalBucket esLoc.h.loc c.1
  unfold runLocForged runSideForged
  rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
    simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    map_bind, map_bind]
  by_cases hguard : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj 3)) = true
  · have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inr (P, c))))).run (esLoc, none) =
        pure (none, (esLoc, none)) := by
      dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, bucketAuthCfg]
      simp only [(show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, pure_bind, bind_assoc, hinv.not_abort.1, hinv.not_win, Bool.false_or, hguard,
        ↓reduceIte, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inr (P, c))))).run (esM, none) =
        pure (none, (esM, none)) := fun la => by
      dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, bucketAuthCfg]
      simp only [(show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        stateT_lift_run, pure_bind, bind_assoc, hinv.not_abort.2, hwinM, hinTr_eq, hsafe_eq, Bool.false_or,
        hguard, ↓reduceIte, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    rw [hS, hM false, hM true]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact ih none (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv)
  · have hguardF : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj 3)) = false :=
      Bool.eq_false_iff.mpr hguard
    have hwin_accLoc : ∀ (st' : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS) (pos : Pos),
        (esLoc.g.accept P st' pos).win = false := fun _ _ => by
      simpa [GameState.accept, GameState.delete] using hinv.not_win
    have hwin_accM : ∀ (st' : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ)) (pos : Pos),
        (esM.g.accept P st' pos).win = false := fun _ _ => by
      simpa [GameState.accept, GameState.delete] using hwinM
    let postInjLoc (p : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) × LocalForgedSlotState Pt Fig8Sig Fig8K Pt) :
        Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × (SlotES Pt ℓ × Option ℕ) :=
      match p.1 with
      | none => (none, ({ esLoc with h := p.2, abort := true }, none))
      | some none => (some RecvResult.rejected, ({ esLoc with h := p.2 }, none))
      | some (some (st', t', i', m')) =>
        if qep + 1 < t' then
          (some RecvResult.rejected, ({ esLoc with h := p.2 }, none))
        else if esLoc.g.trivial 3 ⟨P.other, t', i'⟩ then
          (some (RecvResult.accepted t' i' (some m')),
            ({ esLoc with g := esLoc.g.accept P st' ⟨P.other, t', i'⟩, h := p.2 }, none))
        else if lastLeakGuessAdmissible 3 tL t' then
          (some RecvResult.rejected,
            ({ esLoc with g := { esLoc.g with win := true }, h := p.2 },
             if isNF then some c.1.1 else none))
        else
          (some RecvResult.rejected, ({ esLoc with h := p.2 }, none))
    let postInjM (p : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) :
        Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × (MultiES Pt ℓ × Option ℕ) :=
      match p.1 with
      | none => (none, ({ esM with h := p.2, abort := true }, none))
      | some none => (some RecvResult.rejected, ({ esM with h := p.2 }, none))
      | some (some (st', t', i', m')) =>
        if qep + 1 < t' then
          (some RecvResult.rejected, ({ esM with h := p.2 }, none))
        else if esLoc.g.trivial 3 ⟨P.other, t', i'⟩ then
          (some (RecvResult.accepted t' i' (some m')),
            ({ esM with g := esM.g.accept P st' ⟨P.other, t', i'⟩, h := p.2 }, none))
        else if lastLeakGuessAdmissible 3 tL t' then
          (some RecvResult.rejected,
            ({ esM with g := { esM.g with win := true }, h := p.2 },
             if isNF then some c.1.1 else none))
        else
          (some RecvResult.rejected, ({ esM with h := p.2 }, none))
    have hS : (implLocalForgedSlot hkLoc 1 qep locFs.maxSkip tL
        (.inr (.inl (.inr (P, c))))).run (esLoc, none) =
        (((vRecv hkLoc esLoc.g P (esLoc.g.st P) c none).run esLoc.h) >>= fun p =>
          pure (postInjLoc p)) := by
      dsimp only [implLocalForgedSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        injectE, abortE, commitE, bucketAuthCfg]
      simp only [(show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, stateT_lift_run, liftH_run, pure_bind, bind_assoc,
        hinv.not_abort.1, hinv.not_win, Bool.false_or, hguardF,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
      congr 1; funext ⟨res, h'⟩
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · dsimp only [postInjLoc]
        simp [StateT.run_modify, hinv.not_win]
      · dsimp only [postInjLoc]
        simp [StateT.run_pure, hinv.not_win, hinv.not_abort.1]
      · dsimp only [postInjLoc]
        by_cases hqep_gt : qep + 1 < t'
        · simp [hqep_gt, StateT.run_pure, hinv.not_win, hinv.not_abort.1]
        · simp only [hqep_gt, ↓reduceIte]
          by_cases htriv : esLoc.g.trivial 3 ⟨P.other, t', i'⟩ = true
          · dsimp only [hkLoc, hooksLocalForgedSlot]
            simp only [htriv, StateT.run_bind, StateT.run_modify, StateT.run_pure, liftH_run, pure_bind,
              ↓reduceIte, accept_st_update_self_forged]
            simp [hwin_accLoc, hinv.not_abort.1]
          · have htrivF : esLoc.g.trivial 3 ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
            simp only [htrivF, Bool.false_eq_true, ↓reduceIte]
            by_cases hadm : lastLeakGuessAdmissible 3 tL t' = true
            · simp [hadm, StateT.run_modify,
                isNF, hinv.not_abort.1]
            · have hadmF : lastLeakGuessAdmissible 3 tL t' = false := Bool.eq_false_iff.mpr hadm
              simp [hadmF, StateT.run_pure, hinv.not_win,
                hinv.not_abort.1]
    have hM : ∀ la : Bool, (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL
        (.inr (.inl (.inr (P, c))))).run (esM, none) =
        (((vRecv (hkM la) esM.g P (esM.g.st P) c none).run esM.h) >>= fun p =>
          pure (postInjM p)) := fun la => by
      dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        injectE, abortE, commitE, bucketAuthCfg]
      simp only [(show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, stateT_lift_run, liftH_run, pure_bind, bind_assoc,
        hinv.not_abort.2, hwinM, hinTr_eq, hsafe_eq, Bool.false_or, hguardF,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
        htcur_eq, hhon_eq]
      congr 1; funext ⟨res, h'⟩
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · dsimp only [postInjM]
        simp [StateT.run_modify, hwinM]
      · dsimp only [postInjM]
        simp [StateT.run_pure, hwinM, hinv.not_abort.2]
      · dsimp only [postInjM]
        have htriv_eq : esM.g.trivial 3 ⟨P.other, t', i'⟩ = esLoc.g.trivial 3 ⟨P.other, t', i'⟩ :=
          eraseCtxSt_trivial hinv.ctx_eq
        by_cases hqep_gt : qep + 1 < t'
        · simp [hqep_gt, StateT.run_pure, hwinM, hinv.not_abort.2]
        · simp only [hqep_gt, ↓reduceIte, htriv_eq]
          by_cases htriv : esLoc.g.trivial 3 ⟨P.other, t', i'⟩ = true
          · dsimp only [hkM, hooksFSMultiBucketAuth]
            simp only [htriv, StateT.run_bind, StateT.run_modify, StateT.run_pure, liftH_run, pure_bind,
              ↓reduceIte, accept_st_update_self_forged]
            simp [hwin_accM, hinv.not_abort.2]
          · have htrivF : esLoc.g.trivial 3 ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
            simp only [htrivF, Bool.false_eq_true, ↓reduceIte]
            by_cases hadm : lastLeakGuessAdmissible 3 tL t' = true
            · simp [hadm, StateT.run_modify,
                isNF, hinv.not_abort.2]
            · have hadmF : lastLeakGuessAdmissible 3 tL t' = false := Bool.eq_false_iff.mpr hadm
              simp [hadmF, StateT.run_pure, hwinM,
                hinv.not_abort.2]
    rw [hS, hM false, hM true, simulateQ_bind, bind_assoc,
      simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_bind, StateT.run_bind, bind_assoc]
    let kLoc := fun p =>
      let q1 := postInjLoc p
      runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k q1.1) q1.2.1 q1.2.2
    let kSide := fun (la : Bool)
        (x : (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
            (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
          ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
      let q1 := postInjM x.1
      Prod.fst <$> (simulateQ (pubImpl la) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k q1.1)).run q1.2
        if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run x.2
    change LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((vRecv hkLoc esLoc.g P (esLoc.g.st P) c none).run esLoc.h) >>= kLoc)
      (((simulateQ (pubImpl false)
        ((vRecv (hkM false) esM.g P (esM.g.st P) c none).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
      (((simulateQ (pubImpl true)
        ((vRecv (hkM true) esM.g P (esM.g.st P) c none).run esM.h)).run (fun _ => false, tblL)) >>= kSide true)
    refine vRecv_forged_coupled C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c none
      kLoc kSide
      (fun hLoc' hM' tblM' tblL' =>
        forgedPhase1_exit_halted ℓ Pt C Dh encPt encT idOf q qep tL par ks (k none)
          { esLoc with h := hLoc', abort := true }
          { esM with h := hM', abort := true }
          { esM with h := hM', abort := true }
          none none tblM' tblL' rfl rfl hinv.ctx_eq)
      (fun lhs rhsF hL' tblL' hlf => by
        apply leAdd_of_la_one
        exact forged_lfWin_aborted_eq_one
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par true)
          1 qep locFs.maxSkip tL (pubImpl true)
          (pubFsMultiImpl_inl_run _) (k none) { esM with h := hL', abort := true } none
          (fun _ => false, tblL') rfl hlf)
      (fun rsMap' hLoc' hM' tblM' tblL' hinv' =>
        ih (some .rejected) hinv')
      (fun stLoc' stM' idxOut pmOut rsMap' hLoc' hM' tblM' tblL' hacc hoff_inv => by
        dsimp only [kLoc, kSide, postInjLoc, postInjM]
        by_cases hqep_gt : qep + 1 < c.1.1
        · have hoff : isTargetEp qep tL par c.1.1 = false := by
            by_contra htar
            have htar' : isTargetEp qep tL par c.1.1 = true := Bool.eq_true_of_not_eq_false htar
            have hle := (isTargetEp_imp htar').2.1
            omega
          simp only [hqep_gt, ↓reduceIte]
          exact ih (some .rejected) (hoff_inv hoff)
        · simp only [hqep_gt, ↓reduceIte]
          by_cases htriv : esLoc.g.trivial 3 ⟨P.other, c.1.1, idxOut⟩ = true
          · simp only [htriv, ↓reduceIte]
            exact ih (some (.accepted c.1.1 idxOut (some pmOut)))
              (hacc ⟨P.other, c.1.1, idxOut⟩ rfl)
          · have htrivF : esLoc.g.trivial 3 ⟨P.other, c.1.1, idxOut⟩ = false := Bool.eq_false_iff.mpr htriv
            simp only [htrivF, Bool.false_eq_true, ↓reduceIte]
            by_cases hadm : lastLeakGuessAdmissible 3 tL c.1.1 = true
            · simp only [hadm, ↓reduceIte]
              have hctx_win : eraseCtxSt { esM.g with win := true } = eraseCtxSt { esLoc.g with win := true } := by
                cases hm : esM.g; cases hl : esLoc.g
                have hc := hinv.ctx_eq; rw [hm, hl] at hc
                dsimp [eraseCtxSt] at hc ⊢; injection hc; subst_vars; rfl
              exact forgedPhase1_exit_halted ℓ Pt C Dh encPt encT idOf q qep tL par ks (k (some .rejected))
                { esLoc with g := { esLoc.g with win := true }, h := hLoc' }
                { esM with g := { esM.g with win := true }, h := hM' }
                { esM with g := { esM.g with win := true }, h := hM' }
                (if isNF then some c.1.1 else none)
                (if isNF then some c.1.1 else none)
                tblM' tblL' (by simp) (hinv.not_abort.2.trans hinv.not_abort.1.symm) hctx_win
            · have hadmF : lastLeakGuessAdmissible 3 tL c.1.1 = false := Bool.eq_false_iff.mpr hadm
              have hoff : isTargetEp qep tL par c.1.1 = false := by
                by_contra htar
                have htar' : isTargetEp qep tL par c.1.1 = true := Bool.eq_true_of_not_eq_false htar
                have hlga := (isTargetEp_imp htar').2.2.2.2.1
                rw [hadmF] at hlga; cases hlga
              simp only [hadmF, Bool.false_eq_true, ↓reduceIte]
              exact ih (some .rejected) (hoff_inv hoff))

private theorem forgedPhase1_sim
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (oa : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    {rem : ℕ} (hq : _root_.CryptoGames.SM.MakesAtMostQueries oa rem)
    (hsh : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) oa)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep rem tL par ks ssMap rsMap esLoc esM tblM tblL) :
    LeAdd (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks oa esLoc none)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par false oa esM none tblM)
      (runSideForged C Dh encPt encT idOf ℓ q qep tL par true oa esM none tblL) := by
  induction oa using OracleComp.inductionOn generalizing rem ssMap rsMap esLoc esM tblM tblL with
  | pure _ =>
    have hlf : esM.h.lfWin = false := hinv.htbl.not_lfWin
    unfold runLocForged runSideForged LeAdd
    simp [simulateQ_pure, StateT.run_pure, forgedOut, hlf]
  | query_bind qy k ih =>
    rcases sendMsgsOk_query_bind qy k hsh with ⟨hbad0, hsh_k⟩
    rcases qy with n | sm_q
    · have hq_k := makesAtMostQueries_inl n k hq
      dsimp only [runLocForged, runSideForged]
      rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
        simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
        map_bind, map_bind]
      have hS : (implLocalForgedSlot
          (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
            (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL (.inl n)).run (esLoc, none) =
          (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec (BitVec 256))) (.inl n)) >>=
            fun u => pure (u, (esLoc, none))) := by
        dsimp only [implLocalForgedSlot, HAdd.hAdd, Add.add, QueryImpl.add, stateT_lift_run]
        rfl
      have hM : ∀ la : Bool, (implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL (.inl n)).run (esM, none) =
          (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec _ _ _ _ _) (.inl n)) >>=
            fun u => pure (u, (esM, none))) := fun la => by
        dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add, stateT_lift_run]
        rfl
      have hLoc_inl : simulateQ (keySlotFixedImplF ks)
          (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec (BitVec 256))) (.inl n)) >>=
            fun u => pure (u, (esLoc, (none : Option ℕ)))) =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>=
            fun u => pure (u, (esLoc, (none : Option ℕ)))) := by
        rw [simulateQ_query_bind]
        dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
          keySlotFixedImplF, HAdd.hAdd, Add.add, QueryImpl.add, QueryImpl.ofLift_apply]
        congr 1
      have hM_inl : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
          (simulateQ (pubFsMultiImpl
            (fsImpl (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf)
              (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
            (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec _ _ _ _ _) (.inl n)) >>=
              fun u => pure (u, (esM, (none : Option ℕ))))).run (fun _ => false, tbl) =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>= fun u =>
            pure ((u, (esM, (none : Option ℕ))), (fun _ => false, tbl))) := fun la tbl => by
        rw [simulateQ_query_bind]
        dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
        rw [StateT.run_bind, pubFsMultiImpl_inl_run, bind_assoc]
        congr 1
      rw [hS, hM false, hM true, hLoc_inl, hM_inl false tblM, hM_inl true tblL,
        bind_assoc, bind_assoc, bind_assoc]
      exact leAdd_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ =>
        ih u (hq_k u) (hsh_k u) hinv
    · rcases makesAtMostQueries_inr sm_q k hq with ⟨rem', rfl, hq_k⟩
      rcases sm_q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
      · have hshort : m.1.shortB = true := by
          simp only [_root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg,
            Bool.not_eq_false'] at hbad0
          exact atomicShortPubB_imp_shortB hbad0
        exact step_vSend_forged C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P m r hshort k
          (fun u => ih u (hq_k u) (hsh_k u))
      · dsimp only [runLocForged, runSideForged]
        rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
        dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
        rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, bind_assoc,
          simulateQ_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
          map_bind, map_bind]
        have hS : (implLocalForgedSlot
            (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
              (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par)
            1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL
            (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esLoc, none) =
            pure (none, (esLoc, none)) := by
          simp only [implLocalForgedSlot, HAdd.hAdd, Add.add, QueryImpl.add, StateT.run_pure]
        have hM : ∀ la : Bool, (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
            1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL
            (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esM, none) =
            pure (none, (esM, none)) := fun la => by
          simp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add, StateT.run_pure]
        rw [hS, hM false, hM true]
        simp only [simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih none (hq_k none) (hsh_k none) (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv)
      · exact step_deliver_forged C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c k
          (fun u => ih u (hq_k u) (hsh_k u))
      · exact step_inject_forged C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c k
          (fun u => ih u (hq_k u) (hsh_k u))
      · exact step_corrupt_forged C Dh encPt encT idOf ℓ q qep rem' tL par ks hinv P k
          (fun u => ih u (hq_k u) (hsh_k u))


private theorem localAuthBucketForgedHdrSlot_leAdd_pubFs
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) :
    let M_sess := mSessMain q qep tL
    let side := fun (la : Bool) =>
      Prod.fst <$> (simulateQ (pubFsMultiImpl
        (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
        (redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam 1 qep false la tL par A)).run
        (fun _ => false, fun i => hInit (bs i) (.seed (ks i)))
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        (localAuthBucketForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
          (sIdxForged q tL) 1 qep M_sess tL par A))
      (side false) (side true) := by
  intro M_sess side
  let pubImpl := fun (la : Bool) =>
    pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
  let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
  have hSide_eq : ∀ la : Bool, side la =
      (((simulateQ (pubImpl la)
          ((initFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep false tL par).run {})).run
          (fun _ => false, tbl0)) >>=
        fun ⟨⟨⟨vA, vB⟩, h0⟩, pSt⟩ =>
          Prod.fst <$> (simulateQ (pubImpl la) do
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth
                (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
                1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) A).run
                ({ g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                   h := h0, abort := false }, none)
            if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run pSt) := by
    intro la
    unfold side redFSAuthMultiBucket
    rw [simulateQ_bind, StateT.run_bind, map_bind]
    congr 1; funext ⟨⟨⟨vA, vB⟩, h0⟩, pSt⟩
    cases la
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 2
      have hbody :
          ((simulateQ (implFSMultiBucketAuth
              (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par false)
              1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) A).run
              ({ g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                 h := h0, abort := false }, none) >>=
            fun x => match x.2.2 with
              | none => pure false
              | some tWin => pure (!x.2.1.abort && x.2.1.g.win &&
                  authLosingConditionsAvoided 3 tL tWin x.2.1.g &&
                  (decide (Party.senderOf tWin == Party.A) == par))) =
          ((simulateQ (implFSMultiBucketAuth
              (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par false)
              1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) A).run
              ({ g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                 h := h0, abort := false }, none) >>=
            fun x => pure (forgedOut 3 tL par x.2.1 x.2.2)) := by
        congr 1; funext x; cases x.2.2 <;> rfl
      exact congrArg (simulateQ (pubImpl false)) hbody
    · rfl
  have hLoc_eq :
      simulateQ (keySlotFixedImplF ks)
        (localAuthBucketForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
          (sIdxForged q tL) 1 qep M_sess tL par A) =
      (simulateQ (keySlotFixedImplF ks)
        ((initLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
          (sIdxForged q tL) 1 qep M_sess tL par).run {}) >>=
        fun ⟨vs, h0⟩ =>
          match vs with
          | none => pure false
          | some (vA, vB) =>
            runLocForged C Dh encPt encT idOf ℓ q qep tL par ks A
              { g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                h := h0, abort := false } none) := by
    unfold localAuthBucketForgedSlot runLocForged
    rw [simulateQ_bind]
    congr 1; funext ⟨vs, h0⟩
    cases vs with
    | none => simp [simulateQ_pure]
    | some vp => rcases vp with ⟨vA, vB⟩; rfl
  rw [hLoc_eq, hSide_eq false, hSide_eq true]
  have hInitL :
      (simulateQ (keySlotFixedImplF ks)
        ((initLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
          (sIdxForged q tL) 1 qep M_sess tL par).run {}) >>=
        fun ⟨vs, h0⟩ =>
          match vs with
          | none => pure false
          | some (vA, vB) =>
            runLocForged C Dh encPt encT idOf ℓ q qep tL par ks A
              { g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                h := h0, abort := false } none) =
      (($ᵗ _) >>= fun kr => ($ᵗ _) >>= fun kc =>
        simulateQ (keySlotFixedImplF ks)
          ((rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep M_sess tL par 0 false lam
            ((rootPRNG C.F encPt).init kr)).run {}) >>=
        fun ⟨⟨σ, k0⟩, h0⟩ =>
          let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ
            ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k0)
            ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k0)
          runLocForged C Dh encPt encT idOf ℓ q qep tL par ks A
            { g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
              h := h0, abort := false } none) := by
    unfold initLocalForgedSlot
    simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      run_sampleT_fixedF, bind_assoc, pure_bind]
  have hInitM : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
      (((simulateQ (pubImpl la)
          ((initFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep false tL par).run {})).run
          (fun _ => false, tbl)) >>=
        fun ⟨⟨⟨vA, vB⟩, h0⟩, pSt⟩ =>
          Prod.fst <$> (simulateQ (pubImpl la) do
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth
                (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
                1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) A).run
                ({ g := { st := (fun P => match P with | .A => vA | .B => vB), b := false },
                   h := h0, abort := false }, none)
            if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run pSt) =
      (($ᵗ _) >>= fun kr => ($ᵗ _) >>= fun kc =>
        ((simulateQ (pubImpl la)
          ((rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par 0 false lam
            ((rootPRNG C.F encPt).init kr)).run {})).run (fun _ => false, tbl)) >>=
        fun ⟨⟨⟨σ, k0, _⟩, h0⟩, pSt⟩ =>
          let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ
            (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k0) : Fig8SS ⊕ ℕ)
            (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k0) : Fig8RS ⊕ ℕ)
          Prod.fst <$> (simulateQ (pubImpl la) do
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth
                (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
                1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) A).run
                ({ g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
                   h := h0, abort := false }, none)
            if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run pSt) := by
    intro la tbl
    unfold initFSMultiBucketAuth
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, simulateQ_bind, simulateQ_pure,
      run_sampleT_inl_gen (pubImpl la) (pubFsMultiImpl_inl_run _), bind_assoc, pure_bind]
  rw [hInitL, hInitM false tbl0, hInitM true tbl0]
  refine leAdd_bind ($ᵗ _) fun kr _ => ?_
  refine leAdd_bind ($ᵗ _) fun kc _ => ?_
  cases tL with
  | some l =>
    have hvF : validGuessBucketParAuth 1 (some l) par 0 = false := by
      simp [validGuessBucketParAuth, lastLeakGuessAdmissible, healedBy]
    have hrootL : ((rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q (some l)) 1 qep M_sess
        (some l) par 0 false lam ((rootPRNG C.F encPt).init kr) :
        ForgedSlotHM Pt Fig8Sig Fig8K Pt (Fig8Sig × Fig8K)).run {}) =
        pure (((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam), {}) := by
      unfold rootLocalForgedSlot
      simp [healEpoch]
    have hrootM : ((rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep (some l) par 0 false lam
        ((rootPRNG C.F encPt).init kr) :
        _root_.CryptoGames.SM.Engine.HM
          (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
          (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
          (Fig8Sig × Fig8K × Option Pt)).run {}) =
        pure ((((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1,
               ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).2, none), {}) := by
      unfold rootFSMultiBucketAuth
      simp [healEpoch, hvF]
    rw [hrootL, hrootM]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact forgedPhase1_sim C Dh hD encPt encT idOf ℓ hℓ q qep (some l) par ks A hq hsh
      (mkParties_forgedPhase1Inv C encT idOf ℓ q qep (some l) par ks bs
        ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc)
        ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1
        ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).2 {} {} rfl
        (hookTableInv_empty Pt q qep (some l) par ks))
  | none =>
    have hrootL : ((rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q none) 1 qep M_sess
        none par 0 false lam ((rootPRNG C.F encPt).init kr) :
        ForgedSlotHM Pt Fig8Sig Fig8K Pt (Fig8Sig × Fig8K)).run {}) =
        ((lookupLocalForgedSlotF (sIdxForged q none) M_sess false 0 lam).run {} >>=
          fun ⟨kLookup, h'⟩ =>
            pure ((((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1, kLookup), h')) := by
      unfold rootLocalForgedSlot
      simp [healEpoch]
    rw [hrootL, simulateQ_bind, bind_assoc]
    have hLoc_pure : ∀ x : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt,
        (simulateQ (keySlotFixedImplF ks)
          (pure ((((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1, x.1), x.2)) >>=
          fun ⟨⟨σ, k0⟩, h0⟩ =>
            let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k0)
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k0)
            runLocForged C Dh encPt encT idOf ℓ q qep none par ks A
              { g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
                h := h0, abort := false } none) =
        (let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc)
            ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1
            ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender x.1)
            ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver x.1);
         runLocForged C Dh encPt encT idOf ℓ q qep none par ks A
           { g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
             h := x.2, abort := false } none) := fun _ => by
      rw [simulateQ_pure, pure_bind]
    conv => arg 1; simp only [hLoc_pure]
    let mkES (σ : Fig8Sig) (kVal : Fig8K)
        (h : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) : MultiES Pt ℓ :=
      let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ
        (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender kVal) : Fig8SS ⊕ ℕ)
        (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal) : Fig8RS ⊕ ℕ)
      { g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
        h := h, abort := false }
    have hM_run : ∀ la : Bool,
        (((simulateQ (pubImpl la)
          ((rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep none par 0 false lam
            ((rootPRNG C.F encPt).init kr)).run {})).run (fun _ => false, tbl0)) >>=
          fun ⟨⟨⟨σ, k0, _⟩, h0⟩, pSt⟩ =>
            let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ
              (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k0) : Fig8SS ⊕ ℕ)
              (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k0) : Fig8RS ⊕ ℕ)
            Prod.fst <$> (simulateQ (pubImpl la) do
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth
                  (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false none par la)
                  1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false none) A).run
                  ({ g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
                     h := h0, abort := false }, none)
              if la then return es.h.lfWin else return forgedOut 3 none par es winEp).run pSt) =
        (((simulateQ (pubImpl la)
          ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
            0 lam).run {})).run (fun _ => false, tbl0)) >>=
          fun x =>
            Prod.fst <$> (simulateQ (pubImpl la) do
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth
                  (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false none par la)
                  1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false none) A).run
                  (mkES ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1 x.1.1 x.1.2, none)
              if la then return es.h.lfWin else return forgedOut 3 none par es winEp).run x.2) := by
      intro la
      have hrootM0 :
          ((rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep none par 0 false lam
            ((rootPRNG C.F encPt).init kr) :
            _root_.CryptoGames.SM.Engine.HM
              (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
              (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
              (Fig8Sig × Fig8K × Option Pt)).run {}) =
          ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
            0 lam).run {} >>=
            fun ⟨kLookup, s1⟩ =>
              pure ((((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1,
                kLookup, if validGuessBucketParAuth 1 none par 0 then some lam else none), s1)) := by
        unfold rootFSMultiBucketAuth
        by_cases hv0 : validGuessBucketParAuth 1 none par 0 = true
        · simp [hv0, healEpoch]
        · have hv0F : validGuessBucketParAuth 1 none par 0 = false := Bool.eq_false_iff.mpr hv0
          simp [hv0F, healEpoch]
      rw [hrootM0, simulateQ_bind, StateT.run_bind, bind_assoc]
      congr 1
    rw [hM_run false, hM_run true]
    let kLoc0 (p : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt) : ProbComp Bool :=
      let ps := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc)
        ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1
        ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender p.1)
        ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver p.1)
      runLocForged C Dh encPt encT idOf ℓ q qep none par ks A
        { g := { st := (fun P => match P with | .A => ps.1 | .B => ps.2), b := false },
          h := p.2, abort := false } none
    let kSide0 (la : Bool)
        (x : (Fig8K × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
          ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : ProbComp Bool :=
      Prod.fst <$> (simulateQ (pubImpl la) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false none par la)
            1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false none) A).run
            (mkES ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1 x.1.1 x.1.2, none)
        if la then return es.h.lfWin else return forgedOut 3 none par es winEp).run x.2
    refine lookup_off_step (C := C) (encT := encT) (idOf := idOf) (tblM := tbl0) (tblL := tbl0)
      (isTargetEp_zero qep none par) lam (hookTableInv_empty Pt q qep none par ks) kLoc0 kSide0 ?_
    intro kVal hLoc' hM' hbook _ _ htbl'
    have hbook0 : hM'.book = fun _ => none := hbook
    exact forgedPhase1_sim C Dh hD encPt encT idOf ℓ hℓ q qep none par ks A hq hsh
      (mkParties_forgedPhase1Inv C encT idOf ℓ q qep none par ks bs
        ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc)
        ((rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam).1 kVal hLoc' hM' hbook0 htbl')

/-! ### Top-Level Assembly -/

private theorem multiSessPubToAD_offRange_of_ge_zero {Pt : Type} {ℓ : ℕ}
    (AdvPub : MultiSessPubFsAdv Pt ℓ) (M_sess : ℕ)
    (hqb : ∀ idx, M_sess ≤ idx →
      AdvPub.IsQueryBoundP
        (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0) :
    (multiSessPubToAD protoSignalCodec AdvPub).IsQueryBoundP
      (fun t => sessOffRange M_sess t = true) 0 := by
  apply isQueryBoundP_sessOffRange_of_ge_zero
  intro idx hge
  refine (multiSessPubToAD_isQueryBoundP_sessQueryAt protoSignalCodec AdvPub idx 0 ?_).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx
  exact (hqb idx hge).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx

private theorem localAuthBucketForgedHdrPar_le_eager_pubFsMultiImpl
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let M_sess := mSessMain q qep tL
    let runSide := fun (la : Bool) =>
      sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) 0 M_sess >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
          Prod.fst <$> (simulateQ (pubFsMultiImpl
            (fsImpl (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf)
              (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
            (redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
              lam 1 qep false la tL par A)).run
            (fun _ => false, fun i => hInit (bs i) (.seed (ks i)))
    𝒟[localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      𝒟[runSide false] {true} + 𝒟[runSide true] {true} := by
  intro M_sess runSide
  rw [localAuthBucketForgedHdrPar_eq_eager_ks (dhScheme Dh) (rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam (0 : BitVec 256)
    (sIdxForged q tL) 1 qep M_sess tL par A]
  refine leAdd_bind (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) 0 M_sess) fun ks _ => ?_
  refine leAdd_bind_dummy_loc (sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess) fun bs _ => ?_
  exact localAuthBucketForgedHdrSlot_leAdd_pubFs ℓ Pt C Dh hD encPt encT idOf lam hℓ q qep
    tL par A hq hsh ks bs

attribute [local irreducible] redFSAuthMultiBucketProg in
theorem localAuthBucketForgedHdrPar_le_multiSessRealWinProb
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q B0 qep : ℕ)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let AdvBr := fun la =>
      multiSessPubToAD protoSignalCodec
        ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
            false la tL par).eval (fun _ => A) ())
    𝒟[localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf AdvBr false +
        multiSessRealWinProb C ℓ encT idOf AdvBr true := by
  intro AdvBr
  have _ := hDh; have _ := hinj; have _ := hdum
  have hSide : ∀ la : Bool,
      𝒟[sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) 0 (mSessMain q qep tL) >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false (mSessMain q qep tL) >>= fun bs =>
            Prod.fst <$> (simulateQ (pubFsMultiImpl
              (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf)
                (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
              (redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
                lam 1 qep false la tL par A)).run
              (fun _ => false, fun i => hInit (bs i) (.seed (ks i)))] {true} ≤
        multiSessRealWinProb C ℓ encT idOf AdvBr la := by
    intro la
    let AdvPub : MultiSessPubFsAdv Pt ℓ :=
      (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        false la tL par).eval (fun _ => A) ()
    have hoff : (multiSessPubToAD protoSignalCodec AdvPub).IsQueryBoundP
        (fun t => sessOffRange (mSessMain q qep tL) t = true) 0 := by
      refine multiSessPubToAD_offRange_of_ge_zero AdvPub (mSessMain q qep tL) fun idx hge => ?_
      dsimp only [AdvPub]
      exact (redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero ℓ Pt C Dh encPt encT idOf lam
        q B0 qep false la tL par A hq idx
        (Or.inl (by simpa [mSessMain, Nat.mul_comm] using hge))).of_imp fun x hx => by
          rcases x with _ | ⟨_, _⟩ <;> exact hx
    have hEager := multiFsEager_le_real
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (mSessMain q qep tL) (0 : BitVec 256) la
      (multiSessPubToAD protoSignalCodec AdvPub) hoff
    have hEval : AdvPub =
        redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep false la tL par A := by
      exact (redFSAuthMultiBucketShallow_eval_eq ℓ Pt C Dh encPt encT idOf lam
        q B0 qep false la tL par A hq).trans
        (redFSAuthMultiBucket_atomic_eq_lFS ℓ Pt C Dh encPt encT idOf lam
          q B0 qep hB0 false la tL par A hq hsh)
    have hEq :
        (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) 0 (mSessMain q qep tL) >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false (mSessMain q qep tL) >>= fun bs =>
            Prod.fst <$> (simulateQ (sessLift
              (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf)
                (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
              (multiSessPubToAD protoSignalCodec AdvPub)).run
              (fun i => hInit (bs i) (.seed (ks i)))) =
        (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) 0 (mSessMain q qep tL) >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false (mSessMain q qep tL) >>= fun bs =>
            Prod.fst <$> (simulateQ (pubFsMultiImpl
              (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf)
                (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
              (redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
                lam 1 qep false la tL par A)).run
              (fun _ => false, fun i => hInit (bs i) (.seed (ks i)))) := by
      congr 1; funext ks; congr 1; funext bs
      rw [simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl, hEval]
    rw [← hEq]
    exact hEager
  exact (localAuthBucketForgedHdrPar_le_eager_pubFsMultiImpl ℓ Pt C Dh hD encPt encT idOf lam
    hℓ q qep tL par A hq hsh).trans (add_le_add (hSide false) (hSide true))



end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedHop
