/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedInr
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

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSendRec

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


abbrev locFsOf {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :=
  lFS C protoSignalCodec ℓ encT idOf maxForwardJumps

abbrev hkLocOf {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool) :=
  hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFsOf C ℓ encT idOf)
    (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par

abbrev hkMOf {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par la : Bool) :=
  hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
    (locFsOf C ℓ encT idOf) 1 qep false tL par la

abbrev pubImplOf {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool) :=
  pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))

abbrev fsSendStepSlot {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (s₁Loc : Ctx (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (vpLoc1 : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS) :
    ForgedSlotHM Pt Fig8Sig Fig8K Pt (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × Fig8C Pt)) :=
  let h : Header Pt := (vpLoc1.tcur, vpLoc1.curCkaMsg)
  match vpLoc1.vS with
  | none => pure (some (vpLoc1, (h, default)))
  | some v => do
    match ← (hkLocOf C Dh encPt encT idOf ℓ q qep tL par).fsSend s₁Loc P vpLoc1.tcur v h m none with
    | none => pure none
    | some (v', e) => pure (some ({ vpLoc1 with vS := some v' }, (h, e)))

abbrev fsSendStepM {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (s₁M : Ctx (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (vpM1 : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ)) :
    _root_.CryptoGames.SM.Engine.HM
      (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
      (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
      (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × Fig8C Pt)) :=
  let h : Header Pt := (vpM1.tcur, vpM1.curCkaMsg)
  match vpM1.vS with
  | none => pure (some (vpM1, (h, default)))
  | some v => do
    match ← (hkMOf C Dh encPt encT idOf ℓ q qep tL par la).fsSend s₁M P vpM1.tcur v h m none with
    | none => pure none
    | some (v', e) => pure (some ({ vpM1 with vS := some v' }, (h, e)))


theorem fsSend_record_coupled
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : m.1.shortB = true)
    {s₁Loc : Ctx (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS (LibsignalMsgPublicPart × Plain ℓ) Fig8E}
    {s₁M : Ctx (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) (LibsignalMsgPublicPart × Plain ℓ) Fig8E}
    (hepLoc : esLoc.g.epMgmt 3 qep P r.isSome = some s₁Loc)
    (hctx₁ : eraseCtxSt s₁M = eraseCtxSt s₁Loc)
    (hstLoc1 : s₁Loc.st = esLoc.g.st)
    (hstM1 : s₁M.st = esM.g.st)
    (hpl₁ : postLeak tL s₁Loc = false)
    (vpLoc1 : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS)
    (vpM1 : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))
    (hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
    (hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
    (hvp1 : VPAlign q qep rem' tL par ssMap rsMap P vpLoc1 vpM1)
    (htcur_ep : vpLoc1.tcur = s₁Loc.epoch P)
    (hsends1 : P.sendsIn vpLoc1.tcur = true)
    (htcur_ge : (esLoc.g.st P).tcur ≤ vpLoc1.tcur)
    (htcur_form : vpLoc1.tcur =
      if P.sendsIn ((s₁Loc.st P).tcur + 1) then (s₁Loc.st P).tcur + 1 else (s₁Loc.st P).tcur)
    (htbl1 : HookTableInv Pt q qep rem' tL par ks hLoc1 hM1)
    (hbook1 : hM1.book = esM.h.book)
    (k : Option (Fig8C Pt) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (ih : ∀ u {ssMap' rsMap' esLoc' esM' tblM' tblL'},
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap' rsMap' esLoc' esM' tblM' tblL' →
      LeAdd (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par true (k u) esM' none tblL')) :
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m vpLoc1).run hLoc1) >>=
        fun p =>
          match p.1 with
          | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
              { esLoc with h := p.2, abort := true } none
          | some (st', ct) =>
            let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
            runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
              { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none)
      (((simulateQ (pubImplOf C ℓ encT idOf false)
        ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par false s₁M P m vpM1).run hM1)).run
          (fun _ => false, tblM)) >>=
        fun q0 =>
          Prod.fst <$> (simulateQ (pubImplOf C ℓ encT idOf false) do
            let (u, es1, we1) := match q0.1.1 with
              | none => (none, { esM with h := q0.1.2, abort := true }, none)
              | some (st', ct) =>
                let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                  ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth (hkMOf C Dh encPt encT idOf ℓ q qep tL par false)
                1 qep (locFsOf C ℓ encT idOf).maxSkip false tL) (k u)).run (es1, we1)
            if false then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2)
      (((simulateQ (pubImplOf C ℓ encT idOf true)
        ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par true s₁M P m vpM1).run hM1)).run
          (fun _ => false, tblL)) >>=
        fun q0 =>
          Prod.fst <$> (simulateQ (pubImplOf C ℓ encT idOf true) do
            let (u, es1, we1) := match q0.1.1 with
              | none => (none, { esM with h := q0.1.2, abort := true }, none)
              | some (st', ct) =>
                let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                  ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
            let (_, es, winEp) ←
              (simulateQ (implFSMultiBucketAuth (hkMOf C Dh encPt encT idOf ℓ q qep tL par true)
                1 qep (locFsOf C ℓ encT idOf).maxSkip false tL) (k u)).run (es1, we1)
            if true then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2) := by
  let locFs := locFsOf C ℓ encT idOf
  let hkLoc := hkLocOf C Dh encPt encT idOf ℓ q qep tL par
  let hkM := hkMOf C Dh encPt encT idOf ℓ q qep tL par
  let pubImpl := pubImplOf C ℓ encT idOf
  let stepSlot := fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m vpLoc1
  let stepM := fun la => fsSendStepM C Dh encPt encT idOf ℓ q qep tL par la s₁M P m vpM1
  have hepM_ep : s₁M.epoch = s₁Loc.epoch := congrArg GameState.epoch hctx₁
  have hidxM_eq : s₁M.idx = s₁Loc.idx := congrArg GameState.idx hctx₁
  have hwin1 : s₁Loc.win = false := by
    unfold GameState.epMgmt GameState.leak at hepLoc
    split_ifs at hepLoc <;> injection hepLoc with hs <;> subst hs <;> exact hinv.not_win
  have htL1 : ∀ cur, s₁Loc.tL = some cur → ∃ lk ∈ s₁Loc.leaks, cur = lk :=
    epMgmt_leaks_tL hinv.leaks_tL hepLoc
  have hcu1 : CompUnhealed s₁Loc := compUnhealed_epMgmt hinv.comp_unhealed hepLoc
  let hdr : Header Pt := (vpLoc1.tcur, vpLoc1.curCkaMsg)
  have hhdrM : (vpM1.tcur, vpM1.curCkaMsg) = hdr := by simp [hdr, hvp1.tcur_eq, hvp1.cka_eq]
  rcases hvp1.vS_align with ⟨hv1, hv2⟩ | ⟨ss, hv1, hv2⟩ |
      ⟨tS, idx, hidx, htS_le, hheS, htarS, hsendsS, htS_eq_fn, hv1, hv2⟩
  · dsimp only [stepSlot, stepM, fsSendStepSlot, fsSendStepM]
    simp only [hhdrM, hv1, hv2, StateT.run_pure, simulateQ_pure, pure_bind, hepM_ep, hidxM_eq]
    refine ih (some (hdr, default)) (ssMap' := ssMap) (rsMap' := rsMap) ?_
    let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, (hdr, default)⟩
    refine
      { not_abort := hinv.not_abort
        not_win := by simp [GameState.record, hwin1]
        not_pl := by simpa [GameState.record, postLeak] using hpl₁
        ctx_eq := eraseCtxSt_record hctx₁
        loc_epoch := locEpochInv_send m hinv.loc_epoch hepLoc hvp1.id_loc htcur_form rfl
        comp_unhealed := compUnhealed_record hcu1 ⟨rfl, rfl⟩
        leaks_tL := fun cur hcur => by
          simpa [GameState.record] using htL1 cur (by simpa [GameState.record] using hcur)
        vp_align := fun Q => by
          simp only [GameState.record]
          by_cases hQ : Q = P
          · subst hQ; simpa using hvp1
          · simp only [Function.update_of_ne hQ, hstLoc1, hstM1]
            let hv := hinv.vp_align Q
            exact { hv with tcur_rem := by have := hv.tcur_rem; omega }
        htbl := htbl1
        ss_fresh := fun t1 idx1 htar1 hi1 hall =>
          hinv.ss_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        rs_fresh := fun t1 idx1 htar1 hi1 hall =>
          hinv.rs_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        sess_inv := fun s1 => by rw [hbook1]; exact hinv.sess_inv s1 }
  · let o := locFs.send ss hdr m
    dsimp only [stepSlot, stepM, fsSendStepSlot, fsSendStepM, hkLoc, hkM, hkLocOf, hkMOf,
      hooksLocalForgedSlot, hooksFSMultiBucketAuth]
    simp only [hhdrM, hv1, hv2, StateT.run_pure, simulateQ_pure, pure_bind,
      hepM_ep, hidxM_eq]
    refine ih (some (hdr, o.2)) (ssMap' := ssMap) (rsMap' := rsMap) ?_
    refine
      { not_abort := hinv.not_abort
        not_win := by simp [GameState.record, hwin1]
        not_pl := by simpa [GameState.record, postLeak] using hpl₁
        ctx_eq := eraseCtxSt_record hctx₁
        loc_epoch := locEpochInv_send m hinv.loc_epoch hepLoc hvp1.id_loc htcur_form rfl
        comp_unhealed := compUnhealed_record hcu1 ⟨rfl, rfl⟩
        leaks_tL := fun cur hcur => by
          simpa [GameState.record] using htL1 cur (by simpa [GameState.record] using hcur)
        vp_align := fun Q => by
          simp only [GameState.record]
          by_cases hQ : Q = P
          · subst hQ
            simp only [Function.update_self]
            exact { hvp1 with vS_align := Or.inr (Or.inl ⟨o.1, rfl, rfl⟩) }
          · simp only [Function.update_of_ne hQ, hstLoc1, hstM1]
            let hv := hinv.vp_align Q
            exact { hv with tcur_rem := by have := hv.tcur_rem; omega }
        htbl := htbl1
        ss_fresh := fun t1 idx1 htar1 hi1 hall =>
          hinv.ss_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        rs_fresh := fun t1 idx1 htar1 hi1 hall =>
          hinv.rs_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        sess_inv := fun s1 => by rw [hbook1]; exact hinv.sess_inv s1 }
  · have htS : tS = vpLoc1.tcur := htS_eq_fn hsends1
    let sIdx := sIdxForged q tL tS idx
    rcases isTargetEp_imp htarS with ⟨_, _, _, _, _, hhS, _, _, _, _⟩
    have hsafeLoc : s₁Loc.safeCh 3 P = true := by
      unfold GameState.safeCh
      rw [← htcur_ep, ← htS]
      exact healedBy_of_not_postLeak tL s₁Loc tS hpl₁ hhS
    have hsafeM : s₁M.safeCh 3 P = true :=
      (eraseCtxSt_safeCh hctx₁).trans hsafeLoc
    let o := locFs.send (ssMap sIdx) hdr m
    let bk := (esM.h.book sIdx).getD {}
    let cnt' := bk.fsCount + 1
    let bk' : FSMultiBook Pt Fig8E := { bk with fsCount := cnt', fsTrans := (cnt', hdr, o.2) :: bk.fsTrans }
    have hℓ_bound : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
    rcases forgedSessInv_transmit C signalRoundTripShort_proto ℓ hℓ_bound encT idOf
        (hinv.sess_inv sIdx) hdr m hshort with ⟨sM', sL', htrM, htrL, hsinv'⟩
    have hSlot_run : simulateQ (keySlotFixedImplF ks) (stepSlot.run hLoc1) =
        pure (some ({ vpLoc1 with vS := some o.1 }, (hdr, o.2)), hLoc1) := by
      have hv1' : vpLoc1.vS = some (ssMap sIdx) := hv1
      dsimp only [stepSlot, fsSendStepSlot, hkLoc, hkLocOf, hooksLocalForgedSlot]
      simp only [hv1', StateT.run_pure, simulateQ_pure, pure_bind]
      rfl
    let hM2 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E :=
      { hM1 with book := Function.update hM1.book sIdx (some bk') }
    have hM_run : ((simulateQ (pubImpl false) ((stepM false).run hM1)).run (fun _ => false, tblM)) =
        pure ((some ({ vpM1 with vS := some (.inr sIdx) }, (hdr, o.2)), hM2),
          (fun _ => false, Function.update tblM sIdx sM')) := by
      have hv2' : vpM1.vS = some (.inr sIdx) := hv2
      dsimp only [stepM, fsSendStepM, hkM, hkMOf, pubImpl, pubImplOf, hooksFSMultiBucketAuth]
      simp only [hhdrM, hv2', StateT.run_bind, StateT.run_get, pure_bind, hsafeM,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, modify_run,
        liftFSMultiBucket_transmit_run C ℓ encT idOf false sIdx hdr m hM1 tblM htrM]
      simp only [hM2, bk', cnt', bk, hbook1]
      rfl
    have hL_run : ((simulateQ (pubImpl true) ((stepM true).run hM1)).run (fun _ => false, tblL)) =
        pure ((some ({ vpM1 with vS := some (.inr sIdx) }, (hdr, o.2)), hM2),
          (fun _ => false, Function.update tblL sIdx sL')) := by
      have hv2' : vpM1.vS = some (.inr sIdx) := hv2
      dsimp only [stepM, fsSendStepM, hkM, hkMOf, pubImpl, pubImplOf, hooksFSMultiBucketAuth]
      simp only [hhdrM, hv2', StateT.run_bind, StateT.run_get, pure_bind, hsafeM,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, modify_run,
        liftFSMultiBucket_transmit_run C ℓ encT idOf true sIdx hdr m hM1 tblL htrL]
      simp only [hM2, bk', cnt', bk, hbook1]
      rfl
    rw [hSlot_run, hM_run, hL_run]
    simp only [pure_bind, hepM_ep, hidxM_eq]
    refine ih (some (hdr, o.2))
      (ssMap' := Function.update ssMap sIdx o.1)
      (rsMap' := rsMap)
      (tblM' := Function.update tblM sIdx sM')
      (tblL' := Function.update tblL sIdx sL') ?_
    refine
      { not_abort := hinv.not_abort
        not_win := by simp [GameState.record, hwin1]
        not_pl := by simpa [GameState.record, postLeak] using hpl₁
        ctx_eq := eraseCtxSt_record hctx₁
        loc_epoch := locEpochInv_send m hinv.loc_epoch hepLoc hvp1.id_loc htcur_form rfl
        comp_unhealed := compUnhealed_record hcu1 ⟨rfl, rfl⟩
        leaks_tL := fun cur hcur => by
          simpa [GameState.record] using htL1 cur (by simpa [GameState.record] using hcur)
        vp_align := fun Q => by
          simp only [GameState.record]
          by_cases hQ : Q = P
          · subst hQ
            simp only [Function.update_self]
            exact
              { hvp1 with
                vS_align := Or.inr (Or.inr ⟨tS, idx, hidx, htS_le, hheS, htarS, hsendsS,
                  htS_eq_fn, by simp [sIdx], rfl⟩) }
          · simp only [Function.update_of_ne hQ, hstLoc1, hstM1]
            let hv := hinv.vp_align Q
            refine
              { hv with
                tcur_rem := by have := hv.tcur_rem; omega
                vS_align := ?_ }
            rcases hv.vS_align with h1 | h2 | ⟨tQ, idxQ, hiQ, htQ_le, hheQ, htarQ, hsendsQ, hfnQ, hvQ1, hvQ2⟩
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · have hne_t : tQ ≠ tS := fun he => hQ (sendsIn_exclusive hsendsQ (he ▸ hsendsS))
              have hne_s : sIdxForged q tL tQ idxQ ≠ sIdx := fun hs =>
                hne_t (sIdxForged_inj hheQ hheS hiQ hidx hs).1
              exact Or.inr (Or.inr ⟨tQ, idxQ, hiQ, htQ_le, hheQ, htarQ, hsendsQ, hfnQ,
                by simpa [Function.update_of_ne hne_s] using hvQ1, hvQ2⟩)
        htbl :=
          { not_lfWin := htbl1.not_lfWin
            sess_eq := htbl1.sess_eq
            sess_nodup := htbl1.sess_nodup
            sess_rem := htbl1.sess_rem
            ftbl_off := htbl1.ftbl_off
            ftbl_dom := htbl1.ftbl_dom
            ftbl_val := htbl1.ftbl_val
            used_iff := htbl1.used_iff
            cache_off := htbl1.cache_off
            cache_on := htbl1.cache_on }
        ss_fresh := fun t1 idx1 htar1 hi1 hall => by
          rcases isTargetEp_imp htar1 with ⟨_, _, _, _, _, _, hhe1, _, _, _⟩
          have hne_t : t1 ≠ tS := by
            intro he; subst he
            have hlt := hall P hsendsS
            simp [GameState.record, htS] at hlt
          have hne_s : sIdxForged q tL t1 idx1 ≠ sIdx := fun hs =>
            hne_t (sIdxForged_inj hhe1 hheS hi1 hidx hs).1
          rw [Function.update_of_ne hne_s]
          exact hinv.ss_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        rs_fresh := fun t1 idx1 htar1 hi1 hall =>
          hinv.rs_fresh t1 idx1 htar1 hi1 fun R hR => by
            have h1 := hall R hR
            simp only [GameState.record] at h1
            by_cases hRP : R = P
            · subst hRP; simp only [Function.update_self] at h1; omega
            · simpa [Function.update_of_ne hRP, hstLoc1] using h1
        sess_inv := fun s1 => by
          by_cases hs : s1 = sIdx
          · subst hs; simpa [hM2] using hsinv'
          · simpa [hM2, Function.update_of_ne hs, hbook1] using hinv.sess_inv s1 }


set_option maxHeartbeats 400000 in
theorem vSend_start_coins_forged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : m.1.shortB = true)
    {s₁Loc : Ctx (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS (LibsignalMsgPublicPart × Plain ℓ) Fig8E}
    {s₁M : Ctx (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) (LibsignalMsgPublicPart × Plain ℓ) Fig8E}
    (hepLoc : esLoc.g.epMgmt 3 qep P r.isSome = some s₁Loc)
    (hctx₁ : eraseCtxSt s₁M = eraseCtxSt s₁Loc)
    (hstLoc1 : s₁Loc.st = esLoc.g.st)
    (hstM1 : s₁M.st = esM.g.st)
    (hpl₁ : postLeak tL s₁Loc = false)
    (hsends : P.sendsIn ((esLoc.g.st P).tcur + 1) = true)
    (hep_t0 : s₁Loc.epoch P = (esLoc.g.st P).tcur + 1)
    (k : Option (Fig8C Pt) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (ih : ∀ u {ssMap' rsMap' esLoc' esM' tblM' tblL'},
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap' rsMap' esLoc' esM' tblM' tblL' →
      LeAdd (runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideForged C Dh encPt encT idOf ℓ q qep tL par true (k u) esM' none tblL'))
    (c0 : BitVec 256) :
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let hkM := fun (la : Bool) =>
      hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
    let pubImpl := fun (la : Bool) =>
      pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
    let vpLoc := esLoc.g.st P
    let vpM := esM.g.st P
    let t0 := vpLoc.tcur + 1
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
          (mSessMain q qep tL) tL par t0 false ((dhScheme Dh).send vpLoc.γ c0).2.2 vpLoc.root).run esLoc.h) >>=
        fun r0 =>
          simulateQ (keySlotFixedImplF ks)
            ((fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m
              { vpLoc with tcur := t0, γ := ((dhScheme Dh).send vpLoc.γ c0).1,
                           curCkaMsg := some ((dhScheme Dh).send vpLoc.γ c0).2.1, root := r0.1.1,
                           vS := some (locFs.initSender r0.1.2) }).run
              { r0.2 with loc := { r0.2.loc with
                  cache := Function.update r0.2.loc.cache t0
                    (some (((dhScheme Dh).send vpLoc.γ c0).2.1, r0.1.1, r0.1.2)) } }) >>=
          fun p =>
            match p.1 with
            | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
                { esLoc with h := p.2, abort := true } none
            | some (st', ct) =>
              let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
              runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
                { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none)
      (((simulateQ (pubImpl false)
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
                               vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h)).run
          (fun _ => false, tblM)) >>=
        fun p1 =>
          (((simulateQ (pubImpl false)
            ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par false s₁M P m p1.1.1).run p1.1.2)).run p1.2) >>=
          fun q0 =>
            Prod.fst <$> (simulateQ (pubImpl false) do
              let (u, es1, we1) := match q0.1.1 with
                | none => (none, { esM with h := q0.1.2, abort := true }, none)
                | some (st', ct) =>
                  let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                  (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth (hkM false) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
              if false then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2))
      (((simulateQ (pubImpl true)
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
                               vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h)).run
          (fun _ => false, tblL)) >>=
        fun p1 =>
          (((simulateQ (pubImpl true)
            ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par true s₁M P m p1.1.1).run p1.1.2)).run p1.2) >>=
          fun q0 =>
            Prod.fst <$> (simulateQ (pubImpl true) do
              let (u, es1, we1) := match q0.1.1 with
                | none => (none, { esM with h := q0.1.2, abort := true }, none)
                | some (st', ct) =>
                  let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                  (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth (hkM true) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
              if true then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2)) := by
  intro locFs hkM pubImpl vpLoc vpM t0
  have hvp := hinv.vp_align P
  have ht0_pos : 1 ≤ t0 := Nat.succ_le_succ (Nat.zero_le _)
  have hrun_sim_bind : ∀ {α β : Type} (la : Bool)
      (m1 : OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) α)
      (m2 : α → OracleComp (unifSpec + FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) β)
      (st : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
      (simulateQ (pubImpl la) (m1 >>= m2)).run st =
        ((simulateQ (pubImpl la) m1).run st >>= fun p => (simulateQ (pubImpl la) (m2 p.1)).run p.2) := by
    intros; rw [simulateQ_bind, StateT.run_bind]
  let cOut := (dhScheme Dh).send vpLoc.γ c0
  let T' := cOut.2.1
  let ik0 := cOut.2.2
  let σ0 := vpLoc.root
  have hoff_finish : ∀ (hoff : isTargetEp qep tL par t0 = false) (σ' : Fig8Sig) (kVal : Fig8K)
      (hLoc' : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
      (hM' : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
      (hbook' : hM'.book = esM.h.book)
      (htbl' : HookTableInv Pt q qep rem' tL par ks hLoc' hM'),
      LeAdd
        (simulateQ (keySlotFixedImplF ks)
          ((fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m
            { vpLoc with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                         vS := some (locFs.initSender kVal) }).run
            { hLoc' with loc := { hLoc'.loc with cache := Function.update hLoc'.loc.cache t0 (some (T', σ', kVal)) } }) >>=
          fun p =>
            match p.1 with
            | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
                { esLoc with h := p.2, abort := true } none
            | some (st', ct) =>
              let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
              runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
                { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none)
        (((simulateQ (pubImpl false)
          ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par false s₁M P m
            { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                       vS := some (.inl (locFs.initSender kVal)) }).run
            { hM' with cache := Function.update hM'.cache t0 (some (T', σ', kVal, none)) })).run (fun _ => false, tblM)) >>=
          fun q0 =>
            Prod.fst <$> (simulateQ (pubImpl false) do
              let (u, es1, we1) := match q0.1.1 with
                | none => (none, { esM with h := q0.1.2, abort := true }, none)
                | some (st', ct) =>
                  let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                  (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth (hkM false) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
              if false then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2)
        (((simulateQ (pubImpl true)
          ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par true s₁M P m
            { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                       vS := some (.inl (locFs.initSender kVal)) }).run
            { hM' with cache := Function.update hM'.cache t0 (some (T', σ', kVal, none)) })).run (fun _ => false, tblL)) >>=
          fun q0 =>
            Prod.fst <$> (simulateQ (pubImpl true) do
              let (u, es1, we1) := match q0.1.1 with
                | none => (none, { esM with h := q0.1.2, abort := true }, none)
                | some (st', ct) =>
                  let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                  (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth (hkM true) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
              if true then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2) := by
    intro hoff σ' kVal hLoc' hM' hbook' htbl'
    let hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt :=
      { hLoc' with loc := { hLoc'.loc with cache := Function.update hLoc'.loc.cache t0 (some (T', σ', kVal)) } }
    let hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E :=
      { hM' with cache := Function.update hM'.cache t0 (some (T', σ', kVal, none)) }
    let vpLoc1 : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS :=
      { vpLoc with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                   vS := some (locFs.initSender kVal) }
    let vpM1 : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) :=
      { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                 vS := some (.inl (locFs.initSender kVal)) }
    exact fsSend_record_coupled C Dh encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P m r hshort
      hepLoc hctx₁ hstLoc1 hstM1 hpl₁ vpLoc1 vpM1 hLoc1 hM1
      { id_loc := hvp.id_loc
        id_m := hvp.id_m
        γ_eq := rfl
        root_eq := rfl
        cka_eq := rfl
        tcur_eq := rfl
        tcur_rem := by have := hvp.tcur_rem; dsimp only [vpLoc1, vpLoc, t0] at *; omega
        vR_gt := fun t ht => hvp.vR_gt t (by dsimp only [vpLoc1, vpLoc, t0] at *; omega)
        vS_align := Or.inr (Or.inl ⟨locFs.initSender kVal, rfl, rfl⟩)
        vR_align := hvp.vR_align }
      hep_t0.symm hsends
      (Nat.le_succ _)
      (by
        dsimp only [vpLoc1, vpLoc, t0]
        rw [hstLoc1]
        simp only [hsends, ↓reduceIte])
      { htbl' with
        cache_off := fun t1 h1 => by
          by_cases heq : t1 = t0
          · subst heq; simp [hLoc1, hM1]
          · simpa [hLoc1, hM1, Function.update_of_ne heq] using htbl'.cache_off t1 h1
        cache_on := fun t1 h1 => by
          have hne : t1 ≠ t0 := fun heq => by rw [heq, hoff] at h1; cases h1
          simpa [hLoc1, hM1, Function.update_of_ne hne] using htbl'.cache_on t1 h1 }
      hbook' k ih
  by_cases htar : isTargetEp qep tL par t0 = true
  · rcases isTargetEp_imp htar with ⟨h1_dec, _, hqepF, hv, _, _, hhe, hnot1, hnot2, hntlt⟩
    have hqep_lt : ¬(qep + 1 < t0) := by simpa using hqepF
    have ht0_lt_he : ¬(t0 < healEpoch tL) := by omega
    have hrootL : (rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
        (mSessMain q qep tL) tL par t0 false ik0 σ0).run esLoc.h =
        ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) true t0 ik0).run esLoc.h >>=
          fun p0 =>
            pure ((((rootPRNG C.F encPt).up σ0 ik0).1, p0.1), p0.2)) := by
      unfold rootLocalForgedSlot
      simp [h1_dec, hqep_lt, hv, hnot1, ht0_lt_he]
    have hrootM :
        StateT.run (do
            let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0
            let s1 ← get
            let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
            set ({ s2 with cache := Function.update s2.cache t0 (some (T', σ', kVal, optIdx)) })
            let ssv : Fig8SS ⊕ ℕ := match optIdx with
              | none => .inl (locFs.initSender kVal)
              | some sIdx => .inr sIdx
            return ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                               vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h =
        ((hmTargetM ℓ (q + 1) tL t0 ik0).run esM.h >>= fun p0 =>
          pure ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                           root := ((rootPRNG C.F encPt).up σ0 ik0).1, vS := some (.inr p0.1.2) },
                { p0.2 with
                  cache := Function.update p0.2.cache t0
                    (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1.1, some p0.1.2)) })) := by
      unfold rootFSMultiBucketAuth hmTargetM regSessOptMultiBucket
      simp [hqep_lt, hv, hnot2, StateT.run_bind, StateT.run_get, StateT.run_set]
    dsimp only [cOut, T', ik0, σ0] at hrootL hrootM
    rw [hrootL, hrootM]
    rw [simulateQ_bind, bind_assoc, hrun_sim_bind false, hrun_sim_bind true,
      bind_assoc, bind_assoc]
    simp only [StateT.run_pure, simulateQ_pure, pure_bind]
    have hleAdd_of_eq : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
        LeAdd a2 b2 c2 → a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a1 b1 c1 := by
      rintro _ _ _ _ _ _ h rfl rfl rfl; exact h
    refine hleAdd_of_eq
      (lookup_target_step (C := C) (encT := encT) (idOf := idOf) (tblM := tblM) (tblL := tblL)
        htar ik0 hinv.htbl
        (fun p0 =>
          simulateQ (keySlotFixedImplF ks)
            ((fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m
              { vpLoc with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                           root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                           vS := some (locFs.initSender p0.1) }).run
              { p0.2 with loc := { p0.2.loc with
                  cache := Function.update p0.2.loc.cache t0
                    (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1)) } }) >>=
          fun p =>
            match p.1 with
            | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
                { esLoc with h := p.2, abort := true } none
            | some (st', ct) =>
              let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
              runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
                { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none)
        (fun la p0 =>
          ((simulateQ (pubImpl la)
            ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par la s₁M P m
              { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                         root := ((rootPRNG C.F encPt).up σ0 ik0).1, vS := some (.inr p0.1.1.2) }).run
              { p0.1.2 with
                cache := Function.update p0.1.2.cache t0
                  (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1.1.1, some p0.1.1.2)) })).run p0.2) >>=
          fun q0 =>
            Prod.fst <$> (simulateQ (pubImpl la) do
              let (u, es1, we1) := match q0.1.1 with
                | none => (none, { esM with h := q0.1.2, abort := true }, none)
                | some (st', ct) =>
                  let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                  (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
              let (_, es, winEp) ←
                (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
              if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2)
        ?_)
      (congrArg (Bind.bind _) (funext fun p0 =>
        congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl)))
      (congrArg (Bind.bind _) (funext fun p0 =>
        congrArg (Bind.bind _) (funext fun q0 => by
          rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
            exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
              (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
      (congrArg (Bind.bind _) (funext fun p0 =>
        congrArg (Bind.bind _) (funext fun q0 => by
          rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
            exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
              (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
    intro idx kD hLoc' hM' hidx_len hidx_q hbook' _ _ htbl'
    let sIdx := sIdxForged q tL t0 idx
    have hss_eq : locFs.initSender (ks sIdx) = ssMap sIdx := by
      symm
      exact hinv.ss_fresh t0 idx htar hidx_q fun R hR => by
        have hRP : R = P := sendsIn_exclusive hR hsends
        subst hRP; dsimp only [vpLoc, t0]; omega
    let σ' := ((rootPRNG C.F encPt).up σ0 ik0).1
    let hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt :=
      { hLoc' with loc := { hLoc'.loc with cache := Function.update hLoc'.loc.cache t0 (some (T', σ', ks sIdx)) } }
    let hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E :=
      { hM' with cache := Function.update hM'.cache t0 (some (T', σ', kD, some sIdx)) }
    let vpLoc1 : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS :=
      { vpLoc with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                   vS := some (locFs.initSender (ks sIdx)) }
    let vpM1 : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) :=
      { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                 vS := some (.inr sIdx) }
    refine fsSend_record_coupled C Dh encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P m r hshort
      hepLoc hctx₁ hstLoc1 hstM1 hpl₁ vpLoc1 vpM1 hLoc1 hM1
      { id_loc := hvp.id_loc
        id_m := hvp.id_m
        γ_eq := rfl
        root_eq := rfl
        cka_eq := rfl
        tcur_eq := rfl
        tcur_rem := by have := hvp.tcur_rem; dsimp only [vpLoc1, vpLoc, t0] at *; omega
        vR_gt := fun t ht => hvp.vR_gt t (by dsimp only [vpLoc1, vpLoc, t0] at *; omega)
        vS_align := Or.inr (Or.inr ⟨t0, idx, hidx_q, le_rfl, hhe, htar, hsends,
          fun _ => rfl, by simp [vpLoc1, hss_eq, sIdx], rfl⟩)
        vR_align := hvp.vR_align }
      hep_t0.symm hsends
      (Nat.le_succ _)
      (by
        dsimp only [vpLoc1, vpLoc, t0]
        rw [hstLoc1]
        simp only [hsends, ↓reduceIte])
      { htbl' with
        cache_off := fun t1 h1 => by
          have hne : t1 ≠ t0 := fun heq => by rw [heq, htar] at h1; cases h1
          simpa [hLoc1, hM1, Function.update_of_ne hne] using htbl'.cache_off t1 h1
        cache_on := fun t1 h1 => by
          by_cases heq : t1 = t0
          · subst heq
            exact Or.inr ⟨T', σ', kD, idx, hidx_len,
              by simp [hLoc1, sIdx], by simp [hM1, sIdx]⟩
          · simpa [hLoc1, hM1, Function.update_of_ne heq] using htbl'.cache_on t1 h1 }
      hbook' k ih
  · have hoff : isTargetEp qep tL par t0 = false := Bool.eq_false_iff.mpr htar
    have htbl_mono := hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl
    by_cases hqep : qep + 1 < t0
    · have hrootL_q : (rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
          (mSessMain q qep tL) tL par t0 false ik0 σ0).run esLoc.h =
          pure ((((rootPRNG C.F encPt).up σ0 ik0).1, ((rootPRNG C.F encPt).up σ0 ik0).2), esLoc.h) := by
        unfold rootLocalForgedSlot
        simp [hqep, StateT.run_pure]
      have hrootM_q :
          (StateT.run (do
              let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0
              let s1 ← get
              let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
              set ({ s2 with cache := Function.update s2.cache t0 (some (T', σ', kVal, optIdx)) })
              let ssv : Fig8SS ⊕ ℕ := match optIdx with
                | none => .inl (locFs.initSender kVal)
                | some sIdx => .inr sIdx
              return ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                                 vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h :
            _root_.CryptoGames.SM.Engine.TComp
              (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) _) =
          pure ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                           root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                           vS := some (.inl (locFs.initSender ((rootPRNG C.F encPt).up σ0 ik0).2)) },
                { esM.h with
                  cache := Function.update esM.h.cache t0
                    (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1,
                      ((rootPRNG C.F encPt).up σ0 ik0).2, none)) }) := by
        unfold rootFSMultiBucketAuth regSessOptMultiBucket
        simp [hqep, StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
      dsimp only [cOut, T', ik0, σ0] at hrootL_q hrootM_q
      rw [hrootL_q, hrootM_q]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      have hleAdd_of_eq : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
          LeAdd a2 b2 c2 → a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a1 b1 c1 := by
        rintro _ _ _ _ _ _ h rfl rfl rfl; exact h
      refine hleAdd_of_eq
        (hoff_finish hoff ((rootPRNG C.F encPt).up σ0 ik0).1
          ((rootPRNG C.F encPt).up σ0 ik0).2 esLoc.h esM.h rfl htbl_mono)
        (congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl))
        (congrArg (Bind.bind _) (funext fun q0 => by
          rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
            exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
              (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
        (congrArg (Bind.bind _) (funext fun q0 => by
          rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
            exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
              (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
    · have hqep_dec : decide (qep + 1 < t0) = false := decide_eq_false hqep
      have hvF : validGuessBucketParAuth 1 tL par t0 = false := by
        unfold isTargetEp at hoff
        simp [ht0_pos, hqep] at hoff
        exact hoff
      have hleAdd_of_eq : ∀ {a1 a2 b1 b2 c1 c2 : ProbComp Bool},
          LeAdd a2 b2 c2 → a1 = a2 → b1 = b2 → c1 = c2 → LeAdd a1 b1 c1 := by
        rintro _ _ _ _ _ _ h rfl rfl rfl; exact h
      by_cases hisH : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · have hisH_beq : (tL.isSome && (t0 == healEpoch tL)) = true := by simpa using hisH
        have hrootL_h : (rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
            (mSessMain q qep tL) tL par t0 false ik0 σ0).run esLoc.h =
            (StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec Fig8K)) Pt) >>= fun ir =>
              sampleOrSlotF (mSessMain q qep tL) false (sIdxForged q tL t0 0) >>= fun kSample =>
              pure (((rootPRNG C.F encPt).up σ0 ir).1, kSample)).run esLoc.h := by
          unfold rootLocalForgedSlot
          simp only [hqep_dec, hvF, Bool.and_false, hisH, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        have hrootM_h :
            StateT.run (do
                let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0
                let s1 ← get
                let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
                set ({ s2 with cache := Function.update s2.cache t0 (some (T', σ', kVal, optIdx)) })
                let ssv : Fig8SS ⊕ ℕ := match optIdx with
                  | none => .inl (locFs.initSender kVal)
                  | some sIdx => .inr sIdx
                return ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                                   vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h =
            ((StateT.lift (sampleT (tspec := FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) Pt) :
              _root_.CryptoGames.SM.Engine.HM _ _ Pt).run esM.h >>= fun pIr =>
              ((StateT.lift (sampleT (tspec := FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) Fig8K) :
                _root_.CryptoGames.SM.Engine.HM _ _ Fig8K).run pIr.2 >>= fun pK =>
                pure ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                                 root := ((rootPRNG C.F encPt).up σ0 pIr.1).1,
                                 vS := some (.inl (locFs.initSender pK.1)) },
                      { pK.2 with
                        cache := Function.update pK.2.cache t0
                          (some (T', ((rootPRNG C.F encPt).up σ0 pIr.1).1, pK.1, none)) }))) := by
          unfold rootFSMultiBucketAuth regSessOptMultiBucket
          simp [hqep, hvF, hisH_beq, StateT.run_bind, StateT.run_get, StateT.run_set,
            bind_assoc]
        dsimp only [cOut, T', ik0, σ0] at hrootL_h hrootM_h
        rw [hrootL_h, hrootM_h]
        rw [StateT.run_bind, simulateQ_bind,
          hrun_sim_bind false, hrun_sim_bind true,
          run_sampleT_fixedF,
          run_sampleT_inl_gen (pubImpl false) (pubFsMultiImpl_inl_run _),
          run_sampleT_inl_gen (pubImpl true) (pubFsMultiImpl_inl_run _)]
        simp only [bind_assoc, pure_bind]
        refine leAdd_bind ($ᵗ Pt : ProbComp Pt) fun ir _ => ?_
        rw [StateT.run_bind, simulateQ_bind,
          hrun_sim_bind false, hrun_sim_bind true,
          sampleOrSlotF_false_run,
          run_sampleT_inl_gen (pubImpl false) (pubFsMultiImpl_inl_run _),
          run_sampleT_inl_gen (pubImpl true) (pubFsMultiImpl_inl_run _)]
        simp only [bind_assoc, pure_bind]
        refine leAdd_bind ($ᵗ Fig8K : ProbComp Fig8K) fun kSample _ => ?_
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        refine hleAdd_of_eq
          (hoff_finish hoff ((rootPRNG C.F encPt).up σ0 ir).1 kSample esLoc.h esM.h rfl htbl_mono)
          (congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl))
          (congrArg (Bind.bind _) (funext fun q0 => by
            rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
              exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
          (congrArg (Bind.bind _) (funext fun q0 => by
            rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
              exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
      · have hisHF : (tL.isSome && decide (t0 = healEpoch tL)) = false := Bool.eq_false_iff.mpr hisH
        have hisH_beqF : (tL.isSome && (t0 == healEpoch tL)) = false := by simpa using hisHF
        by_cases htlt : t0 < healEpoch tL
        · have htlt_dec : decide (t0 < healEpoch tL) = true := decide_eq_true htlt
          have hrootL_lt : (rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
              (mSessMain q qep tL) tL par t0 false ik0 σ0).run esLoc.h =
              pure ((((rootPRNG C.F encPt).up σ0 ik0).1, ((rootPRNG C.F encPt).up σ0 ik0).2), esLoc.h) := by
            unfold rootLocalForgedSlot
            simp only [hqep_dec, hisHF, htlt_dec, Bool.false_or, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
          have hrootM_lt :
              (StateT.run (do
                  let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0
                  let s1 ← get
                  let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
                  set ({ s2 with cache := Function.update s2.cache t0 (some (T', σ', kVal, optIdx)) })
                  let ssv : Fig8SS ⊕ ℕ := match optIdx with
                    | none => .inl (locFs.initSender kVal)
                    | some sIdx => .inr sIdx
                  return ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                                     vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h :
                _root_.CryptoGames.SM.Engine.TComp
                  (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E) _) =
              pure ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                               root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                               vS := some (.inl (locFs.initSender ((rootPRNG C.F encPt).up σ0 ik0).2)) },
                    { esM.h with
                      cache := Function.update esM.h.cache t0
                        (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1,
                          ((rootPRNG C.F encPt).up σ0 ik0).2, none)) }) := by
            unfold rootFSMultiBucketAuth regSessOptMultiBucket
            simp [hqep, hvF, hisH_beqF, htlt, StateT.run_bind, StateT.run_get,
              StateT.run_set, pure_bind]
          dsimp only [cOut, T', ik0, σ0] at hrootL_lt hrootM_lt
          rw [hrootL_lt, hrootM_lt]
          simp only [simulateQ_pure, StateT.run_pure, pure_bind]
          refine hleAdd_of_eq
            (hoff_finish hoff ((rootPRNG C.F encPt).up σ0 ik0).1
              ((rootPRNG C.F encPt).up σ0 ik0).2 esLoc.h esM.h rfl htbl_mono)
            (congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl))
            (congrArg (Bind.bind _) (funext fun q0 => by
              rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                  (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
            (congrArg (Bind.bind _) (funext fun q0 => by
              rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                  (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2)))
        · have htlt_decF : decide (t0 < healEpoch tL) = false := decide_eq_false htlt
          have hrootL_off : (rootLocalForgedSlot (rootPRNG C.F encPt) (sIdxForged q tL) 1 qep
              (mSessMain q qep tL) tL par t0 false ik0 σ0).run esLoc.h =
              ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) false t0 ik0).run esLoc.h >>=
                fun p0 =>
                  pure ((((rootPRNG C.F encPt).up σ0 ik0).1, p0.1), p0.2)) := by
            unfold rootLocalForgedSlot
            simp only [hqep_dec, hvF, Bool.and_false, hisHF, htlt_decF, Bool.false_or, Bool.not_false,
              Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_pure]
          have hrootM_off :
              StateT.run (do
                  let (σ', kVal, sid) ← rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0
                  let s1 ← get
                  let (optIdx, s2) := regSessOptMultiBucket (q + 1) false tL t0 sid s1
                  set ({ s2 with cache := Function.update s2.cache t0 (some (T', σ', kVal, optIdx)) })
                  let ssv : Fig8SS ⊕ ℕ := match optIdx with
                    | none => .inl (locFs.initSender kVal)
                    | some sIdx => .inr sIdx
                  return ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T', root := σ',
                                     vS := some ssv } : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))) esM.h =
              ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
                  t0 ik0).run esM.h >>= fun p0 =>
                pure ({ vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                                 root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                                 vS := some (.inl (locFs.initSender p0.1)) },
                      { p0.2 with
                        cache := Function.update p0.2.cache t0
                          (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1, none)) })) := by
            unfold rootFSMultiBucketAuth regSessOptMultiBucket
            simp [hqep, hvF, hisH_beqF, htlt, StateT.run_bind, StateT.run_get, StateT.run_set]
          dsimp only [cOut, T', ik0, σ0] at hrootL_off hrootM_off
          rw [hrootL_off, hrootM_off]
          rw [simulateQ_bind, bind_assoc, hrun_sim_bind false, hrun_sim_bind true,
            bind_assoc, bind_assoc]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
          refine hleAdd_of_eq
            (lookup_off_step (C := C) (encT := encT) (idOf := idOf) (tblM := tblM) (tblL := tblL)
              hoff ik0 htbl_mono
              (fun p0 =>
                simulateQ (keySlotFixedImplF ks)
                  ((fsSendStepSlot C Dh encPt encT idOf ℓ q qep tL par s₁Loc P m
                    { vpLoc with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                                 root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                                 vS := some (locFs.initSender p0.1) }).run
                    { p0.2 with loc := { p0.2.loc with
                        cache := Function.update p0.2.loc.cache t0
                          (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1)) } }) >>=
                fun p =>
                  match p.1 with
                  | none => runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k none)
                      { esLoc with h := p.2, abort := true } none
                  | some (st', ct) =>
                    let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                      ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
                    runLocForged C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
                      { esLoc with g := s₁Loc.record 3 P st' recE false, h := p.2 } none)
              (fun la p0 =>
                ((simulateQ (pubImpl la)
                  ((fsSendStepM C Dh encPt encT idOf ℓ q qep tL par la s₁M P m
                    { vpM with tcur := t0, γ := cOut.1, curCkaMsg := some T',
                               root := ((rootPRNG C.F encPt).up σ0 ik0).1,
                               vS := some (.inl (locFs.initSender p0.1.1)) }).run
                    { p0.1.2 with
                      cache := Function.update p0.1.2.cache t0
                        (some (T', ((rootPRNG C.F encPt).up σ0 ik0).1, p0.1.1, none)) })).run p0.2) >>=
                fun q0 =>
                  Prod.fst <$> (simulateQ (pubImpl la) do
                    let (u, es1, we1) := match q0.1.1 with
                      | none => (none, { esM with h := q0.1.2, abort := true }, none)
                      | some (st', ct) =>
                        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
                          ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
                        (some ct, { esM with g := s₁M.record 3 P st' recE false, h := q0.1.2 }, none)
                    let (_, es, winEp) ←
                      (simulateQ (implFSMultiBucketAuth (hkM la) 1 qep locFs.maxSkip false tL) (k u)).run (es1, we1)
                    if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run q0.2)
              ?_)
            (congrArg (Bind.bind _) (funext fun p0 =>
              congrArg (Bind.bind _) (funext fun p => by rcases p.1 with _ | ⟨st', ct⟩ <;> rfl)))
            (congrArg (Bind.bind _) (funext fun p0 =>
              congrArg (Bind.bind _) (funext fun q0 => by
                rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                  exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                    (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
            (congrArg (Bind.bind _) (funext fun p0 =>
              congrArg (Bind.bind _) (funext fun q0 => by
                rcases q0.1.1 with _ | ⟨st', ct⟩ <;>
                  exact congrArg (Prod.fst <$> ·) (congrFun (congrArg StateT.run
                    (congrArg (simulateQ _) (congrArg (Bind.bind _) (funext fun ⟨_, _, _⟩ => rfl)))) q0.2))))
          intro kVal hLoc' hM' hbook' _ _ htbl'
          exact hoff_finish hoff ((rootPRNG C.F encPt).up σ0 ik0).1 kVal hLoc' hM' hbook' htbl'


end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSendRec
