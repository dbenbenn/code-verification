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
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedRecv

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
  atomicShortPubB_imp_shortB fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
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
  forgedPhase1Inv_mono_rem runLocForged runSideForged epMgmt_align epMgmt_leaks_tL
  mkParties_forgedPhase1Inv)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedInr (
  redFSAuthMultiBucket_atomic_eq_lFS hℓ_rust run_lift_transmit run_lift_deliver_some
  run_lift_inject_none run_lift_inject_some fsSend_inr_step fsRecv_inr_step
  liftFSMultiBucket_transmit_run liftFSMultiBucket_deliver_some_run
  liftFSMultiBucket_inject_none_run liftFSMultiBucket_inject_some_run)

theorem accept_st_update_self_forged {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    { (s.accept P st' pos) with st := Function.update (s.accept P st' pos).st P st' } =
      s.accept P st' pos := by
  cases s; simp [GameState.accept, GameState.delete]

theorem accept_forgedPhase1Inv
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap rsMap' : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ}
    {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (pos : Pos)
    (stLoc' : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS)
    (stM' : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))
    (hLoc' : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
    (hM' : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
    (htcur_ge : (esLoc.g.st P).tcur ≤ stLoc'.tcur)
    (htcur_max : stLoc'.tcur = max (esLoc.g.st P).tcur pos.epoch)
    (hvp' : VPAlign q qep rem' tL par ssMap rsMap' P stLoc' stM')
    (hvp_other : ∀ Q, Q ≠ P → VPAlign q qep rem' tL par ssMap rsMap' Q (esLoc.g.st Q) (esM.g.st Q))
    (htbl' : HookTableInv Pt q qep rem' tL par ks hLoc' hM')
    (hrs_fresh' : ∀ t1 idx1, isTargetEp qep tL par t1 = true → idx1 < q →
      (∀ R, R.sendsIn t1 = false → ((esLoc.g.accept P stLoc' pos).st R).tcur < t1) →
      rsMap' (sIdxForged q tL t1 idx1) =
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks (sIdxForged q tL t1 idx1)))
    (hsess' : ∀ s, ForgedSessInv C ℓ encT idOf (ks s) (ssMap s) (rsMap' s)
      ((hM'.book s).getD {}) (tblM' s) (tblL' s)) :
    ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
      { esLoc with g := esLoc.g.accept P stLoc' pos, h := hLoc' }
      { esM with g := esM.g.accept P stM' pos, h := hM' }
      tblM' tblL' where
  not_abort := hinv.not_abort
  not_win := by simpa [GameState.accept, GameState.delete] using hinv.not_win
  not_pl := by simpa [GameState.accept, GameState.delete, postLeak] using hinv.not_pl
  ctx_eq := eraseCtxSt_accept hinv.ctx_eq
  loc_epoch := locEpochInv_accept hinv.loc_epoch (hvp'.id_loc.trans (hinv.vp_align P).id_loc.symm) htcur_max
  comp_unhealed := compUnhealed_accept hinv.comp_unhealed
  leaks_tL := fun cur hcur => by
    simpa [GameState.accept, GameState.delete] using hinv.leaks_tL cur
      (by simpa [GameState.accept, GameState.delete] using hcur)
  vp_align := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simpa [GameState.accept, GameState.delete] using hvp'
    · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQP] using hvp_other Q hQP
  htbl := htbl'
  ss_fresh := fun t1 idx1 htar1 hi1 hall =>
    hinv.ss_fresh t1 idx1 htar1 hi1 fun R hR => by
      have h1 := hall R hR
      simp only [GameState.accept, GameState.delete] at h1
      by_cases hRP : R = P
      · subst hRP; simp only [Function.update_self] at h1; omega
      · simpa [Function.update_of_ne hRP] using h1
  rs_fresh := hrs_fresh'
  sess_inv := hsess'

private theorem fsRecv_tail_coupled
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (s₁Loc : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS)
    (s₁M : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))
    (hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
    (hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
    (ht0_le : c.1.1 ≤ s₁Loc.tcur)
    (htcur_ge : (esLoc.g.st P).tcur ≤ s₁Loc.tcur)
    (htcur_max : s₁Loc.tcur = max (esLoc.g.st P).tcur c.1.1)
    (hvp1 : VPAlign q qep rem' tL par ssMap rsMap P s₁Loc s₁M)
    (htbl1 : HookTableInv Pt q qep rem' tL par ks hLoc1 hM1)
    (hbook1 : hM1.book = esM.h.book)
    (kLoc : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) ×
      LocalForgedSlotState Pt Fig8Sig Fig8K Pt → ProbComp Bool)
    (kSide : Bool →
      (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
          (LibsignalMsgPublicPart × Plain ℓ))) ×
        FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (habort_lf : ∀ lhs rhsF hL' tblL', hL'.lfWin = true →
      LeAdd lhs rhsF (kSide true ((none, hL'), (fun _ => false, tblL'))))
    (hnone : ∀ rsMap' hLoc' hM' tblM' tblL',
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
        { esLoc with h := hLoc' } { esM with h := hM' } tblM' tblL' →
      LeAdd (kLoc (some none, hLoc'))
        (kSide false ((some none, hM'), (fun _ => false, tblM')))
        (kSide true ((some none, hM'), (fun _ => false, tblL'))))
    (hsome : ∀ stLoc' stM' idxOut pmOut rsMap' hLoc' hM' tblM' tblL',
      (∀ pos : Pos, pos.epoch = c.1.1 →
        ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
          { esLoc with g := esLoc.g.accept P stLoc' pos, h := hLoc' }
          { esM with g := esM.g.accept P stM' pos, h := hM' } tblM' tblL') →
      (isTargetEp qep tL par c.1.1 = false →
        ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
          { esLoc with h := hLoc' } { esM with h := hM' } tblM' tblL') →
      LeAdd (kLoc (some (some (stLoc', c.1.1, idxOut, pmOut)), hLoc'))
        (kSide false ((some (some (stM', c.1.1, idxOut, pmOut)), hM'), (fun _ => false, tblM')))
        (kSide true ((some (some (stM', c.1.1, idxOut, pmOut)), hM'), (fun _ => false, tblL')))) :
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let hkLoc := hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
      (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par
    let hkM := fun (la : Bool) =>
      hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
    let pubImpl := fun (la : Bool) =>
      pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((match s₁Loc.vR c.1.1 with
          | none => return some none
          | some v => do
            match ← hkLoc.fsRecv esLoc.g P c.1.1 v c.1 c.2 rec with
            | none => return none
            | some none => return some none
            | some (some (v', i, m)) =>
              return some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some v') }, c.1.1, i, m))).run hLoc1) >>= kLoc)
      (((simulateQ (pubImpl false)
        ((match s₁M.vR c.1.1 with
          | none => return some none
          | some v => do
            match ← (hkM false).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
            | none => return none
            | some none => return some none
            | some (some (v', i, m)) =>
              return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
        (fun _ => false, tblM)) >>= kSide false)
      (((simulateQ (pubImpl true)
        ((match s₁M.vR c.1.1 with
          | none => return some none
          | some v => do
            match ← (hkM true).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
            | none => return none
            | some none => return some none
            | some (some (v', i, m)) =>
              return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
        (fun _ => false, tblL)) >>= kSide true) := by
  intro locFs hkLoc hkM pubImpl
  have hinv_unchanged : ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap
      { esLoc with h := hLoc1 } { esM with h := hM1 } tblM tblL :=
    { (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv) with
      htbl := htbl1
      sess_inv := fun s => by rw [hbook1]; exact hinv.sess_inv s }
  rcases hvp1.vR_align c.1.1 with ⟨hvLoc, hvM⟩ | ⟨rs, hvLoc, hvM⟩ | ⟨idx, hidx_q, hhe_t0, htar_t0, hsendsF_t0, hvLoc, hvM⟩
  · simp only [hvLoc, hvM, StateT.run_pure, simulateQ_pure, pure_bind]
    exact hnone rsMap hLoc1 hM1 tblM tblL hinv_unchanged
  · simp only [hvLoc, hvM]
    dsimp only [hkLoc, hkM, hooksLocalForgedSlot, hooksFSMultiBucketAuth]
    cases hrec : locFs.receive rs c.1 c.2 with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hnone rsMap hLoc1 hM1 tblM tblL hinv_unchanged
    | some trio =>
      rcases trio with ⟨rs', idxOut, pmOut⟩
      dsimp only [Option.map]
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      refine hsome
        { s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some rs') }
        { s₁M with vR := Function.update s₁M.vR c.1.1 (some (.inl rs')) }
        idxOut pmOut rsMap hLoc1 hM1 tblM tblL
        (fun pos hpos_ep => accept_forgedPhase1Inv C encT idOf ℓ q qep rem' tL par ks hinv P pos
          _ _ hLoc1 hM1 htcur_ge (by rw [hpos_ep]; exact htcur_max)
          { hvp1 with
            vR_gt := fun t ht => by
              dsimp only at ht
              have hne : t ≠ c.1.1 := by omega
              simpa [Function.update_of_ne hne] using hvp1.vR_gt t ht
            vR_align := fun t => by
              by_cases ht : t = c.1.1
              · subst ht; exact Or.inr (Or.inl ⟨rs', by simp, by simp⟩)
              · simpa [Function.update_of_ne ht] using hvp1.vR_align t }
          (fun Q _ =>
            let hv := hinv.vp_align Q
            { hv with tcur_rem := by have := hv.tcur_rem; omega })
          htbl1
          (fun t1 idx1 htar1 hi1 hall =>
            hinv.rs_fresh t1 idx1 htar1 hi1 fun R hR => by
              have h1 := hall R hR
              simp only [GameState.accept, GameState.delete] at h1
              by_cases hRP : R = P
              · subst hRP; simp only [Function.update_self] at h1; omega
              · simpa [Function.update_of_ne hRP] using h1)
          (fun s => by rw [hbook1]; exact hinv.sess_inv s))
        (fun _ => hinv_unchanged)
  · simp only [hvLoc, hvM]
    let sIdx := sIdxForged q tL c.1.1 idx
    rcases isTargetEp_imp htar_t0 with ⟨h1_t0, _, _, _, _, hh_t0, _, _, _, _⟩
    have hplM : postLeak tL esM.g = false := (eraseCtxSt_postLeak hinv.ctx_eq).trans hinv.not_pl
    have hhealed : healedBy esM.g.tL 3 c.1.1 = true :=
      healedBy_of_not_postLeak tL esM.g c.1.1 hplM hh_t0
    have hsess1 : ∀ s, ForgedSessInv C ℓ encT idOf (ks s) (ssMap s) (rsMap s)
        ((hM1.book s).getD {}) (tblM s) (tblL s) := fun s => by
      rw [hbook1]; exact hinv.sess_inv s
    rcases fsRecv_inr_step C Dh hD encPt encT idOf hℓ q qep tL par ks ssMap rsMap esM.g P c.1.1 sIdx
      c.1 c.2 rec hhealed hM1 tblM tblL hsess1 with ⟨hL', tblL', hrunL, hlf⟩ | hstep
    · have hSideT :
          ((simulateQ (pubImpl true)
            ((((hkM true).fsRecv esM.g P c.1.1 (.inr sIdx) c.1 c.2 rec >>= fun x =>
              match x with
              | none => pure none
              | some none => pure (some none)
              | some (some (v', i, m)) =>
                pure (some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m)))).run hM1))).run
            (fun _ => false, tblL)) =
          pure ((none, hL'), (fun _ => false, tblL')) := by
        rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
        dsimp only [hkM, pubImpl] at hrunL ⊢
        rw [hrunL, pure_bind]
        rfl
      rw [hSideT, pure_bind]
      exact habort_lf _ _ hL' tblL' hlf
    · cases hrec : locFs.receive (rsMap sIdx) c.1 c.2 with
      | none =>
        rw [hrec] at hstep
        rcases hstep with ⟨tblM', tblL', hrunM, hrunL, hsess'⟩
        have hLoc_run :
            simulateQ (keySlotFixedImplF ks)
              (((hkLoc.fsRecv esLoc.g P c.1.1 (rsMap sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some v') }, c.1.1, i, m)))).run hLoc1)) =
            pure (some none, hLoc1) := by
          dsimp only [hkLoc, hooksLocalForgedSlot]
          rw [hrec]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hSideM :
            ((simulateQ (pubImpl false)
              ((((hkM false).fsRecv esM.g P c.1.1 (.inr sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m)))).run hM1))).run
              (fun _ => false, tblM)) =
            pure ((some none, hM1), (fun _ => false, tblM')) := by
          rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
          dsimp only [hkM, pubImpl] at hrunM ⊢
          rw [hrunM, pure_bind]
          rfl
        have hSideL :
            ((simulateQ (pubImpl true)
              ((((hkM true).fsRecv esM.g P c.1.1 (.inr sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m)))).run hM1))).run
              (fun _ => false, tblL)) =
            pure ((some none, hM1), (fun _ => false, tblL')) := by
          rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
          dsimp only [hkM, pubImpl] at hrunL ⊢
          rw [hrunL, pure_bind]
          rfl
        rw [hLoc_run, hSideM, hSideL, pure_bind, pure_bind, pure_bind]
        exact hnone rsMap hLoc1 hM1 tblM' tblL'
          { (forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv) with
            htbl := htbl1
            sess_inv := hsess' }
      | some trio =>
        rcases trio with ⟨rsLoc', idxOut, pmOut⟩
        rw [hrec] at hstep
        rcases hstep with ⟨hM', tblM', tblL', hlf_eq, hsess_eq, hft_eq, hcache_eq, hrunM, hrunL, hsess'⟩
        have htbl' : HookTableInv Pt q qep rem' tL par ks hLoc1 hM' :=
          { not_lfWin := hlf_eq.trans htbl1.not_lfWin
            sess_eq := fun t0 => (congrFun hsess_eq t0).trans (htbl1.sess_eq t0)
            sess_nodup := htbl1.sess_nodup
            sess_rem := htbl1.sess_rem
            ftbl_off := fun t0 h0 => ⟨(congrFun hft_eq t0).trans (htbl1.ftbl_off t0 h0).1, (htbl1.ftbl_off t0 h0).2⟩
            ftbl_dom := fun t0 ik h0 => ⟨(htbl1.ftbl_dom t0 ik h0).1, by rw [hft_eq]; exact (htbl1.ftbl_dom t0 ik h0).2⟩
            ftbl_val := htbl1.ftbl_val
            used_iff := htbl1.used_iff
            cache_off := fun t0 h0 => (congrFun hcache_eq t0).trans (htbl1.cache_off t0 h0)
            cache_on := fun t0 h0 => by rw [hcache_eq]; exact htbl1.cache_on t0 h0 }
        have hLoc_run :
            simulateQ (keySlotFixedImplF ks)
              (((hkLoc.fsRecv esLoc.g P c.1.1 (rsMap sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some v') }, c.1.1, i, m)))).run hLoc1)) =
            pure (some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some rsLoc') }, c.1.1, idxOut, pmOut)), hLoc1) := by
          dsimp only [hkLoc, hooksLocalForgedSlot]
          rw [hrec]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hSideM :
            ((simulateQ (pubImpl false)
              ((((hkM false).fsRecv esM.g P c.1.1 (.inr sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m)))).run hM1))).run
              (fun _ => false, tblM)) =
            pure ((some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some (.inr sIdx)) }, c.1.1, idxOut, pmOut)), hM'),
              (fun _ => false, tblM')) := by
          rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
          dsimp only [hkM, pubImpl] at hrunM ⊢
          rw [hrunM, pure_bind]
          simp [StateT.run_pure, simulateQ_pure]
        have hSideL :
            ((simulateQ (pubImpl true)
              ((((hkM true).fsRecv esM.g P c.1.1 (.inr sIdx) c.1 c.2 rec >>= fun x =>
                match x with
                | none => pure none
                | some none => pure (some none)
                | some (some (v', i, m)) =>
                  pure (some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m)))).run hM1))).run
              (fun _ => false, tblL)) =
            pure ((some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some (.inr sIdx)) }, c.1.1, idxOut, pmOut)), hM'),
              (fun _ => false, tblL')) := by
          rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
          dsimp only [hkM, pubImpl] at hrunL ⊢
          rw [hrunL, pure_bind]
          simp [StateT.run_pure, simulateQ_pure]
        rw [hLoc_run, hSideM, hSideL, pure_bind, pure_bind, pure_bind]
        let rsMap' := Function.update rsMap sIdx rsLoc'
        refine hsome
          { s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some rsLoc') }
          { s₁M with vR := Function.update s₁M.vR c.1.1 (some (.inr sIdx)) }
          idxOut pmOut rsMap' hLoc1 hM' tblM' tblL'
          (fun pos hpos_ep => accept_forgedPhase1Inv C encT idOf ℓ q qep rem' tL par ks hinv P pos
            _ _ hLoc1 hM' htcur_ge (by rw [hpos_ep]; exact htcur_max)
            { hvp1 with
              vR_gt := fun t ht => by
                dsimp only at ht
                have hne : t ≠ c.1.1 := by omega
                simpa [Function.update_of_ne hne] using hvp1.vR_gt t ht
              vR_align := fun t => by
                by_cases ht : t = c.1.1
                · subst ht
                  exact Or.inr (Or.inr ⟨idx, hidx_q, hhe_t0, htar_t0, hsendsF_t0,
                    by simp [rsMap', sIdx], by simp [sIdx]⟩)
                · simp only [Function.update_of_ne ht]
                  rcases hvp1.vR_align t with h1 | h2 | ⟨idx1, hi1, hhe1, htar1, hs1, hv1, hv2⟩
                  · exact Or.inl h1
                  · exact Or.inr (Or.inl h2)
                  · have hne_s : sIdxForged q tL t idx1 ≠ sIdx := fun heq =>
                      ht (sIdxForged_inj hhe1 hhe_t0 hi1 hidx_q heq).1
                    exact Or.inr (Or.inr ⟨idx1, hi1, hhe1, htar1, hs1,
                      by simpa [rsMap', Function.update_of_ne hne_s] using hv1, hv2⟩) }
            (fun Q hQP => by
              let hv := hinv.vp_align Q
              exact
                { hv with
                  tcur_rem := by have := hv.tcur_rem; omega
                  vR_align := fun t => by
                    rcases hv.vR_align t with h1 | h2 | ⟨idx1, hi1, hhe1, htar1, hs1, hv1, hv2⟩
                    · exact Or.inl h1
                    · exact Or.inr (Or.inl h2)
                    · have hne_s : sIdxForged q tL t idx1 ≠ sIdx := fun heq => by
                        have ht_eq := (sIdxForged_inj hhe1 hhe_t0 hi1 hidx_q heq).1
                        subst ht_eq
                        exact hQP (sendsIn_false_unique h1_t0 hsendsF_t0 hs1)
                      exact Or.inr (Or.inr ⟨idx1, hi1, hhe1, htar1, hs1,
                        by simpa [rsMap', Function.update_of_ne hne_s] using hv1, hv2⟩) })
            htbl'
            (fun t1 idx1 htar1 hi1 hall => by
              rcases isTargetEp_imp htar1 with ⟨_, _, _, _, _, _, hhe1, _, _, _⟩
              have hne_s : sIdxForged q tL t1 idx1 ≠ sIdx := fun heq => by
                have ht_eq := (sIdxForged_inj hhe1 hhe_t0 hi1 hidx_q heq).1
                subst ht_eq
                have hP_lt := hall P hsendsF_t0
                simp only [GameState.accept, GameState.delete, Function.update_self] at hP_lt
                omega
              dsimp only [rsMap']
              rw [Function.update_of_ne hne_s]
              exact hinv.rs_fresh t1 idx1 htar1 hi1 fun R hR => by
                have h1 := hall R hR
                simp only [GameState.accept, GameState.delete] at h1
                by_cases hRP : R = P
                · subst hRP; simp only [Function.update_self] at h1; omega
                · simpa [Function.update_of_ne hRP] using h1)
            hsess')
          (fun hoff => by rw [htar_t0] at hoff; cases hoff)

theorem vRecv_forged_coupled
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep rem' : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep (rem' + 1) tL par ks ssMap rsMap esLoc esM tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (kLoc : Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × ℕ × ℕ ×
        (LibsignalMsgPublicPart × Plain ℓ))) ×
      LocalForgedSlotState Pt Fig8Sig Fig8K Pt → ProbComp Bool)
    (kSide : Bool →
      (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ ×
          (LibsignalMsgPublicPart × Plain ℓ))) ×
        FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (habort_both : ∀ hLoc' hM' tblM' tblL',
      LeAdd (kLoc (none, hLoc'))
        (kSide false ((none, hM'), (fun _ => false, tblM')))
        (kSide true ((none, hM'), (fun _ => false, tblL'))))
    (habort_lf : ∀ lhs rhsF hL' tblL', hL'.lfWin = true →
      LeAdd lhs rhsF (kSide true ((none, hL'), (fun _ => false, tblL'))))
    (hnone : ∀ rsMap' hLoc' hM' tblM' tblL',
      ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
        { esLoc with h := hLoc' } { esM with h := hM' } tblM' tblL' →
      LeAdd (kLoc (some none, hLoc'))
        (kSide false ((some none, hM'), (fun _ => false, tblM')))
        (kSide true ((some none, hM'), (fun _ => false, tblL'))))
    (hsome : ∀ stLoc' stM' idxOut pmOut rsMap' hLoc' hM' tblM' tblL',
      (∀ pos : Pos, pos.epoch = c.1.1 →
        ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
          { esLoc with g := esLoc.g.accept P stLoc' pos, h := hLoc' }
          { esM with g := esM.g.accept P stM' pos, h := hM' } tblM' tblL') →
      (isTargetEp qep tL par c.1.1 = false →
        ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap'
          { esLoc with h := hLoc' } { esM with h := hM' } tblM' tblL') →
      LeAdd (kLoc (some (some (stLoc', c.1.1, idxOut, pmOut)), hLoc'))
        (kSide false ((some (some (stM', c.1.1, idxOut, pmOut)), hM'), (fun _ => false, tblM')))
        (kSide true ((some (some (stM', c.1.1, idxOut, pmOut)), hM'), (fun _ => false, tblL')))) :
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let hkLoc := hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
      (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par
    let hkM := fun (la : Bool) =>
      hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la
    let pubImpl := fun (la : Bool) =>
      pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((vRecv hkLoc esLoc.g P (esLoc.g.st P) c rec).run esLoc.h) >>= kLoc)
      (((simulateQ (pubImpl false)
        ((vRecv (hkM false) esM.g P (esM.g.st P) c rec).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
      (((simulateQ (pubImpl true)
        ((vRecv (hkM true) esM.g P (esM.g.st P) c rec).run esM.h)).run (fun _ => false, tblL)) >>= kSide true) := by
  intro locFs hkLoc hkM pubImpl
  let vpLoc := esLoc.g.st P
  let vpM := esM.g.st P
  have hvp := hinv.vp_align P
  have hvpLoc_tcur : (esLoc.g.st P).tcur = vpLoc.tcur := rfl
  have hid_loc : vpLoc.id = P := hvp.id_loc
  have hid_m : vpM.id = P := hvp.id_m
  have htcur_vp : vpM.tcur = vpLoc.tcur := hvp.tcur_eq
  have hγ_vp : vpM.γ = vpLoc.γ := hvp.γ_eq
  have hroot_vp : vpM.root = vpLoc.root := hvp.root_eq
  have hplM : postLeak tL esM.g = false := (eraseCtxSt_postLeak hinv.ctx_eq).trans hinv.not_pl
  have hinv_mono := forgedPhase1Inv_mono_rem (Nat.le_succ rem') hinv
  change LeAdd
    (simulateQ (keySlotFixedImplF ks)
      ((vRecv hkLoc esLoc.g P vpLoc c rec).run esLoc.h) >>= kLoc)
    (((simulateQ (pubImpl false)
      ((vRecv (hkM false) esM.g P vpM c rec).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
    (((simulateQ (pubImpl true)
      ((vRecv (hkM true) esM.g P vpM c rec).run esM.h)).run (fun _ => false, tblL)) >>= kSide true)
  unfold vRecv
  simp only [hid_loc, hid_m, htcur_vp]
  by_cases hg : (P.sendsIn c.1.1 || decide (vpLoc.tcur + 1 < c.1.1)) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
    exact hnone rsMap esLoc.h esM.h tblM tblL hinv_mono
  · have hgF : (P.sendsIn c.1.1 || decide (vpLoc.tcur + 1 < c.1.1)) = false := Bool.eq_false_iff.mpr hg
    have hsendsF : P.sendsIn c.1.1 = false := (Bool.or_eq_false_iff.mp hgF).1
    have hnlt_succ : ¬(vpLoc.tcur + 1 < c.1.1) := by
      have h2 := (Bool.or_eq_false_iff.mp hgF).2
      simpa using h2
    simp only [hgF, Bool.false_eq_true, ↓reduceIte]
    by_cases ht_next : c.1.1 = vpLoc.tcur + 1
    · have ht0_pos : 1 ≤ c.1.1 := by omega
      have hvs_t0 : VSAlign q qep tL par ssMap P c.1.1 vpLoc.vS vpM.vS := by
        rcases hvp.vS_align with h1 | h2 | ⟨tS, idxS, hidxS, htS_le, hheS, htarS, hsendsS, _, hvSL, hvSM⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨tS, idxS, hidxS, by omega, hheS, htarS, hsendsS,
            (fun h => by rw [hsendsF] at h; cases h), hvSL, hvSM⟩)
      have hall_recv : ∀ R, R.sendsIn c.1.1 = false → (esLoc.g.st R).tcur < c.1.1 := by
        intro R hR
        have hRP : R = P := sendsIn_false_unique ht0_pos hsendsF hR
        subst hRP
        change vpLoc.tcur < c.1.1
        omega
      simp only [ht_next, ↓reduceIte]
      rw [← ht_next]
      cases hc2 : c.1.2 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hnone rsMap esLoc.h esM.h tblM tblL hinv_mono
      | some Tn =>
        -- Helper for off-target `(γ', σ', kVal)` completion into `fsRecv_tail_coupled`
        have hoff_recv_finish : ∀ (γ' : Fig8Γ Pt) (σ' : Fig8Sig) (kVal : Fig8K)
            (hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
            (hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
            (hbook1 : hM1.book = esM.h.book)
            (htbl1 : HookTableInv Pt q qep rem' tL par ks hLoc1 hM1),
            let s₁Loc : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS :=
              { vpLoc with tcur := c.1.1, γ := γ', root := σ',
                           vR := Function.update vpLoc.vR c.1.1 (some (locFs.initReceiver kVal)) }
            let s₁M : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) :=
              { vpM with tcur := c.1.1, γ := γ', root := σ',
                         vR := Function.update vpM.vR c.1.1 (some (.inl (locFs.initReceiver kVal))) }
            LeAdd
              (simulateQ (keySlotFixedImplF ks)
                ((match s₁Loc.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← hkLoc.fsRecv esLoc.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some v') }, c.1.1, i, m))).run hLoc1) >>= kLoc)
              (((simulateQ (pubImpl false)
                ((match s₁M.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← (hkM false).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
                (fun _ => false, tblM)) >>= kSide false)
              (((simulateQ (pubImpl true)
                ((match s₁M.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← (hkM true).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
                (fun _ => false, tblL)) >>= kSide true) := by
          intro γ' σ' kVal hLoc1 hM1 hbook1 htbl1 s₁Loc s₁M
          exact fsRecv_tail_coupled C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c rec
            s₁Loc s₁M hLoc1 hM1 le_rfl (by dsimp [s₁Loc]; omega) (by dsimp [s₁Loc]; omega)
            { id_loc := hvp.id_loc
              id_m := hvp.id_m
              γ_eq := rfl
              root_eq := rfl
              cka_eq := hvp.cka_eq
              tcur_eq := rfl
              tcur_rem := by have := hvp.tcur_rem; dsimp [s₁Loc]; omega
              vR_gt := fun t ht => by
                dsimp [s₁Loc] at ht
                have hne : t ≠ c.1.1 := by omega
                simpa [s₁Loc, s₁M, Function.update_of_ne hne] using hvp.vR_gt t (by omega)
              vS_align := hvs_t0
              vR_align := fun t => by
                by_cases ht : t = c.1.1
                · subst ht; exact Or.inr (Or.inl ⟨locFs.initReceiver kVal, by simp [s₁Loc], by simp [s₁M]⟩)
                · simpa [s₁Loc, s₁M, Function.update_of_ne ht] using hvp.vR_align t }
            htbl1 hbook1 kLoc kSide habort_lf hnone hsome
        -- Helper for target `(γ', σ', idx)` completion into `fsRecv_tail_coupled`
        have htar_recv_finish : ∀ (htar : isTargetEp qep tL par c.1.1 = true)
            (γ' : Fig8Γ Pt) (σ' : Fig8Sig) (idx : ℕ) (hidx_q : idx < q)
            (hLoc1 : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
            (hM1 : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
            (hbook1 : hM1.book = esM.h.book)
            (htbl1 : HookTableInv Pt q qep rem' tL par ks hLoc1 hM1),
            let sIdx := sIdxForged q tL c.1.1 idx
            let s₁Loc : VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS :=
              { vpLoc with tcur := c.1.1, γ := γ', root := σ',
                           vR := Function.update vpLoc.vR c.1.1 (some (locFs.initReceiver (ks sIdx))) }
            let s₁M : VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) :=
              { vpM with tcur := c.1.1, γ := γ', root := σ',
                         vR := Function.update vpM.vR c.1.1 (some (.inr sIdx)) }
            LeAdd
              (simulateQ (keySlotFixedImplF ks)
                ((match s₁Loc.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← hkLoc.fsRecv esLoc.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁Loc with vR := Function.update s₁Loc.vR c.1.1 (some v') }, c.1.1, i, m))).run hLoc1) >>= kLoc)
              (((simulateQ (pubImpl false)
                ((match s₁M.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← (hkM false).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
                (fun _ => false, tblM)) >>= kSide false)
              (((simulateQ (pubImpl true)
                ((match s₁M.vR c.1.1 with
                  | none => return some none
                  | some v => do
                    match ← (hkM true).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
                    | none => return none
                    | some none => return some none
                    | some (some (v', i, m)) =>
                      return some (some ({ s₁M with vR := Function.update s₁M.vR c.1.1 (some v') }, c.1.1, i, m))).run hM1)).run
                (fun _ => false, tblL)) >>= kSide true) := by
          intro htar γ' σ' idx hidx_q hLoc1 hM1 hbook1 htbl1 sIdx s₁Loc s₁M
          rcases isTargetEp_imp htar with ⟨_, _, _, _, _, _, hhe, _, _, _⟩
          have hrs_eq : rsMap sIdx = locFs.initReceiver (ks sIdx) :=
            hinv.rs_fresh c.1.1 idx htar hidx_q hall_recv
          exact fsRecv_tail_coupled C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c rec
            s₁Loc s₁M hLoc1 hM1 le_rfl (by dsimp [s₁Loc]; omega) (by dsimp [s₁Loc]; omega)
            { id_loc := hvp.id_loc
              id_m := hvp.id_m
              γ_eq := rfl
              root_eq := rfl
              cka_eq := hvp.cka_eq
              tcur_eq := rfl
              tcur_rem := by have := hvp.tcur_rem; dsimp [s₁Loc]; omega
              vR_gt := fun t ht => by
                dsimp [s₁Loc] at ht
                have hne : t ≠ c.1.1 := by omega
                simpa [s₁Loc, s₁M, Function.update_of_ne hne] using hvp.vR_gt t (by omega)
              vS_align := hvs_t0
              vR_align := fun t => by
                by_cases ht : t = c.1.1
                · subst ht
                  exact Or.inr (Or.inr ⟨idx, hidx_q, hhe, htar, hsendsF,
                    by simp [s₁Loc, hrs_eq, sIdx], by simp [s₁M, sIdx]⟩)
                · simpa [s₁Loc, s₁M, Function.update_of_ne ht] using hvp.vR_align t }
            htbl1 hbook1 kLoc kSide habort_lf hnone hsome
        let tailLoc (x : Option (Option (Fig8Γ Pt × Fig8Sig × Fig8RS))) :
            _root_.CryptoGames.SM.Engine.HM (multiSessSpec (keySlotSpec Fig8K))
              (LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
              (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS × ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))) :=
          (match x with
            | none => pure none
            | some none => pure (some none)
            | some (some (γ', σ', rs)) =>
              pure (some (some { vpLoc with tcur := c.1.1, γ := γ', root := σ',
                                            vR := Function.update vpLoc.vR c.1.1 (some rs) }))) >>=
          fun s₁? =>
            match s₁? with
            | none => return none
            | some none => return some none
            | some (some s₁) =>
              match s₁.vR c.1.1 with
              | none => return some none
              | some v => do
                match ← hkLoc.fsRecv esLoc.g P c.1.1 v c.1 c.2 rec with
                | none => return none
                | some none => return some none
                | some (some (v', i, m)) =>
                  return some (some ({ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, c.1.1, i, m))
        let tailM (la : Bool) (x : Option (Option (Fig8Γ Pt × Fig8Sig × (Fig8RS ⊕ ℕ)))) :
            _root_.CryptoGames.SM.Engine.HM
              (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
              (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
              (Option (Option (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) × ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))) :=
          (match x with
            | none => pure none
            | some none => pure (some none)
            | some (some (γ', σ', rs)) =>
              pure (some (some { vpM with tcur := c.1.1, γ := γ', root := σ',
                                          vR := Function.update vpM.vR c.1.1 (some rs) }))) >>=
          fun s₁? =>
            match s₁? with
            | none => return none
            | some none => return some none
            | some (some s₁) =>
              match s₁.vR c.1.1 with
              | none => return some none
              | some v => do
                match ← (hkM la).fsRecv esM.g P c.1.1 v c.1 c.2 rec with
                | none => return none
                | some none => return some none
                | some (some (v', i, m)) =>
                  return some (some ({ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, c.1.1, i, m))
        dsimp only
        suffices LeAdd
            (simulateQ (keySlotFixedImplF ks)
              ((hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn >>= tailLoc).run esLoc.h) >>= kLoc)
            (((simulateQ (pubImpl false)
              (((hkM false).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM false).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
            (((simulateQ (pubImpl true)
              (((hkM true).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM true).run esM.h)).run (fun _ => false, tblL)) >>= kSide true) by
          convert this using 1
          · refine congrArg (fun m => simulateQ _ (StateT.run m _) >>= _)
              (congrArg (_ >>= ·) (funext fun x => ?_))
            rcases x with _ | (_ | ⟨γ', σ', rs⟩)
            · simp only [tailLoc, pure_bind]
            · simp only [tailLoc, pure_bind]
            · simp only [tailLoc, pure_bind, hid_loc]
              cases Function.update vpLoc.vR c.1.1 (some rs) c.1.1 with
              | none => rfl
              | some v => dsimp only; congr 1; funext y; rcases y with _ | (_ | ⟨v', i, m⟩) <;> rfl
          · refine congrArg (fun m => (StateT.run (simulateQ _ (StateT.run m _)) _) >>= _)
              (congrArg (_ >>= ·) (funext fun x => ?_))
            rcases x with _ | (_ | ⟨γ', σ', rs⟩)
            · simp only [tailM, pure_bind]
            · simp only [tailM, pure_bind]
            · simp only [tailM, pure_bind, hid_m]
              cases Function.update vpM.vR c.1.1 (some rs) c.1.1 with
              | none => rfl
              | some v => dsimp only; congr 1; funext y; rcases y with _ | (_ | ⟨v', i, m⟩) <;> rfl
          · refine congrArg (fun m => (StateT.run (simulateQ _ (StateT.run m _)) _) >>= _)
              (congrArg (_ >>= ·) (funext fun x => ?_))
            rcases x with _ | (_ | ⟨γ', σ', rs⟩)
            · simp only [tailM, pure_bind]
            · simp only [tailM, pure_bind]
            · simp only [tailM, pure_bind, hid_m]
              cases Function.update vpM.vR c.1.1 (some rs) c.1.1 with
              | none => rfl
              | some v => dsimp only; congr 1; funext y; rcases y with _ | (_ | ⟨v', i, m⟩) <;> rfl
        by_cases htar : isTargetEp qep tL par c.1.1 = true
        · rcases isTargetEp_imp htar with ⟨h1_t0, _, hqepF, hv, hlga, _, _, hnot1, hnot2, hntlt⟩
          have hqep_lt : ¬(qep + 1 < c.1.1) := by simpa using hqepF
          have ht0_lt_he : ¬(c.1.1 < healEpoch tL) := by simpa using hntlt
          have hmiss_target :
              ∀ (hhonLoc : esLoc.h.loc.cache c.1.1 = none ∨
                  ∃ Tc σc kV, esLoc.h.loc.cache c.1.1 = some (Tc, σc, kV) ∧ Tc ≠ Tn)
                (hhonM : esM.h.cache c.1.1 = none ∨
                  ∃ Tc σc kV optIdx, esM.h.cache c.1.1 = some (Tc, σc, kV, optIdx) ∧ Tc ≠ Tn),
              LeAdd
                (simulateQ (keySlotFixedImplF ks)
                  ((hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn >>= tailLoc).run esLoc.h) >>= kLoc)
                (((simulateQ (pubImpl false)
                  (((hkM false).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM false).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
                (((simulateQ (pubImpl true)
                  (((hkM true).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM true).run esM.h)).run (fun _ => false, tblL)) >>= kSide true) := by
            intro hhonLoc hhonM
            let kk := (dhScheme Dh).receive vpLoc.γ Tn
            have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn).run esLoc.h =
                ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) true c.1.1 kk.2).run esLoc.h >>=
                  fun ⟨kOut, hLoc'⟩ =>
                    pure (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1,
                      locFs.initReceiver kOut)), hLoc')) := by
              dsimp only [hkLoc, hooksLocalForgedSlot]
              rcases hhonLoc with hcL | ⟨Tc, σc, kV, hcL, hTc⟩
              · simp [kk, hcL, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                  pure_bind, hinv.not_pl, h1_t0, hqep_lt, hv, hlga, hnot1, ht0_lt_he]
              · simp [kk, hcL, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                  pure_bind, hinv.not_pl, h1_t0, hqep_lt, hv, hlga, hnot1, ht0_lt_he]
            have hstartM : ∀ la : Bool,
                ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn).run esM.h =
                ((hmTargetM ℓ (q + 1) tL c.1.1 kk.2).run esM.h >>=
                  fun ⟨⟨_, sIdx⟩, hM'⟩ =>
                    pure (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1,
                      .inr sIdx)), hM')) := fun _ => by
              dsimp only [hkM, hooksFSMultiBucketAuth, hmTargetM]
              rcases hhonM with hcM | ⟨Tc, σc, kV, optIdx, hcM, hTc⟩
              · simp [kk, hcM, (show 2 + 1 = 3 from rfl), hγ_vp, hroot_vp, StateT.run_bind,
                  StateT.run_get, StateT.run_set, pure_bind,
                  hplM, hqep_lt, hlga, hnot2, hv]
              · simp [kk, hcM, hTc, (show 2 + 1 = 3 from rfl), hγ_vp, hroot_vp, StateT.run_bind,
                  StateT.run_get, StateT.run_set, pure_bind,
                  hplM, hqep_lt, hlga, hnot2, hv]
            rw [StateT.run_bind, hstartL, bind_assoc, simulateQ_bind, bind_assoc,
              StateT.run_bind, hstartM false, bind_assoc, simulateQ_bind, StateT.run_bind, bind_assoc,
              StateT.run_bind, hstartM true, bind_assoc, simulateQ_bind, StateT.run_bind, bind_assoc]
            let kLoc_tar (p : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt) : ProbComp Bool :=
              simulateQ (keySlotFixedImplF ks)
                ((tailLoc (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1, locFs.initReceiver p.1)))).run p.2) >>= kLoc
            let kSide_tar (la : Bool)
                (x : ((Fig8K × ℕ) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : ProbComp Bool :=
              ((simulateQ (pubImpl la)
                ((tailM la (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1, .inr x.1.1.2)))).run x.1.2)).run x.2) >>= kSide la
            refine lookup_target_step (C := C) (encT := encT) (idOf := idOf) (tblM := tblM) (tblL := tblL)
              htar kk.2 hinv.htbl kLoc_tar kSide_tar ?_
            intro idx kD hLoc' hM' _ hidx_q hbook' _ _ htbl'
            exact htar_recv_finish htar kk.1 (((rootPRNG C.F encPt).up vpLoc.root kk.2).1)
              idx hidx_q hLoc' hM' hbook' htbl'
          rcases hinv.htbl.cache_on c.1.1 htar with ⟨hcL, hcM⟩ | ⟨Tc, σc, kD, idx, hidx_len, hcL, hcM⟩
          · exact hmiss_target (Or.inl hcL) (Or.inl hcM)
          · by_cases hTc : Tc = Tn
            · subst hTc
              have hidx_q : idx < q := by have := hinv.htbl.sess_rem c.1.1; omega
              have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tc).run esLoc.h =
                  pure (some (some (((dhScheme Dh).receive vpLoc.γ Tc).1, σc,
                    locFs.initReceiver (ks (sIdxForged q tL c.1.1 idx)))), esLoc.h) := by
                dsimp only [hkLoc, hooksLocalForgedSlot]
                simp [hcL, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
              have hstartM : ∀ la : Bool,
                  ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tc).run esM.h =
                  pure (some (some (((dhScheme Dh).receive vpLoc.γ Tc).1, σc,
                    .inr (sIdxForged q tL c.1.1 idx))), esM.h) := fun _ => by
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp [hcM, hγ_vp, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
              rw [StateT.run_bind, hstartL, StateT.run_bind, hstartM false, StateT.run_bind, hstartM true]
              exact htar_recv_finish htar (((dhScheme Dh).receive vpLoc.γ Tc).1) σc idx hidx_q
                esLoc.h esM.h rfl (hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl)
            · exact hmiss_target (Or.inr ⟨Tc, σc, _, hcL, hTc⟩) (Or.inr ⟨Tc, σc, _, _, hcM, hTc⟩)
        · have hoff : isTargetEp qep tL par c.1.1 = false := Bool.eq_false_iff.mpr htar
          have hcache_off := hinv.htbl.cache_off c.1.1 hoff
          have hmiss_off :
              ∀ (hhonLoc : esLoc.h.loc.cache c.1.1 = none ∨
                  ∃ Tc σc kV, esLoc.h.loc.cache c.1.1 = some (Tc, σc, kV) ∧ Tc ≠ Tn)
                (hhonM : esM.h.cache c.1.1 = none ∨
                  ∃ Tc σc kV optIdx, esM.h.cache c.1.1 = some (Tc, σc, kV, optIdx) ∧ Tc ≠ Tn),
              LeAdd
                (simulateQ (keySlotFixedImplF ks)
                  ((hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn >>= tailLoc).run esLoc.h) >>= kLoc)
                (((simulateQ (pubImpl false)
                  (((hkM false).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM false).run esM.h)).run (fun _ => false, tblM)) >>= kSide false)
                (((simulateQ (pubImpl true)
                  (((hkM true).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn >>= tailM true).run esM.h)).run (fun _ => false, tblL)) >>= kSide true) := by
            intro hhonLoc hhonM
            by_cases hadm_g : (!(decide (qep + 1 < c.1.1)) && lastLeakGuessAdmissible 3 tL c.1.1) = true
            · have hqep_lt : ¬(qep + 1 < c.1.1) := by
                intro hlt; simp [hlt] at hadm_g
              have hlga : lastLeakGuessAdmissible 3 tL c.1.1 = true := by
                simp [hqep_lt] at hadm_g; exact hadm_g
              have hvgF : validGuessBucketParAuth 1 tL par c.1.1 = false := by
                have h := hoff
                unfold isTargetEp at h
                simp [ht0_pos, hqep_lt] at h
                exact h
              by_cases hisH : (tL.isSome && decide (c.1.1 = healEpoch tL)) = true
              · have hisH_beq : (tL.isSome && (c.1.1 == healEpoch tL)) = true := by simpa using hisH
                have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn).run esLoc.h =
                    pure (none, esLoc.h) := by
                  dsimp only [hkLoc, hooksLocalForgedSlot]
                  rcases hhonLoc with hcL | ⟨Tc, σc, kV, hcL, hTc⟩
                  · simp [hcL, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                      StateT.run_pure, pure_bind, hqep_lt, hlga, hisH]
                  · simp [hcL, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                      StateT.run_pure, pure_bind, hqep_lt, hlga, hisH]
                have hstartM : ∀ la : Bool,
                    ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn).run esM.h =
                    pure (none, esM.h) := fun _ => by
                  dsimp only [hkM, hooksFSMultiBucketAuth]
                  rcases hhonM with hcM | ⟨Tc, σc, kV, optIdx, hcM, hTc⟩
                  · simp [hcM, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                      StateT.run_pure, pure_bind, hqep_lt, hlga, hisH_beq]
                  · simp [hcM, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                      StateT.run_pure, pure_bind, hqep_lt, hlga, hisH_beq]
                rw [StateT.run_bind, hstartL, StateT.run_bind, hstartM false, StateT.run_bind, hstartM true]
                exact habort_both esLoc.h esM.h tblM tblL
              · have hisHF : (tL.isSome && decide (c.1.1 = healEpoch tL)) = false := Bool.eq_false_iff.mpr hisH
                have hisH_beqF : (tL.isSome && (c.1.1 == healEpoch tL)) = false := by simpa using hisHF
                by_cases htlt : c.1.1 < healEpoch tL
                · have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn).run esLoc.h =
                      pure (some none, esLoc.h) := by
                    dsimp only [hkLoc, hooksLocalForgedSlot]
                    rcases hhonLoc with hcL | ⟨Tc, σc, kV, hcL, hTc⟩
                    · simp [hcL, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        StateT.run_pure, pure_bind, hinv.not_pl, hqep_lt, hlga, hisHF, htlt]
                    · simp [hcL, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        StateT.run_pure, pure_bind, hinv.not_pl, hqep_lt, hlga, hisHF, htlt]
                  have hstartM : ∀ la : Bool,
                      ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn).run esM.h =
                      pure (some none, esM.h) := fun _ => by
                    dsimp only [hkM, hooksFSMultiBucketAuth]
                    rcases hhonM with hcM | ⟨Tc, σc, kV, optIdx, hcM, hTc⟩
                    · simp [hcM, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        StateT.run_pure, pure_bind, hplM, hqep_lt, hlga, hisH_beqF, hvgF, htlt]
                    · simp [hcM, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        StateT.run_pure, pure_bind, hplM, hqep_lt, hlga, hisH_beqF, hvgF, htlt]
                  rw [StateT.run_bind, hstartL, StateT.run_bind, hstartM false, StateT.run_bind, hstartM true]
                  exact hnone rsMap esLoc.h esM.h tblM tblL hinv_mono
                · let kk := (dhScheme Dh).receive vpLoc.γ Tn
                  have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn).run esLoc.h =
                      ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) false c.1.1 kk.2).run esLoc.h >>=
                        fun ⟨kOut, hLoc'⟩ =>
                          pure (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1,
                            locFs.initReceiver kOut)), hLoc')) := by
                    dsimp only [hkLoc, hooksLocalForgedSlot]
                    rcases hhonLoc with hcL | ⟨Tc, σc, kV, hcL, hTc⟩
                    · simp [kk, hcL, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        pure_bind, hinv.not_pl, ht0_pos, hqep_lt, hvgF, hlga,
                        hisHF, htlt]
                    · simp [kk, hcL, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                        pure_bind, hinv.not_pl, ht0_pos, hqep_lt, hvgF, hlga,
                        hisHF, htlt]
                  have hstartM : ∀ la : Bool,
                      ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn).run esM.h =
                      ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
                        c.1.1 kk.2).run esM.h >>=
                        fun ⟨k', hM'⟩ =>
                          pure (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1,
                            .inl (locFs.initReceiver k'))), hM')) := fun _ => by
                    dsimp only [hkM, hooksFSMultiBucketAuth]
                    rcases hhonM with hcM | ⟨Tc, σc, kV, optIdx, hcM, hTc⟩
                    · simp [kk, hcM, (show 2 + 1 = 3 from rfl), hγ_vp, hroot_vp, StateT.run_bind,
                        StateT.run_get, pure_bind, hplM, hqep_lt, hlga, hisH_beqF,
                        hvgF, htlt]
                    · simp [kk, hcM, hTc, (show 2 + 1 = 3 from rfl), hγ_vp, hroot_vp, StateT.run_bind,
                        StateT.run_get, pure_bind, hplM, hqep_lt, hlga, hisH_beqF,
                        hvgF, htlt]
                  rw [StateT.run_bind, hstartL, bind_assoc, simulateQ_bind, bind_assoc,
                    StateT.run_bind, hstartM false, bind_assoc, simulateQ_bind, StateT.run_bind, bind_assoc,
                    StateT.run_bind, hstartM true, bind_assoc, simulateQ_bind, StateT.run_bind, bind_assoc]
                  let kLoc_off (p : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt) : ProbComp Bool :=
                    simulateQ (keySlotFixedImplF ks)
                      ((tailLoc (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1, locFs.initReceiver p.1)))).run p.2) >>= kLoc
                  let kSide_off (la : Bool)
                      (x : (Fig8K × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : ProbComp Bool :=
                    ((simulateQ (pubImpl la)
                      ((tailM la (some (some (kk.1, ((rootPRNG C.F encPt).up vpLoc.root kk.2).1, .inl (locFs.initReceiver x.1.1))))).run x.1.2)).run x.2) >>= kSide la
                  refine lookup_off_step (C := C) (encT := encT) (idOf := idOf) (tblM := tblM) (tblL := tblL)
                    hoff kk.2 (hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl) kLoc_off kSide_off ?_
                  intro kVal hLoc' hM' hbook' _ _ htbl'
                  exact hoff_recv_finish kk.1 (((rootPRNG C.F encPt).up vpLoc.root kk.2).1) kVal
                    hLoc' hM' hbook' htbl'
            · have hadmF : (!(decide (qep + 1 < c.1.1)) && lastLeakGuessAdmissible 3 tL c.1.1) = false :=
                Bool.eq_false_iff.mpr hadm_g
              have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tn).run esLoc.h =
                  pure (some none, esLoc.h) := by
                dsimp only [hkLoc, hooksLocalForgedSlot]
                rcases hhonLoc with hcL | ⟨Tc, σc, kV, hcL, hTc⟩
                · simp [hcL, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                    StateT.run_pure, pure_bind, hadmF]
                · simp [hcL, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                    StateT.run_pure, pure_bind, hadmF]
              have hstartM : ∀ la : Bool,
                  ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tn).run esM.h =
                  pure (some none, esM.h) := fun _ => by
                dsimp only [hkM, hooksFSMultiBucketAuth]
                rcases hhonM with hcM | ⟨Tc, σc, kV, optIdx, hcM, hTc⟩
                · simp [hcM, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                    StateT.run_pure, pure_bind, hadmF]
                · simp [hcM, hTc, (show 2 + 1 = 3 from rfl), StateT.run_bind, StateT.run_get,
                    StateT.run_pure, pure_bind, hadmF]
              rw [StateT.run_bind, hstartL, StateT.run_bind, hstartM false, StateT.run_bind, hstartM true]
              exact hnone rsMap esLoc.h esM.h tblM tblL hinv_mono
          cases hcL : esLoc.h.loc.cache c.1.1 with
          | none =>
            have hcM : esM.h.cache c.1.1 = none := by rw [hcache_off, hcL]; rfl
            exact hmiss_off (Or.inl hcL) (Or.inl hcM)
          | some triple =>
            rcases triple with ⟨Tc, σc, kVal⟩
            have hcM : esM.h.cache c.1.1 = some (Tc, σc, kVal, none) := by rw [hcache_off, hcL]; rfl
            by_cases hTc : Tc = Tn
            · subst hTc
              have hstartL : (hkLoc.startRecv esLoc.g P c.1.1 vpLoc.γ vpLoc.root Tc).run esLoc.h =
                  pure (some (some (((dhScheme Dh).receive vpLoc.γ Tc).1, σc,
                    locFs.initReceiver kVal)), esLoc.h) := by
                dsimp only [hkLoc, hooksLocalForgedSlot]
                simp [hcL, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
              have hstartM : ∀ la : Bool,
                  ((hkM la).startRecv esM.g P c.1.1 vpM.γ vpM.root Tc).run esM.h =
                  pure (some (some (((dhScheme Dh).receive vpLoc.γ Tc).1, σc,
                    .inl (locFs.initReceiver kVal))), esM.h) := fun _ => by
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp [hcM, hγ_vp, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
              rw [StateT.run_bind, hstartL, StateT.run_bind, hstartM false, StateT.run_bind, hstartM true]
              exact hoff_recv_finish (((dhScheme Dh).receive vpLoc.γ Tc).1) σc kVal
                esLoc.h esM.h rfl (hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl)
            · exact hmiss_off (Or.inr ⟨Tc, σc, kVal, hcL, hTc⟩) (Or.inr ⟨Tc, σc, kVal, none, hcM, hTc⟩)
    · have ht0_le : c.1.1 ≤ vpLoc.tcur := by omega
      simp only [ht_next, ↓reduceIte, pure_bind]
      have htail := fsRecv_tail_coupled C Dh hD encPt encT idOf ℓ hℓ q qep rem' tL par ks hinv P c rec
        vpLoc vpM esLoc.h esM.h ht0_le le_rfl (Nat.max_eq_left ht0_le).symm
        { hvp with tcur_rem := by have := hvp.tcur_rem; omega }
        (hookTableInv_mono_rem (Nat.le_succ rem') hinv.htbl) rfl kLoc kSide habort_lf hnone hsome
      dsimp only [locFs, hkLoc, hkM, pubImpl] at htail ⊢
      convert htail using 1
      · refine congrArg (fun m => simulateQ _ (StateT.run m _) >>= _) ?_
        cases vpLoc.vR c.1.1 with
        | none => rfl
        | some v => dsimp only; congr 1; funext x; rcases x with _ | (_ | ⟨v', i, m⟩) <;> rfl
      · refine congrArg (fun m => (StateT.run (simulateQ _ (StateT.run m _)) _) >>= _) ?_
        cases vpM.vR c.1.1 with
        | none => rfl
        | some v => dsimp only; congr 1; funext x; rcases x with _ | (_ | ⟨v', i, m⟩) <;> rfl
      · refine congrArg (fun m => (StateT.run (simulateQ _ (StateT.run m _)) _) >>= _) ?_
        cases vpM.vR c.1.1 with
        | none => rfl
        | some v => dsimp only; congr 1; funext x; rcases x with _ | (_ | ⟨v', i, m⟩) <;> rfl


end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedRecv
