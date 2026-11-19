/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedSeed -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShort -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
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

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow

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

@[expose] def isTargetEp (qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) : Bool :=
  decide (1 ≤ t0) && !(decide (qep + 1 < t0)) && validGuessBucketParAuth 1 tL par t0

theorem isTargetEp_zero (qep : ℕ) (tL : Option ℕ) (par : Bool) :
    isTargetEp qep tL par 0 = false := rfl

theorem isTargetEp_imp {qep : ℕ} {tL : Option ℕ} {par : Bool} {t0 : ℕ}
    (h : isTargetEp qep tL par t0 = true) :
    1 ≤ t0 ∧ t0 ≤ qep + 1 ∧ (!decide (qep + 1 < t0)) = true ∧
      validGuessBucketParAuth 1 tL par t0 = true ∧
      lastLeakGuessAdmissible 3 tL t0 = true ∧ healedBy tL 3 t0 = true ∧ healEpoch tL ≤ t0 ∧
      (tL.isSome && decide (t0 = healEpoch tL)) = false ∧
      (tL.isSome && (t0 == healEpoch tL)) = false ∧
      (!decide (t0 < healEpoch tL)) = true := by
  unfold isTargetEp at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨h1, hq⟩, hv⟩
  have h1' : 1 ≤ t0 := of_decide_eq_true h1
  have hle : t0 ≤ qep + 1 := by simp at hq; exact hq
  have hlga : lastLeakGuessAdmissible 3 tL t0 = true := by
    unfold validGuessBucketParAuth at hv; simp only [Bool.and_eq_true] at hv; exact hv.1
  have hh : healedBy tL 3 t0 = true := by
    simpa [lastLeakGuessAdmissible] using hlga
  have hhe : healEpoch tL ≤ t0 := healedBy_imp_healEpoch_le tL t0 hh
  have hnot := not_isSome_and_eq_healEpoch_of_validGuess tL par t0 hv
  have hntlt : (!decide (t0 < healEpoch tL)) = true := by simp; omega
  exact ⟨h1', hle, hq, hv, hlga, hh, hhe, hnot.1, hnot.2, hntlt⟩

theorem sendsIn_succ_false_imp (P : Party) {t : ℕ}
    (h : P.sendsIn (t + 1) = false) : P.sendsIn t = true := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem sendsIn_exclusive {P Q : Party} {t : ℕ}
    (hP : P.sendsIn t = true) (hQ : Q.sendsIn t = true) : P = Q := by
  cases P <;> cases Q <;> simp [Party.sendsIn] at hP hQ ⊢ <;> omega

theorem sim_sampleT_fixedF {K α : Type} [SampleableType α] (ks : ℕ → K) :
    simulateQ (keySlotFixedImplF ks)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α,
      simulateQ (keySlotFixedImplF ks)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind t k ih =>
    change simulateQ (keySlotFixedImplF ks)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)) = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      keySlotFixedImplF, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

theorem run_sampleT_fixedF {T Sig K I α : Type} [SampleableType α]
    (ks : ℕ → K) (st : LocalForgedSlotState T Sig K I) :
    simulateQ (keySlotFixedImplF ks)
      (((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α) :
        ForgedSlotHM T Sig K I α)).run st) =
    (($ᵗ α : ProbComp α) >>= fun x => pure (x, st)) := by
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, sim_sampleT_fixedF]

theorem sim_sampleT_inl_gen {ι σ α : Type} {tspec : OracleSpec ι} [SampleableType α]
    (impl : QueryImpl (unifSpec + tspec) (StateT σ ProbComp))
    (hInl : ∀ (n : ℕ) (s : σ), (impl (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (pSt : σ) :
    (simulateQ impl (sampleT (tspec := tspec) α)).run pSt =
      (($ᵗ α : ProbComp α) >>= fun x => pure (x, pSt)) := by
  suffices h : ∀ oa : ProbComp α,
      (simulateQ impl (liftM oa : OracleComp (unifSpec + tspec) α)).run pSt =
        (oa >>= fun x => pure (x, pSt)) from h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind t k ih =>
    change (simulateQ impl
      ((liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) :
        OracleComp (unifSpec + tspec) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + tspec) α))).run pSt = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, hInl t pSt, bind_assoc, bind_assoc]
    congr 1; funext u; rw [pure_bind]; exact ih u

theorem run_sampleT_inl_gen {ι HS σ α : Type} {tspec : OracleSpec ι} [SampleableType α]
    (impl : QueryImpl (unifSpec + tspec) (StateT σ ProbComp))
    (hInl : ∀ (n : ℕ) (s : σ), (impl (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (st : HS) (pSt : σ) :
    (simulateQ impl (((StateT.lift (sampleT (tspec := tspec) α) :
      _root_.CryptoGames.SM.Engine.HM tspec HS α)).run st)).run pSt =
    (($ᵗ α : ProbComp α) >>= fun x => pure ((x, st), pSt)) := by
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    sim_sampleT_inl_gen impl hInl pSt, bind_assoc, pure_bind]

@[expose] def eraseCtxSt {St M C : Type} (g : GameState St M C) : GameState Unit M C :=
  { g with st := fun _ => () }

theorem eraseCtxSt_postLeak {St₁ St₂ M C : Type} {tL : Option ℕ}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    postLeak tL g₁ = postLeak tL g₂ := by
  have htL : g₁.tL = g₂.tL := congrArg GameState.tL h
  simp [postLeak, htL]

theorem eraseCtxSt_safeCh {St₁ St₂ M C : Type} {Δ : ℕ} {P : Party}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    g₁.safeCh Δ P = g₂.safeCh Δ P := by
  have htL : g₁.tL = g₂.tL := congrArg GameState.tL h
  have hep : g₁.epoch = g₂.epoch := congrArg GameState.epoch h
  simp [GameState.safeCh, htL, hep]

theorem eraseCtxSt_safeInj {St₁ St₂ M C : Type} {Δ : ℕ}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    g₁.safeInj Δ = g₂.safeInj Δ := by
  have htL : g₁.tL = g₂.tL := congrArg GameState.tL h
  have hep : g₁.epoch = g₂.epoch := congrArg GameState.epoch h
  have htr : g₁.trans = g₂.trans := congrArg GameState.trans h
  have hcp : g₁.comp = g₂.comp := congrArg GameState.comp h
  have hcr : g₁.corrs = g₂.corrs := congrArg GameState.corrs h
  have hlk : g₁.leaks = g₂.leaks := congrArg GameState.leaks h
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars; rfl

theorem eraseCtxSt_inTransit {St₁ St₂ M C : Type} [DecidableEq C]
    {P : Party} {c : C}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    g₁.inTransit P c = g₂.inTransit P c := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars; rfl

theorem eraseCtxSt_trivial {St₁ St₂ M C : Type} [DecidableEq C]
    {Δ : ℕ} {pos : Pos}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    g₁.trivial Δ pos = g₂.trivial Δ pos := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars; rfl

theorem eraseCtxSt_corrAllowed {St₁ St₂ M C : Type} {P : Party}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    g₁.corrAllowed P = g₂.corrAllowed P := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars; rfl

theorem eraseCtxSt_epMgmt {St₁ St₂ M C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    (g₁.epMgmt Δ qep P bad).map eraseCtxSt = (g₂.epMgmt Δ qep P bad).map eraseCtxSt := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
  unfold GameState.epMgmt GameState.leak GameState.safeCh
  split_ifs <;> rfl

theorem eraseCtxSt_record {St₁ St₂ M C : Type} {Δ : ℕ} {P : Party}
    {st₁ : St₁} {st₂ : St₂} {recE : Record M C} {ch : Bool}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    eraseCtxSt (g₁.record Δ P st₁ recE ch) = eraseCtxSt (g₂.record Δ P st₂ recE ch) := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
  unfold GameState.record GameState.safeCh
  split_ifs <;> rfl

theorem eraseCtxSt_accept {St₁ St₂ M C : Type} [DecidableEq M] [DecidableEq C]
    {P : Party} {st₁ : St₁} {st₂ : St₂} {pos : Pos}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    eraseCtxSt (g₁.accept P st₁ pos) = eraseCtxSt (g₂.accept P st₂ pos) := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
  rfl

theorem eraseCtxSt_afterCorr {St₁ St₂ M C : Type} {P : Party}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    eraseCtxSt (g₁.afterCorr P) = eraseCtxSt (g₂.afterCorr P) := by
  cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
  rfl

@[expose] def VSAlign {SS : Type} (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ssMap : ℕ → SS) (P : Party) (tcur : ℕ) (vsLoc : Option SS) (vsM : Option (SS ⊕ ℕ)) : Prop :=
  (vsLoc = none ∧ vsM = none) ∨
  (∃ ss, vsLoc = some ss ∧ vsM = some (.inl ss)) ∨
  (∃ tS idx, idx < q ∧ tS ≤ tcur ∧ healEpoch tL ≤ tS ∧
    isTargetEp qep tL par tS = true ∧ P.sendsIn tS = true ∧
    (P.sendsIn tcur = true → tS = tcur) ∧
    vsLoc = some (ssMap (sIdxForged q tL tS idx)) ∧
    vsM = some (.inr (sIdxForged q tL tS idx)))

@[expose] def VRAlign {RS : Type} (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (rsMap : ℕ → RS) (P : Party) (t : ℕ) (vrLoc : Option RS) (vrM : Option (RS ⊕ ℕ)) : Prop :=
  (vrLoc = none ∧ vrM = none) ∨
  (∃ rs, vrLoc = some rs ∧ vrM = some (.inl rs)) ∨
  (∃ idx, idx < q ∧ healEpoch tL ≤ t ∧
    isTargetEp qep tL par t = true ∧ P.sendsIn t = false ∧
    vrLoc = some (rsMap (sIdxForged q tL t idx)) ∧
    vrM = some (.inr (sIdxForged q tL t idx)))

structure VPAlign {Γ T Sig SS RS : Type} (q qep rem : ℕ) (tL : Option ℕ) (par : Bool)
    (ssMap : ℕ → SS) (rsMap : ℕ → RS) (P : Party)
    (vpLoc : VP Γ T Sig SS RS) (vpM : VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) : Prop where
  id_loc : vpLoc.id = P
  id_m : vpM.id = P
  γ_eq : vpM.γ = vpLoc.γ
  root_eq : vpM.root = vpLoc.root
  cka_eq : vpM.curCkaMsg = vpLoc.curCkaMsg
  tcur_eq : vpM.tcur = vpLoc.tcur
  tcur_rem : vpLoc.tcur + rem ≤ q
  vR_gt : ∀ t, vpLoc.tcur < t → vpLoc.vR t = none ∧ vpM.vR t = none
  vS_align : VSAlign q qep tL par ssMap P vpLoc.tcur vpLoc.vS vpM.vS
  vR_align : ∀ t, VRAlign q qep tL par rsMap P t (vpLoc.vR t) (vpM.vR t)

abbrev Fig8Γ (Pt : Type) := CryptoGames.CKA.DDH.State (BitVec 256) Pt
abbrev Fig8Sig := CryptoGames.Ratchet.RootKey
abbrev Fig8K := BitVec 256
abbrev Fig8SS := RatchetSenderState Fig8K
abbrev Fig8RS := RatchetReceiverState Fig8K (BitVec 256)
abbrev Fig8E := ℕ × LibsignalCiphertextWithSalt32

abbrev SlotES (Pt : Type) (ℓ : ℕ) :=
  EState (VP (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS)
    (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × Fig8E)
    (LocalForgedSlotState Pt Fig8Sig Fig8K Pt)

abbrev MultiES (Pt : Type) (ℓ : ℕ) :=
  EState (VP (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ))
    (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × Fig8E)
    (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)

structure HookTableInv
    (Pt : Type) [DecidableEq Pt]
    (q qep rem : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
    (hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) : Prop where
  not_lfWin : hM.lfWin = false
  sess_eq : ∀ t0, hM.sessions t0 = hLoc.sessions t0
  sess_nodup : ∀ t0, (hLoc.sessions t0).Nodup
  sess_rem : ∀ t0, (hLoc.sessions t0).length + rem ≤ q
  ftbl_off : ∀ t0, isTargetEp qep tL par t0 = false →
    hM.fTable t0 = hLoc.loc.fTable t0 ∧ hLoc.sessions t0 = []
  ftbl_dom : ∀ t0 ik, isTargetEp qep tL par t0 = true →
    (((hLoc.loc.fTable t0).lookup ik).isSome ↔ ik ∈ hLoc.sessions t0) ∧
    (((hM.fTable t0).lookup ik).isSome ↔ ik ∈ hLoc.sessions t0)
  ftbl_val : ∀ t0 idx (hidx : idx < (hLoc.sessions t0).length),
    isTargetEp qep tL par t0 = true →
    (hLoc.loc.fTable t0).lookup ((hLoc.sessions t0)[idx]) =
      some (ks (sIdxForged q tL t0 idx))
  used_iff : ∀ sIdx, hLoc.usedSlot sIdx = true ↔
    ∃ t1 idx1, isTargetEp qep tL par t1 = true ∧ idx1 < (hLoc.sessions t1).length ∧
      sIdx = sIdxForged q tL t1 idx1
  cache_off : ∀ t0, isTargetEp qep tL par t0 = false →
    hM.cache t0 = (hLoc.loc.cache t0).map (fun (Tc, σc, kVal) => (Tc, σc, kVal, none))
  cache_on : ∀ t0, isTargetEp qep tL par t0 = true →
    (hLoc.loc.cache t0 = none ∧ hM.cache t0 = none) ∨
    ∃ Tc σc kD idx, idx < (hLoc.sessions t0).length ∧
      hLoc.loc.cache t0 = some (Tc, σc, ks (sIdxForged q tL t0 idx)) ∧
      hM.cache t0 = some (Tc, σc, kD, some (sIdxForged q tL t0 idx))

theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem modify_run {m : Type → Type} [Monad m] {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

theorem liftH_run {ι : Type} {tspec : OracleSpec ι} {Γ T Sig SS RS M E HS α : Type}
    (x : _root_.CryptoGames.SM.Engine.HM tspec HS α)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

theorem hookTableInv_empty (Pt : Type) [DecidableEq Pt]
    (q qep : ℕ) (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) :
    HookTableInv Pt q qep q tL par ks {} {} where
  not_lfWin := rfl
  sess_eq _ := rfl
  sess_nodup _ := List.nodup_nil
  sess_rem _ := by simp
  ftbl_off _ _ := ⟨rfl, rfl⟩
  ftbl_dom _ _ _ := by simp
  ftbl_val _ _ hidx _ := by simp at hidx
  used_iff _ := Iff.intro (fun h => nomatch h) (fun ⟨_, _, _, h, _⟩ => by simp at h)
  cache_off _ _ := rfl
  cache_on _ _ := Or.inl ⟨rfl, rfl⟩

theorem hookTableInv_mono_rem {Pt : Type} [DecidableEq Pt]
    {q qep rem' rem : ℕ} {tL : Option ℕ} {par : Bool} {ks : ℕ → BitVec 256}
    {hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt}
    {hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E}
    (hle : rem' ≤ rem) (htbl : HookTableInv Pt q qep rem tL par ks hLoc hM) :
    HookTableInv Pt q qep rem' tL par ks hLoc hM :=
  { htbl with sess_rem := fun t0 => by have := htbl.sess_rem t0; omega }

structure ForgedPhase1Inv
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q qep rem : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (ssMap : ℕ → Fig8SS)
    (rsMap : ℕ → Fig8RS)
    (esLoc : SlotES Pt ℓ)
    (esM : MultiES Pt ℓ)
    (tblM tblL : ℕ → SessHSt Pt ℓ) : Prop where
  not_abort : esLoc.abort = false ∧ esM.abort = false
  not_win : esLoc.g.win = false
  not_pl : postLeak tL esLoc.g = false
  ctx_eq : eraseCtxSt esM.g = eraseCtxSt esLoc.g
  loc_epoch : LocEpochInv esLoc.g
  comp_unhealed : CompUnhealed esLoc.g
  leaks_tL : ∀ cur, esLoc.g.tL = some cur → ∃ lk ∈ esLoc.g.leaks, cur = lk
  vp_align : ∀ P, VPAlign q qep rem tL par ssMap rsMap P (esLoc.g.st P) (esM.g.st P)
  htbl : HookTableInv Pt q qep rem tL par ks esLoc.h esM.h
  ss_fresh : ∀ t0 idx, isTargetEp qep tL par t0 = true → idx < q →
    (∀ P, P.sendsIn t0 = true → (esLoc.g.st P).tcur < t0) →
    ssMap (sIdxForged q tL t0 idx) =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks (sIdxForged q tL t0 idx))
  rs_fresh : ∀ t0 idx, isTargetEp qep tL par t0 = true → idx < q →
    (∀ P, P.sendsIn t0 = false → (esLoc.g.st P).tcur < t0) →
    rsMap (sIdxForged q tL t0 idx) =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks (sIdxForged q tL t0 idx))
  sess_inv : ∀ sIdx, ForgedSessInv C ℓ encT idOf (ks sIdx) (ssMap sIdx) (rsMap sIdx)
    ((esM.h.book sIdx).getD {}) (tblM sIdx) (tblL sIdx)

theorem isHonestHdr_eq_of_inv
    {Pt : Type} [DecidableEq Pt]
    {q qep rem : ℕ} {tL : Option ℕ} {par : Bool}
    {ks : ℕ → BitVec 256}
    {hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt}
    {hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E}
    (htbl : HookTableInv Pt q qep rem tL par ks hLoc hM)
    (hdr : Header Pt) :
    isHonestHdrMultiBucket hM hdr = isHonestHdrLocalBucket hLoc.loc hdr := by
  unfold isHonestHdrMultiBucket isHonestHdrLocalBucket
  by_cases htar : isTargetEp qep tL par hdr.1 = true
  · rcases htbl.cache_on hdr.1 htar with ⟨h1, h2⟩ | ⟨Tc, σc, kD, idx, _, h1, h2⟩ <;>
      cases hdr.2 <;> simp [h1, h2]
  · have htar' : isTargetEp qep tL par hdr.1 = false := Bool.eq_false_iff.mpr htar
    rw [htbl.cache_off hdr.1 htar']
    cases hLoc.loc.cache hdr.1 <;> cases hdr.2 <;> rfl

theorem forgedPhase1_exit_halted
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (esLoc : SlotES Pt ℓ) (esM esL : MultiES Pt ℓ)
    (we weL : Option ℕ) (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hhalt : (esLoc.abort || esLoc.g.win) = true)
    (habort : esM.abort = esLoc.abort)
    (hctx : eraseCtxSt esM.g = eraseCtxSt esLoc.g) :
    let M_sess := mSessMain q qep tL
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let runSide := fun (la : Bool) (es0 : MultiES Pt ℓ) (we0 : Option ℕ) (tbl0 : ℕ → SessHSt Pt ℓ) =>
      Prod.fst <$> (simulateQ (pubFsMultiImpl
        (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la)
            1 qep locFs.maxSkip false tL) oa).run (es0, we0)
        if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run
        (fun _ => false, tbl0)
    LeAdd
      (simulateQ (keySlotFixedImplF ks) do
        let (_, es, winEp) ←
          (simulateQ (implLocalForgedSlot
            (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
              (sIdxForged q tL) 1 qep M_sess tL par)
            1 qep locFs.maxSkip tL) oa).run (esLoc, we)
        return forgedOut 3 tL par es winEp)
      (runSide false esM we tblM)
      (runSide true esL weL tblL) := by
  intro M_sess locFs runSide
  unfold LeAdd
  rw [forgedSlot_fixed_eq_localGen_of_halted_or_postLeak (dhScheme Dh) (rootPRNG C.F encPt)
    locFs (sIdxForged q tL) ks 1 qep M_sess tL par oa esLoc we (Or.inl hhalt)]
  apply le_add_of_le_left
  simpa [runSide, LeOne] using forged_halted_leOne
    (hooksLocalBucketAuthForgedHdr (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep tL)
    (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par false)
    1 qep locFs.maxSkip tL par
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
    (pubFsMultiImpl_inl_run _) oa { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort } esM we
    (fun _ => false, tblM) hhalt habort (congrArg GameState.win hctx)
    (congrArg GameState.leaks hctx) (congrArg GameState.corrs hctx)

theorem forgedPhase1_exit_lfWin
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (esLoc : SlotES Pt ℓ) (esM esL : MultiES Pt ℓ)
    (we weM weL : Option ℕ) (tblM tblL : ℕ → SessHSt Pt ℓ)
    (habortL : esL.abort = true) (hlf : esL.h.lfWin = true) :
    let M_sess := mSessMain q qep tL
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let runSide := fun (la : Bool) (es0 : MultiES Pt ℓ) (we0 : Option ℕ) (tbl0 : ℕ → SessHSt Pt ℓ) =>
      Prod.fst <$> (simulateQ (pubFsMultiImpl
        (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la)
            1 qep locFs.maxSkip false tL) oa).run (es0, we0)
        if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run
        (fun _ => false, tbl0)
    LeAdd
      (simulateQ (keySlotFixedImplF ks) do
        let (_, es, winEp) ←
          (simulateQ (implLocalForgedSlot
            (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
              (sIdxForged q tL) 1 qep M_sess tL par)
            1 qep locFs.maxSkip tL) oa).run (esLoc, we)
        return forgedOut 3 tL par es winEp)
      (runSide false esM weM tblM)
      (runSide true esL weL tblL) := by
  intro M_sess locFs runSide
  apply leAdd_of_la_one
  simpa [runSide] using forged_lfWin_aborted_eq_one
    (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par true)
    1 qep locFs.maxSkip tL
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
    (pubFsMultiImpl_inl_run _) oa esL weL (fun _ => false, tblL) habortL hlf

theorem forgedPhase1_exit_postLeak
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    {g₀ : Ctx (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS
      (LibsignalMsgPublicPart × Plain ℓ) Fig8E}
    (esLoc : SlotES Pt ℓ) (esM esL : MultiES Pt ℓ)
    (weM weL : Option ℕ) (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hepoch : LocEpochInv esLoc.g)
    (hpl₀ : postLeak tL g₀ = false)
    (hpl₁ : postLeak tL esLoc.g = true)
    (htL : ∀ cur, esLoc.g.tL = some cur → g₀.tL = some cur ∨ ∃ lk ∈ esLoc.g.leaks, cur = lk) :
    let M_sess := mSessMain q qep tL
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let runSide := fun (la : Bool) (es0 : MultiES Pt ℓ) (we0 : Option ℕ) (tbl0 : ℕ → SessHSt Pt ℓ) =>
      Prod.fst <$> (simulateQ (pubFsMultiImpl
        (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) do
        let (_, es, winEp) ←
          (simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep false tL par la)
            1 qep locFs.maxSkip false tL) oa).run (es0, we0)
        if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run
        (fun _ => false, tbl0)
    LeAdd
      (simulateQ (keySlotFixedImplF ks) do
        let (_, es, winEp) ←
          (simulateQ (implLocalForgedSlot
            (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt) locFs
              (sIdxForged q tL) 1 qep M_sess tL par)
            1 qep locFs.maxSkip tL) oa).run (esLoc, none)
        return forgedOut 3 tL par es winEp)
      (runSide false esM weM tblM)
      (runSide true esL weL tblL) := by
  intro M_sess locFs runSide
  unfold LeAdd
  rw [forgedSlot_fixed_eq_localGen_of_halted_or_postLeak (dhScheme Dh) (rootPRNG C.F encPt)
    locFs (sIdxForged q tL) ks 1 qep M_sess tL par oa esLoc none (Or.inr hpl₁)]
  have hdead : LocDeadForged tL { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort } none :=
    locDeadForged_of_postLeak
      (es := { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort }) (g₀ := g₀) hepoch hpl₀ hpl₁ htL
  have hz : 𝒟[simulateQ lImpl do
      let (_, es', we') ←
        (simulateQ (implLocalBucketAuthGen
          (hooksLocalBucketAuthForgedHdr (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep tL)
          1 qep locFs.maxSkip tL true) oa).run
          ({ g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort }, none)
      return forgedOut 3 tL par es' we'] {true} = 0 :=
    evalDist_locForged_eq_zero_of_dead
      (hooksLocalBucketAuthForgedHdr (dhScheme Dh) (rootPRNG C.F encPt) locFs 1 qep tL)
      (fun _ _ _ new => rfl) qep locFs.maxSkip tL par oa
      { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort } none hdead
  rw [hz]; exact zero_le

theorem sampleOrSlotF_false_run {T Sig K I : Type} [SampleableType K]
    (ks : ℕ → K) (M_sess sIdx : ℕ) (st : LocalForgedSlotState T Sig K I) :
    simulateQ (keySlotFixedImplF ks)
      ((sampleOrSlotF M_sess false sIdx : ForgedSlotHM T Sig K I K).run st) =
    (($ᵗ K : ProbComp K) >>= fun x => pure (x, st)) := by
  unfold sampleOrSlotF
  simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, run_sampleT_fixedF]

theorem sampleOrSlotF_true_run {T Sig K I : Type} [SampleableType K]
    (ks : ℕ → K) {M_sess sIdx : ℕ} {st : LocalForgedSlotState T Sig K I}
    (hlt : sIdx < M_sess) (hnot : st.usedSlot sIdx = false) :
    simulateQ (keySlotFixedImplF ks)
      ((sampleOrSlotF M_sess true sIdx : ForgedSlotHM T Sig K I K).run st) =
    pure (ks sIdx, { st with usedSlot := Function.update st.usedSlot sIdx true }) := by
  unfold sampleOrSlotF
  have hcond : (true && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true := by
    simp [hlt, hnot]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_modify]
  dsimp only [StateT.lift, StateT.run]
  erw [simulateQ_query_bind]
  change ((fun a => (a, { st with usedSlot := Function.update st.usedSlot sIdx true })) <$>
    (pure (ks sIdx) : ProbComp K)) = _
  simp

theorem lookup_off_step
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {q qep rem : ℕ} {tL : Option ℕ} {par : Bool}
    {ks : ℕ → BitVec 256}
    {hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt}
    {hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E}
    {tblM tblL : ℕ → SessHSt Pt ℓ}
    {t0 : ℕ} (hoff : isTargetEp qep tL par t0 = false) (ik : Pt)
    (htbl : HookTableInv Pt q qep rem tL par ks hLoc hM)
    (kLoc : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt → ProbComp Bool)
    (kSide : Bool →
      (Fig8K × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) →
      ProbComp Bool)
    (hk : ∀ kVal hLoc' hM',
      hM'.book = hM.book →
      hLoc'.loc.cache = hLoc.loc.cache →
      hM'.cache = hM.cache →
      HookTableInv Pt q qep rem tL par ks hLoc' hM' →
      LeAdd (kLoc (kVal, hLoc'))
        (kSide false ((kVal, hM'), (fun _ => false, tblM)))
        (kSide true ((kVal, hM'), (fun _ => false, tblL)))) :
    let pubImpl := fun (la : Bool) =>
      pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) false t0 ik).run hLoc) >>= kLoc)
      ((simulateQ (pubImpl false)
        ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
          t0 ik).run hM)).run (fun _ => false, tblM) >>= kSide false)
      ((simulateQ (pubImpl true)
        ((lookupMultiBucketF (SS := Fig8SS) (RS := Fig8RS) (M := LibsignalMsgPublicPart × Plain ℓ)
          t0 ik).run hM)).run (fun _ => false, tblL) >>= kSide true) := by
  intro pubImpl
  have ⟨hft, hses0⟩ := htbl.ftbl_off t0 hoff
  unfold lookupLocalForgedSlotF lookupMultiBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hft]
  cases hlk : (hLoc.loc.fTable t0).lookup ik with
  | some kVal =>
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
    exact hk kVal hLoc hM rfl rfl rfl htbl
  | none =>
    simp only [StateT.run_bind, simulateQ_bind, sampleOrSlotF_false_run,
      run_sampleT_inl_gen (pubImpl false) (pubFsMultiImpl_inl_run _),
      run_sampleT_inl_gen (pubImpl true) (pubFsMultiImpl_inl_run _),
      Bool.false_eq_true, ↓reduceIte, modify_run, StateT.run_pure, simulateQ_pure, bind_assoc, pure_bind]
    refine leAdd_bind ($ᵗ Fig8K : ProbComp Fig8K) fun kVal _ => ?_
    refine hk kVal _ _ rfl rfl rfl
      { not_lfWin := htbl.not_lfWin
        sess_eq := htbl.sess_eq
        sess_nodup := htbl.sess_nodup
        sess_rem := htbl.sess_rem
        ftbl_off := fun t1 h1 => by
          by_cases heq : t1 = t0
          · subst heq; simp [hses0]
          · simp [Function.update_of_ne heq, htbl.ftbl_off t1 h1]
        ftbl_dom := fun t1 ik1 h1 => by
          have hne : t1 ≠ t0 := fun heq => by rw [heq, hoff] at h1; cases h1
          simpa [Function.update_of_ne hne] using htbl.ftbl_dom t1 ik1 h1
        ftbl_val := fun t1 idx1 hidx1 h1 => by
          have hne : t1 ≠ t0 := fun heq => by rw [heq, hoff] at h1; cases h1
          simpa [Function.update_of_ne hne] using htbl.ftbl_val t1 idx1 hidx1 h1
        used_iff := htbl.used_iff
        cache_off := htbl.cache_off
        cache_on := htbl.cache_on }

@[expose] def hmTargetM {Pt : Type} [DecidableEq Pt] (ℓ L : ℕ) (tL : Option ℕ) (t0 : ℕ) (ik : Pt) :
    _root_.CryptoGames.SM.Engine.HM
      (FSMultiSpec Fig8SS Fig8RS Pt (LibsignalMsgPublicPart × Plain ℓ) Fig8E)
      (FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) (Fig8K × ℕ) := do
  let kD ← lookupMultiBucketF t0 ik
  let s1 ← get
  let (sIdx, s2) := regSessMultiBucket L false tL t0 ik s1
  set s2
  return (kD, sIdx)

theorem lookup_target_step
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {q qep rem' : ℕ} {tL : Option ℕ} {par : Bool}
    {ks : ℕ → BitVec 256}
    {hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt}
    {hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E}
    {tblM tblL : ℕ → SessHSt Pt ℓ}
    {t0 : ℕ} (htar : isTargetEp qep tL par t0 = true) (ik : Pt)
    (htbl : HookTableInv Pt q qep (rem' + 1) tL par ks hLoc hM)
    (kLoc : Fig8K × LocalForgedSlotState Pt Fig8Sig Fig8K Pt → ProbComp Bool)
    (kSide : Bool →
      ((Fig8K × ℕ) × FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E) ×
        ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) →
      ProbComp Bool)
    (hk : ∀ idx kD hLoc' hM',
      idx < (hLoc'.sessions t0).length →
      idx < q →
      hM'.book = hM.book →
      hLoc'.loc.cache = hLoc.loc.cache →
      hM'.cache = hM.cache →
      HookTableInv Pt q qep rem' tL par ks hLoc' hM' →
      LeAdd (kLoc (ks (sIdxForged q tL t0 idx), hLoc'))
        (kSide false (((kD, sIdxForged q tL t0 idx), hM'), (fun _ => false, tblM)))
        (kSide true (((kD, sIdxForged q tL t0 idx), hM'), (fun _ => false, tblL)))) :
    let pubImpl := fun (la : Bool) =>
      pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
    LeAdd
      (simulateQ (keySlotFixedImplF ks)
        ((lookupLocalForgedSlotF (sIdxForged q tL) (mSessMain q qep tL) true t0 ik).run hLoc) >>= kLoc)
      ((simulateQ (pubImpl false)
        ((hmTargetM ℓ (q + 1) tL t0 ik).run hM)).run (fun _ => false, tblM) >>= kSide false)
      ((simulateQ (pubImpl true)
        ((hmTargetM ℓ (q + 1) tL t0 ik).run hM)).run (fun _ => false, tblL) >>= kSide true) := by
  intro pubImpl
  rcases isTargetEp_imp htar with ⟨_, _, hqep, hv, _, _, hhe, _, _, _⟩
  have ⟨hdomL, hdomM⟩ := htbl.ftbl_dom t0 ik htar
  have hses_eq := htbl.sess_eq t0
  have hses_rem := htbl.sess_rem t0
  unfold lookupLocalForgedSlotF hmTargetM lookupMultiBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hlkL : (hLoc.loc.fTable t0).lookup ik with
  | some kVal =>
    have hmem : ik ∈ hLoc.sessions t0 := hdomL.mp (by simp [hlkL])
    have hsomeM : ((hM.fTable t0).lookup ik).isSome = true := hdomM.mpr hmem
    rcases Option.isSome_iff_exists.mp hsomeM with ⟨kD, hlkM⟩
    have hcont : (hLoc.sessions t0).contains ik = true := List.contains_iff_mem.mpr hmem
    let idx := (hLoc.sessions t0).idxOf ik
    have hidx_len : idx < (hLoc.sessions t0).length := List.idxOf_lt_length_of_mem hmem
    have hget : (hLoc.sessions t0)[idx] = ik := List.getElem_idxOf hidx_len
    have hkVal : kVal = ks (sIdxForged q tL t0 idx) := by
      have hv0 := htbl.ftbl_val t0 idx hidx_len htar
      rw [hget, hlkL] at hv0
      exact Option.some.inj hv0
    have hsIdxM : regSessMultiBucket (q + 1) false tL t0 ik hM = (sIdxForged q tL t0 idx, hM) := by
      unfold regSessMultiBucket sIdxForged
      simp [hmem, hses_eq, idx]
    simp only [hlkM, hcont, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, StateT.run_set, hsIdxM, simulateQ_pure, pure_bind]
    rw [hkVal]
    exact hk idx kD hLoc hM hidx_len (by omega) rfl rfl rfl
      (hookTableInv_mono_rem (Nat.le_succ rem') htbl)
  | none =>
    have hnmem : ik ∉ hLoc.sessions t0 := fun hm => by
      have := hdomL.mpr hm; simp [hlkL] at this
    have hlkM : (hM.fTable t0).lookup ik = none := by
      cases hm : (hM.fTable t0).lookup ik with
      | none => rfl
      | some _ => exfalso; exact hnmem (hdomM.mp (by simp [hm]))
    let idx := (hLoc.sessions t0).length
    have hidx_q : idx < q := by omega
    let sIdx := sIdxForged q tL t0 idx
    have hsIdx_lt : sIdx < mSessMain q qep tL :=
      sIdxForged_lt_mSessMain q qep tL par (by simpa using hqep) hv hidx_q
    have hnot_used : hLoc.usedSlot sIdx = false := by
      cases hu : hLoc.usedSlot sIdx with
      | false => rfl
      | true =>
        exfalso
        rcases (htbl.used_iff sIdx).mp hu with ⟨t1, idx1, htar1, hidx1, heq⟩
        rcases isTargetEp_imp htar1 with ⟨_, _, _, _, _, _, hhe1, _, _, _⟩
        have hrem1 := htbl.sess_rem t1
        have ⟨ht_eq, hi_eq⟩ := sIdxForged_inj hhe hhe1 hidx_q (by omega) heq
        subst ht_eq; omega
    have hslot_run :
        simulateQ (keySlotFixedImplF ks)
          ((sampleOrSlotF (mSessMain q qep tL) true
            (sIdxForged q tL t0 (hLoc.sessions t0).length) :
            ForgedSlotHM Pt Fig8Sig Fig8K Pt Fig8K).run hLoc) =
        pure (ks sIdx, { hLoc with usedSlot := Function.update hLoc.usedSlot sIdx true }) :=
      sampleOrSlotF_true_run ks hsIdx_lt hnot_used
    have hreg : ∀ kD, regSessMultiBucket (q + 1) false tL t0 ik
        { hM with fTable := Function.update hM.fTable t0 ((ik, kD) :: hM.fTable t0) } =
        (sIdx, { hM with
          fTable := Function.update hM.fTable t0 ((ik, kD) :: hM.fTable t0)
          sessions := Function.update hM.sessions t0 (hLoc.sessions t0 ++ [ik]) }) := fun kD => by
      unfold regSessMultiBucket
      simp [hnmem, hses_eq, sIdx, sIdxForged, idx]
    simp only [hlkM, StateT.run_bind, simulateQ_bind, hslot_run,
      run_sampleT_inl_gen (pubImpl false) (pubFsMultiImpl_inl_run _),
      run_sampleT_inl_gen (pubImpl true) (pubFsMultiImpl_inl_run _),
      ↓reduceIte, modify_run, StateT.run_set, StateT.run_pure,
      simulateQ_pure, bind_assoc, pure_bind, hreg]
    refine leAdd_bind_dummy_loc ($ᵗ Fig8K : ProbComp Fig8K) fun kD _ => ?_
    refine hk idx kD _ _ (by simp [idx]) hidx_q rfl rfl rfl ?_
    refine
      { not_lfWin := htbl.not_lfWin
        sess_eq := fun t1 => by
          by_cases heq : t1 = t0
          · subst heq; simp
          · simp [Function.update_of_ne heq, htbl.sess_eq t1]
        sess_nodup := fun t1 => by
          by_cases heq : t1 = t0
          · subst heq
            simp only [Function.update_self]
            exact List.nodup_append.mpr ⟨htbl.sess_nodup t1, List.nodup_singleton ik,
              fun x hx y hy => by simp at hy; subst hy; rintro rfl; exact hnmem hx⟩
          · simp [Function.update_of_ne heq, htbl.sess_nodup t1]
        sess_rem := fun t1 => by
          by_cases heq : t1 = t0
          · subst heq; simp; omega
          · have := htbl.sess_rem t1; simp [Function.update_of_ne heq]; omega
        ftbl_off := fun t1 h1 => by
          have hne : t1 ≠ t0 := fun heq => by rw [heq, htar] at h1; cases h1
          simpa [Function.update_of_ne hne] using htbl.ftbl_off t1 h1
        ftbl_dom := fun t1 ik1 h1 => by
          by_cases heq : t1 = t0
          · subst heq
            simp only [Function.update_self, List.lookup_cons, List.mem_append, List.mem_singleton]
            by_cases hik : ik1 = ik
            · subst hik; simp
            · have hbeq : (ik1 == ik) = false := beq_eq_false_iff_ne.mpr hik
              simp [hbeq, hik, (htbl.ftbl_dom t1 ik1 htar).1, (htbl.ftbl_dom t1 ik1 htar).2]
          · simpa [Function.update_of_ne heq] using htbl.ftbl_dom t1 ik1 h1
        ftbl_val := fun t1 idx1 hidx1 h1 => by
          by_cases heq : t1 = t0
          · subst heq
            simp only [Function.update_self] at hidx1 ⊢
            have hidx1' : idx1 < (hLoc.sessions t1).length + 1 := by simpa using hidx1
            by_cases hi : idx1 = idx
            · subst hi
              simp [idx, List.getElem_append_right (le_refl _), sIdx]
            · have hlt : idx1 < (hLoc.sessions t1).length := by omega
              have hget1 : (hLoc.sessions t1 ++ [ik])[idx1]'hidx1 = (hLoc.sessions t1)[idx1]'hlt :=
                List.getElem_append_left hlt
              have hne_ik : (hLoc.sessions t1)[idx1]'hlt ≠ ik := fun he =>
                hnmem (he ▸ List.getElem_mem hlt)
              have hbeq : ((hLoc.sessions t1)[idx1]'hlt == ik) = false :=
                beq_eq_false_iff_ne.mpr hne_ik
              rw [hget1]
              simp [List.lookup_cons, hbeq, htbl.ftbl_val t1 idx1 hlt htar]
          · simp only [Function.update_of_ne heq] at hidx1 ⊢
            exact htbl.ftbl_val t1 idx1 hidx1 h1
        used_iff := fun s1 => by
          by_cases hs : s1 = sIdx
          · subst hs
            simp only [Function.update_self, true_iff]
            exact ⟨t0, idx, htar, by simp [idx], rfl⟩
          · simp only [Function.update_of_ne hs, htbl.used_iff s1]
            constructor
            · rintro ⟨t1, idx1, h1, hi1, rfl⟩
              refine ⟨t1, idx1, h1, ?_, rfl⟩
              by_cases ht : t1 = t0
              · subst ht; simp [Nat.lt_succ_of_lt hi1]
              · simpa [Function.update_of_ne ht] using hi1
            · rintro ⟨t1, idx1, h1, hi1, rfl⟩
              refine ⟨t1, idx1, h1, ?_, rfl⟩
              by_cases ht : t1 = t0
              · subst ht
                simp only [Function.update_self, List.length_append, List.length_singleton] at hi1
                have hne_i : idx1 ≠ idx := fun he => hs (by subst he; rfl)
                omega
              · simpa [Function.update_of_ne ht] using hi1
        cache_off := htbl.cache_off
        cache_on := fun t1 h1 => by
          rcases htbl.cache_on t1 h1 with ⟨hc1, hc2⟩ | ⟨Tc, σc, kD0, idx0, hi0, hc1, hc2⟩
          · exact Or.inl ⟨hc1, hc2⟩
          · refine Or.inr ⟨Tc, σc, kD0, idx0, ?_, hc1, hc2⟩
            by_cases ht : t1 = t0
            · subst ht; simp [Nat.lt_succ_of_lt hi0]
            · simpa [Function.update_of_ne ht] using hi0 }

theorem forgedPhase1Inv_mono_rem
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {q qep rem' rem : ℕ} {tL : Option ℕ} {par : Bool}
    {ks : ℕ → BitVec 256} {ssMap : ℕ → Fig8SS} {rsMap : ℕ → Fig8RS}
    {esLoc : SlotES Pt ℓ} {esM : MultiES Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hle : rem' ≤ rem)
    (hinv : ForgedPhase1Inv ℓ Pt C encT idOf q qep rem tL par ks ssMap rsMap esLoc esM tblM tblL) :
    ForgedPhase1Inv ℓ Pt C encT idOf q qep rem' tL par ks ssMap rsMap esLoc esM tblM tblL :=
  { hinv with
    vp_align := fun P =>
      let hv := hinv.vp_align P
      { hv with tcur_rem := by have := hv.tcur_rem; omega }
    htbl := hookTableInv_mono_rem hle hinv.htbl }

theorem makesAtMostQueries_inl {St Msg Coins C : Type}
    (n : ℕ)
    (k : Fin (n + 1) → OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) Bool)
    {rem : ℕ}
    (hq : _root_.CryptoGames.SM.MakesAtMostQueries
      (Bind.bind (m := OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C))
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) (.inl n))) k) rem) :
    ∀ u, _root_.CryptoGames.SM.MakesAtMostQueries (k u) rem := by
  unfold _root_.CryptoGames.SM.MakesAtMostQueries at hq ⊢
  rw [isQueryBoundP_query_bind_iff] at hq
  exact fun u => by simpa using hq.2 u

theorem makesAtMostQueries_inr {St Msg Coins C : Type}
    (qy : (_root_.CryptoGames.SM.spec St Msg Coins C).Domain)
    (k : (_root_.CryptoGames.SM.spec St Msg Coins C).Range qy →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) Bool)
    {rem : ℕ}
    (hq : _root_.CryptoGames.SM.MakesAtMostQueries
      (Bind.bind (m := OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C))
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) (.inr qy))) k) rem) :
    ∃ rem', rem = rem' + 1 ∧ ∀ u, _root_.CryptoGames.SM.MakesAtMostQueries (k u) rem' := by
  unfold _root_.CryptoGames.SM.MakesAtMostQueries at hq ⊢
  rw [isQueryBoundP_query_bind_iff] at hq
  have hpos : 0 < rem := by
    rcases hq.1 with hfalse | hpos
    · simp at hfalse
    · exact hpos
  refine ⟨rem - 1, by omega, fun u => by simpa using hq.2 u⟩

theorem sendMsgsOk_query_bind {St Msg Coins C : Type} {ok : Msg → Bool}
    (qy : (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C).Domain)
    (k : (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C).Range qy →
      OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) Bool)
    (hsh : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok
      (Bind.bind (m := OracleComp (unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C))
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.spec St Msg Coins C) qy)) k)) :
    (_root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg ok qy = false) ∧
      ∀ u, _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok (k u) := by
  unfold _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk at hsh ⊢
  rw [isQueryBoundP_query_bind_iff] at hsh
  have hb : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg ok qy = false := by
    rcases hsh.1 with h0 | hpos
    · cases h : _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg ok qy <;> simp_all
    · omega
  exact ⟨hb, fun u => by simpa [hb] using hsh.2 u⟩

abbrev runLocForged {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256)
    (oa : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (esLoc : SlotES Pt ℓ) (we : Option ℕ) : ProbComp Bool :=
  simulateQ (keySlotFixedImplF ks) do
    let (_, es, winEp) ←
      (simulateQ (implLocalForgedSlot
        (hooksLocalForgedSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          (sIdxForged q tL) 1 qep (mSessMain q qep tL) tL par)
        1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL) oa).run (esLoc, we)
    return forgedOut 3 tL par es winEp

abbrev runSideForged {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (oa : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (es0 : MultiES Pt ℓ) (we0 : Option ℕ) (tbl0 : ℕ → SessHSt Pt ℓ) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (pubFsMultiImpl
    (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) do
    let (_, es, winEp) ←
      (simulateQ (implFSMultiBucketAuth
        (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep false tL par la)
        1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip false tL) oa).run (es0, we0)
    if la then return es.h.lfWin else return forgedOut 3 tL par es winEp).run
    (fun _ => false, tbl0)


theorem sendsIn_false_unique {P Q : Party} {t : ℕ} (_ht : 1 ≤ t)
    (hP : P.sendsIn t = false) (hQ : Q.sendsIn t = false) : Q = P := by
  cases P <;> cases Q <;> simp [Party.sendsIn] at hP hQ ⊢ <;> omega

theorem epMgmt_align {St₁ St₂ M C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {g₁ : GameState St₁ M C} {g₂ : GameState St₂ M C} (h : eraseCtxSt g₁ = eraseCtxSt g₂) :
    (g₁.epMgmt Δ qep P bad = none ∧ g₂.epMgmt Δ qep P bad = none) ∨
    ∃ s₁ s₂, g₁.epMgmt Δ qep P bad = some s₁ ∧ g₂.epMgmt Δ qep P bad = some s₂ ∧
      eraseCtxSt s₁ = eraseCtxSt s₂ ∧ s₁.st = g₁.st ∧ s₂.st = g₂.st ∧
      s₂.epoch P = (if P.sendsIn (g₂.epoch P + 1) then g₂.epoch P + 1 else g₂.epoch P) := by
  by_cases hs : P.sendsIn (g₂.epoch P + 1) = true
  · cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
    unfold GameState.epMgmt GameState.leak GameState.safeCh
    simp only [hs, ↓reduceIte]
    split_ifs <;> [exact Or.inl ⟨rfl, rfl⟩; exact Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, by simp⟩;
      exact Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, by simp⟩]
  · cases g₁; cases g₂; dsimp [eraseCtxSt] at h; injection h; subst_vars
    unfold GameState.epMgmt GameState.leak GameState.safeCh
    simp only [Bool.eq_false_iff.mpr hs, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> [exact Or.inl ⟨rfl, rfl⟩; exact Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩]

theorem epMgmt_leaks_tL {St M C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {g s₁ : GameState St M C}
    (htL : ∀ cur, g.tL = some cur → ∃ lk ∈ g.leaks, cur = lk)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    ∀ cur, s₁.tL = some cur → ∃ lk ∈ s₁.leaks, cur = lk := by
  unfold GameState.epMgmt GameState.leak at hep
  split_ifs at hep with hs hq1 hb hq2 <;> injection hep with hs₁ <;> subst hs₁
  · intro cur hcur
    exact ⟨maxOpt g.tL (g.epoch P + 1), List.mem_cons.mpr (Or.inl rfl), (Option.some.inj hcur).symm⟩
  · exact htL
  · exact htL


theorem mkParties_forgedPhase1Inv
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (γA γB : Fig8Γ Pt) (σ0 : Fig8Sig) (k0 : Fig8K)
    (hLoc : LocalForgedSlotState Pt Fig8Sig Fig8K Pt)
    (hM : FSMultiBucketAuthState Pt Fig8Sig Fig8K Pt Fig8E)
    (hbook : hM.book = fun _ => none)
    (htbl : HookTableInv Pt q qep q tL par ks hLoc hM) :
    let locFs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let pLoc := mkParties γA γB σ0 (locFs.initSender k0) (locFs.initReceiver k0)
    let pM := mkParties γA γB σ0 (Sum.inl (locFs.initSender k0) : Fig8SS ⊕ ℕ)
      (Sum.inl (locFs.initReceiver k0) : Fig8RS ⊕ ℕ)
    let gLoc : Ctx (Fig8Γ Pt) Pt Fig8Sig Fig8SS Fig8RS (LibsignalMsgPublicPart × Plain ℓ) Fig8E :=
      { st := (fun P => match P with | .A => pLoc.1 | .B => pLoc.2), b := false }
    let gM : Ctx (Fig8Γ Pt) Pt Fig8Sig (Fig8SS ⊕ ℕ) (Fig8RS ⊕ ℕ) (LibsignalMsgPublicPart × Plain ℓ) Fig8E :=
      { st := (fun P => match P with | .A => pM.1 | .B => pM.2), b := false }
    ForgedPhase1Inv ℓ Pt C encT idOf q qep q tL par ks
      (fun sIdx => locFs.initSender (ks sIdx))
      (fun sIdx => locFs.initReceiver (ks sIdx))
      { g := gLoc, h := hLoc, abort := false }
      { g := gM, h := hM, abort := false }
      (fun i => hInit (bs i) (.seed (ks i)))
      (fun i => hInit (bs i) (.seed (ks i))) := by
  intro locFs pLoc pM gLoc gM
  refine
    { not_abort := ⟨rfl, rfl⟩
      not_win := rfl
      not_pl := by cases tL <;> rfl
      ctx_eq := rfl
      loc_epoch := ⟨fun P => by cases P <;> simp [gLoc, pLoc, mkParties], fun _ hr => by simp [gLoc] at hr⟩
      comp_unhealed := compUnhealed_init _ false
      leaks_tL := fun _ h => nomatch h
      vp_align := fun P => by
        cases P <;> refine
          { id_loc := by simp [gLoc, pLoc, mkParties]
            id_m := by simp [gM, pM, mkParties]
            γ_eq := by simp [gLoc, gM, pLoc, pM, mkParties]
            root_eq := by simp [gLoc, gM, pLoc, pM, mkParties]
            cka_eq := by simp [gLoc, gM, pLoc, pM, mkParties]
            tcur_eq := by simp [gLoc, gM, pLoc, pM, mkParties]
            tcur_rem := by simp [gLoc, pLoc, mkParties]
            vR_gt := fun t ht => by
              have hne : t ≠ 0 := by simp [gLoc, pLoc, mkParties] at ht; omega
              simp [gLoc, gM, pLoc, pM, mkParties, hne]
            vS_align := by
              simp only [gLoc, gM, pLoc, pM, mkParties]
              first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
            vR_align := fun t => by
              by_cases ht0 : t = 0
              · subst ht0
                simp only [gLoc, gM, pLoc, pM, mkParties]
                first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
              · simp [gLoc, gM, pLoc, pM, mkParties, ht0, VRAlign] }
      htbl := htbl
      ss_fresh := fun _ _ _ _ _ => rfl
      rs_fresh := fun _ _ _ _ _ => rfl
      sess_inv := fun sIdx => by
        rw [hbook]
        exact forgedSessInv_init C ℓ encT idOf (ks sIdx) (bs sIdx) }


end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow
