/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
import Computational.Proofs.E2E.SessionAuthMultiRealShiftedAux

public import Computational.Proofs.E2E.SessionAuthMultiRealBase -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.E2E.SpkHop1A
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.SessionCostedFig8.Bundles
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Real Multi-Session Hop-3 Coupling (`localAuthDF* ≤ multiSessRealWinProb`)

Couples the post-PRNG local games of the Stage-2 `DeliverForgePaper` families
(`localAuthDFShiftedDir2Paper`, `localAuthDFShiftedPaper`, `AuthL11.localAuthDFPaper`, and
`localAuthDFPaperBucketRaw`) to the two-mode (`la = false` + `la = true`) real multi-session
`FSMultiSpec` experiments (`multiSessRealWinProb`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiReal

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (Config GameState Pos Record RecvResult authLosingConditionsAvoided
  healedBy lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Engine (Ctx Policy EM HM EState Hooks TComp VP abortE authOut challE
  coinsE commitE deliverE deliverForgeEGen injectEGen liftH run_liftH_bind transmitE
  vRecv vRecvStep1 vRecv_eq_bind vSend vSendStep1 vSend_eq_bind)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiState Header Mode PartyState
  hooksFSMulti initFSMultiRaw liftFSMulti lookupMultiF mkParties realParty regSessMulti
  regSessOptMulti rootFSMulti sampleT redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket FSMultiSpec)
open _root_.CryptoGames.SM.Construction.AuthL11 (EStateL LHSDead LState SMCompDF SMSpecDF
  accept_update_self corrDoom_true_of_ge epoch_eq_other_of_sendsIn_succ eraseSt eraseSt_accept
  eraseSt_chall eraseSt_inTransit eraseSt_leakDoom eraseSt_record eraseSt_safeCh eraseSt_safeInj
  eraseSt_trivial eraseSt_win hooksLocal hooksLocalFixed initLocal initLocalFixed lImpl
  party_eq_receiverOf_of_sendsIn_false regSessOf rootL rootLFixed simulateQ_lImpl_run_lift_sampleT
  vRecvTail)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF
  SchemeAdversaryDF afterCorrShifted bucketAuthCfg corrEShiftedPaper deliverForgeEB1
  deliverForgeTailB1 engRunDFPaperBucket
  evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_dead hooksLocalBucket
  implEDFShiftedB1 implEDFShiftedDir2Paper implEDFShiftedPaperGen inTransit_mem_trans
  initLocalBucket injectEB1 injectTailB1 deliverForgeTailB1_eq_injectTailB1
  injectTailB1_eq_injectTailDF localAuthAtDFShiftedDir2Paper
  localAuthAtDFShiftedDir2Paper_le_localAuthAtFixedDFShiftedDir2Paper
  localAuthAtFixedDFShiftedDir2Paper localAuthDFShiftedDir2Paper
  localAuthDFShiftedDir2Paper_le_sum_localAuthAtDFShiftedDir2Paper localAuthDFShiftedPaper moAuth
  runLocAtDFShiftedDir2Paper runLocAtFixedDFShiftedDir2Paper runLocAtFixedDFShiftedDir2Paper_pure
  runLocAtFixedDFShiftedDir2Paper_query_bind runLocDFShiftedDir2Paper
  stepLDFShiftedDir2Paper stepLFixedDFShiftedDir2Paper trivB1)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lAead lAeadR lChainPRG lFS lIdeal lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (signalRoundTripShort_proto)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (fwd fwd_inl fwd_inr lazyInit multiSessSpec
  sessLift sessLift_inl sessLift_inr sessLiftCore sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl fsSpec)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (LeOne leOne_bind
  leOne_of_lhs_zero)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (ActiveSessInv SessHSt
  activeSessInv_init activeSessInv_to_phase2 activeSessInv_corruptSender
  activeSessInv_transmit activeSessInv_deliver activeSessInv_inject_phase2 activeSessInv_inject_phase1)
open Computational.Proofs.E2E.SessionAuthMultiRealShiftedAux (
  localAuthDFShiftedDir2Paper_le_at_zero redFSAuthDFShiftedDir2PaperMulti_offRange_one)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti
  redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper)

section Dir2PrivateHelpers

private def sessTag {Pt : Type} {ℓ : ℕ} (s : ℕ) :
    QueryImpl
      (unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))
  | .inl n => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n)
  | .inr q => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩)

private theorem simulateQ_sessLift_sessTag {Pt : Type} {ℓ : ℕ} {σ α : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (s : ℕ)
    (inner : OracleComp (unifSpec + fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) α)
    (tbl : ℕ → σ) :
    (simulateQ (sessLift impl) (simulateQ (sessTag s) inner)).run tbl =
      (fun z => (z.1, Function.update tbl s z.2)) <$> (simulateQ (fwd impl) inner).run (tbl s) := by
  induction inner using OracleComp.inductionOn generalizing tbl with
  | pure a => simp
  | query_bind x k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rcases x with n | q
    · simp only [add_apply_inl, sessTag, query, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inl,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.fwd_inl,
        QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B,
        QueryImpl.id'_apply, StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind,
        bind_assoc, pure_bind]
      exact bind_congr fun u => ih u tbl
    · simp only [add_apply_inr, sessTag, query, StateT.run_bind,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.fwd_inr, map_bind]
      have hstep :
          (simulateQ (sessLift impl) (liftM (OracleSpec.query
            (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))
            (.inr ⟨s, q⟩)))).run tbl =
          (fun r => (r.1, Function.update tbl s r.2)) <$> (impl q).run (tbl s) := by
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inr, sessLiftCore, StateT.run_mk]
        rfl
      erw [hstep]
      simp only [bind_map_left]
      refine bind_congr fun z => ?_
      have hget : Function.update tbl s z.2 s = z.2 := Function.update_self s z.2 tbl
      rw [ih z.1 (Function.update tbl s z.2), hget]
      simp [Function.update_idem]

private def pubFsImpl0 {Pt : Type} {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp)) :
    QueryImpl
      (unifSpec + FSMultiSpec
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (StateT (Bool × σ) ProbComp)
  | .inl n => StateT.lift (query (spec := unifSpec) n)
  | .inr ⟨_, q⟩ => StateT.mk fun (ended0, h0) => do
      let ((ans, ended0'), h0') ←
        (simulateQ (fwd impl)
          ((_root_.CryptoGames.FSAEAD.pubRedImpl
            (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (M := Plain ℓ)
            (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
            (.inr q)).run ended0)).run h0
      return (ans, (ended0', h0'))

private def pubTagImpl {Pt : Type} {ℓ : ℕ} :
    QueryImpl
      (unifSpec + FSMultiSpec
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (StateT (ℕ → Bool) (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))))
  | .inl n => StateT.lift (query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n))
  | .inr ⟨s, q⟩ => StateT.mk fun st => do
      let r ← simulateQ (sessTag s)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr q)).run (st s))
      return (r.1, Function.update st s r.2)

private theorem simulateQ_sessLift_multiSessPubToAD_eq_pubFsImpl0
    {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (oa : TComp (FSMultiSpec
      (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) Bool)
    (hoff : oa.IsQueryBoundP (fun x => sessOffRange 1 x = true) 0)
    (tbl : ℕ → σ) :
    Prod.fst <$> (simulateQ (sessLift impl) (multiSessPubToAD protoSignalCodec oa)).run tbl =
      Prod.fst <$> (simulateQ (pubFsImpl0 impl) oa).run (false, tbl 0) := by
  change Prod.fst <$> (simulateQ (sessLift impl) ((simulateQ pubTagImpl oa).run' (fun _ => false))).run tbl =
    Prod.fst <$> (simulateQ (pubFsImpl0 impl) oa).run (false, tbl 0)
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  suffices hgen : ∀ (pubSt : ℕ → Bool) (tbl : ℕ → σ),
      (fun z : (Bool × (ℕ → Bool)) × (ℕ → σ) => z.1.1) <$>
        (simulateQ (sessLift impl) ((simulateQ pubTagImpl oa).run pubSt)).run tbl =
      Prod.fst <$> (simulateQ (pubFsImpl0 impl) oa).run (pubSt 0, tbl 0) from
    hgen (fun _ => false) tbl
  induction oa using OracleComp.inductionOn with
  | pure a => intro pubSt tbl; simp
  | query_bind x k ih =>
    intro pubSt tbl
    rw [isQueryBoundP_query_bind_iff] at hoff
    have hnp : ¬ (sessOffRange 1 x = true) := hoff.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (k u).IsQueryBoundP (fun x => sessOffRange 1 x = true) 0 :=
      fun u => by simpa [hnp] using hoff.2 u
    rcases x with n | ⟨s, q⟩
    · have hL :
          (simulateQ (sessLift impl) ((pubTagImpl (.inl n)).run pubSt)).run tbl =
            ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
              fun u => pure ((u, pubSt), tbl)) := by
        simp [pubTagImpl, query, _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inl,
          QueryImpl.ofLift_eq_id']
      have hR :
          (pubFsImpl0 impl (.inl n)).run (pubSt 0, tbl 0) =
            ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
              fun u => pure (u, (pubSt 0, tbl 0))) := by
        simp [pubFsImpl0]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, hL, hR, bind_assoc, pure_bind, map_bind]
      exact bind_congr fun u => ih u (hcont u) pubSt tbl
    · have hs0 : s = 0 := by
        have hlt : s < 1 := by simpa [sessOffRange] using hnp
        omega
      subst hs0
      have hL :
          (simulateQ (sessLift impl) ((pubTagImpl (.inr ⟨0, q⟩)).run pubSt)).run tbl =
            (fun z => ((z.1.1, Function.update pubSt 0 z.1.2), Function.update tbl 0 z.2)) <$>
              (simulateQ (fwd impl)
                ((_root_.CryptoGames.FSAEAD.pubRedImpl
                  (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                  (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
                  (AD := Header Pt) (M := Plain ℓ)
                  (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
                  (.inr q)).run (pubSt 0))).run (tbl 0) := by
        simp [pubTagImpl, simulateQ_sessLift_sessTag, Functor.map_map]
      have hR :
          (pubFsImpl0 impl (.inr ⟨0, q⟩)).run (pubSt 0, tbl 0) =
            (((simulateQ (fwd impl)
                ((_root_.CryptoGames.FSAEAD.pubRedImpl
                  (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                  (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
                  (AD := Header Pt) (M := Plain ℓ)
                  (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
                  (.inr q)).run (pubSt 0))).run (tbl 0) : ProbComp _) >>=
              fun r => pure (r.1.1, (r.1.2, r.2))) := rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, hL, hR]
      erw [map_bind, map_bind, bind_map_left, bind_assoc]
      refine bind_congr fun z => ?_
      erw [pure_bind]
      simpa [Function.update_self] using
        ih z.1.1 (hcont z.1.1) (Function.update pubSt 0 z.1.2) (Function.update tbl 0 z.2)

private theorem party_eq_senderOf_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    P = Party.senderOf t := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

private theorem lFS_initSender_eq {Pt : Type}
    (C : Crypto) (codec : _root_.CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (k : BitVec 256) :
    (lFS C codec ℓ encT idOf maxSkip).initSender k =
      (_root_.CryptoGames.FSAEAD.fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).initSender k :=
  rfl

private theorem lFS_initReceiver_eq {Pt : Type}
    (C : Crypto) (codec : _root_.CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (k : BitVec 256) :
    (lFS C codec ℓ encT idOf maxSkip).initReceiver k =
      (_root_.CryptoGames.FSAEAD.fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).initReceiver k :=
  rfl

private theorem lFS_send_eq {Pt : Type}
    (C : Crypto) (codec : _root_.CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ)
    (ss : _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) (h : Header Pt)
    (pm : LibsignalMsgPublicPart × Plain ℓ) :
    (lFS C codec ℓ encT idOf maxSkip).send ss h pm =
      (_root_.CryptoGames.FSAEAD.fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).send
        ss (h, pm.1) pm.2 :=
  rfl

private theorem lFS_receive_eq {Pt : Type}
    (C : Crypto) (codec : _root_.CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ)
    (rs : _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (h : Header Pt)
    (ic : ℕ × LibsignalCiphertextWithSalt32) :
    (lFS C codec ℓ encT idOf maxSkip).receive rs h ic =
      match lPubOf codec ic.2 with
      | none => none
      | some p =>
        ((_root_.CryptoGames.FSAEAD.fromAEADPRG (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip).receive
          rs (h, p) ic).map (fun o => (o.1, o.2.1, (p, o.2.2))) := by
  rcases ic with ⟨i, ct⟩
  unfold lFS _root_.CryptoGames.FSAEAD.fromAEADPRG _root_.CryptoGames.AEADScheme.movePubPartToAD lAeadR
  dsimp only
  cases hlk : rs.skippedKeys.lookup i with
  | some key =>
    cases hp : lPubOf codec ct with
    | none => simp
    | some p => simp only [Option.map_map, Function.comp_def]
  | none =>
    by_cases hw : i ≤ rs.lastIndex ∨ maxSkip < i - rs.lastIndex - 1
    · simp only [hw, ↓reduceIte]
      cases lPubOf codec ct <;> rfl
    · simp only [hw, ↓reduceIte]
      cases hp : lPubOf codec ct with
      | none => simp
      | some p => simp only [Option.map_map, Function.comp_def]

private theorem pubFsImpl0_inl_run {Pt : Type} {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (n : ℕ) (s : Bool × σ) :
    (pubFsImpl0 impl (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)) := by
  simp [pubFsImpl0]

private theorem pubFsImpl0_transmit_run {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (s : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (ℕ × LibsignalCiphertextWithSalt32)}
    {s' : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la) (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, pm.1), pm.2)).run s = pure (u, s')) :
    (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
      (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (h, pm)))))⟩)).run (false, s) =
    pure (u, (false, s')) := by
  simp [pubFsImpl0, _root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.transmitQuery,
    fwd, fsImpl, _root_.CryptoGames.FSAEAD.Thm5.oraclesWith]
  erw [hstep]
  simp

private theorem pubFsImpl0_corruptSender_run {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sIdx : ℕ)
    (s : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))}
    {s' : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
        (C := LibsignalCiphertextWithSalt32) (m := ProbComp) (lChainPRG C.F)
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false) ()).run s = pure (u, s')) :
    (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false))
      (.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩)).run (false, s) =
    pure (u, (false, s')) := by
  simp [pubFsImpl0, _root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.corruptSenderQuery,
    fwd, fsImpl, _root_.CryptoGames.FSAEAD.Thm5.oraclesWith]
  erw [hstep]
  simp

private theorem pubFsImpl0_deliver_some_run {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec ct = some p)
    (s : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))}
    {s' : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.deliverH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)
        (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run s = pure (u, s')) :
    (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
      (.inr ⟨sIdx, .inl (.inr (h, (i, ct)))⟩)).run (false, s) =
    pure (u.map (_root_.CryptoGames.FSAEAD.withPub p), (false, s')) := by
  simp [pubFsImpl0, _root_.CryptoGames.FSAEAD.pubRedImpl, hp_pub,
    _root_.CryptoGames.FSAEAD.deliverQuery, fwd, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith]
  erw [hstep]
  simp

private theorem pubFsImpl0_inject_none_run {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (hp_none : lPubOf protoSignalCodec ct = none)
    (s : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
      (.inr ⟨sIdx, .inr (h, (i, ct))⟩)).run (false, s) =
    pure (some .rejected, (false, s)) := by
  simp [pubFsImpl0, _root_.CryptoGames.FSAEAD.pubRedImpl, hp_none]

private theorem pubFsImpl0_inject_some_run {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (i : ℕ) (ct : LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec ct = some p)
    (s : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))}
    {s' : _root_.CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.injectH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)
        (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, p), (i, ct))).run s = pure (u, s')) :
    (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
      (.inr ⟨sIdx, .inr (h, (i, ct))⟩)).run (false, s) =
    pure (u.map (_root_.CryptoGames.FSAEAD.withPub p), (false, s')) := by
  simp [pubFsImpl0, _root_.CryptoGames.FSAEAD.pubRedImpl, hp_pub,
    _root_.CryptoGames.FSAEAD.injectQuery, fwd, fsImpl,
    _root_.CryptoGames.FSAEAD.Thm5.oraclesWith]
  erw [hstep]
  simp


private abbrev DDHSt (Pt : Type) := _root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt
private abbrev SS256 := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)
private abbrev RS256 := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)
private abbrev MsgPt (ℓ : ℕ) := LibsignalMsgPublicPart × Plain ℓ
private abbrev Ct32 := ℕ × LibsignalCiphertextWithSalt32
private abbrev Dir2ESL (Pt : Type) (ℓ : ℕ) :=
  EStateL (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) Ct32 (BitVec 256) Pt
private abbrev Dir2ESM (Pt : Type) (ℓ : ℕ) :=
  EState (VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ))
    (MsgPt ℓ) (Header Pt × Ct32) (FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32)

private def LeAdd0 (cLoc cM cL : ProbComp Bool) : Prop :=
  𝒟[cLoc] {true} ≤ 𝒟[cM] {true} + 𝒟[cL] {true}

private theorem leAdd0_of_lhs_zero {cLoc cM cL : ProbComp Bool} (h0 : 𝒟[cLoc] {true} = 0) :
    LeAdd0 cLoc cM cL := by
  unfold LeAdd0; rw [h0]; simp

private theorem leAdd0_of_le_main {cLoc cM cL : ProbComp Bool} (hle : 𝒟[cLoc] {true} ≤ 𝒟[cM] {true}) :
    LeAdd0 cLoc cM cL := by
  unfold LeAdd0; exact hle.trans le_self_add

private theorem leAdd0_of_la_one {cLoc cM cL : ProbComp Bool} (h1 : 𝒟[cL] {true} = 1) :
    LeAdd0 cLoc cM cL := by
  unfold LeAdd0; rw [h1]
  have hle1 : 𝒟[cLoc] {true} ≤ 1 := by
    calc 𝒟[cLoc] {true} ≤ 𝒟[cLoc] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  exact hle1.trans le_add_self

private theorem leAdd0_bind {α : Type} (oa : ProbComp α) {fLoc fM fL : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeAdd0 (fLoc a) (fM a) (fL a)) :
    LeAdd0 (oa >>= fLoc) (oa >>= fM) (oa >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [pure_bind]; exact h a (by simp)
  | query_bind t k ih =>
    unfold LeAdd0
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] {true} =
          ∫⁻ u, 𝒟[g u] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := fun g => by
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fLoc), h1 (fun u => k u >>= fM), h1 (fun u => k u >>= fL),
      ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩

private theorem leAdd0_bind_dummy_loc {α : Type} (oa : ProbComp α)
    {cLoc : ProbComp Bool} {fM fL : α → ProbComp Bool}
    (h : ∀ a ∈ support oa, LeAdd0 cLoc (fM a) (fL a)) :
    LeAdd0 cLoc (oa >>= fM) (oa >>= fL) := by
  have hL := leAdd0_bind oa (fLoc := fun _ => cLoc) h
  unfold LeAdd0 at hL ⊢
  rwa [OracleComp.evalDist_bind_const oa cLoc] at hL

private theorem run_liftFSMulti0_transmit {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (h : Header Pt) (pm : MsgPt ℓ)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32) (s : SessHSt Pt ℓ)
    {u : Option Ct32} {s' : SessHSt Pt ℓ}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la) (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, pm.1), pm.2)).run s = pure (u, s')) :
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
      ((liftFSMulti 0
        (_root_.CryptoGames.FSAEAD.transmitQuery (SenderState := SS256) (ReceiverState := RS256) h pm)).run hM)).run
      (false, s) =
    pure ((u, hM), (false, s')) := by
  simp [liftFSMulti, _root_.CryptoGames.FSAEAD.transmitQuery, query]
  erw [← query_eq_liftM, simulateQ_query]
  dsimp only [OracleSpec.query]
  erw [id_map, pubFsImpl0_transmit_run C encT idOf la 0 h pm s hstep]
  simp

private theorem run_liftFSMulti0_corruptSender {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32) (s : SessHSt Pt ℓ)
    {u : Option SS256} {s' : SessHSt Pt ℓ}
    (hstep : ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F)
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run s = pure (u, s')) :
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
      ((liftFSMulti 0
        (_root_.CryptoGames.FSAEAD.corruptSenderQuery (SenderState := SS256) (ReceiverState := RS256)
          (AssocData := Header Pt) (Message := MsgPt ℓ) (Ciphertext := Ct32))).run hM)).run
      (false, s) =
    pure ((u, hM), (false, s')) := by
  simp [liftFSMulti, _root_.CryptoGames.FSAEAD.corruptSenderQuery, query]
  erw [← query_eq_liftM, simulateQ_query]
  dsimp only [OracleSpec.query]
  erw [id_map, pubFsImpl0_corruptSender_run C encT idOf 0 s hstep]
  simp

private theorem run_liftFSMulti0_deliver_some {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (h : Header Pt) (e : Ct32) (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec e.2 = some p)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32) (s : SessHSt Pt ℓ)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.deliverH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)
        (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run s = pure (u, s')) :
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
      ((liftFSMulti 0
        (_root_.CryptoGames.FSAEAD.deliverQuery (SenderState := SS256) (ReceiverState := RS256)
          (Message := MsgPt ℓ) h e)).run hM)).run (false, s) =
    pure ((u.map (_root_.CryptoGames.FSAEAD.withPub p), hM), (false, s')) := by
  rcases e with ⟨i, ct⟩
  dsimp only at hp_pub
  simp [liftFSMulti, _root_.CryptoGames.FSAEAD.deliverQuery, query]
  erw [← query_eq_liftM, simulateQ_query]
  dsimp only [OracleSpec.query]
  erw [id_map, pubFsImpl0_deliver_some_run C encT idOf la 0 h i ct p hp_pub s hstep]
  simp

private theorem run_liftFSMulti0_inject_none {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (h : Header Pt) (e : Ct32) (hp_none : lPubOf protoSignalCodec e.2 = none)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32) (s : SessHSt Pt ℓ) :
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
      ((liftFSMulti 0
        (_root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS256) (ReceiverState := RS256)
          (Message := MsgPt ℓ) h e)).run hM)).run (false, s) =
    pure ((some _root_.CryptoGames.FSAEAD.ReceiveResult.rejected, hM), (false, s)) := by
  rcases e with ⟨i, ct⟩
  dsimp only at hp_none
  simp [liftFSMulti, _root_.CryptoGames.FSAEAD.injectQuery, query]
  erw [← query_eq_liftM, simulateQ_query]
  dsimp only [OracleSpec.query]
  erw [id_map, pubFsImpl0_inject_none_run C encT idOf la 0 h i ct hp_none s]
  simp

private theorem run_liftFSMulti0_inject_some {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (h : Header Pt) (e : Ct32) (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec e.2 = some p)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32) (s : SessHSt Pt ℓ)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.injectH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)
        (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run s = pure (u, s')) :
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
      ((liftFSMulti 0
        (_root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS256) (ReceiverState := RS256)
          (Message := MsgPt ℓ) h e)).run hM)).run (false, s) =
    pure ((u.map (_root_.CryptoGames.FSAEAD.withPub p), hM), (false, s')) := by
  rcases e with ⟨i, ct⟩
  dsimp only at hp_pub
  simp [liftFSMulti, _root_.CryptoGames.FSAEAD.injectQuery, query]
  erw [← query_eq_liftM, simulateQ_query]
  dsimp only [OracleSpec.query]
  erw [id_map, pubFsImpl0_inject_some_run C encT idOf la 0 h i ct p hp_pub s hstep]
  simp

private def runMulti0 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) (la : Bool)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (es : Dir2ESM Pt ℓ) (st0 : Bool × SessHSt Pt ℓ) : ProbComp Bool :=
  Prod.fst <$>
    (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
      (do
        let (_, es') ← (simulateQ (implEDFShiftedPaperGen true l
            (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
              ⟨false, some (l - 1), t⟩ false la)
            2 qep maxForwardJumps t
            (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy)
          oa).run es
        return (if la then es'.h.lfWin else authOut 2 (⟨true, some (l - 1), t⟩ : Mode).policy es'))).run st0

private theorem runMulti0_pure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) (la a : Bool) (es : Dir2ESM Pt ℓ) (st0 : Bool × SessHSt Pt ℓ) :
    runMulti0 C Dh encPt encT idOf qep l t la (pure a) es st0 =
      pure (if la then es.h.lfWin else authOut 2 (⟨true, some (l - 1), t⟩ : Mode).policy es) := by
  simp [runMulti0]

private theorem runMulti0_query_bind {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) (la : Bool)
    (q : (SMSpecDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32).Domain)
    (cont : _ → SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (es : Dir2ESM Pt ℓ) (st0 : Bool × SessHSt Pt ℓ) :
    runMulti0 C Dh encPt encT idOf qep l t la
      ((liftM (OracleSpec.query q) : SMCompDF _ _ _ _ _ _ _ _ _) >>= cont) es st0 =
      ((simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
        ((implEDFShiftedPaperGen true l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
            ⟨false, some (l - 1), t⟩ false la)
          2 qep maxForwardJumps t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy q).run es)).run st0 >>=
        fun z => runMulti0 C Dh encPt encT idOf qep l t la (cont z.1.1) z.1.2 z.2) := by
  unfold runMulti0
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self,
    simulateQ_bind, StateT.run_bind, bind_assoc, map_bind]

private theorem evalDist_runLocAtFixed_eq_zero_of_abort
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l : ℕ) (mo : Mode) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hab : esL.abort = true) :
    𝒟[runLocAtFixedDFShiftedDir2Paper cka prng fs 0 qep l mo 0 k_fs oa esL] {true} = 0 :=
  evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_dead cka prng fs 0 qep l mo 0 k_fs oa esL
    (LHSDead.of_abort 0 (moAuth mo) 0 hab)

private theorem challE_auth_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep : ℕ) (tL : Option ℕ) (t : ℕ) (P : Party) (m₀ m₁ : M) (rc : Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (challE hk 2 qep (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy (P, m₀, m₁, rc)).run es =
      pure (none, es) := by
  unfold challE
  dsimp only [Mode.cfg, Config.auth]
  simp only [Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp
  · cases es.g.epMgmt 2 qep P rc.isSome <;> simp

private theorem corrDoom_true_of_receiver_epoch_ge {St Msg C : Type}
    (l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (g : GameState St Msg C) (P : Party) (hP : P = Party.receiverOf t)
    (hep : t ≤ g.epoch P) :
    (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom g P = true := by
  subst hP
  have hvg : lastLeakGuessAdmissible (2 + 0) (some (l - 1)) t = true := by
    simp [lastLeakGuessAdmissible]; omega
  exact corrDoom_true_of_ge 0 ⟨true, some (l - 1), t⟩ rfl hvg g hep

set_option synthInstance.maxHeartbeats 200000 in
private theorem simulateQ_pubFsImpl0_sampleT_Only {Pt : Type} {ℓ : ℕ} {σ α : Type}
    [SampleableType α]
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (st0 : Bool × σ) :
    (simulateQ (pubFsImpl0 impl) (sampleT α)).run st0 =
      (($ᵗ α : ProbComp α) >>= fun x => pure (x, st0)) := by
  let G := FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32
  unfold sampleT
  induction ($ᵗ α : ProbComp α) using OracleComp.inductionOn generalizing st0 with
  | pure a => simp
  | query_bind n k ih =>
    change (simulateQ (pubFsImpl0 impl) (simulateQ _ (liftM (query n) >>= k) :
        OracleComp (unifSpec + G) α)).run st0 =
      ((query (spec := unifSpec) n >>= k) >>= fun a => pure (a, st0))
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, bind_assoc]
    exact congrArg (query (spec := unifSpec) n >>= ·) (funext fun u => ih u st0)

private theorem simulateQ_pubFsImpl0_run_lift_sampleT {Pt : Type} {ℓ : ℕ} {σ HS α : Type}
    [SampleableType α]
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (hM : HS) (st0 : Bool × σ) :
    (simulateQ (pubFsImpl0 impl)
      ((StateT.lift (sampleT α) : HM (FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32) HS α).run hM)).run st0 =
      (($ᵗ α : ProbComp α) >>= fun x => pure ((x, hM), st0)) := by
  change (simulateQ (pubFsImpl0 impl) (sampleT α >>= fun a => pure (a, hM))).run st0 = _
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    simulateQ_pubFsImpl0_sampleT_Only, bind_assoc, pure_bind]

private theorem initFSMultiRaw_pubFsImpl0_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ} {σ : Type}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (l t : ℕ) (ht2 : 2 ≤ t)
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (st0 : Bool × σ) :
    (simulateQ (pubFsImpl0 impl)
      (initFSMultiRaw (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨false, some (l - 1), t⟩ false)).run st0 =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun kr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun kc =>
        if ((⟨false, some (l - 1), t⟩ : Mode).tL.isSome &&
            0 = (⟨false, some (l - 1), t⟩ : Mode).tH) = true then
          ($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
            let p := (CryptoGames.Ratchet.rootPRNG C.F encPt).up
              ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr) Ir
            let pAB := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) p.1
              (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender p.2))
              (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver p.2))
            pure ({ g := { st := fun | .A => pAB.1 | .B => pAB.2, b := false }, h := {} }, st0)
        else
          let p := (CryptoGames.Ratchet.rootPRNG C.F encPt).up
            ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr) lam
          let pAB := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) p.1
            (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender p.2))
            (Sum.inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver p.2))
          pure ({ g := { st := fun | .A => pAB.1 | .B => pAB.2, b := false }, h := {} }, st0)) := by
  have htStar_lt : ¬ (⟨false, some (l - 1), t⟩ : Mode).tStar < 0 := by dsimp; omega
  have htStar_ne : ¬ (0 = (⟨false, some (l - 1), t⟩ : Mode).tStar) := by dsimp; omega
  unfold initFSMultiRaw
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pubFsImpl0_sampleT_Only, bind_assoc, pure_bind]
  refine congrArg (($ᵗ BitVec 256 : ProbComp _) >>= ·) (funext fun kr => ?_)
  refine congrArg (($ᵗ BitVec 256 : ProbComp _) >>= ·) (funext fun kc => ?_)
  by_cases htH0 : ((⟨false, some (l - 1), t⟩ : Mode).tL.isSome &&
      0 = (⟨false, some (l - 1), t⟩ : Mode).tH) = true
  · simp only [rootFSMulti, htStar_lt, htStar_ne, htH0, ↓reduceIte,
      StateT.run_bind, simulateQ_bind, simulateQ_pubFsImpl0_run_lift_sampleT,
      StateT.run_pure, simulateQ_pure, regSessOptMulti, bind_assoc, pure_bind]
    exact congrArg (($ᵗ Pt : ProbComp _) >>= ·) (funext fun _ => rfl)
  · simp only [rootFSMulti, htStar_lt, htStar_ne, htH0, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, simulateQ_pure, regSessOptMulti, pure_bind]
    rfl

private theorem evalDist_runMulti0_true_eq_one_of_lfWin
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (esL_F : Dir2ESM Pt ℓ) (stL : Bool × SessHSt Pt ℓ)
    (hab : esL_F.abort = true) (hlf : esL_F.h.lfWin = true) :
    𝒟[runMulti0 C Dh encPt encT idOf qep l t true oa esL_F stL] {true} = 1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => rw [runMulti0_pure]; simp [hlf]
  | query_bind q cont ih =>
    rw [runMulti0_query_bind C Dh encPt encT idOf qep l t true q cont esL_F stL]
    rcases q with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · have hStep : (implEDFShiftedPaperGen true l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
            ⟨false, some (l - 1), t⟩ false true)
          2 qep maxForwardJumps t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy (.inl n)).run esL_F =
        (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32) (.inl n)) >>=
          fun u => pure (u, esL_F)) := by
        simp [implEDFShiftedPaperGen, QueryImpl.add_apply_inl, coinsE]
      rw [hStep, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, pubFsImpl0_inl_run, bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), (1 : ℝ≥0∞) ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => ih u
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    all_goals
      simp only [implEDFShiftedPaperGen, injectEGen, deliverForgeEGen, QueryImpl.add_apply,
        transmitE, challE, deliverE, injectEB1, corrEShiftedPaper, deliverForgeEB1,
        StateT.run_bind, StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact ih none

private theorem leAdd_lfWin_terminal {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {cLoc cM : ProbComp Bool}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (esL_F : Dir2ESM Pt ℓ) (stL : Bool × SessHSt Pt ℓ)
    (hab : esL_F.abort = true) (hlf : esL_F.h.lfWin = true) :
    LeAdd0 cLoc cM (runMulti0 C Dh encPt encT idOf qep l t true oa esL_F stL) :=
  leAdd0_of_la_one (evalDist_runMulti0_true_eq_one_of_lfWin C Dh encPt encT idOf qep l t oa esL_F stL hab hlf)

private theorem both_win_leOne
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) (k_fs : BitVec 256)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (esL : Dir2ESL Pt ℓ) (esM : Dir2ESM Pt ℓ) (stM : Bool × SessHSt Pt ℓ)
    (habL : esL.abort = false) (habM : esM.abort = false)
    (hwinL : esL.g.win = true) (hwinM : esM.g.win = true)
    (herase : eraseSt esL.g = eraseSt esM.g) :
    LeOne
      (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs oa esL)
      (runMulti0 C Dh encPt encT idOf qep l t false oa esM stM) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [runLocAtFixedDFShiftedDir2Paper_pure, runMulti0_pure]
    have hauth : authOut 2 (moAuth ⟨false, some (l - 1), t⟩).policy esL =
        authOut 2 (⟨true, some (l - 1), t⟩ : Mode).policy esM := by
      simp only [authOut, moAuth, habL, habM, hwinL, hwinM,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_authOK herase]
    cases hb : authOut 2 (⟨true, some (l - 1), t⟩ : Mode).policy esM
    · simp [LeOne, hauth, hb]
    · cases hidx : (esL.h.lastIdx == some 0) <;> simp [LeOne, hauth, hb]
  | query_bind q cont ih =>
    rw [runLocAtFixedDFShiftedDir2Paper_query_bind,
        runMulti0_query_bind C Dh encPt encT idOf qep l t false q cont esM stM]
    unfold stepLFixedDFShiftedDir2Paper
    rcases q with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · have hL : (implEDFShiftedB1 l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (2 + 0) qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip
          (⟨false, some (l - 1), t⟩ : Mode).tStar
          (moAuth ⟨false, some (l - 1), t⟩).cfg (moAuth ⟨false, some (l - 1), t⟩).policy (.inl n)).run esL =
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n)) >>=
          fun u => pure (u, esL)) := by
        simp [implEDFShiftedB1, QueryImpl.add_apply_inl, coinsE]
      have hM : (implEDFShiftedPaperGen true l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
            ⟨false, some (l - 1), t⟩ false false)
          2 qep maxForwardJumps t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy (.inl n)).run esM =
        (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32) (.inl n)) >>=
          fun u => pure (u, esM)) := by
        simp [implEDFShiftedPaperGen, QueryImpl.add_apply_inl, coinsE]
      rw [hL, hM, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, pubFsImpl0_inl_run, bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ => ih u
    all_goals
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, injectEGen, deliverForgeEGen,
        QueryImpl.add_apply, transmitE, challE, deliverE,
        injectEB1, corrEShiftedPaper, deliverForgeEB1, StateT.run_bind, StateT.run_get,
        pure_bind, hwinL, hwinM, Bool.or_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact ih none

private structure Dir2Sync {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep t : ℕ) (phase1 : Bool) (k_fs : BitVec 256) (ss0 : SS256) (rs0 : RS256)
    (esL : Dir2ESL Pt ℓ) (esM : Dir2ESM Pt ℓ) (sM sL : SessHSt Pt ℓ) : Prop where
  habL : esL.abort = false
  habM : esM.abort = false
  hwinL : esL.g.win = false
  hwinM : esM.g.win = false
  hlfM : esM.h.lfWin = false
  herase : eraseSt esL.g = eraseSt esM.g
  hidL : ∀ P, (esL.g.st P).id = P
  hidM : ∀ P, (esM.g.st P).id = P
  htcurL : ∀ P, (esL.g.st P).tcur = esL.g.epoch P
  htcurM : ∀ P, (esM.g.st P).tcur = esL.g.epoch P
  hγ : ∀ P, (esM.g.st P).γ = (esL.g.st P).γ
  hroot : ∀ P, (esM.g.st P).root = (esL.g.st P).root
  htrans_wf : ∀ r ∈ esL.g.trans, r.ct.1.1 = r.pos.epoch ∧ r.pos.sender = Party.senderOf r.pos.epoch
  hinv : ActiveSessInv C ℓ encT idOf phase1 k_fs ss0 rs0 ((esM.h.book 0).getD {}) sM sL
  hscorr2 : phase1 = false → ((esM.h.book 0).getD {}).sCorr = true
  hbk_trans : ((esM.h.book 0).getD {}).fsTrans =
    (esL.g.trans.filter (fun r => r.pos.epoch == t)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2))
  hbk_count : (esL.g.st (Party.senderOf t)).tcur = t →
    ((esM.h.book 0).getD {}).fsCount = esL.g.idx (Party.senderOf t)
  hsess_nil : ¬ t ≤ (esL.g.st (Party.senderOf t)).tcur →
    esL.h.sessions = [] ∧ esM.h.sessions = [] ∧
    esL.h.cache t = none ∧ esM.h.cache t = none ∧
    esM.h.book 0 = none ∧ phase1 = true ∧
    ss0 = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k_fs ∧
    rs0 = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k_fs
  hsess_sent : t ≤ (esL.g.st (Party.senderOf t)).tcur →
    t ≤ qep ∧ ∃ Tc σc km, esL.h.cache t = some (Tc, σc, k_fs, some 0) ∧
      esM.h.cache t = some (Tc, σc, km, some 0)
  hcache_ne : ∀ ep, ep ≠ t →
    (esL.h.cache ep = none ∧ esM.h.cache ep = none) ∨
    ∃ Tc σc k, esL.h.cache ep = some (Tc, σc, k, none) ∧ esM.h.cache ep = some (Tc, σc, k, none)
  hvS_rel : ∀ P,
    ((esL.g.st P).vS = none ∧ (esM.g.st P).vS = none ∧
      ¬ (P = Party.senderOf t ∧ (esL.g.st P).tcur = t) ∧
      (esM.g.st P).curCkaMsg = (esL.g.st P).curCkaMsg) ∨
    (∃ ss, (esL.g.st P).vS = some (ss, none) ∧ (esM.g.st P).vS = some (Sum.inl ss) ∧
      ¬ (P = Party.senderOf t ∧ (esL.g.st P).tcur = t) ∧
      (esM.g.st P).curCkaMsg = (esL.g.st P).curCkaMsg) ∨
    (t ≤ (esL.g.st (Party.senderOf t)).tcur ∧ P = Party.senderOf t ∧
      ((esL.g.st P).tcur = t ∨ P.sendsIn (esL.g.st P).tcur = false) ∧
      (esL.g.st P).vS = some (ss0, some 0) ∧ (esM.g.st P).vS = some (Sum.inr 0) ∧
      (esM.g.st P).curCkaMsg = (esL.g.st P).curCkaMsg)
  hvR_ne : ∀ P ep, (P, ep) ≠ (Party.receiverOf t, t) →
    ((esL.g.st P).vR ep = none ∧ (esM.g.st P).vR ep = none) ∨
    ∃ rs, (esL.g.st P).vR ep = some (rs, none) ∧ (esM.g.st P).vR ep = some (Sum.inl rs)
  hvR_star :
    ((esL.g.st (Party.receiverOf t)).vR t = none ∧ (esM.g.st (Party.receiverOf t)).vR t = none ∧
      rs0 = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k_fs) ∨
    (t ≤ (esL.g.st (Party.senderOf t)).tcur ∧ t ≤ (esL.g.st (Party.receiverOf t)).tcur ∧
      (esL.g.st (Party.receiverOf t)).vR t = some (rs0, some 0) ∧
      (esM.g.st (Party.receiverOf t)).vR t = some (Sum.inr 0))

private theorem Dir2Sync.hepoch {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.epoch = esL.g.epoch := congrArg GameState.epoch hs.herase.symm

private theorem Dir2Sync.hidx {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.idx = esL.g.idx := congrArg GameState.idx hs.herase.symm

private theorem Dir2Sync.htL {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.tL = esL.g.tL := congrArg GameState.tL hs.herase.symm

private theorem Dir2Sync.htrans {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.trans = esL.g.trans := congrArg GameState.trans hs.herase.symm

private theorem Dir2Sync.hchall {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.chall = esL.g.chall := congrArg GameState.chall hs.herase.symm

private theorem Dir2Sync.hcomp {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.comp = esL.g.comp := congrArg GameState.comp hs.herase.symm

private theorem Dir2Sync.hleaks {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL) :
    esM.g.leaks = esL.g.leaks := congrArg GameState.leaks hs.herase.symm

private theorem dir2Sync_init_state {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep t : ℕ) (ht2 : 2 ≤ t)
    (k_fs kc : BitVec 256) (b_fs : Bool) (σ0 k0 : BitVec 256) :
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let pL := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ0
      (fs.initSender k0, none) (fs.initReceiver k0, none)
    let pM := mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ0
      (Sum.inl (fs.initSender k0)) (Sum.inl (fs.initReceiver k0))
    Dir2Sync (ℓ := ℓ) C encT idOf qep t true k_fs (fs.initSender k_fs) (fs.initReceiver k_fs)
      { g := { st := fun P => match P with | .A => pL.1 | .B => pL.2, b := false }, h := {} }
      { g := { st := fun | .A => pM.1 | .B => pM.2, b := false }, h := {} }
      (_root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))
      (_root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs)) := by
  intro fs pL pM
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [eraseSt, pL, pM, mkParties]
  · intro P; cases P <;> rfl
  · intro P; cases P <;> rfl
  · intro P; cases P <;> rfl
  · intro P; cases P <;> rfl
  · intro P; cases P <;> rfl
  · intro P; cases P <;> rfl
  · intro r hr; cases hr
  · exact activeSessInv_init C ℓ encT idOf true k_fs b_fs
  · intro hp; cases hp
  · intro heq; exfalso; cases hs : Party.senderOf t <;> simp [hs, pL, mkParties] at heq <;> omega
  · intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro hge; exfalso; cases hs : Party.senderOf t <;> simp [hs, pL, mkParties] at hge <;> omega
  · intro ep _; exact Or.inl ⟨rfl, rfl⟩
  · intro P; cases P with
    | A =>
      dsimp [pL, pM, mkParties]
      exact Or.inl ⟨rfl, rfl, fun ⟨_, heq⟩ => by omega, rfl⟩
    | B =>
      dsimp [pL, pM, mkParties]
      exact Or.inr (Or.inl ⟨_, rfl, rfl, fun ⟨_, heq⟩ => by omega, rfl⟩)
  · intro P ep _
    cases P with
    | A =>
      cases ep with
      | zero => dsimp [pL, pM, mkParties]; exact Or.inr ⟨_, rfl, rfl⟩
      | succ n => dsimp [pL, pM, mkParties]; exact Or.inl ⟨rfl, rfl⟩
    | B => cases ep <;> (dsimp [pL, pM, mkParties]; exact Or.inl ⟨rfl, rfl⟩)
  · refine Or.inl ⟨?_, ?_, rfl⟩
    · cases Party.receiverOf t <;> (simp [pL, mkParties]; try omega)
    · cases Party.receiverOf t <;> (simp [pM, mkParties]; try omega)

private theorem dir2Sync_init {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep l t : ℕ) (ht2 : 2 ≤ t)
    (k_fs : BitVec 256) (b_fs : Bool)
    (A : AdversaryDF (Fig8St Pt) (MsgPt ℓ) (BitVec 256) (Fig8C Pt))
    (hstep : ∀ esL esM sM sL ss0 rs0,
      Dir2Sync (ℓ := ℓ) C encT idOf qep t true k_fs ss0 rs0 esL esM sM sL →
      LeAdd0
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs A esL)
        (runMulti0 C Dh encPt encT idOf qep l t false A esM (false, sM))
        (runMulti0 C Dh encPt encT idOf qep l t true A esM (false, sL))) :
    LeAdd0
      (localAuthAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep 0 l k_fs (some (l - 1)) t A)
      (Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t false A)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs)))
      (Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t true A)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))) := by
  have htStar_lt : ¬ (⟨false, some (l - 1), t⟩ : Mode).tStar < 0 := by dsimp; omega
  have htStar_ne : ¬ (0 = (⟨false, some (l - 1), t⟩ : Mode).tStar) := by dsimp; omega
  have hRHS : ∀ la : Bool,
      Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs)) =
      (((simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
        (initFSMultiRaw (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨false, some (l - 1), t⟩ false)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))) >>= fun z =>
          runMulti0 C Dh encPt encT idOf qep l t la A z.1 z.2) := by
    intro la
    have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    unfold redFSAuthDFShiftedDir2PaperMulti redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper runMulti0
    dsimp only [Bool.not_false, Nat.add_zero]
    rw [hms]
    simp only [bind_assoc, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def]
    rfl
  rw [hRHS false, hRHS true,
    initFSMultiRaw_pubFsImpl0_run C Dh encPt encT idOf lam l t ht2,
    initFSMultiRaw_pubFsImpl0_run C Dh encPt encT idOf lam l t ht2]
  unfold localAuthAtFixedDFShiftedDir2Paper initLocalFixed
  simp only [StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, bind_assoc, pure_bind]
  refine leAdd0_bind ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fun kr _ => ?_
  refine leAdd0_bind ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fun kc _ => ?_
  by_cases htH0 : ((⟨false, some (l - 1), t⟩ : Mode).tL.isSome &&
      0 = (⟨false, some (l - 1), t⟩ : Mode).tH) = true
  · simp only [rootLFixed, htStar_lt, htStar_ne, htH0, ↓reduceIte,
      StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT,
      StateT.run_pure, simulateQ_pure, regSessOf, bind_assoc, pure_bind]
    refine leAdd0_bind ($ᵗ Pt : ProbComp Pt) fun _ _ => ?_
    exact hstep _ _ _ _ _ _ (dir2Sync_init_state C Dh encT idOf qep t ht2 k_fs kc b_fs _ _)
  · simp only [rootLFixed, htStar_lt, htStar_ne, htH0, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, simulateQ_pure, regSessOf, pure_bind]
    exact hstep _ _ _ _ _ _ (dir2Sync_init_state C Dh encT idOf qep t ht2 k_fs kc b_fs _ _)

private theorem hℓ_rust_bound {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) :
    ℓ + 16 < _root_.CryptoGames.LibsignalSession.rustLenBound := by
  unfold _root_.CryptoGames.LibsignalSession.rustLenBound; omega

private theorem sendMsgsOkDF_query_bind {St Msg Coins C : Type} (ok : Msg → Bool)
    (q : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Domain)
    (cont : _ → OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool)
    (h : SendMsgsOkDF ok (((liftM (OracleSpec.query q) :
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) _) >>= cont :
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool))) :
    (∀ P m rc, q = .inr (.inl (.inl (.inl (.inl (.inl (P, m, rc)))))) → ok m = true) ∧
      ∀ u, SendMsgsOkDF ok (cont u) := by
  have h0 := _root_.CryptoGames.LibsignalSM.Proofs.WireHop.isQueryBoundP_zero_query_bind
    (P := fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true) q cont h
  refine ⟨fun P m rc hq => ?_, h0.2⟩
  have hnb := h0.1
  subst hq
  simp [badSendMsgDF] at hnb
  exact hnb

private theorem dir2_vR_not_inr_at_t {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep l t : ℕ} (ht2 : 2 ≤ t) (hl : l = t - 1)
    {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party)
    (hcdoom : (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esL.g P = false) :
    ((esM.g.st P).vR t = none ∨ ∃ rs, (esM.g.st P).vR t = some (Sum.inl rs)) ∧
    ∀ ep, ((esL.g.st P).vR ep = none ∧ (esM.g.st P).vR ep = none) ∨
      ∃ rs, (esL.g.st P).vR ep = some (rs, none) ∧ (esM.g.st P).vR ep = some (Sum.inl rs) := by
  have hno_star : ∀ sIdx, (esM.g.st P).vR t ≠ some (Sum.inr sIdx) := by
    intro sIdx hvR
    by_cases hP : P = Party.receiverOf t
    · subst hP
      rcases hs.hvR_star with ⟨_, hM, _⟩ | ⟨_, hge, _, _⟩
      · rw [hM] at hvR; cases hvR
      · rw [hs.htcurL] at hge
        have hc := corrDoom_true_of_receiver_epoch_ge l t ht2 hl esL.g (Party.receiverOf t) rfl hge
        rw [hc] at hcdoom; cases hcdoom
    · rcases hs.hvR_ne P t (fun h => hP (congrArg Prod.fst h)) with ⟨_, hM⟩ | ⟨rs, _, hM⟩ <;>
        (rw [hM] at hvR; cases hvR)
  refine ⟨?_, fun ep => ?_⟩
  · cases hv : (esM.g.st P).vR t with
    | none => exact Or.inl rfl
    | some v =>
      cases v with
      | inl rs => exact Or.inr ⟨rs, rfl⟩
      | inr sIdx => exact False.elim (hno_star sIdx hv)
  · by_cases hPep : (P, ep) = (Party.receiverOf t, t)
    · have hP_eq : P = Party.receiverOf t := congrArg Prod.fst hPep
      have hep_eq : ep = t := congrArg Prod.snd hPep
      subst hP_eq; subst hep_eq
      rcases hs.hvR_star with ⟨hL, hM, _⟩ | ⟨_, _, _, hM⟩
      · exact Or.inl ⟨hL, hM⟩
      · exact False.elim (hno_star 0 hM)
    · exact hs.hvR_ne P ep hPep

private theorem dir2Sync_afterCorrShifted {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep l t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party) :
    Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0
      { esL with g := afterCorrShifted l esL.g P }
      { esM with g := afterCorrShifted l esM.g P } sM sL := by
  have hstL : (afterCorrShifted l esL.g P).st = esL.g.st := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have hstM : (afterCorrShifted l esM.g P).st = esM.g.st := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have hwinL : (afterCorrShifted l esL.g P).win = esL.g.win := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have hwinM : (afterCorrShifted l esM.g P).win = esM.g.win := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have hepL : (afterCorrShifted l esL.g P).epoch = esL.g.epoch := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have hidxL : (afterCorrShifted l esL.g P).idx = esL.g.idx := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  have htrL : (afterCorrShifted l esL.g P).trans = esL.g.trans := by
    unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
  refine
    { habL := hs.habL, habM := hs.habM,
      hwinL := hwinL.trans hs.hwinL, hwinM := hwinM.trans hs.hwinM, hlfM := hs.hlfM,
      herase := _root_.CryptoGames.SM.Construction.DeliverForge.eraseSt_afterCorrShifted hs.herase l P,
      hidL := fun Q => by dsimp; rw [hstL]; exact hs.hidL Q,
      hidM := fun Q => by dsimp; rw [hstM]; exact hs.hidM Q,
      htcurL := fun Q => by dsimp; rw [hstL, hepL]; exact hs.htcurL Q,
      htcurM := fun Q => by dsimp; rw [hstM, hepL]; exact hs.htcurM Q,
      hγ := fun Q => by dsimp; rw [hstM, hstL]; exact hs.hγ Q,
      hroot := fun Q => by dsimp; rw [hstM, hstL]; exact hs.hroot Q,
      htrans_wf := fun r hr => hs.htrans_wf r (htrL ▸ hr),
      hinv := hs.hinv, hscorr2 := hs.hscorr2,
      hbk_trans := by dsimp; rw [htrL]; exact hs.hbk_trans,
      hbk_count := by dsimp; rw [hstL, hidxL]; exact hs.hbk_count,
      hsess_nil := by dsimp; rw [hstL]; exact hs.hsess_nil,
      hsess_sent := by dsimp; rw [hstL]; exact hs.hsess_sent,
      hcache_ne := hs.hcache_ne,
      hvS_rel := fun Q => by dsimp; rw [hstL, hstM]; exact hs.hvS_rel Q,
      hvR_ne := fun Q ep hne => by dsimp; rw [hstL, hstM]; exact hs.hvR_ne Q ep hne,
      hvR_star := by dsimp; rw [hstL, hstM]; exact hs.hvR_star }

private theorem stateT_run_liftH {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem dir2_realParty_eq {Pt : Type} {ℓ : ℕ}
    {esL : Dir2ESL Pt ℓ} {esM : Dir2ESM Pt ℓ}
    (P : Party) (vSM vSL : Option SS256) (hvS : vSM = vSL)
    (vRM vRL : ℕ → Option RS256) (hvR : vRM = vRL)
    (hid : (esM.g.st P).id = (esL.g.st P).id)
    (hroot : (esM.g.st P).root = (esL.g.st P).root)
    (hγ : (esM.g.st P).γ = (esL.g.st P).γ)
    (hcka : (esM.g.st P).curCkaMsg = (esL.g.st P).curCkaMsg)
    (htcur : (esM.g.st P).tcur = (esL.g.st P).tcur) :
    realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root vSM vRM =
    realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root vSL vRL := by
  dsimp only [realParty]; congr 1

private theorem dir2_corrE_cases {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    {phase1 : Bool} (k_fs : BitVec 256) {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party) :
    (∃ esL', esL'.abort = true ∧
      simulateQ lImpl
        ((corrEShiftedPaper l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (⟨true, some (l - 1), t⟩ : Mode).policy P).run esL) = pure (none, esL')) ∨
    (∃ u esL' esM',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL' esM' sM sL ∧
      simulateQ lImpl
        ((corrEShiftedPaper l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (⟨true, some (l - 1), t⟩ : Mode).policy P).run esL) = pure (u, esL') ∧
      ∀ la st0,
        (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))
          ((corrEShiftedPaper l
            (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la)
            (⟨true, some (l - 1), t⟩ : Mode).policy P).run esM)).run st0 = pure ((u, esM'), st0)) ∨
    (∃ u esL' esM' sM',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0 rs0 esL' esM' sM' sL ∧
      simulateQ lImpl
        ((corrEShiftedPaper l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (⟨true, some (l - 1), t⟩ : Mode).policy P).run esL) = pure (u, esL') ∧
      (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
        ((corrEShiftedPaper l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false false)
          (⟨true, some (l - 1), t⟩ : Mode).policy P).run esM)).run (false, sM) =
        pure ((u, esM'), (false, sM'))) := by
  have hallow_eq : esM.g.corrAllowedPaper P = esL.g.corrAllowedPaper P := by
    simp only [GameState.corrAllowedPaper, hs.hchall]
  by_cases hallow : esL.g.corrAllowedPaper P = true
  · have hdoom_eq :
        ((⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esM.g (afterCorrShifted l esM.g P) ||
          (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esM.g P) =
        ((⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esL.g (afterCorrShifted l esL.g P) ||
          (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esL.g P) := by
      simp only [Policy.leakDoom, Policy.corrDoom, afterCorrShifted, GameState.leak,
        hs.hepoch, hs.htL, hs.hleaks]
    by_cases hdoom :
        ((⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esL.g (afterCorrShifted l esL.g P) ||
          (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esL.g P) = true
    · refine Or.inl ⟨{ esL with abort := true }, rfl, ?_⟩
      unfold corrEShiftedPaper
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.hwinL, Bool.false_or,
        hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdoom, abortE,
        StateT.run_modify, StateT.run_pure, simulateQ_pure]
    · have hcdoom : (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esL.g P = false := by
        cases h : (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom esL.g P <;> simp_all
      obtain ⟨hvRt, hvR_all⟩ := dir2_vR_not_inr_at_t ht2 hl hs P hcdoom
      have hs_ac := dir2Sync_afterCorrShifted (l := l) hs P
      have hstL : (afterCorrShifted l esL.g P).st = esL.g.st := by
        unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
      have hstM : (afterCorrShifted l esM.g P).st = esM.g.st := by
        unfold afterCorrShifted GameState.leak; split_ifs <;> rfl
      have hid_eq := (hs.hidM P).trans (hs.hidL P).symm
      have htcur_eq := (hs.htcurM P).trans (hs.htcurL P).symm
      rcases hs.hvS_rel P with ⟨hvSL, hvSM, _, hcka⟩ | ⟨ss, hvSL, hvSM, _, hcka⟩ |
          ⟨ht_le, _, _, hvSL, hvSM, hcka⟩
      · refine Or.inr (Or.inl
          ⟨some (realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root none
             (fun ep => ((esL.g.st P).vR ep).map Prod.fst)), _, _, hs_ac, ?_, fun la st0 => ?_⟩)
        · simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
            hs.habL, hs.hwinL, Bool.false_or, hallow, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hdoom, stateT_run_liftH, hooksLocalFixed, hvSL,
            StateT.run_modify, StateT.run_pure, simulateQ_pure]
          simp [Option.map]
        · rcases hvRt with hvRt | ⟨rs_t, hvRt⟩ <;>
            (simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
              hs.habM, hs.hwinM, Bool.false_or, hallow_eq, hallow, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom, stateT_run_liftH,
              hooksFSMulti, hvSM, hvRt, StateT.run_modify, StateT.run_pure,
              simulateQ_pure];
             congr 4
             exact dir2_realParty_eq P none none rfl _ _
               (funext fun ep => by rcases hvR_all ep with ⟨hL, hM⟩ | ⟨rs, hL, hM⟩ <;> simp [hL, hM])
               hid_eq (hs.hroot P) (hs.hγ P) hcka htcur_eq)
      · refine Or.inr (Or.inl
          ⟨some (realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (some ss)
             (fun ep => ((esL.g.st P).vR ep).map Prod.fst)), _, _, hs_ac, ?_, fun la st0 => ?_⟩)
        · simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
            hs.habL, hs.hwinL, Bool.false_or, hallow, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hdoom, stateT_run_liftH, hooksLocalFixed, hvSL,
            StateT.run_modify, StateT.run_pure, simulateQ_pure]
          simp [Option.map]
        · rcases hvRt with hvRt | ⟨rs_t, hvRt⟩ <;>
            (simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
              hs.habM, hs.hwinM, Bool.false_or, hallow_eq, hallow, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom, stateT_run_liftH,
              hooksFSMulti, hvSM, hvRt, StateT.run_modify, StateT.run_pure,
              simulateQ_pure];
             congr 4
             exact dir2_realParty_eq P (some ss) (some ss) rfl _ _
               (funext fun ep => by rcases hvR_all ep with ⟨hL, hM⟩ | ⟨rs, hL, hM⟩ <;> simp [hL, hM])
               hid_eq (hs.hroot P) (hs.hγ P) hcka htcur_eq)
      · have hinv2 : ActiveSessInv C ℓ encT idOf false k_fs ss0 rs0 ((esM.h.book 0).getD {}) sM sL := by
          cases phase1 with
          | false => exact hs.hinv
          | true => exact activeSessInv_to_phase2 C ℓ encT idOf hs.hinv
        obtain ⟨sM', hcorr_step, hinv'⟩ := activeSessInv_corruptSender C ℓ encT idOf hinv2
        have hrun_corr := run_liftFSMulti0_corruptSender (Pt := Pt) C encT idOf esM.h sM hcorr_step
        let bk_c : FSMultiBook Pt Ct32 := { ((esM.h.book 0).getD {}) with sCorr := true }
        let h_c : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
          { esM.h with book := (Function.update esM.h.book 0 (some bk_c)) }
        refine Or.inr (Or.inr
          ⟨some (realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root (some ss0)
             (fun ep => ((esL.g.st P).vR ep).map Prod.fst)),
           { esL with g := afterCorrShifted l esL.g P },
           { esM with g := afterCorrShifted l esM.g P, h := h_c },
           sM', ?_, ?_, ?_⟩)
        · exact
            { hs_ac with
              hinv := by simpa [h_c, bk_c, Function.update_self] using hinv'
              hscorr2 := fun _ => by simp [h_c, bk_c, Function.update_self]
              hbk_trans := by simpa [h_c, bk_c, Function.update_self] using hs_ac.hbk_trans
              hbk_count := by simpa [h_c, bk_c, Function.update_self] using hs_ac.hbk_count
              hsess_nil := fun hnot => False.elim (hnot (by simpa [hstL] using ht_le)) }
        · simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
            hs.habL, hs.hwinL, Bool.false_or, hallow, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hdoom, stateT_run_liftH, hooksLocalFixed, hvSL,
            StateT.run_modify, StateT.run_pure, simulateQ_pure]
          simp [Option.map]
        · rcases hvRt with hvRt | ⟨rs_t, hvRt⟩ <;>
            (simp only [corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
              hs.habM, hs.hwinM, Bool.false_or, hallow_eq, hallow, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom, stateT_run_liftH,
              hooksFSMulti, hvSM, hvRt, StateT.run_modify, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, bind_assoc, hrun_corr];
             congr 4
             exact dir2_realParty_eq P (some ss0) (some ss0) rfl _ _
               (funext fun ep => by rcases hvR_all ep with ⟨hL, hM⟩ | ⟨rs, hL, hM⟩ <;> simp [hL, hM])
               hid_eq (hs.hroot P) (hs.hγ P) hcka htcur_eq)
  · have hallow_f : esL.g.corrAllowedPaper P = false := Bool.eq_false_iff.mpr hallow
    refine Or.inr (Or.inl ⟨none, esL, esM, hs, ?_, fun la st0 => ?_⟩)
    · simp [corrEShiftedPaper, hs.habL, hs.hwinL, hallow_f]
    · simp [corrEShiftedPaper, hs.habM, hs.hwinM, hallow_eq, hallow_f]

private theorem dir2_epMgmt_sync {StL StM Msg C : Type}
    {gL : GameState StL Msg C} {gM : GameState StM Msg C}
    (herase : eraseSt gL = eraseSt gM) (qep : ℕ) (P : Party) (bad : Bool) :
    (gL.epMgmt 2 qep P bad = none ∧ gM.epMgmt 2 qep P bad = none) ∨
    ∃ s₁L s₁M,
      gL.epMgmt 2 qep P bad = some s₁L ∧
      gM.epMgmt 2 qep P bad = some s₁M ∧
      eraseSt s₁L = eraseSt s₁M ∧
      s₁L.st = gL.st ∧ s₁M.st = gM.st ∧
      s₁L.win = gL.win ∧ s₁M.win = gM.win ∧
      s₁L.trans = gL.trans ∧
      (∀ Q, Q ≠ P → s₁L.epoch Q = gL.epoch Q ∧ s₁L.idx Q = gL.idx Q) ∧
      ((P.sendsIn (gL.epoch P + 1) = false ∧ s₁L.epoch P = gL.epoch P ∧ s₁L.idx P = gL.idx P) ∨
       (P.sendsIn (gL.epoch P + 1) = true ∧ s₁L.epoch P = gL.epoch P + 1 ∧
        s₁L.idx P = 0 ∧ gL.epoch P + 1 ≤ qep)) := by
  obtain ⟨hep, hidx, htL, htr, hch, hcp, hma, hb, hwin, hlk, hcr⟩ :
      gL.epoch = gM.epoch ∧ gL.idx = gM.idx ∧ gL.tL = gM.tL ∧ gL.trans = gM.trans ∧
      gL.chall = gM.chall ∧ gL.comp = gM.comp ∧ gL.maxAcc = gM.maxAcc ∧ gL.b = gM.b ∧
      gL.win = gM.win ∧ gL.leaks = gM.leaks ∧ gL.corrs = gM.corrs := by
    simpa [eraseSt] using herase
  have hsafe : gM.safeCh 2 P = gL.safeCh 2 P := by
    unfold GameState.safeCh; rw [← htL, ← hep]
  by_cases hsends : P.sendsIn (gL.epoch P + 1) = true
  · by_cases hq : qep < gL.epoch P + 1
    · have h1 : gL.epMgmt 2 qep P bad = none := by simp [GameState.epMgmt, hsends, hq]
      have h2 : gM.epMgmt 2 qep P bad = none := by simp [GameState.epMgmt, ← hep, hsends, hq]
      exact Or.inl ⟨h1, h2⟩
    · let gL' := if bad && !gL.safeCh 2 P then gL.leak (gL.epoch P + 1) else gL
      let gM' := if bad && !gL.safeCh 2 P then gM.leak (gL.epoch P + 1) else gM
      have h1 : gL.epMgmt 2 qep P bad = some
          { gL' with epoch := Function.update gL'.epoch P (gL'.epoch P + 1),
                     idx := Function.update gL'.idx P 0 } := by
        simp [GameState.epMgmt, hsends, hq, gL']
      have h2 : gM.epMgmt 2 qep P bad = some
          { gM' with epoch := Function.update gM'.epoch P (gM'.epoch P + 1),
                     idx := Function.update gM'.idx P 0 } := by
        simp [GameState.epMgmt, ← hep, hsends, hq, hsafe, gM']
      refine Or.inr ⟨_, _, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        Or.inr ⟨hsends, ?_, ?_, by omega⟩⟩
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;>
          simp [gL', gM', hb_bad, eraseSt, GameState.leak, hep, hidx, htL, htr, hch, hcp, hma, hb, hwin, hlk, hcr]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gL', hb_bad, GameState.leak]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gM', hb_bad, GameState.leak]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gL', hb_bad, GameState.leak]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gM', hb_bad, GameState.leak]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gL', hb_bad, GameState.leak]
      · intro Q hQP; cases hb_bad : (bad && !gL.safeCh 2 P) <;>
          simp [gL', hb_bad, GameState.leak, Function.update_of_ne hQP]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gL', hb_bad, GameState.leak, Function.update_self]
      · cases hb_bad : (bad && !gL.safeCh 2 P) <;> simp [gL', hb_bad, GameState.leak, Function.update_self]
  · have hsends_f : P.sendsIn (gL.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
    by_cases hq : qep < gL.epoch P
    · have h1 : gL.epMgmt 2 qep P bad = none := by simp [GameState.epMgmt, hsends_f, hq]
      have h2 : gM.epMgmt 2 qep P bad = none := by simp [GameState.epMgmt, ← hep, hsends_f, hq]
      exact Or.inl ⟨h1, h2⟩
    · have h1 : gL.epMgmt 2 qep P bad = some gL := by simp [GameState.epMgmt, hsends_f, hq]
      have h2 : gM.epMgmt 2 qep P bad = some gM := by simp [GameState.epMgmt, ← hep, hsends_f, hq]
      exact Or.inr ⟨gL, gM, h1, h2, herase, rfl, rfl, rfl, rfl, rfl,
        fun _ _ => ⟨rfl, rfl⟩, Or.inl ⟨hsends_f, rfl, rfl⟩⟩

private theorem sendsIn_of_succ_false {P : Party} {ep : ℕ} (h : P.sendsIn (ep + 1) = false) :
    P.sendsIn ep = true := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

private theorem other_eq_senderOf_of_sendsIn_false {P : Party} {ep : ℕ} (h : P.sendsIn ep = false) :
    P.other = Party.senderOf ep := by
  cases P <;> simp [Party.other, Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

private theorem list_bv8_beq_iff : ∀ l1 l2 : List (BitVec 8), List.beq l1 l2 = true ↔ l1 = l2
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by simp [List.beq, Bool.and_eq_true, list_bv8_beq_iff l1 l2]

private theorem hdr_ct_beq_iff {Pt : Type} [DecidableEq Pt] :
    ∀ (x y : Header Pt × Ct32), (x == y) = true ↔ x = y
  | ⟨⟨t1, o1⟩, n1, ⟨l1, c1⟩, b1⟩, ⟨⟨t2, o2⟩, n2, ⟨l2, c2⟩, b2⟩ => by
    cases o1 <;> cases o2 <;>
      (change ((t1 == t2 && _) && (n1 == n2 && ((List.beq l1 l2 && c1 == c2) && b1 == b2))) = true ↔ _;
       dsimp only [BEq.beq, Option.instBEq, Option.instBEq.beq];
       simp [Bool.and_eq_true, list_bv8_beq_iff])

private theorem dir2_fsTrans_idx_eq {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {phase1 : Bool} {k_fs : BitVec 256} {ss0 : SS256} {rs0 : RS256}
    {bk : FSMultiBook Pt Ct32} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k_fs ss0 rs0 bk sM sL)
    {x : ℕ × Header Pt × Ct32} (hx : x ∈ bk.fsTrans) :
    x.1 = x.2.2.1 := by
  rcases hinv with ⟨stR, hinv⟩
  rw [hinv.bk_trans] at hx
  rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
  exact (congrArg Prod.fst (hinv.syncRM.wf_state.inTransit_valid r hr).2.2).symm

private theorem dir2_matched_of_inTransit_some {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    {c : Header Pt × Ct32} {r : Record (MsgPt ℓ) (Header Pt × Ct32)}
    (hin : esL.g.inTransit (Party.senderOf t) c = some r) (hct : c.1.1 = t) :
    ∃ mEntry,
      ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = some mEntry ∧
      mEntry.1 = r.pos.idx ∧ r.pos.epoch = t ∧ r.pos.sender = Party.senderOf t := by
  obtain ⟨hr_mem, hr_snd, hr_ct⟩ := inTransit_mem_trans hin
  have hr_wf := hs.htrans_wf r hr_mem
  have hr_ep : r.pos.epoch = t := by rw [← hr_wf.1, hr_ct, hct]
  have hx_mem : (r.pos.idx, c.1, c.2) ∈ ((esM.h.book 0).getD {}).fsTrans := by
    rw [hs.hbk_trans]
    refine List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr_mem, by simp [hr_ep]⟩, ?_⟩
    rw [hr_ct]
  have hc_beq : ((c.1, c.2) == (c.1, c.2)) = true := (hdr_ct_beq_iff (c.1, c.2) (c.1, c.2)).mpr rfl
  cases hfind : ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind _ hx_mem
    rw [hc_beq] at hfalse; simp at hfalse
  | some mEntry =>
    have hm_mem := List.mem_of_find?_eq_some hfind
    have hm_eq : mEntry.2 = (c.1, c.2) :=
      (hdr_ct_beq_iff _ _).mp
        (List.find?_some (p := fun x : ℕ × Header Pt × Ct32 => x.2 == (c.1, c.2)) hfind)
    have hidx_r := dir2_fsTrans_idx_eq hs.hinv hx_mem
    have hidx_m := dir2_fsTrans_idx_eq hs.hinv hm_mem
    refine ⟨mEntry, rfl, ?_, hr_ep, hr_snd⟩
    rw [hidx_m, hm_eq]; exact hidx_r.symm

private theorem dir2_matched_of_inTransit_none {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    {c : Header Pt × Ct32}
    (hin : esL.g.inTransit (Party.senderOf t) c = none) (_hct : c.1.1 = t) :
    ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := by
  cases hfind : ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) with
  | none => rfl
  | some mEntry =>
    exfalso
    have hm_mem := List.mem_of_find?_eq_some hfind
    have hm_eq : mEntry.2 = (c.1, c.2) :=
      (hdr_ct_beq_iff _ _).mp
        (List.find?_some (p := fun x : ℕ × Header Pt × Ct32 => x.2 == (c.1, c.2)) hfind)
    rw [hs.hbk_trans] at hm_mem
    rcases List.mem_map.mp hm_mem with ⟨r, hr_filt, hr_m⟩
    obtain ⟨hr_mem, hr_ep_b⟩ := List.mem_filter.mp hr_filt
    have hr_ep : r.pos.epoch = t := by simpa using hr_ep_b
    have hr_snd : r.pos.sender = Party.senderOf t := by rw [(hs.htrans_wf r hr_mem).2, hr_ep]
    have hr_ct : r.ct = c := by
      have h2 : (r.ct.1, r.ct.2) = (c.1, c.2) := (congrArg Prod.snd hr_m).trans hm_eq
      exact Prod.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)
    unfold GameState.inTransit at hin
    have hnone := List.find?_eq_none.mp hin r hr_mem
    simp [hr_snd, hr_ct] at hnone

private theorem dir2Sync_accept_ne {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party) (ep i' : ℕ) (hsends_f : P.sendsIn ep = false)
    (hep_le : ep ≤ (esL.g.st P).tcur + 1) (hPep : (P, ep) ≠ (Party.receiverOf t, t))
    (γ' : DDHSt Pt) (σ' : BitVec 256) (rs' : RS256) (hL' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hL_sess : hL'.sessions = esL.h.sessions) (hL_cache : hL'.cache = esL.h.cache) :
    let stL' : PartyState (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) :=
      { esL.g.st P with tcur := max (esL.g.st P).tcur ep, γ := γ', root := σ',
                        vR := Function.update (esL.g.st P).vR ep (some (rs', none)) }
    let stM' : VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) :=
      { esM.g.st P with tcur := max (esM.g.st P).tcur ep, γ := γ', root := σ',
                        vR := Function.update (esM.g.st P).vR ep (some (Sum.inl rs')) }
    let pos : Pos := ⟨P.other, ep, i'⟩
    Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0
      { esL with g := esL.g.accept P stL' pos, h := hL' }
      { esM with g := esM.g.accept P stM' pos } sM sL := by
  intro stL' stM' pos
  have hP_recv : P = Party.receiverOf ep := party_eq_receiverOf_of_sendsIn_false P ep hsends_f
  have hep_ne_t : ep ≠ t := fun h => hPep (by subst h; simp [hP_recv])
  have htcur_eq := (hs.htcurM P).trans (hs.htcurL P).symm
  have htcur_sender_iff :
      t ≤ ((esL.g.accept P stL' pos).st (Party.senderOf t)).tcur ↔
        t ≤ (esL.g.st (Party.senderOf t)).tcur := by
    simp only [GameState.accept, GameState.delete]
    by_cases hPs : Party.senderOf t = P
    · subst hPs; simp only [Function.update_self, stL']; omega
    · simp only [Function.update_of_ne hPs]
  have htr_filt : ((esL.g.accept P stL' pos).trans.filter (fun r => r.pos.epoch == t)) =
      (esL.g.trans.filter (fun r => r.pos.epoch == t)) := by
    simp only [GameState.accept, GameState.delete, List.filter_comm]
    refine (List.filter_eq_self.mpr ?_)
    intro r hr
    obtain ⟨_, hr_ep_b⟩ := List.mem_filter.mp hr
    have hr_ep : r.pos.epoch = t := by simpa using hr_ep_b
    suffices hne_pos : r.pos ≠ pos by simp [hne_pos]
    intro heq_pos
    have := congrArg Pos.epoch heq_pos
    dsimp [pos] at this
    exact hep_ne_t (this.symm.trans hr_ep)
  refine
    { habL := hs.habL, habM := hs.habM,
      hwinL := hs.hwinL, hwinM := hs.hwinM, hlfM := hs.hlfM,
      herase := eraseSt_accept hs.herase P stL' stM' pos,
      hidL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', hs.hidL]
        · simp [Function.update_of_ne hQ, hs.hidL],
      hidM := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stM', hs.hidM]
        · simp [Function.update_of_ne hQ, hs.hidM],
      htcurL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', pos, hs.htcurL]
        · simp [Function.update_of_ne hQ, hs.htcurL],
      htcurM := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stM', pos, htcur_eq, hs.htcurL]
        · simp [Function.update_of_ne hQ, hs.htcurM],
      hγ := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hγ],
      hroot := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hroot],
      htrans_wf := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact hs.htrans_wf r hr.1,
      hinv := hs.hinv, hscorr2 := hs.hscorr2,
      hbk_trans := by dsimp; rw [htr_filt]; exact hs.hbk_trans,
      hbk_count := fun heq_t => by
        simp only [GameState.accept, GameState.delete] at heq_t ⊢
        by_cases hPs : Party.senderOf t = P
        · subst hPs; simp only [Function.update_self, stL'] at heq_t
          exact hs.hbk_count (by omega)
        · simp only [Function.update_of_ne hPs] at heq_t
          exact hs.hbk_count heq_t,
      hsess_nil := fun hnot => by
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs.hsess_nil (mt htcur_sender_iff.mpr hnot)
        exact ⟨hL_sess.trans h1, h2, by rw [hL_cache]; exact h3, h4, h5, h6, h7, h8⟩,
      hsess_sent := fun hge => by
        obtain ⟨hq, Tc, σc, km, hcL, hcM⟩ := hs.hsess_sent (htcur_sender_iff.mp hge)
        exact ⟨hq, Tc, σc, km, by dsimp; rw [hL_cache]; exact hcL, hcM⟩,
      hcache_ne := fun ep' hne => by
        dsimp; rw [hL_cache]; exact hs.hcache_ne ep' hne,
      hvS_rel := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp only [Function.update_self, stL', stM']
          rcases hs.hvS_rel Q with ⟨hL, hM, hnot, hc⟩ | ⟨ss, hL, hM, hnot, hc⟩ |
              ⟨ht_le, hQs, hcur_or, hL, hM, hc⟩
          · exact Or.inl ⟨hL, hM, fun ⟨hQs, hm⟩ => hnot ⟨hQs, by omega⟩, hc⟩
          · exact Or.inr (Or.inl ⟨ss, hL, hM, fun ⟨hQs, hm⟩ => hnot ⟨hQs, by omega⟩, hc⟩)
          · refine Or.inr (Or.inr ⟨?_, hQs, ?_, hL, hM, hc⟩)
            · subst hQs; simp only [Function.update_self]; omega
            · by_cases hle : ep ≤ (esL.g.st Q).tcur
              · rw [Nat.max_eq_left hle]; exact hcur_or
              · rw [Nat.max_eq_right (by omega)]; exact Or.inr hsends_f
        · simp only [Function.update_of_ne hQ]
          rcases hs.hvS_rel Q with h1 | h2 | ⟨ht_le, hQs, hrest⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · refine Or.inr (Or.inr ⟨?_, hQs, hrest⟩)
            have := htcur_sender_iff.mpr ht_le
            simpa [GameState.accept, GameState.delete] using this,
      hvR_ne := fun Q ep' hne => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp only [Function.update_self, stL', stM']
          by_cases hep' : ep' = ep
          · subst hep'; exact Or.inr ⟨rs', by simp, by simp⟩
          · simp only [Function.update_of_ne hep']; exact hs.hvR_ne Q ep' hne
        · simp only [Function.update_of_ne hQ]; exact hs.hvR_ne Q ep' hne,
      hvR_star := by
        simp only [GameState.accept, GameState.delete]
        by_cases hPr : Party.receiverOf t = P
        · subst hPr; simp only [Function.update_self, stL', stM', Function.update_of_ne hep_ne_t.symm]
          rcases hs.hvR_star with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
          · exact Or.inl ⟨h1, h2, h3⟩
          · refine Or.inr ⟨?_, by omega, h3, h4⟩
            have := htcur_sender_iff.mpr h1
            simpa [GameState.accept, GameState.delete] using this
        · simp only [Function.update_of_ne hPr]
          rcases hs.hvR_star with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
          · exact Or.inl ⟨h1, h2, h3⟩
          · refine Or.inr ⟨?_, h2, h3, h4⟩
            have := htcur_sender_iff.mpr h1
            simpa [GameState.accept, GameState.delete] using this }

private theorem dir2_filter_accept_at_t {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (t drop : ℕ) (p : Record (MsgPt ℓ) (Header Pt × Ct32) → Bool)
    (hp : ∀ r, (r.pos.epoch == t) = true → r.pos.sender = Party.senderOf t →
      p r = (r.pos.idx != drop)) :
    ∀ (tr : List (Record (MsgPt ℓ) (Header Pt × Ct32))),
      (∀ r ∈ tr, r.ct.1.1 = r.pos.epoch ∧ r.pos.sender = Party.senderOf r.pos.epoch) →
      List.filter (fun x : ℕ × Header Pt × Ct32 => x.1 != drop)
        (List.map (fun r => (r.pos.idx, r.ct.1, r.ct.2))
          (List.filter (fun r => r.pos.epoch == t) tr)) =
      List.map (fun r => (r.pos.idx, r.ct.1, r.ct.2))
        (List.filter (fun r => r.pos.epoch == t) (List.filter p tr))
  | [], _ => rfl
  | r :: rs, hwf => by
    have hr_wf := hwf r List.mem_cons_self
    have ih := dir2_filter_accept_at_t t drop p hp rs
      (fun r' hr' => hwf r' (List.mem_cons_of_mem _ hr'))
    by_cases hep : (r.pos.epoch == t) = true
    · have hep_eq : r.pos.epoch = t := by simpa using hep
      have hsnd_eq : r.pos.sender = Party.senderOf t := by rw [hr_wf.2, hep_eq]
      simp only [List.filter_cons, hep, ↓reduceIte, List.map_cons, hp r hep hsnd_eq]
      cases (r.pos.idx != drop) <;> simp [hep, ih]
    · have hep_f : (r.pos.epoch == t) = false := Bool.eq_false_iff.mpr hep
      simp only [List.filter_cons, hep_f, Bool.false_eq_true, ↓reduceIte]
      cases p r <;> simp [hep_f, ih]

private theorem dir2Sync_accept_at_t {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 rs' esL esM sM sM' sL sL'}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (ht_sent : t ≤ (esL.g.st (Party.senderOf t)).tcur)
    (ht_le : t ≤ (esL.g.st (Party.receiverOf t)).tcur + 1)
    (γ' : DDHSt Pt) (σ' : BitVec 256) (drop : ℕ)
    (hinv' : ActiveSessInv C ℓ encT idOf phase1 k_fs ss0 rs'
      { ((esM.h.book 0).getD {}) with fsTrans := ((esM.h.book 0).getD {}).fsTrans.filter (·.1 != drop) }
      sM' sL') :
    let P := Party.receiverOf t
    let stL' : PartyState (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) :=
      { esL.g.st P with tcur := max (esL.g.st P).tcur t, γ := γ', root := σ',
                        vR := Function.update (esL.g.st P).vR t (some (rs', some 0)) }
    let stM' : VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) :=
      { esM.g.st P with tcur := max (esM.g.st P).tcur t, γ := γ', root := σ',
                        vR := Function.update (esM.g.st P).vR t (some (Sum.inr 0)) }
    let pos : Pos := ⟨Party.senderOf t, t, drop⟩
    let bk' : FSMultiBook Pt Ct32 :=
      { ((esM.h.book 0).getD {}) with fsTrans := ((esM.h.book 0).getD {}).fsTrans.filter (·.1 != drop) }
    let hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
      { esM.h with book := (Function.update esM.h.book 0 (some bk')) }
    Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs'
      { esL with g := esL.g.accept P stL' pos, h := { esL.h with lastIdx := some 0 } }
      { esM with g := esM.g.accept P stM' pos, h := hM' } sM' sL' := by
  intro P stL' stM' pos bk' hM'
  have hPs_ne : Party.senderOf t ≠ P := by
    dsimp only [P, Party.receiverOf, Party.other]
    cases Party.senderOf t <;> intro h <;> cases h
  have htcur_eq := (hs.htcurM P).trans (hs.htcurL P).symm
  have hbk_trans' : bk'.fsTrans =
      ((esL.g.accept P stL' pos).trans.filter (fun r => r.pos.epoch == t)).map
        (fun r => (r.pos.idx, r.ct.1, r.ct.2)) := by
    dsimp only [bk', pos]
    rw [hs.hbk_trans]
    simp only [GameState.accept, GameState.delete]
    refine dir2_filter_accept_at_t t drop _ ?_ esL.g.trans hs.htrans_wf
    intro r hep hsnd
    have hep_eq : r.pos.epoch = t := by simpa using hep
    rcases hr_p : r.pos with ⟨s0, e0, i0⟩
    rw [hr_p] at hep_eq hsnd; dsimp at hep_eq hsnd ⊢; subst hep_eq hsnd
    by_cases hi : i0 = drop
    · subst hi; simp
    · have hne : ({ sender := Party.senderOf e0, epoch := e0, idx := i0 } : Pos) ≠
          { sender := Party.senderOf e0, epoch := e0, idx := drop } :=
        fun h => hi (congrArg Pos.idx h)
      simp [bne, BEq.beq, hi, hne]
  refine
    { habL := hs.habL, habM := hs.habM,
      hwinL := hs.hwinL, hwinM := hs.hwinM, hlfM := hs.hlfM,
      herase := eraseSt_accept hs.herase P stL' stM' pos,
      hidL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', hs.hidL]
        · simp [Function.update_of_ne hQ, hs.hidL],
      hidM := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stM', hs.hidM]
        · simp [Function.update_of_ne hQ, hs.hidM],
      htcurL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', pos, hs.htcurL]
        · simp [Function.update_of_ne hQ, hs.htcurL],
      htcurM := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stM', pos, htcur_eq, hs.htcurL]
        · simp [Function.update_of_ne hQ, hs.htcurM],
      hγ := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hγ],
      hroot := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hroot],
      htrans_wf := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact hs.htrans_wf r hr.1,
      hinv := by simpa [hM', bk', Function.update_self] using hinv',
      hscorr2 := fun hp => by dsimp [hM', bk']; rw [Function.update_self]; exact hs.hscorr2 hp,
      hbk_trans := by simpa [hM', Function.update_self] using hbk_trans',
      hbk_count := fun heq_t => by
        simp only [GameState.accept, GameState.delete, Function.update_of_ne hPs_ne] at heq_t
        dsimp [hM', bk']; rw [Function.update_self]
        exact hs.hbk_count heq_t,
      hsess_nil := fun hnot => by
        simp only [GameState.accept, GameState.delete, Function.update_of_ne hPs_ne] at hnot
        exact False.elim (hnot ht_sent),
      hsess_sent := fun _ => hs.hsess_sent ht_sent,
      hcache_ne := hs.hcache_ne,
      hvS_rel := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp only [Function.update_self, stL', stM']
          rcases hs.hvS_rel P with ⟨hL, hM, _, hc⟩ | ⟨ss, hL, hM, _, hc⟩ | ⟨_, hPs_eq, _⟩
          · exact Or.inl ⟨hL, hM, fun ⟨h1, _⟩ => hPs_ne h1.symm, hc⟩
          · exact Or.inr (Or.inl ⟨ss, hL, hM, fun ⟨h1, _⟩ => hPs_ne h1.symm, hc⟩)
          · exact False.elim (hPs_ne hPs_eq.symm)
        · simp only [Function.update_of_ne hQ, Function.update_of_ne hPs_ne]
          exact hs.hvS_rel Q,
      hvR_ne := fun Q ep' hne => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp only [Function.update_self, stL', stM']
          have hep' : ep' ≠ t := fun h => hne (by subst h; rfl)
          simp only [Function.update_of_ne hep']; exact hs.hvR_ne P ep' hne
        · simp only [Function.update_of_ne hQ]; exact hs.hvR_ne Q ep' hne,
      hvR_star := by
        simp only [GameState.accept, GameState.delete, Function.update_of_ne hPs_ne]
        refine Or.inr ⟨ht_sent, ?_, ?_, ?_⟩
        · simp [P, stL']
        · simp [P, stL']
        · simp [P, stM'] }

private theorem dir2Sync_record_ne {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    {s₁L : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) (MsgPt ℓ) Ct32}
    {s₁M : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) (MsgPt ℓ) Ct32}
    (P : Party) (hs₁_er : eraseSt s₁L = eraseSt s₁M)
    (hs₁_stL : s₁L.st = esL.g.st) (hs₁_stM : s₁M.st = esM.g.st)
    (hs₁_winL : s₁L.win = esL.g.win) (hs₁_winM : s₁M.win = esM.g.win)
    (hs₁_tr : s₁L.trans = esL.g.trans)
    (hs₁_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q ∧ s₁L.idx Q = esL.g.idx Q)
    (hep_ge : esL.g.epoch P ≤ s₁L.epoch P)
    (hep_le : s₁L.epoch P ≤ esL.g.epoch P + 1)
    (hP_sends : P = Party.senderOf (s₁L.epoch P))
    (hep_ne_t : s₁L.epoch P ≠ t)
    (γ' : DDHSt Pt) (T' : Option Pt) (σ' : BitVec 256)
    (vSL : Option (SS256 × Option ℕ)) (vSM : Option (SS256 ⊕ ℕ))
    (hvS_new : (vSL = none ∧ vSM = none) ∨ ∃ ss, vSL = some (ss, none) ∧ vSM = some (Sum.inl ss))
    (m : MsgPt ℓ) (e : Ct32)
    (hL' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32)
    (hh_sess : hL'.sessions = esL.h.sessions ∧ hM'.sessions = esM.h.sessions)
    (hh_book : hM'.book = esM.h.book ∧ hM'.lfWin = esM.h.lfWin)
    (hh_cache_t : hL'.cache t = esL.h.cache t ∧ hM'.cache t = esM.h.cache t)
    (hh_cache_ne : ∀ ep', ep' ≠ t →
      (hL'.cache ep' = none ∧ hM'.cache ep' = none) ∨
      ∃ Tc σc k, hL'.cache ep' = some (Tc, σc, k, none) ∧ hM'.cache ep' = some (Tc, σc, k, none)) :
    let stL' : PartyState (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) :=
      { esL.g.st P with tcur := s₁L.epoch P, γ := γ', curCkaMsg := T', root := σ', vS := vSL }
    let stM' : VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) :=
      { esM.g.st P with tcur := s₁L.epoch P, γ := γ', curCkaMsg := T', root := σ', vS := vSM }
    let recL : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (s₁L.epoch P, T'), e⟩
    let recM : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (s₁L.epoch P, T'), e⟩
    Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0
      { esL with g := s₁L.record 2 P stL' recL false, h := hL' }
      { esM with g := s₁M.record 2 P stM' recM false, h := hM' } sM sL := by
  intro stL' stM' recL recM
  have hs₁_ep : s₁M.epoch = s₁L.epoch := congrArg GameState.epoch hs₁_er.symm
  have hs₁_idx : s₁M.idx = s₁L.idx := congrArg GameState.idx hs₁_er.symm
  have hrec_eq : recM = recL := by dsimp [recL, recM]; rw [hs₁_ep, hs₁_idx]
  have htcur_sender_iff :
      t ≤ ((s₁L.record 2 P stL' recL false).st (Party.senderOf t)).tcur ↔
        t ≤ (esL.g.st (Party.senderOf t)).tcur := by
    simp only [GameState.record, hs₁_stL]
    by_cases hPs : Party.senderOf t = P
    · subst hPs; simp only [Function.update_self, stL', hs.htcurL]; omega
    · simp only [Function.update_of_ne hPs]
  have htcur_mono : ∀ Q, (esL.g.st Q).tcur ≤ ((s₁L.record 2 P stL' recL false).st Q).tcur := by
    intro Q; simp only [GameState.record, hs₁_stL]
    by_cases hQ : Q = P
    · subst hQ; simp only [Function.update_self, stL', hs.htcurL]; exact hep_ge
    · simp only [Function.update_of_ne hQ]; exact le_rfl
  exact
    { habL := hs.habL,
      habM := hs.habM,
      hwinL := by simp [GameState.record, hs₁_winL, hs.hwinL],
      hwinM := by simp [GameState.record, hs₁_winM, hs.hwinM],
      hlfM := by dsimp only; rw [hh_book.2]; exact hs.hlfM,
      herase := hrec_eq ▸ eraseSt_record hs₁_er 2 P stL' stM' recL false,
      hidL := fun Q => by
        simp only [GameState.record, hs₁_stL]
        by_cases hQ : Q = P
        · subst Q; simp [stL', hs.hidL P]
        · simp [Function.update_of_ne hQ, hs.hidL Q],
      hidM := fun Q => by
        simp only [GameState.record, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stM', hs.hidM P]
        · simp [Function.update_of_ne hQ, hs.hidM Q],
      htcurL := fun Q => by
        simp only [GameState.record, hs₁_stL]
        by_cases hQ : Q = P
        · subst Q; simp [stL']
        · simp [Function.update_of_ne hQ, hs.htcurL Q, (hs₁_other Q hQ).1],
      htcurM := fun Q => by
        simp only [GameState.record, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stM']
        · simp [Function.update_of_ne hQ, hs.htcurM Q, (hs₁_other Q hQ).1],
      hγ := fun Q => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hγ Q],
      hroot := fun Q => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hroot Q],
      htrans_wf := fun r hr => by
        simp only [GameState.record, hs₁_tr, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨rfl, hP_sends⟩
        · exact hs.htrans_wf r hr,
      hinv := by dsimp only; rw [hh_book.1]; exact hs.hinv,
      hscorr2 := by dsimp only; rw [hh_book.1]; exact hs.hscorr2,
      hbk_trans := by
        dsimp only; rw [hh_book.1]
        have hbeq : (recL.pos.epoch == t) = false := beq_false_of_ne hep_ne_t
        simp only [GameState.record, hs₁_tr, List.filter_cons, hbeq, Bool.false_eq_true, ↓reduceIte]
        exact hs.hbk_trans,
      hbk_count := fun htcur => by
        dsimp only; rw [hh_book.1]
        simp only [GameState.record, hs₁_stL] at htcur ⊢
        by_cases hPs : Party.senderOf t = P
        · subst hPs; simp only [Function.update_self, stL'] at htcur; exact absurd htcur hep_ne_t
        · simp only [Function.update_of_ne hPs] at htcur ⊢
          rw [(hs₁_other _ hPs).2]
          exact hs.hbk_count htcur,
      hsess_nil := fun hnot => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs.hsess_nil (mt htcur_sender_iff.mpr hnot)
        exact ⟨hh_sess.1.trans h1, hh_sess.2.trans h2, hh_cache_t.1.trans h3,
          hh_cache_t.2.trans h4, (congrFun hh_book.1 0).trans h5, h6, h7, h8⟩,
      hsess_sent := fun hle => by
        obtain ⟨hq, Tc, σc, km, hcL, hcM⟩ := hs.hsess_sent (htcur_sender_iff.mp hle)
        exact ⟨hq, Tc, σc, km, hh_cache_t.1.trans hcL, hh_cache_t.2.trans hcM⟩,
      hcache_ne := hh_cache_ne,
      hvS_rel := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_self]
          rcases hvS_new with ⟨hL0, hM0⟩ | ⟨ss, hL0, hM0⟩
          · exact Or.inl ⟨hL0, hM0, fun h => hep_ne_t h.2, rfl⟩
          · exact Or.inr (Or.inl ⟨ss, hL0, hM0, fun h => hep_ne_t h.2, rfl⟩)
        · rcases hs.hvS_rel Q with ⟨h1, h2, h3, h4⟩ | ⟨ss, h1, h2, h3, h4⟩ |
              ⟨h1, h2, h3, h4, h5, h6⟩
          · simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_of_ne hQ]
            exact Or.inl ⟨h1, h2, h3, h4⟩
          · simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_of_ne hQ]
            exact Or.inr (Or.inl ⟨ss, h1, h2, h3, h4⟩)
          · have hle' := htcur_sender_iff.mpr h1
            simp only [GameState.record, hs₁_stL] at hle'
            simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_of_ne hQ]
            exact Or.inr (Or.inr ⟨hle', h2, h3, h4, h5, h6⟩),
      hvR_ne := fun Q ep' hne => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, stL', stM']; exact hs.hvR_ne P ep' hne
        · simp only [Function.update_of_ne hQ]; exact hs.hvR_ne Q ep' hne,
      hvR_star := by
        rcases hs.hvR_star with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
        · left
          refine ⟨?_, ?_, h3⟩
          · simp only [GameState.record, hs₁_stL]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stL']; rw [← hPs]; exact h1
            · rw [Function.update_of_ne hPs]; exact h1
          · simp only [GameState.record, hs₁_stM]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stM']; rw [← hPs]; exact h2
            · rw [Function.update_of_ne hPs]; exact h2
        · right
          refine ⟨le_trans h1 (htcur_mono _), le_trans h2 (htcur_mono _), ?_, ?_⟩
          · simp only [GameState.record, hs₁_stL]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stL']; rw [← hPs]; exact h3
            · rw [Function.update_of_ne hPs]; exact h3
          · simp only [GameState.record, hs₁_stM]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stM']; rw [← hPs]; exact h4
            · rw [Function.update_of_ne hPs]; exact h4 }

private theorem dir2Sync_record_at_t {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {C : Crypto} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qep t : ℕ} {phase1 phase1' : Bool} {k_fs : BitVec 256}
    {ss0 ss0' : SS256} {rs0 : RS256} {esL : Dir2ESL Pt ℓ} {esM : Dir2ESM Pt ℓ}
    {sM sL sM' sL' : SessHSt Pt ℓ}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    {s₁L : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) (MsgPt ℓ) Ct32}
    {s₁M : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) (MsgPt ℓ) Ct32}
    (P : Party) (hs₁_er : eraseSt s₁L = eraseSt s₁M)
    (hs₁_stL : s₁L.st = esL.g.st) (hs₁_stM : s₁M.st = esM.g.st)
    (hs₁_winL : s₁L.win = esL.g.win) (hs₁_winM : s₁M.win = esM.g.win)
    (hs₁_tr : s₁L.trans = esL.g.trans)
    (hs₁_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q ∧ s₁L.idx Q = esL.g.idx Q)
    (hep_ge : esL.g.epoch P ≤ s₁L.epoch P)
    (hP_sends : P = Party.senderOf t)
    (hep_eq_t : s₁L.epoch P = t)
    (ht_le_qep : t ≤ qep)
    (γ' : DDHSt Pt) (T' : Option Pt) (σ' : BitVec 256)
    (m : MsgPt ℓ) (e : Ct32)
    (hL' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32)
    (bk' : FSMultiBook Pt Ct32)
    (hbk_eq : hM'.book 0 = some bk')
    (hlf_eq : hM'.lfWin = false)
    (hh_cache_t : ∃ Tc σc km, hL'.cache t = some (Tc, σc, k_fs, some 0) ∧
      hM'.cache t = some (Tc, σc, km, some 0))
    (hh_cache_ne : ∀ ep', ep' ≠ t →
      (hL'.cache ep' = none ∧ hM'.cache ep' = none) ∨
      ∃ Tc σc k, hL'.cache ep' = some (Tc, σc, k, none) ∧ hM'.cache ep' = some (Tc, σc, k, none))
    (hinv' : ActiveSessInv C ℓ encT idOf phase1' k_fs ss0' rs0 bk' sM' sL')
    (hscorr2' : phase1' = false → bk'.sCorr = true)
    (hbk_cnt' : bk'.fsCount = s₁L.idx P + 1)
    (hbk_tr' : bk'.fsTrans = (s₁L.idx P + 1, (t, T'), e) :: ((esM.h.book 0).getD {}).fsTrans) :
    let stL' : PartyState (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) :=
      { esL.g.st P with tcur := t, γ := γ', curCkaMsg := T', root := σ', vS := some (ss0', some 0) }
    let stM' : VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) :=
      { esM.g.st P with tcur := t, γ := γ', curCkaMsg := T', root := σ', vS := some (Sum.inr 0) }
    let recL : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (t, T'), e⟩
    let recM : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (t, T'), e⟩
    Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1' k_fs ss0' rs0
      { esL with g := s₁L.record 2 P stL' recL false, h := hL' }
      { esM with g := s₁M.record 2 P stM' recM false, h := hM' } sM' sL' := by
  intro stL' stM' recL recM
  have hs₁_ep : s₁M.epoch = s₁L.epoch := congrArg GameState.epoch hs₁_er.symm
  have hs₁_idx : s₁M.idx = s₁L.idx := congrArg GameState.idx hs₁_er.symm
  have hrec_eq : recM = recL := by dsimp [recL, recM]; rw [hs₁_ep, hs₁_idx]
  have hbk_getD : (hM'.book 0).getD {} = bk' := by simp [hbk_eq]
  have htcur_sender_t : ((s₁L.record 2 P stL' recL false).st (Party.senderOf t)).tcur = t := by
    simp [GameState.record, hs₁_stL, ← hP_sends, stL']
  have htcur_mono : ∀ Q, (esL.g.st Q).tcur ≤ ((s₁L.record 2 P stL' recL false).st Q).tcur := by
    intro Q; simp only [GameState.record, hs₁_stL]
    by_cases hQ : Q = P
    · subst Q; simp only [Function.update_self, stL', hs.htcurL, ← hep_eq_t]; exact hep_ge
    · simp only [Function.update_of_ne hQ]; exact le_rfl
  exact
    { habL := hs.habL,
      habM := hs.habM,
      hwinL := by simp [GameState.record, hs₁_winL, hs.hwinL],
      hwinM := by simp [GameState.record, hs₁_winM, hs.hwinM],
      hlfM := hlf_eq,
      herase := hrec_eq ▸ eraseSt_record hs₁_er 2 P stL' stM' recL false,
      hidL := fun Q => by
        simp only [GameState.record, hs₁_stL]
        by_cases hQ : Q = P
        · subst Q; simp [stL', hs.hidL P]
        · simp [Function.update_of_ne hQ, hs.hidL Q],
      hidM := fun Q => by
        simp only [GameState.record, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stM', hs.hidM P]
        · simp [Function.update_of_ne hQ, hs.hidM Q],
      htcurL := fun Q => by
        simp only [GameState.record, hs₁_stL]
        by_cases hQ : Q = P
        · subst Q; simp [stL', hep_eq_t]
        · simp [Function.update_of_ne hQ, hs.htcurL Q, (hs₁_other Q hQ).1],
      htcurM := fun Q => by
        simp only [GameState.record, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stM', hep_eq_t]
        · simp [Function.update_of_ne hQ, hs.htcurM Q, (hs₁_other Q hQ).1],
      hγ := fun Q => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hγ Q],
      hroot := fun Q => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp [stL', stM']
        · simp [Function.update_of_ne hQ, hs.hroot Q],
      htrans_wf := fun r hr => by
        simp only [GameState.record, hs₁_tr, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨hep_eq_t.symm, by dsimp [recL]; rw [hep_eq_t]; exact hP_sends⟩
        · exact hs.htrans_wf r hr,
      hinv := by dsimp only; rw [hbk_getD]; exact hinv',
      hscorr2 := by dsimp only; rw [hbk_getD]; exact hscorr2',
      hbk_trans := by
        dsimp only; rw [hbk_getD, hbk_tr']
        simp only [GameState.record, recL, hs₁_tr, hep_eq_t, BEq.rfl, ↓reduceIte,
          List.filter_cons, List.map_cons]
        exact congrArg ((s₁L.idx P + 1, (t, T'), e) :: ·) hs.hbk_trans,
      hbk_count := fun _ => by
        dsimp only; rw [hbk_getD, hbk_cnt']
        simp [GameState.record, recL, ← hP_sends],
      hsess_nil := fun hnot => absurd (le_of_eq htcur_sender_t.symm) hnot,
      hsess_sent := fun _ => ⟨ht_le_qep, hh_cache_t⟩,
      hcache_ne := hh_cache_ne,
      hvS_rel := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_self]
          exact Or.inr (Or.inr ⟨by rw [← hP_sends]; simp [stL'],
            hP_sends, Or.inl rfl, rfl, rfl, rfl⟩)
        · simp only [GameState.record, hs₁_stL, hs₁_stM, Function.update_of_ne hQ]
          rcases hs.hvS_rel Q with ⟨h1, h2, h3, h4⟩ | ⟨ss, h1, h2, h3, h4⟩ |
              ⟨_, h2, _, _, _, _⟩
          · exact Or.inl ⟨h1, h2, h3, h4⟩
          · exact Or.inr (Or.inl ⟨ss, h1, h2, h3, h4⟩)
          · exact absurd (h2.trans hP_sends.symm) hQ,
      hvR_ne := fun Q ep' hne => by
        simp only [GameState.record, hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, stL', stM']; exact hs.hvR_ne P ep' hne
        · simp only [Function.update_of_ne hQ]; exact hs.hvR_ne Q ep' hne,
      hvR_star := by
        rcases hs.hvR_star with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
        · left
          refine ⟨?_, ?_, h3⟩
          · simp only [GameState.record, hs₁_stL]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stL']; rw [← hPs]; exact h1
            · rw [Function.update_of_ne hPs]; exact h1
          · simp only [GameState.record, hs₁_stM]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stM']; rw [← hPs]; exact h2
            · rw [Function.update_of_ne hPs]; exact h2
        · right
          refine ⟨by rw [htcur_sender_t], le_trans h2 (htcur_mono _), ?_, ?_⟩
          · simp only [GameState.record, hs₁_stL]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stL']; rw [← hPs]; exact h3
            · rw [Function.update_of_ne hPs]; exact h3
          · simp only [GameState.record, hs₁_stM]
            by_cases hPs : Party.receiverOf t = P
            · rw [hPs, Function.update_self]; dsimp only [stM']; rw [← hPs]; exact h4
            · rw [Function.update_of_ne hPs]; exact h4 }

private theorem mode_tH_eq (l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1) :
    (⟨false, some (l - 1), t⟩ : Mode).tH = t := by
  simp [Mode.tH, _root_.CryptoGames.SM.Construction.healEpoch]; omega

private theorem dir2_vRecv_step1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {qep l t : ℕ} {phase1 : Bool} {k_fs : BitVec 256} {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party) (c : Header Pt × Ct32)
    (hsends_f : P.sendsIn c.1.1 = false)
    (ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    (∃ s₁L? s₁M?,
      (vRecvStep1 hkL esL.g P (esL.g.st P) c).run esL.h = pure (s₁L?, esL.h) ∧
      (∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (s₁M?, esM.h)) ∧
      ((s₁L? = some none ∧ s₁M? = some none) ∨
       (∃ s₁L s₁M, s₁L? = some (some s₁L) ∧ s₁M? = some (some s₁M) ∧
         s₁L.vR c.1.1 = none ∧ s₁M.vR c.1.1 = none))) ∨
    (c.1.1 ≠ t ∧ ∃ γ' σ' rs,
      (vRecvStep1 hkL esL.g P (esL.g.st P) c).run esL.h =
        pure (some (some
          { esL.g.st P with
            tcur := max (esL.g.st P).tcur c.1.1, γ := γ', root := σ',
            vR := Function.update (esL.g.st P).vR c.1.1 (some (rs, none)) }), esL.h) ∧
      (∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h =
        pure (some (some
          { esM.g.st P with
            tcur := max (esM.g.st P).tcur c.1.1, γ := γ', root := σ',
            vR := Function.update (esM.g.st P).vR c.1.1 (some (Sum.inl rs)) }), esM.h))) ∨
    (c.1.1 = t ∧ P = Party.receiverOf t ∧ t ≤ (esL.g.st (Party.senderOf t)).tcur ∧ t ≤ qep ∧
      ∃ γ' σ',
        (vRecvStep1 hkL esL.g P (esL.g.st P) c).run esL.h =
          pure (some (some
            { esL.g.st P with
              tcur := max (esL.g.st P).tcur t, γ := γ', root := σ',
              vR := Function.update (esL.g.st P).vR t (some (rs0, some 0)) }), esL.h) ∧
        (∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h =
          pure (some (some
            { esM.g.st P with
              tcur := max (esM.g.st P).tcur t, γ := γ', root := σ',
              vR := Function.update (esM.g.st P).vR t (some (Sum.inr 0)) }), esM.h))) := by
  intro hkL hkM
  rcases c with ⟨⟨ep0, Topt⟩, ct0⟩
  dsimp only at hsends_f ht_le ⊢
  have htcur_eq : (esM.g.st P).tcur = (esL.g.st P).tcur := (hs.htcurM P).trans (hs.htcurL P).symm
  have hP_recv : P = Party.receiverOf ep0 := party_eq_receiverOf_of_sendsIn_false P ep0 hsends_f
  by_cases heq : ep0 = (esL.g.st P).tcur + 1
  · have heqM : ep0 = (esM.g.st P).tcur + 1 := by rw [htcur_eq]; exact heq
    have hifL : ∀ {α} (x y : α), (if ep0 = (esL.g.st P).tcur + 1 then x else y) = x :=
      fun _ _ => by simp [heq]
    have hifM : ∀ {α} (x y : α), (if ep0 = (esM.g.st P).tcur + 1 then x else y) = x :=
      fun _ _ => by simp [heqM]
    have hmaxL : max (esL.g.st P).tcur ep0 = ep0 := Nat.max_eq_right (by omega)
    have hmaxM : max (esM.g.st P).tcur ep0 = ep0 := Nat.max_eq_right (by omega)
    rcases Topt with _ | Tn
    · left
      refine ⟨some none, some none, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
      · unfold vRecvStep1; dsimp only; rw [hifL]; rfl
      · intro la; unfold vRecvStep1; dsimp only; rw [hifM]; rfl
    · by_cases hct : ep0 = t
      · subst hct
        by_cases hsnd_le : ep0 ≤ (esL.g.st (Party.senderOf ep0)).tcur
        · obtain ⟨hqep, Tc, σc, km, hcL, hcM⟩ := hs.hsess_sent hsnd_le
          by_cases hTc : Tc = Tn
          · subst hTc
            have hnot_rcv : ¬ ep0 ≤ (esL.g.st (Party.receiverOf ep0)).tcur := by
              rw [← hP_recv]; omega
            have hrs0 : rs0 = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k_fs := by
              rcases hs.hvR_star with ⟨_, _, h3⟩ | ⟨_, h2, _, _⟩
              · exact h3
              · exact absurd h2 hnot_rcv
            right; right
            refine ⟨rfl, hP_recv, hsnd_le, hqep,
              ((dhScheme Dh).receive (esL.g.st P).γ Tc).1, σc, ?_, ?_⟩
            · unfold vRecvStep1; dsimp only
              rw [hifL, hmaxL]
              dsimp only [hkL, hooksLocalFixed]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL, ↓reduceIte,
                StateT.run_pure, ← hrs0]
            · intro la
              unfold vRecvStep1; dsimp only
              rw [hifM, hmaxM]
              dsimp only [hkM, hooksFSMulti]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM, ↓reduceIte,
                StateT.run_pure, hs.hγ P]
          · have hifTc : ∀ {α} (x y : α), (if Tc = Tn then x else y) = y :=
              fun _ _ => by simp [hTc]
            left
            refine ⟨some none, some none, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
            · unfold vRecvStep1; dsimp only; rw [hifL]
              dsimp only [hkL, hooksLocalFixed]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL]; rw [hifTc]; rfl
            · intro la; unfold vRecvStep1; dsimp only; rw [hifM]
              dsimp only [hkM, hooksFSMulti]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM]; rw [hifTc]; rfl
        · obtain ⟨_, _, hcL, hcM, _, _, _, _⟩ := hs.hsess_nil hsnd_le
          left
          refine ⟨some none, some none, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
          · unfold vRecvStep1; dsimp only; rw [hifL]
            dsimp only [hkL, hooksLocalFixed]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL]; rfl
          · intro la; unfold vRecvStep1; dsimp only; rw [hifM]
            dsimp only [hkM, hooksFSMulti]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM]; rfl
      · rcases hs.hcache_ne ep0 hct with ⟨hcL, hcM⟩ | ⟨Tc, σc, k, hcL, hcM⟩
        · left
          refine ⟨some none, some none, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
          · unfold vRecvStep1; dsimp only; rw [hifL]
            dsimp only [hkL, hooksLocalFixed]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL]; rfl
          · intro la; unfold vRecvStep1; dsimp only; rw [hifM]
            dsimp only [hkM, hooksFSMulti]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM]; rfl
        · by_cases hTc : Tc = Tn
          · subst hTc
            right; left
            refine ⟨hct, ((dhScheme Dh).receive (esL.g.st P).γ Tc).1, σc,
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k, ?_, ?_⟩
            · unfold vRecvStep1; dsimp only
              rw [hifL, hmaxL]
              dsimp only [hkL, hooksLocalFixed]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL, ↓reduceIte, StateT.run_pure]
            · intro la; unfold vRecvStep1; dsimp only
              rw [hifM, hmaxM]
              dsimp only [hkM, hooksFSMulti]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM, ↓reduceIte,
                StateT.run_pure, hs.hγ P]
          · have hifTc : ∀ {α} (x y : α), (if Tc = Tn then x else y) = y :=
              fun _ _ => by simp [hTc]
            left
            refine ⟨some none, some none, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
            · unfold vRecvStep1; dsimp only; rw [hifL]
              dsimp only [hkL, hooksLocalFixed]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL]; rw [hifTc]; rfl
            · intro la; unfold vRecvStep1; dsimp only; rw [hifM]
              dsimp only [hkM, hooksFSMulti]
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hcM]; rw [hifTc]; rfl
  · have heqM : ep0 ≠ (esM.g.st P).tcur + 1 := by rw [htcur_eq]; exact heq
    have hifL : ∀ {α} (x y : α), (if ep0 = (esL.g.st P).tcur + 1 then x else y) = y :=
      fun _ _ => by simp [heq]
    have hifM : ∀ {α} (x y : α), (if ep0 = (esM.g.st P).tcur + 1 then x else y) = y :=
      fun _ _ => by simp [heqM]
    have hmaxL : max (esL.g.st P).tcur ep0 = (esL.g.st P).tcur := Nat.max_eq_left (by omega)
    have hmaxM : max (esM.g.st P).tcur ep0 = (esM.g.st P).tcur := Nat.max_eq_left (by omega)
    by_cases hct : ep0 = t
    · subst hct
      rcases hs.hvR_star with ⟨hvL, hvM, _⟩ | ⟨hsnd_le, _, hvL, hvM⟩
      · left
        refine ⟨some (some (esL.g.st P)), some (some (esM.g.st P)), ?_, ?_,
          Or.inr ⟨esL.g.st P, esM.g.st P, rfl, rfl, hP_recv ▸ hvL, hP_recv ▸ hvM⟩⟩
        · unfold vRecvStep1; dsimp only; rw [hifL]; rfl
        · intro la; unfold vRecvStep1; dsimp only; rw [hifM]; rfl
      · obtain ⟨hqep, _⟩ := hs.hsess_sent hsnd_le
        right; right
        have hupdL : Function.update (esL.g.st P).vR ep0 (some (rs0, some 0)) = (esL.g.st P).vR :=
          Function.update_eq_self_iff.mpr (hP_recv ▸ hvL).symm
        have hupdM : Function.update (esM.g.st P).vR ep0 (some (Sum.inr 0)) = (esM.g.st P).vR :=
          Function.update_eq_self_iff.mpr (hP_recv ▸ hvM).symm
        refine ⟨rfl, hP_recv, hsnd_le, hqep, (esL.g.st P).γ, (esL.g.st P).root, ?_, ?_⟩
        · unfold vRecvStep1; dsimp only
          rw [hifL, hmaxL, hupdL]
          cases esL.g.st P; rfl
        · intro la; unfold vRecvStep1; dsimp only
          rw [hifM, hmaxM, hupdM, ← hs.hγ P, ← hs.hroot P]
          cases esM.g.st P; rfl
    · have hne_pair : (P, ep0) ≠ (Party.receiverOf t, t) := fun h => hct (congrArg Prod.snd h)
      rcases hs.hvR_ne P ep0 hne_pair with ⟨hvL, hvM⟩ | ⟨rs, hvL, hvM⟩
      · left
        refine ⟨some (some (esL.g.st P)), some (some (esM.g.st P)), ?_, ?_,
          Or.inr ⟨esL.g.st P, esM.g.st P, rfl, rfl, hvL, hvM⟩⟩
        · unfold vRecvStep1; dsimp only; rw [hifL]; rfl
        · intro la; unfold vRecvStep1; dsimp only; rw [hifM]; rfl
      · right; left
        have hupdL : Function.update (esL.g.st P).vR ep0 (some (rs, none)) = (esL.g.st P).vR :=
          Function.update_eq_self_iff.mpr hvL.symm
        have hupdM : Function.update (esM.g.st P).vR ep0 (some (Sum.inl rs)) = (esM.g.st P).vR :=
          Function.update_eq_self_iff.mpr hvM.symm
        refine ⟨hct, (esL.g.st P).γ, (esL.g.st P).root, rs, ?_, ?_⟩
        · unfold vRecvStep1; dsimp only
          rw [hifL, hmaxL, hupdL]
          cases esL.g.st P; rfl
        · intro la; unfold vRecvStep1; dsimp only
          rw [hifM, hmaxM, hupdM, ← hs.hγ P, ← hs.hroot P]
          cases esM.g.st P; rfl

private def LeRel : Bool → ProbComp Bool → ProbComp Bool → ProbComp Bool → Prop
  | true, cLoc, cM, cL => LeAdd0 cLoc cM cL
  | false, cLoc, cM, _ => LeOne cLoc cM

private theorem leRel_of_lhs_zero {phase1 : Bool} {cLoc cM cL : ProbComp Bool}
    (h0 : 𝒟[cLoc] {true} = 0) : LeRel phase1 cLoc cM cL := by
  cases phase1
  · exact leOne_of_lhs_zero h0
  · exact leAdd0_of_lhs_zero h0

private theorem leRel_to_phase2 {phase1 : Bool} {cLoc cM cL : ProbComp Bool}
    (h : LeOne cLoc cM) : LeRel phase1 cLoc cM cL := by
  cases phase1
  · exact h
  · exact leAdd0_of_le_main h

private theorem leRel_bind_unif {α : Type} {phase1 : Bool} (m0 : ProbComp α)
    (fLoc fM fL : α → ProbComp Bool)
    (h : ∀ x ∈ support m0, LeRel phase1 (fLoc x) (fM x) (fL x)) :
    LeRel phase1 (m0 >>= fLoc) (m0 >>= fM) (m0 >>= fL) := by
  cases phase1
  · exact leOne_bind m0 h
  · exact leAdd0_bind m0 h

private theorem estate_eta_false {V M C H : Type} (es : EState V M C H) (h : es.abort = false) :
    ({ g := es.g, h := es.h, abort := false } : EState V M C H) = es := by
  cases es; dsimp at h ⊢; subst h; rfl

private theorem activeSessInv_any_to_phase2 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ssLoc : SS256} {rsLoc : RS256}
    {bk : FSMultiBook Pt Ct32} {sM sL sL' : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL) :
    ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL' := by
  cases phase1
  · obtain ⟨stR, h⟩ := hinv
    exact ⟨stR, { h with syncRML := fun hp => Bool.noConfusion hp }⟩
  · exact activeSessInv_to_phase2 C ℓ encT idOf hinv

private theorem sendsIn_false_of_other_senderOf {P : Party} {ep : ℕ}
    (h : P.other = Party.senderOf ep) : P.sendsIn ep = false := by
  cases P <;> simp [Party.other, Party.senderOf, Party.sendsIn] at h ⊢ <;> omega

private theorem dir2_fsSend0_cases
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hℓ : ℓ < 10 ^ 6) (qep l t : ℕ) {phase1 : Bool} (k_fs : BitVec 256)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    {s₁L : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) (MsgPt ℓ) Ct32}
    {s₁M : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) (MsgPt ℓ) Ct32}
    (P : Party) (hs₁_er : eraseSt s₁L = eraseSt s₁M)
    (hs₁_stL : s₁L.st = esL.g.st) (hs₁_stM : s₁M.st = esM.g.st)
    (hs₁_winL : s₁L.win = esL.g.win) (hs₁_winM : s₁M.win = esM.g.win)
    (hs₁_tr : s₁L.trans = esL.g.trans)
    (hs₁_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q ∧ s₁L.idx Q = esL.g.idx Q)
    (hep_ge : esL.g.epoch P ≤ s₁L.epoch P)
    (hP_sends : P = Party.senderOf t)
    (hep_eq_t : s₁L.epoch P = t)
    (ht_le_qep : t ≤ qep)
    (γ' : DDHSt Pt) (T' : Option Pt) (σ' : BitVec 256)
    (m : MsgPt ℓ) (hm : atomicShortPubB m.1 = true)
    (hL₁ : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM₁ : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32)
    (hh_book1 : hM₁.book = esM.h.book ∧ hM₁.lfWin = false)
    (hh_cache_t : ∃ Tc σc km, hL₁.cache t = some (Tc, σc, k_fs, some 0) ∧
      hM₁.cache t = some (Tc, σc, km, some 0))
    (hh_cache_ne : ∀ ep', ep' ≠ t →
      (hL₁.cache ep' = none ∧ hM₁.cache ep' = none) ∨
      ∃ Tc σc k, hL₁.cache ep' = some (Tc, σc, k, none) ∧ hM₁.cache ep' = some (Tc, σc, k, none))
    (hcnt_eq : ((esM.h.book 0).getD {}).fsCount = s₁L.idx P) :
    let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ss0 (t, T') m
    let stL' : PartyState (DDHSt Pt) Pt (BitVec 256) (SS256 × Option ℕ) (RS256 × Option ℕ) :=
      { esL.g.st P with tcur := t, γ := γ', curCkaMsg := T', root := σ', vS := some (o.1, some 0) }
    let stM' : VP (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) :=
      { esM.g.st P with tcur := t, γ := γ', curCkaMsg := T', root := σ', vS := some (Sum.inr 0) }
    let recL : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (t, T'), o.2⟩
    let recM : Record (MsgPt ℓ) (Header Pt × Ct32) :=
      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (t, T'), o.2⟩
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    (∃ hM' sM' sL',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs o.1 rs0
        { esL with g := s₁L.record 2 P stL' recL false, h := hL₁ }
        { esM with g := s₁M.record 2 P stM' recM false, h := hM' } sM' sL' ∧
      (simulateQ (implM false)
        (((hkM false).fsSend s₁M P t (.inr 0) (t, T') m none).run hM₁)).run (false, sM) =
        pure ((some (.inr 0, o.2), hM'), (false, sM')) ∧
      (phase1 = true →
        (simulateQ (implM true)
          (((hkM true).fsSend s₁M P t (.inr 0) (t, T') m none).run hM₁)).run (false, sL) =
          pure ((some (.inr 0, o.2), hM'), (false, sL')))) ∨
    (∃ hM' sM',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs o.1 rs0
        { esL with g := s₁L.record 2 P stL' recL false, h := hL₁ }
        { esM with g := s₁M.record 2 P stM' recM false, h := hM' } sM' sL ∧
      (simulateQ (implM false)
        (((hkM false).fsSend s₁M P t (.inr 0) (t, T') m none).run hM₁)).run (false, sM) =
        pure ((some (.inr 0, o.2), hM'), (false, sM'))) := by
  intro o stL' stM' recL recM hkM implM
  have hbk1 : (hM₁.book 0).getD {} = (esM.h.book 0).getD {} := by rw [hh_book1.1]
  have hshort : m.1.shortB = true := atomicShortPubB_imp_shortB hm
  by_cases hcs : (!(s₁M.safeCh (2 + 0) P) && !((hM₁.book 0).getD {}).sCorr) = true
  · right
    have hinv2 : ActiveSessInv C ℓ encT idOf false k_fs ss0 rs0 ((esM.h.book 0).getD {}) sM sL :=
      match phase1, hs.hinv with
      | false, h => h
      | true, h => activeSessInv_to_phase2 C ℓ encT idOf h
    obtain ⟨sM_c, hcorr_step, hinv_c⟩ := activeSessInv_corruptSender C ℓ encT idOf hinv2
    have hrun_corr := run_liftFSMulti0_corruptSender (Pt := Pt) C encT idOf hM₁ sM hcorr_step
    let bk_c : FSMultiBook Pt Ct32 := { (esM.h.book 0).getD {} with sCorr := true }
    let hM_c : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
      { hM₁ with book := (Function.update hM₁.book 0 (some bk_c)) }
    obtain ⟨sM', _, hM_tr, _, hinv_tmp⟩ :=
      activeSessInv_transmit C signalRoundTripShort_proto ℓ (hℓ_rust_bound hℓ) encT idOf
        hinv_c (t, T') m hshort
    have hrun_tr := run_liftFSMulti0_transmit (Pt := Pt) C encT idOf false (t, T') m hM_c sM_c hM_tr
    let bk' : FSMultiBook Pt Ct32 :=
      { bk_c with fsCount := bk_c.fsCount + 1, fsTrans := (bk_c.fsCount + 1, (t, T'), o.2) :: bk_c.fsTrans }
    have hinv' : ActiveSessInv C ℓ encT idOf false k_fs o.1 rs0 bk' sM' sL :=
      let ⟨stR, h⟩ := hinv_tmp
      ⟨stR, { h with syncRML := fun hp => Bool.noConfusion hp }⟩
    let hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
      { hM_c with book := (Function.update hM_c.book 0 (some bk')) }
    refine ⟨hM', sM', ?_, ?_⟩
    · exact dir2Sync_record_at_t hs P hs₁_er hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr
        hs₁_other hep_ge hP_sends hep_eq_t ht_le_qep γ' T' σ' m o.2 hL₁ hM' bk'
        (by simp [hM']) hh_book1.2 hh_cache_t hh_cache_ne hinv' (fun _ => rfl)
        (by dsimp [bk', bk_c]; rw [hcnt_eq])
        (by dsimp [bk', bk_c]; rw [hcnt_eq])
    · dsimp only [hkM, hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hcs, ↓reduceIte,
        Bool.false_eq_true, simulateQ_bind]
      rw [hrun_corr]
      simp only [pure_bind, StateT.run_bind, StateT.run_modify,
        Bool.false_eq_true, ↓reduceIte, Bool.not_true, simulateQ_bind, hbk1]
      change ((simulateQ (implM false) ((liftFSMulti 0 _).run hM_c)).run (false, sM_c) >>= _) = _
      rw [hrun_tr]
      simp [hM', hM_c, bk', bk_c, o]
  · left
    have hcs_f : (!(s₁M.safeCh (2 + 0) P) && !((hM₁.book 0).getD {}).sCorr) = false :=
      Bool.eq_false_iff.mpr hcs
    obtain ⟨sM', sL', hM_tr, hL_tr, hinv'⟩ :=
      activeSessInv_transmit C signalRoundTripShort_proto ℓ (hℓ_rust_bound hℓ) encT idOf
        hs.hinv (t, T') m hshort
    have hrun_trM := run_liftFSMulti0_transmit (Pt := Pt) C encT idOf false (t, T') m hM₁ sM hM_tr
    let bk' : FSMultiBook Pt Ct32 :=
      { (esM.h.book 0).getD {} with
        fsCount := ((esM.h.book 0).getD {}).fsCount + 1,
        fsTrans := (((esM.h.book 0).getD {}).fsCount + 1, (t, T'), o.2) :: ((esM.h.book 0).getD {}).fsTrans }
    let hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
      { hM₁ with book := (Function.update hM₁.book 0 (some bk')) }
    refine ⟨hM', sM', sL', ?_, ?_, ?_⟩
    · exact dir2Sync_record_at_t hs P hs₁_er hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr
        hs₁_other hep_ge hP_sends hep_eq_t ht_le_qep γ' T' σ' m o.2 hL₁ hM' bk'
        (by simp [hM']) hh_book1.2 hh_cache_t hh_cache_ne hinv'
        (fun hp => by dsimp [bk']; exact hs.hscorr2 hp)
        (by dsimp [bk']; rw [hcnt_eq])
        (by dsimp [bk']; rw [hcnt_eq])
    · dsimp only [hkM, hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hcs_f, Bool.false_eq_true,
        ↓reduceIte, Bool.not_true, simulateQ_bind]
      rw [hrun_trM]
      simp [hM', bk', hbk1, o]
    · intro hp1
      have hrun_trL := run_liftFSMulti0_transmit (Pt := Pt) C encT idOf true (t, T') m hM₁ sL (hL_tr hp1)
      dsimp only [hkM, hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hcs_f, Bool.false_eq_true,
        ↓reduceIte, Bool.not_true, simulateQ_bind]
      rw [hrun_trL]
      simp [hM', bk', hbk1, o]

private theorem hooksLocalFixed_fsRecv_eq
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR Sig I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode) (j : ℕ) (k_fs : K) (ctx : _) (P : Party) (ep : ℕ)
    (rsvR : RS × Option ℕ) (h : Header T) (e : E) (rec : _) :
    (hooksLocalFixed cka prng fs mo j k_fs).fsRecv ctx P ep rsvR h e rec = (do
      match fs.receive rsvR.1 h e with
      | none => return some none
      | some (rs', i, m) =>
        modify fun s => { s with lastIdx := rsvR.2 }
        return some (some ((rs', rsvR.2), i, m))) := rfl

private theorem hooksFSMulti_fsRecv_inl_eq
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (ctx : _) (P : Party) (t0 : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : _) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv ctx P t0 (.inl rs) h e rec =
      pure (some ((fs.receive rs h e).map fun o => (.inl o.1, o.2.1, o.2.2))) := rfl

private theorem ct32_beq_iff : ∀ (a b : Ct32), (a == b) = true ↔ a = b
  | ⟨n1, ⟨l1, c1⟩, b1⟩, ⟨n2, ⟨l2, c2⟩, b2⟩ => by
    change (n1 == n2 && ((List.beq l1 l2 && c1 == c2) && b1 == b2)) = true ↔ _
    simp [Bool.and_eq_true, list_bv8_beq_iff]

private theorem hooksFSMulti_fsRecv_inr_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (mo : Mode) (la : Bool)
    (ctx : Ctx (DDHSt Pt) Pt (BitVec 256) (SS256 ⊕ ℕ) (RS256 ⊕ ℕ) (MsgPt ℓ) Ct32)
    (P : Party) (t0 sIdx : ℕ) (h : Header Pt) (e : Ct32)
    (rec : Option (Record (MsgPt ℓ) (Header Pt × Ct32))) :
    (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 mo false la).fsRecv
      ctx P t0 (.inr sIdx) h e rec = (do
      let s ← get
      let bk := (s.book sIdx).getD {}
      let matched := bk.fsTrans.find? (fun x => x.2 == (h, e))
      let ok ← if matched.isNone && !(healedBy ctx.tL 2 t0) && !bk.sCorr then
          if la then pure false
          else do
            match ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
                (SenderState := SS256) (ReceiverState := RS256)
                (AssocData := Header Pt) (Message := MsgPt ℓ) (Ciphertext := Ct32)) with
            | none => pure false
            | some _ =>
              modify fun s =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
              pure true
        else pure true
      if !ok then return none
      let res ← if matched.isSome then
          liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.deliverQuery
            (SenderState := SS256) (ReceiverState := RS256) (Message := MsgPt ℓ) h e)
        else
          liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.injectQuery
            (SenderState := SS256) (ReceiverState := RS256) (Message := MsgPt ℓ) h e)
      match res with
      | none => return none
      | some .rejected => return some none
      | some (.accepted i mo') =>
        let s1 ← get
        let bk1 := (s1.book sIdx).getD {}
        if la && matched.isNone && (!bk1.sCorr) && decide (bk1.fsCount < i) then
          modify fun s => { s with lfWin := true }
          return none
        else
          let drop := (matched.map (·.1)).getD i
          modify fun s =>
            let b := (s.book sIdx).getD {}
            let b' : FSMultiBook Pt Ct32 := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
            { s with book := Function.update s.book sIdx (some b') }
          match mo', rec with
          | some m, _ => return some (some (.inr sIdx, i, m))
          | none, some r => return some (some (.inr sIdx, i, r.msg))
          | none, none => return none) := by
  have hfind : ∀ (tr : List (ℕ × Header Pt × Ct32)),
      List.find? (fun x => @BEq.beq (Header Pt × Ct32)
        (@instBEqProd (Header Pt) Ct32 inferInstance (@instBEqOfDecidableEq Ct32 inferInstance))
        x.2 (h, e)) tr =
      List.find? (fun x => x.2 == (h, e)) tr := by
    intro tr; congr 1; funext x
    change (x.2.1 == h && decide (x.2.2 = e)) = (x.2.1 == h && x.2.2 == e)
    congr 1
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq, ct32_beq_iff])
  unfold hooksFSMulti; dsimp only
  simp only [Nat.add_zero, hfind]
  congr 1; funext s
  by_cases hc1 : ((List.find? (fun x => x.2 == (h, e)) ((s.book sIdx).getD {}).fsTrans).isNone &&
      !(healedBy ctx.tL 2 t0) && !((s.book sIdx).getD {}).sCorr) = true
  · simp only [hc1, ↓reduceIte]
    cases la
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1; funext u
      cases u
      · rfl
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        congr 1; funext _
        by_cases hm : (List.find? (fun x => x.2 == (h, e)) ((s.book sIdx).getD {}).fsTrans).isSome = true
        · simp only [hm, ↓reduceIte]
          congr 1; funext res
          rcases res with _ | (_ | ⟨i, mo'⟩)
          · rfl
          · rfl
          · cases mo' <;> cases rec <;> rfl
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext res
          rcases res with _ | (_ | ⟨i, mo'⟩)
          · rfl
          · rfl
          · cases mo' <;> cases rec <;> rfl
    · rfl
  · simp only [hc1, ↓reduceIte, pure_bind, Bool.not_true, Bool.false_eq_true]
    by_cases hm : (List.find? (fun x => x.2 == (h, e)) ((s.book sIdx).getD {}).fsTrans).isSome = true
    · simp only [hm, ↓reduceIte]
      congr 1; funext res
      rcases res with _ | (_ | ⟨i, mo'⟩)
      · rfl
      · rfl
      · cases mo' <;> cases rec <;> rfl
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext res
      rcases res with _ | (_ | ⟨i, mo'⟩)
      · rfl
      · rfl
      · cases mo' <;> cases rec <;> rfl

private theorem dir2_deliverE
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hℓ : ℓ < 10 ^ 6) (qep l t : ℕ) {phase1 : Bool} (k_fs : BitVec 256)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (P : Party) (c : Header Pt × Ct32) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    ∃ u esL' esM' sM' sL' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0' esL' esM' sM' sL' ∧
      simulateQ lImpl
        ((deliverE hkL maxForwardJumps (moAuth ⟨false, some (l - 1), t⟩).cfg (P, c)).run esL) =
        pure (u, esL') ∧
      (simulateQ (implM false)
        ((deliverE (hkM false) maxForwardJumps (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c)).run esM)).run
        (false, sM) = pure ((u, esM'), (false, sM')) ∧
      (phase1 = true →
        (simulateQ (implM true)
          ((deliverE (hkM true) maxForwardJumps (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c)).run esM)).run
          (false, sL) = pure ((u, esM'), (false, sL'))) := by
  intro hkL hkM implM
  have hin_eq : esM.g.inTransit P.other c = esL.g.inTransit P.other c :=
    eraseSt_inTransit hs.herase.symm P.other c
  have hdelWinL : ((moAuth ⟨false, some (l - 1), t⟩).cfg (M := MsgPt ℓ)).deliverWin = false := rfl
  have hdelWinM : ((⟨true, some (l - 1), t⟩ : Mode).cfg (M := MsgPt ℓ)).deliverWin = false := rfl
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habL, hs.habM, hs.hwinL, hs.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hin_eq]
  cases hin : esL.g.inTransit P.other c with
  | none =>
    exact ⟨none, esL, esM, sM, sL, rs0, hs, by simp, by simp, fun _ => by simp⟩
  | some r =>
    obtain ⟨hr_mem, hr_snd, hr_ct⟩ := inTransit_mem_trans hin
    have hr_wf := hs.htrans_wf r hr_mem
    have hPother_s : P.other = Party.senderOf c.1.1 := by
      rw [← hr_snd, hr_wf.2, ← hr_wf.1, hr_ct]
    have hsends_f : P.sendsIn c.1.1 = false := sendsIn_false_of_other_senderOf hPother_s
    have hP_recv : P = Party.receiverOf c.1.1 := party_eq_receiverOf_of_sendsIn_false P c.1.1 hsends_f
    have htcur_eq : (esM.g.st P).tcur = (esL.g.st P).tcur := (hs.htcurM P).trans (hs.htcurL P).symm
    have hcondL_eq :
        ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidL P, hsends_f, Bool.false_or]
    have hcondM_eq :
        ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidM P, htcur_eq, hsends_f, Bool.false_or]
    by_cases hgt : (esL.g.st P).tcur + 1 < c.1.1
    · have hcL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondL_eq, decide_eq_true_eq]; exact hgt
      have hcM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondM_eq, decide_eq_true_eq]; exact hgt
      refine ⟨some .rejected, esL, esM, sM, sL, rs0, hs, ?_, ?_, fun _ => ?_⟩
      · simp [vRecv, hcL, hdelWinL]
      · simp [vRecv, hcM, hdelWinM]
      · simp [vRecv, hcM, hdelWinM]
    · have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := Nat.le_of_not_lt hgt
      have hcL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondL_eq, decide_eq_false_iff_not]; exact hgt
      have hcM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondM_eq, decide_eq_false_iff_not]; exact hgt
      dsimp only [hkL, hkM]
      simp only [vRecv_eq_bind, hcL, hcM, Bool.false_eq_true, ↓reduceIte, stateT_run_liftH,
        StateT.run_bind, pure_bind, simulateQ_bind, bind_assoc]
      rcases dir2_vRecv_step1 C Dh encPt encT idOf (l := l) hs P c hsends_f ht_le with
        ⟨s₁L?, s₁M?, hst1L, hst1M, hnone_cases⟩ |
        ⟨hct_ne, γ', σ', rs, hst1L, hst1M⟩ |
        ⟨hct_t, hPr, hsnd_le, _, γ', σ', hst1L, hst1M⟩
      · rcases hnone_cases with ⟨rfl, rfl⟩ | ⟨s₁L, s₁M, rfl, rfl, hvL, hvM⟩
        · refine ⟨some .rejected, esL, esM, sM, sL, rs0, hs, ?_, ?_, fun _ => ?_⟩
          · rw [hst1L]; simp [hdelWinL]
          · rw [hst1M false]; simp [hdelWinM]
          · rw [hst1M true]; simp [hdelWinM]
        · refine ⟨some .rejected, esL, esM, sM, sL, rs0, hs, ?_, ?_, fun _ => ?_⟩
          · rw [hst1L]; simp [hvL, hdelWinL]
          · rw [hst1M false]; simp [hvM, hdelWinM]
          · rw [hst1M true]; simp [hvM, hdelWinM]
      · have hne_pair : (P, c.1.1) ≠ (Party.receiverOf t, t) := fun h => hct_ne (congrArg Prod.snd h)
        cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs c.1 c.2 with
        | none =>
          refine ⟨some .rejected, esL, esM, sM, sL, rs0, hs, ?_, ?_, fun _ => ?_⟩
          · rw [hst1L]
            simp only [Function.update_self, hooksLocalFixed_fsRecv_eq, hrcv,
              StateT.run_pure, pure_bind, simulateQ_pure, hdelWinL,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          · rw [hst1M false]
            simp only [Function.update_self, hooksFSMulti_fsRecv_inl_eq, hrcv,
              Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure, hdelWinM,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          · rw [hst1M true]
            simp only [Function.update_self, hooksFSMulti_fsRecv_inl_eq, hrcv,
              Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure, hdelWinM,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        | some rim =>
          rcases rim with ⟨rs', i', m'⟩
          have hr_pos : (⟨P.other, c.1.1, r.pos.idx⟩ : Pos) = r.pos := by
            rcases hrp : r.pos with ⟨s0, e0, i0⟩
            have h1 := hr_snd; have h2 := hr_wf.1
            rw [hrp] at h1 h2; dsimp at h1 h2 ⊢; rw [hr_ct] at h2
            subst h1 h2; rfl
          have hs' := dir2Sync_accept_ne hs P c.1.1 r.pos.idx hsends_f ht_le hne_pair
            γ' σ' rs' { esL.h with lastIdx := none } rfl rfl
          dsimp only at hs'
          rw [hr_pos] at hs'
          refine ⟨some (.accepted c.1.1 i' (if esL.g.chall.contains r.pos then none else some m')),
            _, _, sM, sL, rs0, hs', ?_, ?_, fun _ => ?_⟩
          · rw [hst1L]
            simp only [Function.update_self, hrcv,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              commitE, hooksLocalFixed, stateT_run_liftH, Function.update_idem, accept_update_self,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              simulateQ_pure, hdelWinL]
          · rw [hst1M false]
            simp only [Function.update_self, hrcv,
              Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              commitE, hooksFSMulti, stateT_run_liftH, Function.update_idem, accept_update_self,
              Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              simulateQ_pure, hdelWinM, hs.hchall]
          · rw [hst1M true]
            simp only [Function.update_self, hrcv,
              Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              commitE, hooksFSMulti, stateT_run_liftH, Function.update_idem, accept_update_self,
              Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              simulateQ_pure, hdelWinM, hs.hchall]
      · have hin' : esL.g.inTransit (Party.senderOf t) c = some r := by
          rwa [← hct_t, ← hPother_s]
        obtain ⟨mEntry, hmatch, hm_idx, hr_ep, hr_s⟩ := dir2_matched_of_inTransit_some hs hin' hct_t
        have hr_pos_t : (⟨Party.senderOf t, t, mEntry.1⟩ : Pos) = r.pos := by
          rcases hrp : r.pos with ⟨s0, e0, i0⟩
          rw [hrp] at hm_idx hr_ep hr_s; dsimp at hm_idx hr_ep hr_s ⊢
          subst hm_idx hr_ep hr_s; rfl
        obtain ⟨p, hpub, hdel_cases⟩ :=
          activeSessInv_deliver C hD signalRoundTripShort_proto ℓ (hℓ_rust_bound hℓ)
            encT idOf hs.hinv c.1 c.2 hmatch
        cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 with
        | none =>
          rw [hrcv] at hdel_cases
          obtain ⟨sM', sL', hM_del, hL_del, hinv'⟩ := hdel_cases
          have hrunM := run_liftFSMulti0_deliver_some (Pt := Pt) C encT idOf false
            c.1 c.2 p hpub esM.h sM hM_del
          refine ⟨some .rejected, esL, esM, sM', sL', rs0, { hs with hinv := hinv' }, ?_, ?_, ?_⟩
          · rw [hst1L]
            simp only [hct_t, Function.update_self, hooksLocalFixed_fsRecv_eq, hrcv,
              StateT.run_pure, pure_bind, simulateQ_pure, hdelWinL,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          · rw [hst1M false]
            dsimp only [implM]
            simp only [hct_t, StateT.run_bind, StateT.run_get, pure_bind,
              Function.update_self, hooksFSMulti_fsRecv_inr_eq, hmatch, Option.isNone_some,
              Bool.false_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              Option.isSome_some, simulateQ_pure, simulateQ_bind, bind_assoc]
            rw [hrunM]
            simp only [Option.map_some, _root_.CryptoGames.FSAEAD.withPub, pure_bind,
              StateT.run_pure, simulateQ_pure, hdelWinM, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte]
          · intro hp1
            have hrunL := run_liftFSMulti0_deliver_some (Pt := Pt) C encT idOf true
              c.1 c.2 p hpub esM.h sL (hL_del hp1)
            rw [hst1M true]
            dsimp only [implM]
            simp only [hct_t, StateT.run_bind, StateT.run_get, pure_bind,
              Function.update_self, hooksFSMulti_fsRecv_inr_eq, hmatch, Option.isNone_some,
              Bool.false_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              Option.isSome_some, simulateQ_pure, simulateQ_bind, bind_assoc]
            rw [hrunL]
            simp only [Option.map_some, _root_.CryptoGames.FSAEAD.withPub, pure_bind,
              StateT.run_pure, simulateQ_pure, hdelWinM, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte]
        | some rim =>
          rcases rim with ⟨rs', idxOut, pmOut⟩
          rw [hrcv] at hdel_cases
          obtain ⟨hm_eq, sM', sL', hM_del, hL_del, hpm_fst, hinv'⟩ := hdel_cases
          have hwp : _root_.CryptoGames.FSAEAD.withPub p (.accepted idxOut (some pmOut.2)) =
              .accepted idxOut (some pmOut) := by
            rcases pmOut with ⟨p1, p2⟩; dsimp at hpm_fst; subst hpm_fst; rfl
          have hrunM := run_liftFSMulti0_deliver_some (Pt := Pt) C encT idOf false
            c.1 c.2 p hpub esM.h sM hM_del
          have ht_le_t : t ≤ (esL.g.st (Party.receiverOf t)).tcur + 1 := by
            rw [← hPr, ← hct_t]; exact ht_le
          have hs' := dir2Sync_accept_at_t hs hsnd_le ht_le_t γ' σ' mEntry.1 hinv'
          dsimp only at hs'
          rw [← hPr, hr_pos_t] at hs'
          refine ⟨some (.accepted t idxOut (if esL.g.chall.contains r.pos then none else some pmOut)),
            _, _, sM', sL', rs', hs', ?_, ?_, ?_⟩
          · rw [hst1L]
            simp only [hct_t, Function.update_self, hrcv,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              commitE, hooksLocalFixed, stateT_run_liftH, Function.update_idem, accept_update_self,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              simulateQ_pure, hdelWinL]
          · rw [hst1M false]
            dsimp only [implM]
            simp only [hct_t, StateT.run_bind, StateT.run_get, pure_bind,
              Function.update_self, hooksFSMulti_fsRecv_inr_eq, hmatch, Option.isNone_some,
              Bool.false_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              Option.isSome_some, simulateQ_pure, simulateQ_bind, bind_assoc]
            rw [hrunM]
            simp only [Option.map_some, hwp, StateT.run_bind, StateT.run_get, StateT.run_modify,
              StateT.run_pure, pure_bind, Bool.not_true, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte, Option.getD_some, hm_eq, commitE, hooksFSMulti,
              stateT_run_liftH, Function.update_idem, accept_update_self, simulateQ_pure,
              hdelWinM, hs.hchall]
          · intro hp1
            have hrunL := run_liftFSMulti0_deliver_some (Pt := Pt) C encT idOf true
              c.1 c.2 p hpub esM.h sL (hL_del hp1)
            rw [hst1M true]
            dsimp only [implM]
            simp only [hct_t, StateT.run_bind, StateT.run_get, pure_bind,
              Function.update_self, hooksFSMulti_fsRecv_inr_eq, hmatch, Option.isNone_some,
              Bool.false_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              Option.isSome_some, simulateQ_pure, simulateQ_bind, bind_assoc]
            rw [hrunL]
            simp only [Option.map_some, hwp, StateT.run_bind, StateT.run_get, StateT.run_modify,
              StateT.run_pure, pure_bind, Bool.not_true, Bool.and_false,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.getD_some, hm_eq,
              commitE, hooksFSMulti, stateT_run_liftH, Function.update_idem, accept_update_self,
              simulateQ_pure, hdelWinM, hs.hchall]

private theorem hooksLocalFixed_startSend_none
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR Sig I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode) (j : ℕ) (k_fs : K) (ctx : _) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) :
    (hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P ep γ σ none =
      (StateT.lift (sampleT CCoins) >>= fun c0 =>
        (hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P ep γ σ (some c0)) := by
  simp only [hooksLocalFixed, pure_bind]

private theorem hooksLocalFixed_startSend_some
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR Sig I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode) (j : ℕ) (k_fs : K) (ctx : _) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (c0 : CCoins) :
    (hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P ep γ σ (some c0) =
      (let c := cka.send γ c0
       rootLFixed prng mo j k_fs ep c.2.2 σ >>= fun r =>
         regSessOf r.2.2 >>= fun idx? =>
           modify (fun s => { s with cache := Function.update s.cache ep (some (c.2.1, r.1, r.2.1, idx?)) }) >>= fun _ =>
             pure (some (c.1, c.2.1, r.1, (fs.initSender r.2.1, idx?)))) := by
  simp only [hooksLocalFixed, pure_bind]

private theorem hooksLocalFixed_fsSend_eq
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR Sig I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode) (j : ℕ) (k_fs : K) (ctx : _) (P : Party) (ep : ℕ) (ssv : SS × Option ℕ) (h : Header T) (m : M) (pair : _) :
    (hooksLocalFixed cka prng fs mo j k_fs).fsSend ctx P ep ssv h m pair =
      pure (let o := fs.send ssv.1 h m; some ((o.1, ssv.2), o.2)) := rfl

private theorem hooksFSMulti_startSend_none
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (ctx : _) (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ none =
      (StateT.lift (sampleT CCoins) >>= fun c0 =>
        (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ (some c0)) := by
  simp only [hooksFSMulti, pure_bind]

private theorem hooksFSMulti_startSend_some
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (ctx : _) (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (c0 : CCoins) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ (some c0) =
      (let c := cka.send γ c0
       rootFSMulti prng mo ep c.2.2 σ >>= fun r =>
         regSessOptMulti r.2.2 >>= fun optIdx =>
           modify (fun s => { s with cache := Function.update s.cache ep (some (c.2.1, r.1, r.2.1, optIdx)) }) >>= fun _ =>
             pure (some (c.1, c.2.1, r.1, match optIdx with
               | none => .inl (fs.initSender r.2.1)
               | some sIdx => .inr sIdx))) := by
  simp only [hooksFSMulti, pure_bind]
  congr 1

private def vSendStepTail
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv T Sv SSv RSv M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (Δcka : ℕ) (s₁ : GameState (VP Γv T Sv SSv RSv) M (Header T × E)) (P : Party) (m : M)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (p : Option (VP Γv T Sv SSv RSv × (Header T × E)) × HS) :
    TComp tspec (Option (Header T × E) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (match p.1 with
    | none => do abortE; return none
    | some (st', c) => do
      modify fun (es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
        { es' with g := s₁.record Δcka P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false }
      return some c).run { es with h := p.2 }

private theorem transmitE_to_vSendStepTail
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δcka qep : ℕ) (pol : Policy)
    (P : Party) (m : M) (rc : Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (s₁ : GameState (VP Γv T Sv SSv RSv) M (Header T × E))
    (hab : es.abort = false) (hwin : es.g.win = false)
    (hep : es.g.epMgmt Δcka qep P rc.isSome = some s₁)
    (hld : pol.leakDoom es.g s₁ = false) :
    (transmitE hk Δcka qep pol (P, m, rc)).run es =
      ((vSend hk s₁ P (s₁.st P) m none rc).run es.h >>=
        vSendStepTail Δcka s₁ P m es) := by
  unfold transmitE
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  simp only [hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hep, hld]
  rw [run_liftH_bind]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | ⟨st', c⟩, h'⟩ <;> simp [vSendStepTail, hab]

private theorem hooksFSMulti_fsSend_inl
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (ctx : _) (P : Party) (ep : ℕ) (ss : SS) (h : Header T) (m : M) (pair : _) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).fsSend ctx P ep (.inl ss) h m pair =
      pure (let o := fs.send ss h m; some (.inl o.1, o.2)) := rfl

private theorem dir2_transmitE
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hℓ : ℓ < 10 ^ 6) (qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    {phase1 : Bool} (k_fs : BitVec 256)
    (P : Party) (m : MsgPt ℓ) (rc : Option (BitVec 256))
    (hm : atomicShortPubB m.1 = true)
    (cont : Option (Header Pt × Ct32) →
      SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (hnext : ∀ u esL' esM' sM' sL' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0' rs0' esL' esM' sM' sL' →
      LeRel phase1
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))
        (runMulti0 C Dh encPt encT idOf qep l t true (cont u) esM' (false, sL')))
    (hto2 : ∀ u esL' esM' sM' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0' rs0' esL' esM' sM' sL →
      LeOne
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    LeRel phase1
      (simulateQ lImpl
        ((transmitE hkL (2 + 0) qep (moAuth ⟨false, some (l - 1), t⟩).policy (P, m, rc)).run esL) >>=
        fun r => runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont r.1) r.2)
      ((simulateQ (implM false)
        ((transmitE (hkM false) 2 qep (⟨true, some (l - 1), t⟩ : Mode).policy (P, m, rc)).run esM)).run
        (false, sM) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t false (cont r.1.1) r.1.2 r.2)
      ((simulateQ (implM true)
        ((transmitE (hkM true) 2 qep (⟨true, some (l - 1), t⟩ : Mode).policy (P, m, rc)).run esM)).run
        (false, sL) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t true (cont r.1.1) r.1.2 r.2) := by
  intro hkL hkM implM
  have hpol : (moAuth ⟨false, some (l - 1), t⟩).policy = (⟨true, some (l - 1), t⟩ : Mode).policy := rfl
  rcases dir2_epMgmt_sync hs.herase qep P rc.isSome with
    ⟨hL_ep, hM_ep⟩ |
    ⟨s₁L, s₁M, hL_ep, hM_ep, hs₁_er, hs₁_stL, hs₁_stM, hs₁_winL, hs₁_winM, hs₁_tr, hs₁_other, hcases_ep⟩
  · unfold transmitE
    simp only [Nat.add_zero, hpol, StateT.run_bind, StateT.run_get, pure_bind,
      hs.habL, hs.habM, hs.hwinL, hs.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      hL_ep, hM_ep, StateT.run_pure, simulateQ_pure]
    exact hnext none esL esM sM sL ss0 rs0 hs
  · have hld_eq :
        (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esM.g s₁M =
        (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esL.g s₁L :=
      eraseSt_leakDoom hs.herase.symm hs₁_er.symm (⟨true, some (l - 1), t⟩ : Mode).policy
    by_cases hld : (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esL.g s₁L = true
    · unfold transmitE
      simp only [Nat.add_zero, hpol, StateT.run_bind, StateT.run_get, pure_bind,
        hs.habL, hs.habM, hs.hwinL, hs.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        hL_ep, hM_ep, hld, abortE, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      exact leRel_of_lhs_zero (evalDist_runLocAtFixed_eq_zero_of_abort (dhScheme Dh)
        (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) qep l
        ⟨false, some (l - 1), t⟩ k_fs (cont none) _ rfl)
    · have hld_f : (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esL.g s₁L = false :=
        Bool.eq_false_iff.mpr hld
      have hld_fL : (moAuth ⟨false, some (l - 1), t⟩).policy.leakDoom esL.g s₁L = false := by
        rw [hpol]; exact hld_f
      have hld_fM : (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom esM.g s₁M = false := by
        rw [hld_eq]; exact hld_f
      rw [show (2 + 0 : ℕ) = 2 from rfl,
          transmitE_to_vSendStepTail hkL 2 qep _ P m rc esL s₁L hs.habL hs.hwinL hL_ep hld_fL,
          transmitE_to_vSendStepTail (hkM false) 2 qep _ P m rc esM s₁M hs.habM hs.hwinM hM_ep hld_fM,
          transmitE_to_vSendStepTail (hkM true) 2 qep _ P m rc esM s₁M hs.habM hs.hwinM hM_ep hld_fM]
      have hstP_L : s₁L.st P = esL.g.st P := congrFun hs₁_stL P
      have hstP_M : s₁M.st P = esM.g.st P := congrFun hs₁_stM P
      rw [hstP_L, hstP_M]
      rcases hcases_ep with ⟨hsends_f, hep_eq, hidx_eq⟩ | ⟨hsends_t, hep_eq, hidx_eq, hqep_le⟩
      · have hP_sends : P = Party.senderOf (s₁L.epoch P) :=
          party_eq_senderOf_of_sendsIn (sendsIn_of_succ_false (hep_eq ▸ hsends_f))
        have hep_ge : esL.g.epoch P ≤ s₁L.epoch P := le_of_eq hep_eq.symm
        have hep_le : s₁L.epoch P ≤ esL.g.epoch P + 1 := by omega
        have htcur_s1L : (esL.g.st P).tcur = s₁L.epoch P := (hs.htcurL P).trans hep_eq.symm
        have htcur_s1M : (esM.g.st P).tcur = s₁L.epoch P := (hs.htcurM P).trans hep_eq.symm
        simp only [vSend, hs.hidL P, hs.hidM P, hs.htcurL P, hs.htcurM P,
          hsends_f, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rcases hs.hvS_rel P with ⟨hvL, hvM, hnot_t, hcka⟩ | ⟨ss, hvL, hvM, hnot_t, hcka⟩ |
            ⟨ht_le, hPs, hcur_or, hvL, hvM, hcka⟩
        · have hep_ne_t : s₁L.epoch P ≠ t := fun h => hnot_t ⟨h ▸ hP_sends, htcur_s1L.trans h⟩
          have hs' := dir2Sync_record_ne hs P hs₁_er hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr
            hs₁_other hep_ge hep_le hP_sends hep_ne_t
            (esL.g.st P).γ (esL.g.st P).curCkaMsg (esL.g.st P).root none none (Or.inl ⟨rfl, rfl⟩)
            m default esL.h esM.h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hs.hcache_ne
          dsimp only at hs'
          have hstL_id :
              { esL.g.st P with
                tcur := s₁L.epoch P, γ := (esL.g.st P).γ,
                curCkaMsg := (esL.g.st P).curCkaMsg, root := (esL.g.st P).root, vS := none } =
              esL.g.st P := by
            rw [← htcur_s1L, ← hvL]
          have hstM_id :
              { esM.g.st P with
                tcur := s₁L.epoch P, γ := (esL.g.st P).γ,
                curCkaMsg := (esL.g.st P).curCkaMsg, root := (esL.g.st P).root, vS := none } =
              esM.g.st P := by
            rw [← htcur_s1M, ← hs.hγ P, ← hcka, ← hs.hroot P, ← hvM]
          rw [hstL_id, hstM_id] at hs'
          dsimp only [implM]
          simp only [hvL, hvM, ← hep_eq, hcka, vSendStepTail, StateT.run_bind, StateT.run_pure,
            pure_bind, StateT.run_modify, simulateQ_pure]
          exact hnext (some ((s₁L.epoch P, (esL.g.st P).curCkaMsg), default)) _ _ sM sL ss0 rs0 hs'
        · have hep_ne_t : s₁L.epoch P ≠ t := fun h => hnot_t ⟨h ▸ hP_sends, htcur_s1L.trans h⟩
          let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ss
            (s₁L.epoch P, (esL.g.st P).curCkaMsg) m
          have hs' := dir2Sync_record_ne hs P hs₁_er hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr
            hs₁_other hep_ge hep_le hP_sends hep_ne_t
            (esL.g.st P).γ (esL.g.st P).curCkaMsg (esL.g.st P).root
            (some (o.1, none)) (some (Sum.inl o.1)) (Or.inr ⟨o.1, rfl, rfl⟩)
            m o.2 esL.h esM.h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hs.hcache_ne
          dsimp only at hs'
          rw [hs.hidL P, hs.hidM P] at hs'
          dsimp only [hkL, hkM, implM]
          simp only [hvL, hvM, ← hep_eq, hcka, hs.hγ P, hs.hroot P,
            hooksLocalFixed_fsSend_eq, hooksFSMulti_fsSend_inl, vSendStepTail,
            StateT.run_bind, StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure]
          exact hnext (some ((s₁L.epoch P, (esL.g.st P).curCkaMsg), o.2)) _ _ sM sL ss0 rs0 hs'
        · have hsends_cur : P.sendsIn (esL.g.st P).tcur = true := by
            rw [htcur_s1L]; exact sendsIn_of_succ_false (hep_eq ▸ hsends_f)
          have htcur_t : (esL.g.st P).tcur = t :=
            hcur_or.resolve_right (by rw [hsends_cur]; decide)
          have hep_t : s₁L.epoch P = t := htcur_s1L.symm.trans htcur_t
          obtain ⟨ht_qep, hcache_t⟩ := hs.hsess_sent ht_le
          have hcnt_eq : ((esM.h.book 0).getD {}).fsCount = s₁L.idx P := by
            rw [hs.hbk_count (hPs ▸ htcur_t), ← hPs, hidx_eq]
          let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ss0
            (t, (esL.g.st P).curCkaMsg) m
          rcases dir2_fsSend0_cases C Dh encPt encT idOf hℓ qep l t k_fs hs P hs₁_er
            hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr hs₁_other hep_ge hPs hep_t ht_qep
            (esL.g.st P).γ (esL.g.st P).curCkaMsg (esL.g.st P).root m hm esL.h esM.h
            ⟨rfl, hs.hlfM⟩ hcache_t hs.hcache_ne hcnt_eq with
            ⟨hM', sM', sL', hs', hrunM, hrunL⟩ | ⟨hM', sM', hs', hrunM⟩
          · dsimp only at hs'
            rw [hs.hidL P, hs.hidM P, hep_t] at hs'
            cases phase1 with
            | false =>
              dsimp only [LeRel, implM]
              simp only [hvL, hvM, ← hep_eq, hep_t, hcka, hs.hγ P, hs.hroot P, hkL,
                hooksLocalFixed_fsSend_eq, vSendStepTail, StateT.run_bind, StateT.run_pure,
                pure_bind, StateT.run_modify, simulateQ_pure, simulateQ_bind, bind_assoc]
              rw [hrunM]; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              exact hnext (some ((t, (esL.g.st P).curCkaMsg), o.2)) _ _ sM' sL' o.1 rs0 hs'
            | true =>
              dsimp only [LeRel, implM]
              have hrunL' := hrunL rfl
              simp only [hvL, hvM, ← hep_eq, hep_t, hcka, hs.hγ P, hs.hroot P, hkL,
                hooksLocalFixed_fsSend_eq, vSendStepTail, StateT.run_bind, StateT.run_pure,
                pure_bind, StateT.run_modify, simulateQ_pure, simulateQ_bind, bind_assoc]
              rw [hrunM, hrunL']; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              exact hnext (some ((t, (esL.g.st P).curCkaMsg), o.2)) _ _ sM' sL' o.1 rs0 hs'
          · dsimp only at hs'
            rw [hs.hidL P, hs.hidM P, hep_t] at hs'
            refine leRel_to_phase2 ?_
            dsimp only [implM]
            simp only [hvL, hvM, ← hep_eq, hep_t, hcka, hs.hγ P, hs.hroot P, hkL,
              hooksLocalFixed_fsSend_eq, vSendStepTail, StateT.run_bind, StateT.run_pure,
              pure_bind, StateT.run_modify, simulateQ_pure, simulateQ_bind, bind_assoc]
            rw [hrunM]; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
            exact hto2 (some ((t, (esL.g.st P).curCkaMsg), o.2)) _ _ sM' o.1 rs0 hs'
      · have hP_sends : P = Party.senderOf (s₁L.epoch P) :=
          hep_eq.symm ▸ party_eq_senderOf_of_sendsIn hsends_t
        have hep_ge : esL.g.epoch P ≤ s₁L.epoch P := by omega
        have hep_le : s₁L.epoch P ≤ esL.g.epoch P + 1 := by omega
        suffices hcoins : ∀ c0 : BitVec 256,
            LeRel phase1
              (simulateQ lImpl
                ((vSend hkL s₁L P (esL.g.st P) m none (some c0)).run esL.h >>=
                  vSendStepTail 2 s₁L P m esL) >>=
                fun r => runLocAtFixedDFShiftedDir2Paper (dhScheme Dh)
                  (CryptoGames.Ratchet.rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l
                  ⟨false, some (l - 1), t⟩ 0 k_fs (cont r.1) r.2)
              ((simulateQ (implM false)
                ((vSend (hkM false) s₁M P (esM.g.st P) m none (some c0)).run esM.h >>=
                  vSendStepTail 2 s₁M P m esM)).run (false, sM) >>=
                fun r => runMulti0 C Dh encPt encT idOf qep l t false (cont r.1.1) r.1.2 r.2)
              ((simulateQ (implM true)
                ((vSend (hkM true) s₁M P (esM.g.st P) m none (some c0)).run esM.h >>=
                  vSendStepTail 2 s₁M P m esM)).run (false, sL) >>=
                fun r => runMulti0 C Dh encPt encT idOf qep l t true (cont r.1.1) r.1.2 r.2) by
          rcases rc with _ | c0
          · dsimp only [hkL, hkM, implM]
            simp only [vSend, hs.hidL P, hs.hidM P, hs.htcurL P, hs.htcurM P, hsends_t, ↓reduceIte,
              hooksLocalFixed_startSend_none, hooksFSMulti_startSend_none,
              StateT.run_bind, bind_assoc, simulateQ_bind,
              simulateQ_lImpl_run_lift_sampleT, simulateQ_pubFsImpl0_run_lift_sampleT, pure_bind]
            refine leRel_bind_unif ($ᵗ (BitVec 256)) _ _ _ fun c0 _ => ?_
            simpa only [hkL, hkM, implM, vSend, hs.hidL P, hs.hidM P, hs.htcurL P, hs.htcurM P,
              hsends_t, ↓reduceIte, StateT.run_bind, bind_assoc, simulateQ_bind, pure_bind] using
              hcoins c0
          · exact hcoins c0
        intro c0
        simp only [vSend, hs.hidL P, hs.hidM P, hs.htcurL P, hs.htcurM P,
          hsends_t, ↓reduceIte, hs.hγ P, hs.hroot P]
        let ep1 := esL.g.epoch P + 1
        let ck := (dhScheme Dh).send (esL.g.st P).γ c0
        have htH : (⟨false, some (l - 1), t⟩ : Mode).tH = t := mode_tH_eq l t ht2 hl
        by_cases hep_t : ep1 = t
        · have hep_s1_t : s₁L.epoch P = t := hep_eq.trans hep_t
          have hP_sends_t : P = Party.senderOf t := hep_s1_t ▸ hP_sends
          have hnot_sent : ¬ t ≤ (esL.g.st (Party.senderOf t)).tcur := by
            rw [← hP_sends_t, hs.htcurL P]; omega
          obtain ⟨hsessL, hsessM, _, _, hbk0, _, hss0, _⟩ := hs.hsess_nil hnot_sent
          dsimp only [hkL, hkM, implM]
          simp only [hooksLocalFixed_startSend_some, hooksFSMulti_startSend_some]
          unfold rootLFixed rootFSMulti
          have htLis : (⟨false, some (l - 1), t⟩ : Mode).tL.isSome = true := rfl
          simp only [show esL.g.epoch P + 1 = t from hep_t,
            lt_irrefl, ↓reduceIte, htLis, htH, decide_true, Bool.true_and,
            StateT.run_bind, bind_assoc, simulateQ_bind,
            simulateQ_lImpl_run_lift_sampleT, simulateQ_pubFsImpl0_run_lift_sampleT, pure_bind]
          refine leRel_bind_unif ($ᵗ Pt) _ _ _ fun Ir _ => ?_
          refine leRel_bind_unif ($ᵗ (BitVec 256)) _ _ _ fun kr _ => ?_
          let σ' := ((CryptoGames.Ratchet.rootPRNG C.F encPt).up (esL.g.st P).root Ir).1
          have hdec_ir : decide (Ir ∉ ([] : List Pt)) = true := decide_eq_true List.not_mem_nil
          let hL₁ : LState Pt (BitVec 256) (BitVec 256) Pt :=
            { esL.h with sessions := [Ir],
                         cache := Function.update esL.h.cache t (some (ck.2.1, σ', k_fs, some 0)) }
          let hM₁ : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
            { esM.h with sessions := [Ir],
                         cache := Function.update esM.h.cache t (some (ck.2.1, σ', kr, some 0)) }
          have hregL : (regSessOf (some Ir)).run esL.h = pure (some 0, { esL.h with sessions := [Ir] }) := by
            simp [regSessOf, _root_.CryptoGames.SM.Construction.AuthL11.regSess, hsessL]
          have hregM : ∀ {SS RS M'},
              (regSessOptMulti (SS := SS) (RS := RS) (M := M') (E := Ct32) (some Ir)).run esM.h =
              pure (some 0, { esM.h with sessions := [Ir] }) := by
            intro SS RS M'; simp [regSessOptMulti, regSessMulti, hsessM]
          have hcache_t1 : ∃ Tc σc km, hL₁.cache t = some (Tc, σc, k_fs, some 0) ∧
              hM₁.cache t = some (Tc, σc, km, some 0) :=
            ⟨ck.2.1, σ', kr, by simp [hL₁], by simp [hM₁]⟩
          have hcache_ne1 : ∀ ep', ep' ≠ t →
              (hL₁.cache ep' = none ∧ hM₁.cache ep' = none) ∨
              ∃ Tc σc k, hL₁.cache ep' = some (Tc, σc, k, none) ∧
                hM₁.cache ep' = some (Tc, σc, k, none) := by
            intro ep' hne; simp only [hL₁, hM₁, Function.update_of_ne hne]; exact hs.hcache_ne ep' hne
          have hcnt_eq : ((esM.h.book 0).getD {}).fsCount = s₁L.idx P := by
            rw [hbk0, hidx_eq]; rfl
          let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ss0 (t, some ck.2.1) m
          rcases dir2_fsSend0_cases C Dh encPt encT idOf hℓ qep l t k_fs hs P hs₁_er
            hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr hs₁_other hep_ge hP_sends_t hep_s1_t
            (hep_t ▸ hqep_le) ck.1 (some ck.2.1) σ' m hm hL₁ hM₁ ⟨rfl, hs.hlfM⟩
            hcache_t1 hcache_ne1 hcnt_eq with
            ⟨hM', sM', sL', hs', hrunM, hrunL⟩ | ⟨hM', sM', hs', hrunM⟩
          · dsimp only at hs'
            rw [hs.hidL P, hs.hidM P] at hs'
            cases phase1 with
            | false =>
              dsimp only [LeRel]
              simp only [StateT.run_get, StateT.run_pure, pure_bind, hsessL, hdec_ir,
                List.length_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte,
                hregL, hregM, StateT.run_modify, hooksLocalFixed_fsSend_eq, ← hss0,
                vSendStepTail, StateT.run_bind, simulateQ_pure]
              rw [hrunM]; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              exact hnext (some ((t, some ck.2.1), o.2)) _ _ sM' sL' o.1 rs0 hs'
            | true =>
              dsimp only [LeRel]
              have hrunL' := hrunL rfl
              simp only [StateT.run_get, StateT.run_pure, pure_bind, hsessL, hdec_ir,
                List.length_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte,
                hregL, hregM, StateT.run_modify, hooksLocalFixed_fsSend_eq, ← hss0,
                vSendStepTail, StateT.run_bind, simulateQ_pure]
              rw [hrunM, hrunL']; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
              exact hnext (some ((t, some ck.2.1), o.2)) _ _ sM' sL' o.1 rs0 hs'
          · dsimp only at hs'
            rw [hs.hidL P, hs.hidM P] at hs'
            refine leRel_to_phase2 ?_
            simp only [StateT.run_get, StateT.run_pure, pure_bind, hsessL, hdec_ir,
              List.length_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte,
              hregL, hregM, StateT.run_modify, hooksLocalFixed_fsSend_eq, ← hss0,
              vSendStepTail, StateT.run_bind, simulateQ_pure]
            rw [hrunM]; simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
            exact hto2 (some ((t, some ck.2.1), o.2)) _ _ sM' o.1 rs0 hs'
        · have hep_s1_ne : s₁L.epoch P ≠ t := hep_eq ▸ hep_t
          let p := (CryptoGames.Ratchet.rootPRNG C.F encPt).up (esL.g.st P).root ck.2.2
          have hrootL : (rootLFixed (CryptoGames.Ratchet.rootPRNG C.F encPt)
              ⟨false, some (l - 1), t⟩ 0 k_fs ep1 ck.2.2 (esL.g.st P).root).run esL.h =
              pure ((p.1, p.2, none), esL.h) := by
            unfold rootLFixed; rw [htH]
            by_cases hlt : t < ep1 <;> simp [hlt, hep_t, p]
          have hrootM : ∀ {SS RS M'},
              (rootFSMulti (SS := SS) (RS := RS) (T := Pt) (M := M') (E := Ct32)
                (CryptoGames.Ratchet.rootPRNG C.F encPt)
                ⟨false, some (l - 1), t⟩ ep1 ck.2.2 (esL.g.st P).root).run esM.h =
              pure ((p.1, p.2, none), esM.h) := by
            intro SS RS M'; unfold rootFSMulti; rw [htH]
            by_cases hlt : t < ep1 <;> simp [hlt, hep_t, p]
          let hL' : LState Pt (BitVec 256) (BitVec 256) Pt :=
            { esL.h with cache := Function.update esL.h.cache ep1 (some (ck.2.1, p.1, p.2, none)) }
          let hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
            { esM.h with cache := Function.update esM.h.cache ep1 (some (ck.2.1, p.1, p.2, none)) }
          let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
          let o := fs.send (fs.initSender p.2) (ep1, some ck.2.1) m
          have hcache_ne' : ∀ ep', ep' ≠ t →
              (hL'.cache ep' = none ∧ hM'.cache ep' = none) ∨
              ∃ Tc σc k, hL'.cache ep' = some (Tc, σc, k, none) ∧
                hM'.cache ep' = some (Tc, σc, k, none) := by
            intro ep' hne; dsimp only [hL', hM']
            by_cases heq' : ep' = ep1
            · subst heq'; exact Or.inr ⟨ck.2.1, p.1, p.2, by simp, by simp⟩
            · simp only [Function.update_of_ne heq']; exact hs.hcache_ne ep' hne
          have hs' := dir2Sync_record_ne hs P hs₁_er hs₁_stL hs₁_stM hs₁_winL hs₁_winM hs₁_tr
            hs₁_other hep_ge hep_le hP_sends hep_s1_ne ck.1 (some ck.2.1) p.1
            (some (o.1, none)) (some (Sum.inl o.1)) (Or.inr ⟨o.1, rfl, rfl⟩) m o.2 hL' hM'
            ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
            ⟨by simp [hL', Function.update_of_ne (Ne.symm hep_t)],
             by simp [hM', Function.update_of_ne (Ne.symm hep_t)]⟩
            hcache_ne'
          dsimp only [ep1, ck] at hrootL hrootM
          dsimp only [ep1] at hs'
          rw [hep_eq, hs.hidL P, hs.hidM P] at hs'
          dsimp only [hkL, hkM, implM]
          simp only [hooksLocalFixed_startSend_some, hooksFSMulti_startSend_some, bind_assoc,
            StateT.run_bind, pure_bind, hrootL, hrootM, regSessOf, regSessOptMulti,
            StateT.run_modify, StateT.run_pure, hooksLocalFixed_fsSend_eq, hooksFSMulti_fsSend_inl,
            vSendStepTail, simulateQ_pure, hep_eq]
          exact hnext (some ((ep1, some ck.2.1), o.2)) _ _ sM sL ss0 rs0 hs'

private def recvStep1Tail
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (qep : ℕ) (mo : Mode)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c : Header T × E)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (q : Option (Option (VP Γv T Sv SSv RSv)) × HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  match q.1 with
  | none => (do abortE; return none).run { es with h := q.2 }
  | some none => pure (some RecvResult.rejected, { es with h := q.2 })
  | some (some s₁) =>
    _root_.CryptoGames.SM.Construction.DeliverForge.injectTailB1 qep mo hk P c s₁
      { es with h := q.2 }

private theorem injectEB1_to_tail
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep : ℕ) (mo : Mode) (P : Party) (c : Header T × E)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hab : es.abort = false) (hwin : es.g.win = false)
    (hin : es.g.inTransit P.other c = none) (hsafe : es.g.safeInj 2 = true)
    (hc : ((es.g.st P).id.sendsIn c.1.1 || decide ((es.g.st P).tcur + 1 < c.1.1)) = false) :
    (_root_.CryptoGames.SM.Construction.DeliverForge.injectEB1 hk qep mo.tStar mo.cfg (P, c)).run es =
      ((vRecvStep1 hk es.g P (es.g.st P) c).run es.h >>=
        recvStep1Tail qep mo hk P c es) := by
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hab, hwin, hin, Option.isSome_none,
    hsafe, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [vRecv_eq_bind]
  simp only [hc, Bool.false_eq_true, ↓reduceIte, stateT_run_liftH, StateT.run_bind, bind_assoc]
  congr 1; funext ⟨q1, q2⟩
  rcases q1 with _ | (_ | s₁)
  · simp [recvStep1Tail, hab]
  · simp [recvStep1Tail, hab]
  · dsimp only [recvStep1Tail]
    simp only [_root_.CryptoGames.SM.Construction.DeliverForge.injectTailB1, run_liftH_bind,
      vRecvTail, pure_bind]
    congr 1

private theorem deliverForgeEB1_to_tail
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep : ℕ) (mo : Mode) (P : Party) (c c' : Header T × E)
    (r : Record M (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hab : es.abort = false) (hwin : es.g.win = false)
    (hin : es.g.inTransit P.other c = some r)
    (hin' : es.g.inTransit P.other c' = none)
    (hguard : (es.g.comp.contains r.pos || (c.1 != c'.1)) = false)
    (hr_ep : r.pos.epoch = c'.1.1)
    (hc : ((es.g.st P).id.sendsIn c'.1.1 || decide ((es.g.st P).tcur + 1 < c'.1.1)) = false) :
    (_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 hk qep mo.tStar mo.cfg
        (P, c, c')).run es =
      ((vRecvStep1 hk es.g P (es.g.st P) c').run es.h >>=
        recvStep1Tail qep mo hk P c' es) := by
  have hguard' : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || (c.1 != c'.1)) = false := by
    rw [hin', Option.isSome_none, Bool.false_or]; exact hguard
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hab, hwin, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hin, hguard']
  rw [vRecv_eq_bind]
  simp only [hc, Bool.false_eq_true, ↓reduceIte, stateT_run_liftH, StateT.run_bind, bind_assoc]
  congr 1; funext ⟨q1, q2⟩
  rcases q1 with _ | (_ | s₁)
  · simp [recvStep1Tail, hab]
  · simp [recvStep1Tail, hab]
  · dsimp only [recvStep1Tail]
    rw [← _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeTailB1_eq_injectTailB1
      qep mo hk P c' r hr_ep s₁ { es with h := q2 }]
    simp only [_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeTailB1, run_liftH_bind,
      vRecvTail, pure_bind]
    congr 1

private theorem dir2_injectTail
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) {phase1 : Bool} (k_fs : BitVec 256)
    (P : Party) (c : Header Pt × Ct32)
    (cont : Option (RecvResult (MsgPt ℓ)) →
      SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (hin : esL.g.inTransit P.other c = none)
    (hsends_f : P.sendsIn c.1.1 = false)
    (ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1)
    (hnext : ∀ u esL' esM' sM' sL' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0' rs0' esL' esM' sM' sL' →
      LeRel phase1
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))
        (runMulti0 C Dh encPt encT idOf qep l t true (cont u) esM' (false, sL')))
    (hto2 : ∀ u esL' esM' sM' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0' rs0' esL' esM' sM' sL →
      LeOne
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    LeRel phase1
      (simulateQ lImpl
        ((vRecvStep1 hkL esL.g P (esL.g.st P) c).run esL.h >>=
          recvStep1Tail qep ⟨true, some (l - 1), t⟩ hkL P c esL) >>=
        fun r => runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont r.1) r.2)
      ((simulateQ (implM false)
        ((vRecvStep1 (hkM false) esM.g P (esM.g.st P) c).run esM.h >>=
          recvStep1Tail qep ⟨true, some (l - 1), t⟩ (hkM false) P c esM)).run (false, sM) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t false (cont r.1.1) r.1.2 r.2)
      ((simulateQ (implM true)
        ((vRecvStep1 (hkM true) esM.g P (esM.g.st P) c).run esM.h >>=
          recvStep1Tail qep ⟨true, some (l - 1), t⟩ (hkM true) P c esM)).run (false, sL) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t true (cont r.1.1) r.1.2 r.2) := by
  intro hkL hkM implM
  dsimp only [hkL, hkM]
  rcases dir2_vRecv_step1 C Dh encPt encT idOf (l := l) hs P c hsends_f ht_le with
    ⟨s₁L?, s₁M?, hst1L, hst1M, hnone_cases⟩ |
    ⟨hct_ne, γ', σ', rs, hst1L, hst1M⟩ |
    ⟨hct_t, hPr, hsnd_le, ht_qep, γ', σ', hst1L, hst1M⟩
  · rcases hnone_cases with ⟨rfl, rfl⟩ | ⟨s₁L, s₁M, rfl, rfl, hvL, hvM⟩
    · rw [hst1L, hst1M false, hst1M true]
      simp only [pure_bind, recvStep1Tail, simulateQ_pure, StateT.run_pure]
      exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
    · rw [hst1L, hst1M false, hst1M true]
      simp only [pure_bind, recvStep1Tail, _root_.CryptoGames.SM.Construction.DeliverForge.injectTailB1,
        run_liftH_bind, vRecvTail, hvL, hvM, StateT.run_pure, simulateQ_pure]
      exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
  · rw [hst1L, hst1M false, hst1M true]
    simp only [pure_bind, recvStep1Tail, _root_.CryptoGames.SM.Construction.DeliverForge.injectTailB1,
      run_liftH_bind, vRecvTail, Function.update_self,
      hooksLocalFixed_fsRecv_eq, hooksFSMulti_fsRecv_inl_eq]
    cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs c.1 c.2 with
    | none =>
      simp only [Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure]
      exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
    | some rim =>
      rcases rim with ⟨rs', i', m'⟩
      let hL_non : LState Pt (BitVec 256) (BitVec 256) Pt := { esL.h with lastIdx := none }
      have hs_non : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0
          { esL with h := hL_non } esM sM sL :=
        { habL := hs.habL, habM := hs.habM, hwinL := hs.hwinL, hwinM := hs.hwinM,
          hlfM := hs.hlfM, herase := hs.herase, hidL := hs.hidL, hidM := hs.hidM,
          htcurL := hs.htcurL, htcurM := hs.htcurM, hγ := hs.hγ, hroot := hs.hroot,
          htrans_wf := hs.htrans_wf, hinv := hs.hinv, hscorr2 := hs.hscorr2,
          hbk_trans := hs.hbk_trans, hbk_count := hs.hbk_count,
          hsess_nil := hs.hsess_nil, hsess_sent := hs.hsess_sent,
          hcache_ne := hs.hcache_ne, hvS_rel := hs.hvS_rel,
          hvR_ne := hs.hvR_ne, hvR_star := hs.hvR_star }
      simp only [Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        exact hnext (some .rejected) { esL with h := hL_non } esM sM sL ss0 rs0 hs_non
      · simp only [hqep, ↓reduceIte]
        let pos : Pos := ⟨P.other, c.1.1, i'⟩
        have htriv_eq : trivB1 t esM.g pos = trivB1 t esL.g pos :=
          _root_.CryptoGames.SM.Construction.DeliverForge.eraseSt_trivB1_l11 hs.herase.symm t pos
        rw [htriv_eq]
        cases htriv : trivB1 t esL.g pos with
        | false =>
          have hinjF : ((⟨true, some (l - 1), t⟩ : Mode).cfg (M := MsgPt ℓ)).injectFull c.1.1 = false := by
            simp [Mode.cfg, Config.auth, beq_eq_false_iff_ne.mpr hct_ne]
          simp only [Bool.false_eq_true, ↓reduceIte, hinjF, StateT.run_pure, simulateQ_pure, pure_bind]
          exact hnext (some .rejected) { esL with h := hL_non } esM sM sL ss0 rs0 hs_non
        | true =>
          have hne_pair : (P, c.1.1) ≠ (Party.receiverOf t, t) := fun h => hct_ne (congrArg Prod.snd h)
          have hs' := dir2Sync_accept_ne hs_non P c.1.1 i' hsends_f ht_le hne_pair γ' σ' rs' hL_non rfl rfl
          dsimp only at hs'
          simp only [↓reduceIte, commitE, hooksLocalFixed, hooksFSMulti, StateT.run_bind,
            stateT_run_liftH, StateT.run_pure, pure_bind, StateT.run_modify,
            Function.update_idem, accept_update_self, simulateQ_pure]
          exact hnext (some (.accepted c.1.1 i' (some m'))) _ _ sM sL ss0 rs0 hs'
  · rw [hst1L, hst1M false, hst1M true]
    have hPo : P.other = Party.senderOf t :=
      other_eq_senderOf_of_sendsIn_false (hct_t ▸ hsends_f)
    have hin_s : esL.g.inTransit (Party.senderOf t) c = none := hPo ▸ hin
    let bk := ((esM.h.book 0).getD {})
    have hmatch : bk.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none :=
      dir2_matched_of_inTransit_none hs hin_s hct_t
    have ht_le_t : t ≤ (esL.g.st (Party.receiverOf t)).tcur + 1 := by
      rw [← hPr, ← hct_t]; exact ht_le
    have hqep_f : ¬ (qep + 1 < t) := by omega
    have hinjFull : ((⟨true, some (l - 1), t⟩ : Mode).cfg (M := MsgPt ℓ)).injectFull t = true := by
      simp [Mode.cfg, Config.auth]
    have htStar_m : (⟨true, some (l - 1), t⟩ : Mode).tStar = t := rfl
    have herase_win : eraseSt { esL.g with win := true } = eraseSt { esM.g with win := true } := by
      change { eraseSt esL.g with win := true } = { eraseSt esM.g with win := true }
      rw [hs.herase]
    simp only [pure_bind, recvStep1Tail, _root_.CryptoGames.SM.Construction.DeliverForge.injectTailB1,
      run_liftH_bind, vRecvTail, hct_t, Function.update_self,
      hooksLocalFixed_fsRecv_eq, hooksFSMulti_fsRecv_inr_eq, hs.htL]
    by_cases hneed_corr : (!(healedBy esL.g.tL 2 t) && !bk.sCorr) = true
    · refine leRel_to_phase2 ?_
      have hinv2 : ActiveSessInv C ℓ encT idOf false k_fs ss0 rs0 bk sM sL :=
        activeSessInv_any_to_phase2 C ℓ encT idOf hs.hinv
      obtain ⟨sM_c, hcorr_step, hinv_c⟩ := activeSessInv_corruptSender C ℓ encT idOf hinv2
      let bk_c : FSMultiBook Pt Ct32 := { bk with sCorr := true }
      let hM_c : FSMultiState Pt (BitVec 256) (BitVec 256) Pt Ct32 :=
        { esM.h with book := (Function.update esM.h.book 0 (some bk_c)) }
      have hbk_c_get : (hM_c.book 0).getD {} = bk_c := by simp [hM_c]
      have hrun_corr := run_liftFSMulti0_corruptSender (Pt := Pt) C encT idOf esM.h sM hcorr_step
      have hs_c : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0 rs0
          esL { esM with h := hM_c } sM_c sL :=
        { habL := hs.habL, habM := hs.habM, hwinL := hs.hwinL, hwinM := hs.hwinM,
          hlfM := hs.hlfM, herase := hs.herase, hidL := hs.hidL, hidM := hs.hidM,
          htcurL := hs.htcurL, htcurM := hs.htcurM, hγ := hs.hγ, hroot := hs.hroot,
          htrans_wf := hs.htrans_wf,
          hinv := by dsimp only; rw [hbk_c_get]; exact hinv_c,
          hscorr2 := fun _ => by dsimp only; rw [hbk_c_get],
          hbk_trans := by dsimp only; rw [hbk_c_get]; exact hs.hbk_trans,
          hbk_count := fun ht => by dsimp only; rw [hbk_c_get]; exact hs.hbk_count ht,
          hsess_nil := fun hnot => absurd hsnd_le hnot,
          hsess_sent := hs.hsess_sent,
          hcache_ne := hs.hcache_ne,
          hvS_rel := hs.hvS_rel,
          hvR_ne := hs.hvR_ne,
          hvR_star := hs.hvR_star }
      dsimp only [implM]
      simp only [StateT.run_bind, StateT.run_get, pure_bind,
        show ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none from hmatch,
        Option.isNone_none, Option.isSome_none, Bool.true_and,
        show (!healedBy esL.g.tL 2 t && !((esM.h.book 0).getD {}).sCorr) = true from hneed_corr,
        Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
      rw [hrun_corr]
      simp only [StateT.run_bind, pure_bind, StateT.run_modify, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
        bind_assoc]
      cases hpub : lPubOf protoSignalCodec c.2.2 with
      | none =>
        have hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 = none := by
          rw [lFS_receive_eq C protoSignalCodec ℓ encT idOf maxForwardJumps rs0 c.1 c.2, hpub]
        have hrun_inj := run_liftFSMulti0_inject_none (Pt := Pt) C encT idOf false c.1 c.2 hpub hM_c sM_c
        rw [hrun_inj]
        simp only [hrcv, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure]
        exact hto2 (some .rejected) esL { esM with h := hM_c } sM_c ss0 rs0 hs_c
      | some p =>
        have hmatch_c : bk_c.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := hmatch
        have hinj_cases := activeSessInv_inject_phase2 C ℓ encT idOf hinv_c rfl c.1 c.2 hmatch_c p hpub
        cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 with
        | none =>
          rw [hrcv] at hinj_cases
          obtain ⟨sM', hinj_step, hinv'⟩ := hinj_cases
          have hrun_inj := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
            hM_c sM_c hinj_step
          rw [hrun_inj]
          simp only [Option.map_none, StateT.run_pure,
            pure_bind, simulateQ_pure]
          exact hto2 (some .rejected) esL { esM with h := hM_c } sM' ss0 rs0
            { hs_c with hinv := by dsimp only; rw [hbk_c_get]; exact hinv' }
        | some rim =>
          rcases rim with ⟨rs', idxOut, pmOut⟩
          rw [hrcv] at hinj_cases
          obtain ⟨sM', hinj_step, hpm_fst, hinv'⟩ := hinj_cases
          have hwp : _root_.CryptoGames.FSAEAD.withPub p (.accepted idxOut (some pmOut.2)) =
              .accepted idxOut (some pmOut) := by
            rcases pmOut with ⟨p1, p2⟩; dsimp at hpm_fst; subst hpm_fst; rfl
          have hrun_inj := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
            hM_c sM_c hinj_step
          rw [hrun_inj]
          simp only [Option.map_some, hwp, StateT.run_bind, StateT.run_get, StateT.run_modify,
            StateT.run_pure, pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            Option.map_none, Option.getD_none, simulateQ_pure, hqep_f]
          let pos : Pos := ⟨P.other, t, idxOut⟩
          have htriv_eq : trivB1 t esM.g pos = trivB1 t esL.g pos :=
            _root_.CryptoGames.SM.Construction.DeliverForge.eraseSt_trivB1_l11 hs.herase.symm t pos
          rw [htriv_eq]
          cases htriv : trivB1 t esL.g pos with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, hinjFull]
            exact both_win_leOne C Dh encPt encT idOf qep l t k_fs (cont (some .rejected))
              _ _ (false, sM') hs.habL hs.habM rfl rfl herase_win
          | true =>
            have hs' := dir2Sync_accept_at_t hs_c hsnd_le ht_le_t γ' σ' idxOut
              (by dsimp only; rw [hbk_c_get]; exact hinv')
            dsimp only at hs'
            rw [← hPo, ← hPr] at hs'
            simp only [↓reduceIte, commitE, hooksLocalFixed, hooksFSMulti, StateT.run_bind,
              stateT_run_liftH, StateT.run_pure, pure_bind, StateT.run_modify,
              Function.update_idem, accept_update_self, simulateQ_pure]
            exact hto2 (some (.accepted t idxOut (some pmOut))) _ _ sM' ss0 rs' hs'
    · have hneed_f : (!healedBy esL.g.tL 2 t && !((esM.h.book 0).getD {}).sCorr) = false :=
        Bool.eq_false_iff.mpr hneed_corr
      dsimp only [implM]
      simp only [StateT.run_bind, StateT.run_get, pure_bind,
        show ((esM.h.book 0).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none from hmatch,
        Option.isNone_none, Option.isSome_none, Bool.true_and, hneed_f,
        Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        simulateQ_bind, bind_assoc]
      cases hpub : lPubOf protoSignalCodec c.2.2 with
      | none =>
        have hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 = none := by
          rw [lFS_receive_eq C protoSignalCodec ℓ encT idOf maxForwardJumps rs0 c.1 c.2, hpub]
        have hrunM := run_liftFSMulti0_inject_none (Pt := Pt) C encT idOf false c.1 c.2 hpub esM.h sM
        have hrunL := run_liftFSMulti0_inject_none (Pt := Pt) C encT idOf true c.1 c.2 hpub esM.h sL
        rw [hrunM, hrunL]
        simp only [hrcv, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure]
        exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
      | some p =>
        cases phase1 with
        | false =>
          dsimp only [LeRel]
          have hscorr : bk.sCorr = true := hs.hscorr2 rfl
          have hinj_cases := activeSessInv_inject_phase2 C ℓ encT idOf hs.hinv hscorr c.1 c.2 hmatch p hpub
          cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 with
          | none =>
            rw [hrcv] at hinj_cases
            obtain ⟨sM', hinj_step, hinv'⟩ := hinj_cases
            have hrunM := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
              esM.h sM hinj_step
            rw [hrunM]
            simp only [Option.map_none, StateT.run_pure,
              pure_bind, simulateQ_pure]
            exact hnext (some .rejected) esL esM sM' sL ss0 rs0 { hs with hinv := hinv' }
          | some rim =>
            rcases rim with ⟨rs', idxOut, pmOut⟩
            rw [hrcv] at hinj_cases
            obtain ⟨sM', hinj_step, hpm_fst, hinv'⟩ := hinj_cases
            have hwp : _root_.CryptoGames.FSAEAD.withPub p (.accepted idxOut (some pmOut.2)) =
                .accepted idxOut (some pmOut) := by
              rcases pmOut with ⟨p1, p2⟩; dsimp at hpm_fst; subst hpm_fst; rfl
            have hrunM := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
              esM.h sM hinj_step
            rw [hrunM]
            simp only [Option.map_some, hwp, StateT.run_bind, StateT.run_get, StateT.run_modify,
              StateT.run_pure, pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              Option.map_none, Option.getD_none, simulateQ_pure, hqep_f]
            let pos : Pos := ⟨P.other, t, idxOut⟩
            have htriv_eq : trivB1 t esM.g pos = trivB1 t esL.g pos :=
              _root_.CryptoGames.SM.Construction.DeliverForge.eraseSt_trivB1_l11 hs.herase.symm t pos
            rw [htriv_eq]
            cases htriv : trivB1 t esL.g pos with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, hinjFull]
              exact both_win_leOne C Dh encPt encT idOf qep l t k_fs (cont (some .rejected))
                _ _ (false, sM') hs.habL hs.habM rfl rfl herase_win
            | true =>
              have hs' := dir2Sync_accept_at_t hs hsnd_le ht_le_t γ' σ' idxOut hinv'
              dsimp only at hs'
              rw [← hPo, ← hPr] at hs'
              simp only [↓reduceIte, commitE, hooksLocalFixed, hooksFSMulti, StateT.run_bind,
                stateT_run_liftH, StateT.run_pure, pure_bind, StateT.run_modify,
                Function.update_idem, accept_update_self, simulateQ_pure]
              exact hnext (some (.accepted t idxOut (some pmOut))) _ _ sM' sL ss0 rs' hs'
        | true =>
          dsimp only [LeRel]
          rcases activeSessInv_inject_phase1 C ℓ encT idOf hs.hinv c.1 c.2 hmatch p hpub with
            ⟨msg, sL', hscorr_f, hcnt_lt, hL_inj⟩ | hinj_cases
          · have hrunL := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf true c.1 c.2 p hpub
              esM.h sL hL_inj
            rw [hrunL]
            have hscorr_f' : ((esM.h.book 0).getD {}).sCorr = false := hscorr_f
            simp only [Option.map_some, _root_.CryptoGames.FSAEAD.withPub, StateT.run_bind,
              StateT.run_get, pure_bind, Bool.true_and, hscorr_f', Bool.not_false,
              decide_eq_true hcnt_lt, ↓reduceIte, StateT.run_modify, StateT.run_pure,
              abortE, simulateQ_pure]
            exact leAdd_lfWin_terminal C Dh encPt encT idOf qep l t (cont none)
              { esM with h := { esM.h with lfWin := true }, abort := true } (false, sL') rfl rfl
          · cases hrcv : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs0 c.1 c.2 with
            | none =>
              rw [hrcv] at hinj_cases
              obtain ⟨sM', sL', hM_inj, hL_inj, hinv'⟩ := hinj_cases
              have hrunM := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
                esM.h sM hM_inj
              have hrunL := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf true c.1 c.2 p hpub
                esM.h sL hL_inj
              rw [hrunM, hrunL]
              simp only [Option.map_none, StateT.run_pure,
                pure_bind, simulateQ_pure]
              exact hnext (some .rejected) esL esM sM' sL' ss0 rs0 { hs with hinv := hinv' }
            | some rim =>
              rcases rim with ⟨rs', idxOut, pmOut⟩
              rw [hrcv] at hinj_cases
              obtain ⟨sM', sL', hM_inj, hL_inj, hle_cnt, hpm_fst, hinv'⟩ := hinj_cases
              have hwp : _root_.CryptoGames.FSAEAD.withPub p (.accepted idxOut (some pmOut.2)) =
                  .accepted idxOut (some pmOut) := by
                rcases pmOut with ⟨p1, p2⟩; dsimp at hpm_fst; subst hpm_fst; rfl
              have hlf_not : ((!((esM.h.book 0).getD {}).sCorr) &&
                  decide (((esM.h.book 0).getD {}).fsCount < idxOut)) = false := by
                cases hsc : ((esM.h.book 0).getD {}).sCorr
                · simp [Nat.not_lt.mpr (hle_cnt hsc)]
                · simp
              have hrunM := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf false c.1 c.2 p hpub
                esM.h sM hM_inj
              have hrunL := run_liftFSMulti0_inject_some (Pt := Pt) C encT idOf true c.1 c.2 p hpub
                esM.h sL hL_inj
              rw [hrunM, hrunL]
              simp only [Option.map_some, hwp, StateT.run_bind, StateT.run_get, StateT.run_modify,
                StateT.run_pure, pure_bind, Bool.false_and, Bool.false_eq_true,
                hlf_not, ↓reduceIte, Option.map_none, Option.getD_none, simulateQ_pure,
                hqep_f]
              let pos : Pos := ⟨P.other, t, idxOut⟩
              have htriv_eq : trivB1 t esM.g pos = trivB1 t esL.g pos :=
                _root_.CryptoGames.SM.Construction.DeliverForge.eraseSt_trivB1_l11 hs.herase.symm t pos
              rw [htriv_eq]
              cases htriv : trivB1 t esL.g pos with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, hinjFull]
                exact leAdd0_of_le_main (both_win_leOne C Dh encPt encT idOf qep l t k_fs
                  (cont (some .rejected)) _ _ (false, sM') hs.habL hs.habM rfl rfl herase_win)
              | true =>
                have hs' := dir2Sync_accept_at_t hs hsnd_le ht_le_t γ' σ' idxOut hinv'
                dsimp only at hs'
                rw [← hPo, ← hPr] at hs'
                simp only [↓reduceIte, commitE, hooksLocalFixed, hooksFSMulti, StateT.run_bind,
                  stateT_run_liftH, StateT.run_pure, pure_bind, StateT.run_modify,
                  Function.update_idem, accept_update_self, simulateQ_pure]
                exact hnext (some (.accepted t idxOut (some pmOut))) _ _ sM' sL' ss0 rs' hs'

private theorem dir2_injectE
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) {phase1 : Bool} (k_fs : BitVec 256)
    (P : Party) (c : Header Pt × Ct32)
    (cont : Option (RecvResult (MsgPt ℓ)) →
      SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (hnext : ∀ u esL' esM' sM' sL' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0' rs0' esL' esM' sM' sL' →
      LeRel phase1
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))
        (runMulti0 C Dh encPt encT idOf qep l t true (cont u) esM' (false, sL')))
    (hto2 : ∀ u esL' esM' sM' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0' rs0' esL' esM' sM' sL →
      LeOne
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    LeRel phase1
      (simulateQ lImpl
        ((_root_.CryptoGames.SM.Construction.DeliverForge.injectEB1 hkL qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c)).run esL) >>=
        fun r => runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont r.1) r.2)
      ((simulateQ (implM false)
        ((_root_.CryptoGames.SM.Construction.DeliverForge.injectEB1 (hkM false) qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c)).run esM)).run (false, sM) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t false (cont r.1.1) r.1.2 r.2)
      ((simulateQ (implM true)
        ((_root_.CryptoGames.SM.Construction.DeliverForge.injectEB1 (hkM true) qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c)).run esM)).run (false, sL) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t true (cont r.1.1) r.1.2 r.2) := by
  intro hkL hkM implM
  have hin_eq : esM.g.inTransit P.other c = esL.g.inTransit P.other c :=
    eraseSt_inTransit hs.herase.symm P.other c
  have hsafe_eq : esM.g.safeInj 2 = esL.g.safeInj 2 := by
    simp only [GameState.safeInj, hs.htL, hs.hepoch]
  cases hin : esL.g.inTransit P.other c with
  | some r =>
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hin_eq, hin, Option.isSome_some,
      Bool.or_true, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact hnext none esL esM sM sL ss0 rs0 hs
  | none =>
    cases hsafe : esL.g.safeInj 2 with
    | false =>
      unfold _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsafe_eq, hsafe, Bool.not_false,
        Bool.or_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact hnext none esL esM sM sL ss0 rs0 hs
    | true =>
      have htcur_eq : (esM.g.st P).tcur = (esL.g.st P).tcur := (hs.htcurM P).trans (hs.htcurL P).symm
      cases hsends : P.sendsIn c.1.1 with
      | true =>
        unfold _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
          hin_eq, hin, Option.isSome_none, hsafe_eq, hsafe, Bool.not_true, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte, vRecv, hs.hidL P, hs.hidM P, hsends, Bool.true_or,
          stateT_run_liftH, StateT.run_pure, simulateQ_pure,
          estate_eta_false esL hs.habL, estate_eta_false esM hs.habM]
        exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
      | false =>
        by_cases hgt : (esL.g.st P).tcur + 1 < c.1.1
        · have hdL : decide ((esL.g.st P).tcur + 1 < c.1.1) = true := decide_eq_true hgt
          have hdM : decide ((esM.g.st P).tcur + 1 < c.1.1) = true := by rw [htcur_eq]; exact hdL
          unfold _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
            hin_eq, hin, Option.isSome_none, hsafe_eq, hsafe, Bool.not_true, Bool.or_self,
            Bool.false_eq_true, ↓reduceIte, vRecv, hdL, hdM, Bool.or_true,
            stateT_run_liftH, StateT.run_pure, simulateQ_pure,
            estate_eta_false esL hs.habL, estate_eta_false esM hs.habM]
          exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
        · have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := Nat.le_of_not_lt hgt
          have hcL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false := by
            rw [hs.hidL P, hsends, Bool.false_or, decide_eq_false_iff_not]; exact hgt
          have hcM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
            rw [hs.hidM P, htcur_eq, hsends, Bool.false_or, decide_eq_false_iff_not]; exact hgt
          rw [injectEB1_to_tail hkL qep ⟨true, some (l - 1), t⟩ P c esL hs.habL hs.hwinL hin hsafe hcL,
              injectEB1_to_tail (hkM false) qep ⟨true, some (l - 1), t⟩ P c esM hs.habM hs.hwinM
                (hin_eq.trans hin) (hsafe_eq.trans hsafe) hcM,
              injectEB1_to_tail (hkM true) qep ⟨true, some (l - 1), t⟩ P c esM hs.habM hs.hwinM
                (hin_eq.trans hin) (hsafe_eq.trans hsafe) hcM]
          simpa only [hkL, hkM, implM] using
            (dir2_injectTail C Dh encPt encT idOf qep l t k_fs P c cont hs hin hsends ht_le hnext hto2)

private theorem dir2_deliverForgeE
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep l t : ℕ) {phase1 : Bool} (k_fs : BitVec 256)
    (P : Party) (c c' : Header Pt × Ct32)
    (cont : Option (RecvResult (MsgPt ℓ)) →
      SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0 rs0 esL esM sM sL)
    (hnext : ∀ u esL' esM' sM' sL' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t phase1 k_fs ss0' rs0' esL' esM' sM' sL' →
      LeRel phase1
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))
        (runMulti0 C Dh encPt encT idOf qep l t true (cont u) esM' (false, sL')))
    (hto2 : ∀ u esL' esM' sM' ss0' rs0',
      Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0' rs0' esL' esM' sM' sL →
      LeOne
        (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont u) esL')
        (runMulti0 C Dh encPt encT idOf qep l t false (cont u) esM' (false, sM'))) :
    let hkL := hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs
    let hkM := fun la => hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 ⟨false, some (l - 1), t⟩ false la
    let implM := fun la => pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))
    LeRel phase1
      (simulateQ lImpl
        ((_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 hkL qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c, c')).run esL) >>=
        fun r => runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
          (cont r.1) r.2)
      ((simulateQ (implM false)
        ((_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 (hkM false) qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c, c')).run esM)).run (false, sM) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t false (cont r.1.1) r.1.2 r.2)
      ((simulateQ (implM true)
        ((_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 (hkM true) qep t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (P, c, c')).run esM)).run (false, sL) >>=
        fun r => runMulti0 C Dh encPt encT idOf qep l t true (cont r.1.1) r.1.2 r.2) := by
  intro hkL hkM implM
  have hin_eq : esM.g.inTransit P.other c = esL.g.inTransit P.other c :=
    eraseSt_inTransit hs.herase.symm P.other c
  cases hin : esL.g.inTransit P.other c with
  | none =>
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte, hin_eq, hin, StateT.run_pure, simulateQ_pure]
    exact hnext none esL esM sM sL ss0 rs0 hs
  | some r =>
    have hin'_eq : esM.g.inTransit P.other c' = esL.g.inTransit P.other c' :=
      eraseSt_inTransit hs.herase.symm P.other c'
    have hcomp_eq : esM.g.comp = esL.g.comp := hs.hcomp
    cases hin' : esL.g.inTransit P.other c' with
    | some r' =>
      unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, hin_eq, hin, hin'_eq, hin',
        Option.isSome_some, Bool.true_or, StateT.run_pure, simulateQ_pure]
      exact hnext none esL esM sM sL ss0 rs0 hs
    | none =>
      cases hguard : (esL.g.comp.contains r.pos || (c.1 != c'.1)) with
      | true =>
        have hgL : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || (c.1 != c'.1)) = true := by
          rw [hin', Option.isSome_none, Bool.false_or]; exact hguard
        have hgM : ((esM.g.inTransit P.other c').isSome || esM.g.comp.contains r.pos || (c.1 != c'.1)) = true := by
          rw [hin'_eq, hin', hcomp_eq, Option.isSome_none, Bool.false_or]; exact hguard
        unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte, hin_eq, hin, hgL, hgM,
          StateT.run_pure, simulateQ_pure]
        exact hnext none esL esM sM sL ss0 rs0 hs
      | false =>
        have hcc' : (c.1 != c'.1) = false := (Bool.or_eq_false_iff.mp hguard).2
        have hc_hdr : c.1 = c'.1 := by simpa [bne_iff_ne] using hcc'
        obtain ⟨hr_mem, hr_snd, hr_ct⟩ := inTransit_mem_trans hin
        have hr_wf := hs.htrans_wf r hr_mem
        have hr_ep : r.pos.epoch = c'.1.1 := by rw [← hc_hdr, ← hr_ct, hr_wf.1]
        have hPother_s : P.other = Party.senderOf c'.1.1 := by
          rw [← hr_ep, ← hr_snd, hr_wf.2]
        have hsends_f : P.sendsIn c'.1.1 = false := sendsIn_false_of_other_senderOf hPother_s
        have htcur_eq : (esM.g.st P).tcur = (esL.g.st P).tcur := (hs.htcurM P).trans (hs.htcurL P).symm
        by_cases hgt : (esL.g.st P).tcur + 1 < c'.1.1
        · have hgL : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || (c.1 != c'.1)) = false := by
            rw [hin', Option.isSome_none, Bool.false_or]; exact hguard
          have hgM : ((esM.g.inTransit P.other c').isSome || esM.g.comp.contains r.pos || (c.1 != c'.1)) = false := by
            rw [hin'_eq, hin', hcomp_eq, Option.isSome_none, Bool.false_or]; exact hguard
          have hdL : decide ((esL.g.st P).tcur + 1 < c'.1.1) = true := decide_eq_true hgt
          have hdM : decide ((esM.g.st P).tcur + 1 < c'.1.1) = true := by rw [htcur_eq]; exact hdL
          unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hs.habL, hs.habM, hs.hwinL, hs.hwinM,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hin_eq, hin, hgL, hgM,
            vRecv, hdL, hdM, Bool.or_true, stateT_run_liftH, StateT.run_pure, simulateQ_pure,
            estate_eta_false esL hs.habL, estate_eta_false esM hs.habM]
          exact hnext (some .rejected) esL esM sM sL ss0 rs0 hs
        · have ht_le : c'.1.1 ≤ (esL.g.st P).tcur + 1 := Nat.le_of_not_lt hgt
          have hcL : ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) = false := by
            rw [hs.hidL P, hsends_f, Bool.false_or, decide_eq_false_iff_not]; exact hgt
          have hcM : ((esM.g.st P).id.sendsIn c'.1.1 || decide ((esM.g.st P).tcur + 1 < c'.1.1)) = false := by
            rw [hs.hidM P, htcur_eq, hsends_f, Bool.false_or, decide_eq_false_iff_not]; exact hgt
          have hguardM : (esM.g.comp.contains r.pos || (c.1 != c'.1)) = false := by
            rw [hcomp_eq]; exact hguard
          rw [deliverForgeEB1_to_tail hkL qep ⟨true, some (l - 1), t⟩ P c c' r esL
                hs.habL hs.hwinL hin hin' hguard hr_ep hcL,
              deliverForgeEB1_to_tail (hkM false) qep ⟨true, some (l - 1), t⟩ P c c' r esM
                hs.habM hs.hwinM (hin_eq.trans hin) (hin'_eq.trans hin') hguardM hr_ep hcM,
              deliverForgeEB1_to_tail (hkM true) qep ⟨true, some (l - 1), t⟩ P c c' r esM
                hs.habM hs.hwinM (hin_eq.trans hin) (hin'_eq.trans hin') hguardM hr_ep hcM]
          simpa only [hkL, hkM, implM] using
            (dir2_injectTail C Dh encPt encT idOf qep l t k_fs P c' cont hs hin' hsends_f ht_le hnext hto2)

private theorem dir2_run_phase2
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (k_fs : BitVec 256)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (hsh : SendMsgsOkDF (fun m : MsgPt ℓ => atomicShortPubB m.1) oa)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t false k_fs ss0 rs0 esL esM sM sL) :
    LeOne
      (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
        oa esL)
      (runMulti0 C Dh encPt encT idOf qep l t false oa esM (false, sM)) := by
  induction oa using OracleComp.inductionOn generalizing esL esM sM sL ss0 rs0 with
  | pure a =>
    rw [runLocAtFixedDFShiftedDir2Paper_pure, runMulti0_pure]
    simp [LeOne, authOut, hs.hwinL]
  | query_bind q cont ih =>
    have ⟨hok_send, hsh'⟩ := sendMsgsOkDF_query_bind (fun m : MsgPt ℓ => atomicShortPubB m.1) q cont hsh
    rw [runLocAtFixedDFShiftedDir2Paper_query_bind,
        runMulti0_query_bind C Dh encPt encT idOf qep l t false q cont esM (false, sM)]
    unfold stepLFixedDFShiftedDir2Paper
    rcases q with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · have hL : (implEDFShiftedB1 l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (2 + 0) qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip
          (⟨false, some (l - 1), t⟩ : Mode).tStar
          (moAuth ⟨false, some (l - 1), t⟩).cfg (moAuth ⟨false, some (l - 1), t⟩).policy (.inl n)).run esL =
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n)) >>=
          fun u => pure (u, esL)) := by
        simp [implEDFShiftedB1, QueryImpl.add_apply_inl, coinsE]
      have hM : (implEDFShiftedPaperGen true l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
            ⟨false, some (l - 1), t⟩ false false)
          2 qep maxForwardJumps t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy (.inl n)).run esM =
        (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32) (.inl n)) >>=
          fun u => pure (u, esM)) := by
        simp [implEDFShiftedPaperGen, QueryImpl.add_apply_inl, coinsE]
      rw [hL, hM, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, pubFsImpl0_inl_run, bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ =>
        ih u (hsh' u) hs
    · have hm : atomicShortPubB m.1 = true := hok_send P m rc rfl
      dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact dir2_transmitE C Dh encPt encT idOf hℓ qep l t ht2 hl k_fs P m rc hm cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' => ih u (hsh' u) hs')
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      have hmo : moAuth ⟨false, some (l - 1), t⟩ = (⟨true, some (l - 1), t⟩ : Mode) := rfl
      rw [hmo, Nat.add_zero, challE_auth_run, challE_auth_run]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih none (hsh' none) hs
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      obtain ⟨u, esL', esM', sM', sL', rs0', hs', hL, hM, _⟩ :=
        dir2_deliverE C Dh hD encPt encT idOf hℓ qep l t k_fs hs P c
      have hmax : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
      rw [hmax, hL, hM, pure_bind, pure_bind]
      exact ih u (hsh' u) hs'
    · dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, injectEGen, ↓reduceIte,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact dir2_injectE C Dh encPt encT idOf qep l t k_fs P c cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' => ih u (hsh' u) hs')
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      have hmo : (moAuth ⟨false, some (l - 1), t⟩).policy = (⟨true, some (l - 1), t⟩ : Mode).policy := rfl
      rw [hmo]
      rcases dir2_corrE_cases C Dh encPt encT idOf qep l t ht2 hl k_fs hs P with
        ⟨esL', hab', hL⟩ | ⟨u, esL', esM', hs', hL, hM⟩ | ⟨u, esL', esM', sM', hs', hL, hM⟩
      · rw [hL, pure_bind]
        exact leOne_of_lhs_zero (evalDist_runLocAtFixed_eq_zero_of_abort (dhScheme Dh)
          (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) qep l
          ⟨false, some (l - 1), t⟩ k_fs (cont none) esL' hab')
      · rw [hL, hM false (false, sM), pure_bind, pure_bind]
        exact ih u (hsh' u) hs'
      · rw [hL, hM, pure_bind, pure_bind]
        exact ih u (hsh' u) hs'
    · dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, deliverForgeEGen, ↓reduceIte,
        QueryImpl.add_apply_inr]
      exact dir2_deliverForgeE C Dh encPt encT idOf qep l t k_fs P c c' cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' => ih u (hsh' u) hs')

private theorem dir2_run_phase1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (k_fs : BitVec 256)
    (oa : SMCompDF (DDHSt Pt) Pt (BitVec 256) SS256 RS256 (MsgPt ℓ) (BitVec 256) Ct32 Bool)
    (hsh : SendMsgsOkDF (fun m : MsgPt ℓ => atomicShortPubB m.1) oa)
    {ss0 rs0 esL esM sM sL}
    (hs : Dir2Sync (Pt := Pt) (ℓ := ℓ) C encT idOf qep t true k_fs ss0 rs0 esL esM sM sL) :
    LeAdd0
      (runLocAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0 qep l ⟨false, some (l - 1), t⟩ 0 k_fs
        oa esL)
      (runMulti0 C Dh encPt encT idOf qep l t false oa esM (false, sM))
      (runMulti0 C Dh encPt encT idOf qep l t true oa esM (false, sL)) := by
  induction oa using OracleComp.inductionOn generalizing esL esM sM sL ss0 rs0 with
  | pure a =>
    rw [runLocAtFixedDFShiftedDir2Paper_pure, runMulti0_pure, runMulti0_pure]
    simp [LeAdd0, authOut, hs.hwinL]
  | query_bind q cont ih =>
    have ⟨hok_send, hsh'⟩ := sendMsgsOkDF_query_bind (fun m : MsgPt ℓ => atomicShortPubB m.1) q cont hsh
    rw [runLocAtFixedDFShiftedDir2Paper_query_bind,
        runMulti0_query_bind C Dh encPt encT idOf qep l t false q cont esM (false, sM),
        runMulti0_query_bind C Dh encPt encT idOf qep l t true q cont esM (false, sL)]
    unfold stepLFixedDFShiftedDir2Paper
    rcases q with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · have hL : (implEDFShiftedB1 l
          (hooksLocalFixed (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) ⟨false, some (l - 1), t⟩ 0 k_fs)
          (2 + 0) qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip
          (⟨false, some (l - 1), t⟩ : Mode).tStar
          (moAuth ⟨false, some (l - 1), t⟩).cfg (moAuth ⟨false, some (l - 1), t⟩).policy (.inl n)).run esL =
        (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n)) >>=
          fun u => pure (u, esL)) := by
        simp [implEDFShiftedB1, QueryImpl.add_apply_inl, coinsE]
      have hM : ∀ la, (implEDFShiftedPaperGen true l
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 0
            ⟨false, some (l - 1), t⟩ false la)
          2 qep maxForwardJumps t
          (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy (.inl n)).run esM =
        (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS256 RS256 Pt (MsgPt ℓ) Ct32) (.inl n)) >>=
          fun u => pure (u, esM)) := fun _ => by
        simp [implEDFShiftedPaperGen, QueryImpl.add_apply_inl, coinsE]
      rw [hL, hM false, hM true, simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, pubFsImpl0_inl_run, bind_assoc, pure_bind]
      exact leAdd0_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ =>
        ih u (hsh' u) hs
    · have hm : atomicShortPubB m.1 = true := hok_send P m rc rfl
      dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact dir2_transmitE C Dh encPt encT idOf hℓ qep l t ht2 hl k_fs P m rc hm cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' =>
          dir2_run_phase2 C Dh hD encPt encT idOf hℓ qep l t ht2 hl k_fs (cont u) (hsh' u) hs')
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      have hmo : moAuth ⟨false, some (l - 1), t⟩ = (⟨true, some (l - 1), t⟩ : Mode) := rfl
      rw [hmo, Nat.add_zero, challE_auth_run, challE_auth_run, challE_auth_run]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih none (hsh' none) hs
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      obtain ⟨u, esL', esM', sM', sL', rs0', hs', hL, hM, hLa⟩ :=
        dir2_deliverE C Dh hD encPt encT idOf hℓ qep l t k_fs hs P c
      have hmax : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
      rw [hmax, hL, hM, hLa rfl, pure_bind, pure_bind, pure_bind]
      exact ih u (hsh' u) hs'
    · dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, injectEGen, ↓reduceIte,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact dir2_injectE C Dh encPt encT idOf qep l t k_fs P c cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' =>
          dir2_run_phase2 C Dh hD encPt encT idOf hℓ qep l t ht2 hl k_fs (cont u) (hsh' u) hs')
    · simp only [implEDFShiftedB1, implEDFShiftedPaperGen, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      have hmo : (moAuth ⟨false, some (l - 1), t⟩).policy = (⟨true, some (l - 1), t⟩ : Mode).policy := rfl
      rw [hmo]
      rcases dir2_corrE_cases C Dh encPt encT idOf qep l t ht2 hl k_fs hs P with
        ⟨esL', hab', hL⟩ | ⟨u, esL', esM', hs', hL, hM⟩ | ⟨u, esL', esM', sM', hs', hL, hM⟩
      · rw [hL, pure_bind]
        exact leAdd0_of_lhs_zero (evalDist_runLocAtFixed_eq_zero_of_abort (dhScheme Dh)
          (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) qep l
          ⟨false, some (l - 1), t⟩ k_fs (cont none) esL' hab')
      · rw [hL, hM false (false, sM), hM true (false, sL), pure_bind, pure_bind, pure_bind]
        exact ih u (hsh' u) hs'
      · rw [hL, hM, pure_bind, pure_bind]
        exact leAdd0_of_le_main
          (dir2_run_phase2 C Dh hD encPt encT idOf hℓ qep l t ht2 hl k_fs (cont u) (hsh' u) hs')
    · dsimp only [SMSpecDF, _root_.CryptoGames.SM.Construction.DeliverForge.specDF,
        _root_.CryptoGames.SM.specDF, _root_.CryptoGames.SM.spec,
        Sum.elim_inl, Sum.elim_inr] at cont hsh' ih ⊢
      simp only [implEDFShiftedB1, implEDFShiftedPaperGen, deliverForgeEGen, ↓reduceIte,
        QueryImpl.add_apply_inr]
      exact dir2_deliverForgeE C Dh encPt encT idOf qep l t k_fs P c c' cont hs
        (fun u _ _ _ _ _ _ hs' => ih u (hsh' u) hs')
        (fun u _ _ _ _ _ hs' =>
          dir2_run_phase2 C Dh hD encPt encT idOf hℓ qep l t ht2 hl k_fs (cont u) (hsh' u) hs')

private theorem localAuthAtFixed_leAdd_redFSAuthMulti0
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (_hinj : Function.Injective encT) (_hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (k_fs : BitVec 256) (b_fs : Bool)
    (A : AdversaryDF (Fig8St Pt) (MsgPt ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : MsgPt ℓ => atomicShortPubB m.1) A) :
    LeAdd0
      (localAuthAtFixedDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep 0 l k_fs (some (l - 1)) t A)
      (Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t false A)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs)))
      (Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t true A)).run
        (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))) :=
  dir2Sync_init C Dh encPt encT idOf lam qep l t ht2 k_fs b_fs A fun _ _ _ _ _ _ hs =>
    dir2_run_phase1 C Dh hD encPt encT idOf hℓ qep l t ht2 hl k_fs A hsh hs

end Dir2PrivateHelpers

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


/-- `B1` (`localAuthDFShiftedDir2Paper`) post-PRNG local game bounded by the two-mode
(`la = false` + `la = true`) `multiSessRealWinProb` of `redFSAuthDFShiftedDir2PaperMulti`. -/
theorem localAuthDFShiftedDir2Paper_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A)
    𝒟[localAuthDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep l (some (l - 1)) t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  intro Adv
  let cka := dhScheme Dh
  let prng := CryptoGames.Ratchet.rootPRNG C.F encPt
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let ideal := lIdeal C protoSignalCodec ℓ encT
  let ae := lAeadR C protoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let red := fun la => redFSAuthDFShiftedDir2PaperMulti cka prng fs lam qep l t la A
  have hoff_red : ∀ la, (red la).IsQueryBoundP (fun x => sessOffRange 1 x = true) 0 :=
    fun la => redFSAuthDFShiftedDir2PaperMulti_offRange_one cka prng fs lam ht2 la A
  have hoff_adv : ∀ la, (Adv la).IsQueryBoundP (fun x => sessOffRange 1 x = true) 0 :=
    fun la => multiSessPubToAD_offRange protoSignalCodec (red la) 1 (hoff_red la)
  refine (localAuthDFShiftedDir2Paper_le_at_zero cka prng fs lam q qep l t ht2 A hq).trans ?_
  refine (localAuthAtDFShiftedDir2Paper_le_localAuthAtFixedDFShiftedDir2Paper cka prng fs lam 0 qep
    0 l (some (l - 1)) t A).trans ?_
  let seed0 : ProbComp (SessHSt Pt ℓ) :=
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun k =>
        pure (_root_.CryptoGames.FSAEAD.Thm5.hInit b (.seed k))
  have hrhs : ∀ la,
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun k_fs =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b_fs =>
            Prod.fst <$> (simulateQ (pubFsImpl0 (fsImpl ideal ae G maxForwardJumps
                (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la))) (red la)).run
              (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))] {true} ≤
        multiSessRealWinProb C ℓ encT idOf Adv la := by
    intro la
    let impl := fsImpl ideal ae G maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)
    have hswap :
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun k_fs =>
            ($ᵗ Bool : ProbComp Bool) >>= fun b_fs =>
              Prod.fst <$> (simulateQ (pubFsImpl0 impl) (red la)).run
                (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))] =
          𝒟[seed0 >>= fun v =>
              Prod.fst <$> (simulateQ (sessLift (lazyInit seed0 impl)) (Adv la)).run
                (Function.update (fun _ : ℕ => (none : Option (SessHSt Pt ℓ))) 0 (some v))] := by
      have hdeq := _root_.CryptoGames.Lazy.DEq.swap
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) ($ᵗ Bool : ProbComp Bool)
        (fun k_fs b_fs => Prod.fst <$> (simulateQ (pubFsImpl0 impl) (red la)).run
          (false, _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs)))
      rw [hdeq.evalDist_eq]
      dsimp only [seed0]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b_fs => ?_
      refine evalDist_bind_congr ($ᵗ BitVec 256 : ProbComp (BitVec 256)) _ _ fun k_fs => ?_
      have hsim := simulateQ_sessLift_multiSessPubToAD_eq_pubFsImpl0 impl (red la) (hoff_red la)
        (fun _ => _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))
      have hoff0 := sessLift_lazyInit_eq_of_offRange seed0 impl 1 (Adv la) (hoff_adv la)
        (fun _ => _root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))
        (Function.update (fun _ : ℕ => (none : Option (SessHSt Pt ℓ))) 0
          (some (_root_.CryptoGames.FSAEAD.Thm5.hInit b_fs (.seed k_fs))))
        (fun i hi => by
          have hi0 : i = 0 := by omega
          subst hi0; simp)
      exact congrArg evalDist (hsim.symm.trans hoff0.symm)
    rw [hswap, sessLift_lazyInit_step_evalDist seed0 impl (Adv la) (fun _ => none) 0 rfl]
    have hbd := _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_lazy_boolDist_le
      seed0 impl fsInit impl 1 (Adv la) (hoff_adv la)
    have hsum0 : (∑ k ∈ Finset.range 1,
        𝒟[seed0 >>= fun s => Prod.fst <$> (simulateQ (fwd impl)
            (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
              (lazyInit seed0 impl) (lazyInit fsInit impl)
              (Adv la) (fun _ => none) (fun _ => none) k)).run s].boolDist
          𝒟[fsInit >>= fun s => Prod.fst <$> (simulateQ (fwd impl)
            (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
              (lazyInit seed0 impl) (lazyInit fsInit impl)
              (Adv la) (fun _ => none) (fun _ => none) k)).run s]) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hseed_eq :
          𝒟[seed0 >>= fun s => Prod.fst <$> (simulateQ (fwd impl)
              (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
                (lazyInit seed0 impl) (lazyInit fsInit impl)
                (Adv la) (fun _ => none) (fun _ => none) k)).run s] =
            𝒟[fsInit >>= fun s => Prod.fst <$> (simulateQ (fwd impl)
              (_root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
                (lazyInit seed0 impl) (lazyInit fsInit impl)
                (Adv la) (fun _ => none) (fun _ => none) k)).run s] := by
        let B := _root_.CryptoVerification.E2E.Signed.SessionRouter.sessAdv
          (lazyInit seed0 impl) (lazyInit fsInit impl) (Adv la) (fun _ => none) (fun _ => none) k
        change 𝒟[seed0 >>= fun s => Prod.fst <$> (simulateQ (fwd impl) B).run s] =
          𝒟[fsInit >>= fun s => Prod.fst <$> (simulateQ (fwd impl) B).run s]
        dsimp only [seed0, impl]
        unfold fsInit
        simp only [bind_assoc, pure_bind, _root_.CryptoVerification.E2E.Signed.SessionFS.fwd_fsImpl]
        refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
        let P := _root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la
        let D := _root_.CryptoGames.FSAEAD.Thm5.DG G
        let fill := _root_.CryptoGames.FSAEAD.Thm5.seedFill
          (CK := BitVec 256) (MK := BitVec 256)
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
          (C := LibsignalCiphertextWithSalt32) 0
        have hI := _root_.CryptoGames.FSAEAD.Thm5.seedFill_idem
          (CK := BitVec 256) (MK := BitVec 256)
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
          (C := LibsignalCiphertextWithSalt32) 0
        have hK : ∀ h h' : _root_.CryptoGames.FSAEAD.Thm5.HState
            (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
            (Plain ℓ) LibsignalCiphertextWithSalt32,
            h.keys.length = h'.keys.length → fill h = fill h' := by
          intro h h' hl; funext sl; cases sl <;> simp [fill, _root_.CryptoGames.FSAEAD.Thm5.seedFill, hl]
        have hGen := _root_.CryptoGames.FSAEAD.Thm5.comm_genStep_seed
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
          (C := LibsignalCiphertextWithSalt32) G P 0 le_rfl
        have hRev := _root_.CryptoGames.FSAEAD.Thm5.comm_reveal_seed
          (CK := BitVec 256) (MK := BitVec 256)
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
          (C := LibsignalCiphertextWithSalt32) 0
        have hc := _root_.CryptoGames.Lazy.Comm.simulateQ hI
          (_root_.CryptoGames.FSAEAD.Thm5.comm_impl ideal ae G maxForwardJumps P D hI hK hGen hRev) B
          (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown)
        have hdeq : _root_.CryptoGames.Lazy.DEq
            ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
              (_root_.CryptoGames.Lazy.fillSt fill (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown) >>=
                (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxForwardJumps P D
                  (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))) B).run))
            ((fun z => Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1) <$>
              (simulateQ (_root_.CryptoGames.FSAEAD.Thm5.implWith ideal ae G maxForwardJumps P D none) B).run
                (_root_.CryptoGames.FSAEAD.Thm5.hInit b .unknown)) :=
          (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
            Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _).symm.trans
            ((_root_.CryptoGames.Lazy.DEq.map hc _).trans
              (_root_.CryptoGames.Lazy.map_fillOut (fill := fill)
                Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit _))
        have h0 : _root_.CryptoGames.Lazy.fillSt fill
            (_root_.CryptoGames.FSAEAD.Thm5.hInit (CK := BitVec 256) (MK := BitVec 256)
              (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ)
              (C := LibsignalCiphertextWithSalt32) b .unknown) =
            (($ᵗ BitVec 256) >>= fun k => pure (_root_.CryptoGames.FSAEAD.Thm5.hInit b (.seed k))) := by
          simp [fill, _root_.CryptoGames.Lazy.fillSt, _root_.CryptoGames.FSAEAD.Thm5.seedFill,
            _root_.CryptoGames.FSAEAD.Thm5.hInit, map_eq_bind_pure_comp]
        have heq := _root_.CryptoGames.Lazy.DEq.evalDist_eq hdeq
        rw [h0] at heq
        simpa only [Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, P, D] using heq
      rw [hseed_eq]
      exact MeasureTheory.Measure.boolDist_self _
    rw [hsum0] at hbd
    unfold multiSessRealWinProb
    calc
      _ ≤ 𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit fsInit impl)) (Adv la)).run
            (fun _ => none)] {true} +
          𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit seed0 impl)) (Adv la)).run
            (fun _ => none)].boolDist
          𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit fsInit impl)) (Adv la)).run
            (fun _ => none)] := MeasureTheory.Measure.apply_true_le_add_boolDist _ _
      _ ≤ _ + 0 := add_le_add le_rfl hbd
      _ = _ := add_zero _
  refine (leAdd0_bind ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fun k_fs _ =>
    leAdd0_bind_dummy_loc ($ᵗ Bool : ProbComp Bool) fun b_fs _ =>
      localAuthAtFixed_leAdd_redFSAuthMulti0 C Dh hD encPt encT hinj hdum idOf lam hℓ
        qep l t ht2 hl k_fs b_fs A hsh).trans
    (add_le_add (hrhs false) (hrhs true))


end LibsignalBridges

end

end Computational.Proofs.E2E.SessionAuthMultiReal
