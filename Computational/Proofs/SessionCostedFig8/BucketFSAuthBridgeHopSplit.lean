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
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopAtomic
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthBridge
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.SM.Theorem1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSplit

public section

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState withPub)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt hp hInit)
open _root_.CryptoGames.SM (Pos GameState Record RecvResult
  healedBy ltOpt maxOpt lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (PartyState Header SchemeAdversary healEpoch
  FSMultiSpec FSMultiBook mkParties realParty sampleT)
open _root_.CryptoGames.SM.Engine (Hooks HM EState VP Ctx vSend vSendStep1 vSend_eq_bind
  vRecv vRecvStep1 vRecv_eq_bind run_liftH_bind abortE commitE deliverE injectE)
open _root_.CryptoGames.SM.Construction.AuthL11 (lImpl nilSpec eraseSt eraseSt_win eraseSt_corrAllowed)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  dummyKey lChainPRG lAeadR lIdeal lFS lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit multiSessSpec sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (badSendMsg_query_bind_step
  badSendMsg_transmit_false)
open _root_.ReductionDsl (isGameQuery)
open Computational.Proofs.E2E.SessionAuthBridge (MultiSessFsAdv multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg
  LocalBucketAuthState rootLocalBucketAuth hooksLocalBucketAuth hooksLocalBucketAuthMain
  initLocalBucketAuth implLocalBucketAuthGen localAuthBucketMainPar)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (redFSAuthMultiBucketShallow
  redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  lookupMultiBucketF regSessMultiBucket regSessOptMultiBucket validGuessBucketParAuth
  rootFSMultiBucketAuth hooksFSMultiBucketAuth initFSMultiBucketAuth implFSMultiBucketAuth
  redFSAuthMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (sIdxMain mSessMain keySlotSpec
  sIdxMain_inj healedBy_of_not_postLeak lFS_receive_eq
  pubFsMultiImpl_corruptSender_run pubFsMultiImpl_inject_none_run pubFsMultiImpl_inject_some_run
  LeAdd LeOne leAdd_of_lhs_zero leAdd_of_le_main leAdd_of_la_one leOne_of_lhs_zero
  leAdd_bind leAdd_bind_dummy_loc leOne_bind
  sampleVec multiFsEager_le_real isQueryBoundP_sessOffRange_of_ge_zero
  pubFsMultiImpl simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl
  pubFsMultiImpl_inl_run)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (mainParOut
  halted_leOne lfWin_aborted_eq_one SessHSt ActiveSessInv activeSessInv_init
  activeSessInv_corruptSender activeSessInv_inject_phase2 activeSessInv_inject_phase1)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot (LocalMainSlotState
  deliverE_localMain_pure injectE_localMain_pure sim_sampleT_lImpl
  sampleOrSlot lookupLocalMainSlotF rootLocalMainSlot hooksLocalMainSlot
  initLocalMainSlot implLocalMainSlot localAuthBucketMainSlot
  keySlotFixedImpl localAuthBucketMainPar_eq_eager_ks sim_sampleT_fixed)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopAtomic (
  redFSAuthMultiBucket_main_atomic_eq)

/-! ## 0. Shared Coupling Invariant & Continuation Runners -/

private theorem sim_sampleT_run_of_inl {ι S : Type} {G : OracleSpec.{0, 0} ι} {α : Type} [SampleableType α]
    (impl : QueryImpl (unifSpec + G) (StateT S ProbComp))
    (hinl : ∀ (n : ℕ) (s : S),
      (impl (.inl n)).run s = (($ᵗ Fin (n + 1) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (st : S) :
    (simulateQ impl (sampleT (tspec := G) α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  suffices h1 : ∀ (oa : ProbComp α),
      (simulateQ impl (liftM oa : OracleComp (unifSpec + G) α)).run st =
      (oa >>= fun a => pure (a, st)) from
    h1 ($ᵗ α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind t k ih =>
    change (simulateQ impl
      ((liftM (OracleSpec.query (spec := unifSpec + G) (.inl t)) : OracleComp (unifSpec + G) _) >>=
        fun u => (liftM (k u) : OracleComp (unifSpec + G) α))).run st = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, hinl]
    change (($ᵗ Fin (t + 1) : ProbComp _) >>= fun u => pure (u, st)) >>= _ =
      ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= k) >>= _
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem sim_sampleT_pubFs_run {Pt : Type} {ℓ : ℕ} {α : Type} [SampleableType α]
    (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec
      (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (SessHSt Pt ℓ) ProbComp))
    (st : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) :
    (simulateQ (pubFsMultiImpl impl)
      (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) :=
  sim_sampleT_run_of_inl (pubFsMultiImpl impl) (fun n s => pubFsMultiImpl_inl_run impl n s) st

private abbrev LocESt (Pt : Type) (ℓ : ℕ) :=
  EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
    (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)

private abbrev SideESt (Pt : Type) (ℓ : ℕ) :=
  EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
    (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))

private structure CoupledInv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ q qep : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256)))
    (esLoc : LocESt Pt ℓ) (esM esL : SideESt Pt ℓ)
    (winEp : Option ℕ) (tblM tblL : ℕ → SessHSt Pt ℓ) : Prop where
  habort_loc : esLoc.abort = false
  habort_M : esM.abort = false
  hwin_loc : esLoc.g.win = false
  hwe : winEp = none
  herase : eraseSt esM.g = eraseSt esLoc.g
  hep_le : ∀ Q, esLoc.g.epoch Q ≤ esLoc.g.epoch Q.other + 1
  hep_sends : ∀ Q, esLoc.g.epoch Q.other < esLoc.g.epoch Q → Q.sendsIn (esLoc.g.epoch Q) = true
  hphase1 : phase1 = true →
    postLeak tL esLoc.g = false ∧ esL = esM ∧ esM.h.lfWin = false ∧
    (∀ t0, actEp t0 ≠ none → ((esM.h.book (sIdxMain q tL t0)).getD {}).sCorr = false)
  hphase2 : phase1 = false →
    ∃ cur, esLoc.g.tL = some cur ∧ ltOpt tL cur = true ∧ ∀ t0, actEp t0 ≠ none → t0 ≤ cur
  hparty_id : ∀ P, (esLoc.g.st P).id = P ∧ (esM.g.st P).id = P
  hparty_tcur : ∀ P, (esLoc.g.st P).tcur = esLoc.g.epoch P ∧ (esM.g.st P).tcur = (esLoc.g.st P).tcur
  hparty_base : ∀ P, (esM.g.st P).γ = (esLoc.g.st P).γ ∧
    (esM.g.st P).curCkaMsg = (esLoc.g.st P).curCkaMsg ∧
    (esM.g.st P).root = (esLoc.g.st P).root
  htcur_le : ∀ P, (esLoc.g.st P).tcur + rem ≤ q
  hvR_gt : ∀ P t, (esLoc.g.st P).tcur < t → (esLoc.g.st P).vR t = none ∧ (esM.g.st P).vR t = none
  hvS : ∀ P, match (esLoc.g.st P).vS with
    | none => (esM.g.st P).vS = none ∧ P.sendsIn (esLoc.g.st P).tcur = false
    | some ss => ∃ ts, ts ≤ (esLoc.g.st P).tcur ∧ P.sendsIn ts = true ∧
      (P.sendsIn (esLoc.g.st P).tcur = true → ts = (esLoc.g.st P).tcur) ∧
      match actEp ts with
      | none => (esM.g.st P).vS = some (.inl ss)
      | some (ssA, _) => ss = ssA ∧ (esM.g.st P).vS = some (.inr (sIdxMain q tL ts))
  hvR : ∀ P t, match (esLoc.g.st P).vR t with
    | none => (esM.g.st P).vR t = none
    | some rs => P.sendsIn t = false ∧ t ≤ (esLoc.g.st P).tcur ∧ match actEp t with
      | none => (esM.g.st P).vR t = some (.inl rs)
      | some (_, rsA) => rs = rsA ∧ (esM.g.st P).vR t = some (.inr (sIdxMain q tL t))
  hcache : ∀ t,
    (esLoc.h.loc.cache t = none ∧ esM.h.cache t = none) ∨
    (1 ≤ t ∧ t ≤ (esLoc.g.st (Party.senderOf t)).tcur ∧
      ∃ Tc σc kVal,
        esLoc.h.loc.cache t = some (Tc, σc, kVal) ∧
        match actEp t with
        | none => esM.h.cache t = some (Tc, σc, kVal, none)
        | some (_, rsA) =>
          kVal = ks (sIdxMain q tL t) ∧
          (∃ kM, esM.h.cache t = some (Tc, σc, kM, some (sIdxMain q tL t))) ∧
          ((esLoc.g.st (Party.receiverOf t)).vR t = none →
            rsA = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal))
  hfuture : ∀ t, (esLoc.g.st (Party.senderOf t)).tcur < t →
    actEp t = none ∧ esLoc.h.loc.cache t = none ∧ esM.h.cache t = none ∧
    esLoc.h.loc.fTable t = [] ∧ esM.h.fTable t = [] ∧ esM.h.sessions t = []
  hact : ∀ t0 ssLoc rsLoc, actEp t0 = some (ssLoc, rsLoc) →
    healEpoch tL ≤ t0 ∧ t0 ≤ qep + 1 ∧ validGuessBucketParAuth 1 tL par t0 = true ∧
    t0 ≤ (esLoc.g.st (Party.senderOf t0)).tcur ∧
    let sIdx := sIdxMain q tL t0
    let bk := (esM.h.book sIdx).getD {}
    ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) ssLoc rsLoc bk (tblM sIdx) (tblL sIdx) ∧
    ((esLoc.g.st (Party.senderOf t0)).tcur = t0 → esLoc.g.idx (Party.senderOf t0) = bk.fsCount) ∧
    bk.fsTrans = (esLoc.g.trans.filter (fun r => r.pos.epoch == t0)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2))
  hunalloc : ∀ sIdx, sIdx < mSessMain q qep tL →
    (∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp t0 = none) →
    esLoc.h.usedSlot sIdx = false ∧ esM.h.book sIdx = none ∧
    tblM sIdx = hInit (bs sIdx) (.seed (ks sIdx)) ∧
    (phase1 = true → tblL sIdx = hInit (bs sIdx) (.seed (ks sIdx)))
  htrans : ∀ r ∈ esLoc.g.trans,
    r.pos.epoch = r.ct.1.1 ∧ r.pos.sender = Party.senderOf r.pos.epoch ∧
    r.pos.epoch ≤ (esLoc.g.st r.pos.sender).tcur

private theorem CoupledInv.mono_rem {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ q qep : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {tL : Option ℕ} {par : Bool} {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem rem' : ℕ}
    {actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem actEp esLoc esM esL winEp tblM tblL)
    (hrem : rem' ≤ rem) :
    CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp esLoc esM esL winEp tblM tblL :=
  { hinv with htcur_le := fun P => (Nat.add_le_add_left hrem _).trans (hinv.htcur_le P) }

private abbrev Fig8Dom (Pt : Type) (ℓ : ℕ) :=
  unifSpec + _root_.CryptoGames.SM.spec (Fig8St Pt)
    (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

private def runLocCont {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256)
    (oa : OracleComp (Fig8Dom Pt ℓ) Bool) (esLoc : LocESt Pt ℓ) (winEp : Option ℕ) : ProbComp Bool :=
  simulateQ (keySlotFixedImpl ks) (do
    let (_, es, we) ← (simulateQ (implLocalMainSlot
      (hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 q qep (mSessMain q qep tL) tL par)
      1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL) oa).run (esLoc, winEp)
    return mainParOut 3 tL par es we)

private def runSideCont {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (oa : OracleComp (Fig8Dom Pt ℓ) Bool)
    (esS : SideESt Pt ℓ) (winEp : Option ℕ) (tbl : ℕ → SessHSt Pt ℓ) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) (do
    let (_, es, we) ← (simulateQ (implFSMultiBucketAuth
      (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
      1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL) oa).run (esS, winEp)
    if la then return es.h.lfWin else return mainParOut 3 tL par es we)).run (fun _ => false, tbl)

private theorem runLocCont_step {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (i : (Fig8Dom Pt ℓ).Domain)
    (k : (Fig8Dom Pt ℓ).Range i → OracleComp (Fig8Dom Pt ℓ) Bool) (esLoc : LocESt Pt ℓ) (winEp : Option ℕ) :
    runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) i) >>= k) esLoc winEp =
    (do
      let p ← simulateQ (keySlotFixedImpl ks)
        ((implLocalMainSlot
          (hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 q qep (mSessMain q qep tL) tL par)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip tL i).run (esLoc, winEp))
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k p.1) p.2.1 p.2.2) := by
  unfold runLocCont
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
  rw [StateT.run_bind, bind_assoc, simulateQ_bind]

private theorem runSideCont_step {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (i : (Fig8Dom Pt ℓ).Domain)
    (k : (Fig8Dom Pt ℓ).Range i → OracleComp (Fig8Dom Pt ℓ) Bool)
    (esS : SideESt Pt ℓ) (winEp : Option ℕ) (tbl : ℕ → SessHSt Pt ℓ) :
    runSideCont C Dh encPt encT idOf ℓ q qep tL par la
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) i) >>= k) esS winEp tbl =
    Prod.fst <$> (do
      let p ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
        ((implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL i).run
          (esS, winEp))).run (fun _ => false, tbl)
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) (do
        let (_, es, we) ← (simulateQ (implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL) (k p.1.1)).run p.1.2
        if la then return es.h.lfWin else return mainParOut 3 tL par es we)).run p.2) := by
  unfold runSideCont
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
  rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind]

private theorem lfWin_exit_leAdd {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool) {cLoc cM : ProbComp Bool}
    (oa : OracleComp (Fig8Dom Pt ℓ) Bool) (esL : SideESt Pt ℓ) (winEpL : Option ℕ) (tblL : ℕ → SessHSt Pt ℓ)
    (habort : esL.abort = true) (hlf : esL.h.lfWin = true) :
    LeAdd cLoc cM (runSideCont C Dh encPt encT idOf ℓ q qep tL par true oa esL winEpL tblL) := by
  refine leAdd_of_la_one ?_; unfold runSideCont; simp only [↓reduceIte]
  exact lfWin_aborted_eq_one
    (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par true) 1 qep maxForwardJumps tL
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
    (fun n s => pubFsMultiImpl_inl_run _ n s) oa esL winEpL (fun _ => false, tblL) habort hlf

/-! ## 1. Sub-lemmas for `BucketFSAuthBridgeHop` -/


/-! ### Transmit Helpers for `step_transmit_coupled` -/

section R71Tx

open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames (PRFPRNG CKAScheme FSAEADScheme Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult
  transmitQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt hp hInit)
open _root_.CryptoGames.SM (GameState Record RecvResult
  healedBy ltOpt maxOpt lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (PartyState Header SchemeAdversary healEpoch
  FSMultiSpec FSMultiBook mkParties realParty sampleT)
open _root_.CryptoGames.SM.Engine (Hooks HM EState VP Ctx
  liftH run_liftH_bind abortE commitE
  vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind deliverE injectE)
open _root_.CryptoGames.SM.Construction.AuthL11 (lImpl nilSpec
  eraseSt eraseSt_epoch eraseSt_idx eraseSt_tL eraseSt_trans eraseSt_chall eraseSt_comp
  eraseSt_maxAcc eraseSt_b eraseSt_win eraseSt_leaks eraseSt_corrs eraseSt_update_st
  eraseSt_safeCh eraseSt_safeInj eraseSt_inTransit eraseSt_corrAllowed eraseSt_afterCorr
  eraseSt_record eraseSt_accept sendsIn_other eq_senderOf_of_sendsIn)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  dummyKey lAeadR lChainPRG lIdeal lFS lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey SignalRoundTripShort
  maxForwardJumps rustLenBound)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsImpl)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg
  LocalBucketAuthState LocalBucketAuthEState lookupLocalBucketAuthF rootLocalBucketAuth
  hooksLocalBucketAuth hooksLocalBucketAuthMain initLocalBucketAuth implLocalBucketAuthGen
  localAuthBucketMainPar)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  liftFSMultiBucket lookupMultiBucketF regSessMultiBucket regSessOptMultiBucket
  validGuessBucketParAuth rootFSMultiBucketAuth isHonestHdrMultiBucket hooksFSMultiBucketAuth
  initFSMultiBucketAuth implFSMultiBucketAuth redFSAuthMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (sIdxMain mSessMain
  healedBy_imp_healEpoch_le sIdxMain_lt_mSessMain sIdxMain_inj healedBy_of_not_postLeak
  receiverOf_eq_of_sender_par ltOpt_of_healedBy_le
  LeAdd LeOne leAdd_of_lhs_zero leAdd_of_le_main leAdd_of_la_one leOne_of_lhs_zero
  leAdd_bind leAdd_bind_dummy_loc leOne_bind leOne_bind_dummy_loc
  sampleVec keySlotSpec pubFsMultiImpl pubFsMultiImpl_inl_run pubFsMultiImpl_transmit_run
  pubFsMultiImpl_corruptSender_run pubFsMultiImpl_deliver_some_run
  pubFsMultiImpl_inject_none_run pubFsMultiImpl_inject_some_run)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (mainParOut
  halted_leOne lfWin_aborted_eq_one corrs_sub_epMgmt cLoc_zero_of_receiver_corr
  SessHSt ActiveSessInvAt ActiveSessInv activeSessInv_init activeSessInv_to_phase2
  activeSessInv_corruptSender activeSessInv_transmit activeSessInv_deliver
  activeSessInv_inject_phase2 activeSessInv_inject_phase1)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot (LocalMainSlotState
  SlotHM sampleOrSlot lookupLocalMainSlotF rootLocalMainSlot hooksLocalMainSlot
  initLocalMainSlot LocalMainSlotEState implLocalMainSlot localAuthBucketMainSlot
  keySlotFixedImpl sim_sampleT_lImpl sim_sampleT_fixed
  vRecv_localMain_pure deliverE_localMain_pure injectE_localMain_pure)

private abbrev CoupledInv_r71tx {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) :=
  CoupledInv C ℓ q qep encT idOf tL par ks bs

private abbrev SmSpec_r71tx (Pt : Type) (ℓ : ℕ) := Fig8Dom Pt ℓ

private abbrev SmAdv_r71tx (Pt : Type) (ℓ : ℕ) := OracleComp (SmSpec_r71tx Pt ℓ) Bool

private abbrev MultiHSt_r71tx (Pt : Type) :=
  FSMultiBucketAuthState Pt CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.ChainKey Pt
    (ℕ × LibsignalCiphertextWithSalt32)

private abbrev MultiESt_r71tx (Pt : Type) (ℓ : ℕ) := SideESt Pt ℓ

private abbrev ActMap_r71tx :=
  ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))

private abbrev locFS_r71tx {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :=
  lFS C protoSignalCodec ℓ encT idOf maxForwardJumps

private theorem evalDist_bind_const_true_r71tx {α : Type} (mx : ProbComp α) (my : ProbComp Bool) :
    𝒟[mx >>= fun _ => my] {true} = 𝒟[my] {true} := by
  let _ : MeasurableSpace α := ⊤
  have : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
    Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_const,
    MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]

private theorem leAdd_bind_dummy_rhs_r71tx {α : Type} [SampleableType α] {cLoc : ProbComp Bool}
    {fM fL : α → ProbComp Bool} (h : ∀ x, LeAdd cLoc (fM x) (fL x)) :
    LeAdd cLoc (($ᵗ α : ProbComp α) >>= fM) (($ᵗ α : ProbComp α) >>= fL) := by
  unfold LeAdd
  rw [← evalDist_bind_const_true_r71tx ($ᵗ α) cLoc]
  exact leAdd_bind ($ᵗ α) fun a _ => h a

private theorem sim_lift_transmit_run_r71tx {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (ℕ × LibsignalCiphertextWithSalt32)} {s' : SessHSt Pt ℓ}
    (htr : (_root_.CryptoGames.FSAEAD.Thm5.transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 la)
        (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((hdr, pm.1), pm.2)).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((liftFSMultiBucket sIdx (transmitQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256)) hdr pm)).run h)).run
      (fun _ => false, tbl) =
    pure ((u, h), (fun _ => false, Function.update tbl sIdx s')) := by
  unfold liftFSMultiBucket transmitQuery
  rw [stateT_lift_run, query_eq_liftM, simulateQ_query]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, query_eq_liftM]
  change (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
    ((id <$> liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, pm)))))⟩))) >>= fun u => pure (u, h))).run
    (fun _ => false, tbl) = _
  rw [id_map, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
  rw [StateT.run_bind]
  erw [pubFsMultiImpl_transmit_run C ℓ encT idOf la sIdx hdr pm tbl htr]
  simp

private def RootPost_r71tx {Pt : Type} [DecidableEq Pt] (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256) (t0 : ℕ)
    (stLoc stLoc' : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)
    (stM stM' : FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (kLoc kM : BitVec 256) (optIdx : Option ℕ) : Prop :=
  stLoc'.loc.cache = stLoc.loc.cache ∧
  stM'.cache = stM.cache ∧ stM'.book = stM.book ∧ stM'.lfWin = stM.lfWin ∧
  (∀ t, t ≠ t0 → stLoc'.loc.fTable t = stLoc.loc.fTable t ∧
    stM'.fTable t = stM.fTable t ∧ stM'.sessions t = stM.sessions t) ∧
  ((optIdx = none ∧ kM = kLoc ∧ stLoc'.usedSlot = stLoc.usedSlot) ∨
   (optIdx = some (sIdxMain q tL t0) ∧ healEpoch tL ≤ t0 ∧ t0 ≤ qep + 1 ∧
     validGuessBucketParAuth 1 tL par t0 = true ∧ kLoc = ks (sIdxMain q tL t0) ∧
     stLoc'.usedSlot = Function.update stLoc.usedSlot (sIdxMain q tL t0) true))

private theorem run_stateT_lift_r71tx {σ : Type} {m : Type → Type} [Monad m] {α : Type}
    (c : m α) (s : σ) :
    (StateT.lift c).run s = (c >>= fun a => pure (a, s)) := rfl

private theorem sim_slot_pos_run_r71tx {T Sig I : Type}
    (ks : ℕ → BitVec 256) (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ)
    (st : LocalMainSlotState T Sig (BitVec 256) I)
    (hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true) :
    simulateQ (keySlotFixedImpl ks) ((sampleOrSlot M_sess useSlot sIdx).run st) =
      pure (ks sIdx, { st with usedSlot := Function.update st.usedSlot sIdx true }) := by
  simp only [sampleOrSlot, hc, ↓reduceIte, StateT.run_bind, StateT.run_get,
    StateT.run_modify, pure_bind, run_stateT_lift_r71tx, query_eq_liftM,
    simulateQ_bind, simulateQ_query, simulateQ_pure, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, keySlotFixedImpl, QueryImpl.add_apply_inr,
    _root_.CryptoVerification.E2E.Signed.SessionRouter.fwd]
  rfl

private theorem sim_slot_neg_run_r71tx {T Sig I : Type}
    (ks : ℕ → BitVec 256) (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ)
    (st : LocalMainSlotState T Sig (BitVec 256) I)
    (hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = false) :
    simulateQ (keySlotFixedImpl ks) ((sampleOrSlot M_sess useSlot sIdx).run st) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun k => pure (k, st)) := by
  simp only [sampleOrSlot, StateT.run_bind, StateT.run_get, pure_bind, hc, Bool.false_eq_true,
    ↓reduceIte, run_stateT_lift_r71tx, simulateQ_bind, simulateQ_pure, sim_sampleT_fixed]

private theorem root_coupled_leAdd_r71tx {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (C : Crypto) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256)
    (t0 : ℕ) (ik0 : Pt) (σ0 : BitVec 256)
    (stLoc : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)
    (stM : FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (contLoc : BitVec 256 → BitVec 256 → LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt → ProbComp Bool)
    (contM contL : BitVec 256 → BitVec 256 → Option ℕ →
      FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hfLoc : stLoc.loc.fTable t0 = [])
    (hfM : stM.fTable t0 = [])
    (hsesM : stM.sessions t0 = [])
    (hun : validGuessBucketParAuth 1 tL par t0 = true → t0 ≤ qep + 1 →
      stLoc.usedSlot (sIdxMain q tL t0) = false)
    (hpost : ∀ σ' kLoc kM optIdx stLoc' stM' stPM' stPL',
      stPM' = (fun _ => false, tblM) → stPL' = (fun _ => false, tblL) →
      RootPost_r71tx q qep tL par ks t0 stLoc stLoc' stM stM' kLoc kM optIdx →
      LeAdd (contLoc σ' kLoc stLoc') (contM σ' kM optIdx stM' stPM') (contL σ' kM optIdx stM' stPL')) :
    LeAdd
      (do
        let p ← simulateQ (keySlotFixedImpl ks)
          ((rootLocalMainSlot (rootPRNG C.F encPt) 1 q qep (mSessMain q qep tL)
            tL par t0 false ik0 σ0).run stLoc)
        contLoc p.1.1 p.1.2 p.2)
      (do
        let p ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
          ((rootFSMultiBucketAuth
            (T := Pt)
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ)
            (E := ℕ × LibsignalCiphertextWithSalt32)
            (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0).run stM)).run (fun _ => false, tblM)
        let (optIdx, s2) := regSessOptMultiBucket (q + 1) true tL t0 p.1.1.2.2 p.1.2
        contM p.1.1.1 p.1.1.2.1 optIdx s2 p.2)
      (do
        let p ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
          ((rootFSMultiBucketAuth
            (T := Pt)
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ)
            (E := ℕ × LibsignalCiphertextWithSalt32)
            (rootPRNG C.F encPt) 1 qep tL par t0 false ik0 σ0).run stM)).run (fun _ => false, tblL)
        let (optIdx, s2) := regSessOptMultiBucket (q + 1) true tL t0 p.1.1.2.2 p.1.2
        contL p.1.1.1 p.1.1.2.1 optIdx s2 p.2) := by
  dsimp only [rootLocalMainSlot, rootFSMultiBucketAuth]
  by_cases hgt : qep + 1 < t0
  · simp only [Bool.false_or, hgt, decide_true, ↓reduceIte, StateT.run_pure,
      pure_bind, simulateQ_pure, regSessOptMultiBucket]
    exact hpost _ _ _ none stLoc stM _ _ rfl rfl
      ⟨rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have hle : t0 ≤ qep + 1 := by omega
    simp only [Bool.false_or, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hvg : validGuessBucketParAuth 1 tL par t0 = true
    · have hh : healedBy tL 3 t0 = true := by
        simp [validGuessBucketParAuth, lastLeakGuessAdmissible] at hvg; exact hvg.1
      have hhe : healEpoch tL ≤ t0 := healedBy_imp_healEpoch_le tL t0 hh
      have hnotlt : ¬ (t0 < healEpoch tL) := by omega
      have hslt : sIdxMain q tL t0 < mSessMain q qep tL :=
        sIdxMain_lt_mSessMain q qep tL par t0 (by simp [hgt]) hvg
      have hus : stLoc.usedSlot (sIdxMain q tL t0) = false := hun hvg hle
      have hc_pos : (true &&
          decide (sIdxMain q tL t0 < mSessMain q qep tL) &&
          !stLoc.usedSlot (sIdxMain q tL t0)) = true := by
        simp [hslt, hus]
      simp only [hvg, ↓reduceIte]
      by_cases heqH : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · have heqH_beq : (tL.isSome && (t0 == healEpoch tL)) = true := by
          simpa [beq_iff_eq] using heqH
        simp only [heqH, heqH_beq, ↓reduceIte, StateT.run_bind, run_stateT_lift_r71tx,
          simulateQ_bind, bind_assoc, sim_sampleT_fixed, sim_sampleT_pubFs_run, pure_bind,
          StateT.run_pure, simulateQ_pure,
          sim_slot_pos_run_r71tx ks _ true _ stLoc hc_pos, regSessOptMultiBucket, regSessMultiBucket,
          hsesM, List.not_mem_nil, List.length_nil, List.nil_append, Nat.add_zero]
        change LeAdd (($ᵗ Pt) >>= _) (($ᵗ Pt) >>= _) (($ᵗ Pt) >>= _)
        refine leAdd_bind ($ᵗ Pt) fun ir _ => ?_
        change LeAdd _ (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _)
        refine leAdd_bind_dummy_rhs_r71tx fun kDummy => ?_
        exact hpost _ _ _ (some (sIdxMain q tL t0)) _ _ _ _ rfl rfl
          ⟨rfl, rfl, rfl, rfl, fun t hne => ⟨rfl, rfl, by simp [hne]⟩,
           Or.inr ⟨rfl, hhe, hle, hvg, rfl, rfl⟩⟩
      · simp only [Bool.not_eq_true] at heqH
        have heqH_beq : (tL.isSome && (t0 == healEpoch tL)) = false := by
          simpa [beq_iff_eq] using heqH
        simp only [heqH, heqH_beq, Bool.false_eq_true, ↓reduceIte, hnotlt, decide_false,
          Bool.not_false, lookupLocalMainSlotF, lookupMultiBucketF, StateT.run_bind,
          StateT.run_get, pure_bind, hfLoc, hfM, List.lookup_nil, simulateQ_bind, bind_assoc,
          sim_slot_pos_run_r71tx ks _ true _ stLoc hc_pos, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, run_stateT_lift_r71tx, sim_sampleT_pubFs_run,
          regSessOptMultiBucket, regSessMultiBucket, hsesM, List.not_mem_nil,
          List.length_nil, List.nil_append, Nat.add_zero]
        change LeAdd _ (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _)
        refine leAdd_bind_dummy_rhs_r71tx fun kDummy => ?_
        exact hpost _ _ _ (some (sIdxMain q tL t0)) _ _ _ _ rfl rfl
          ⟨rfl, rfl, rfl, rfl, fun t hne => by simp [hne],
           Or.inr ⟨rfl, hhe, hle, hvg, rfl, rfl⟩⟩
    · simp only [Bool.not_eq_true] at hvg
      have hc_neg : (false &&
          decide (sIdxMain q tL t0 < mSessMain q qep tL) &&
          !stLoc.usedSlot (sIdxMain q tL t0)) = false := rfl
      simp only [hvg, Bool.false_eq_true, ↓reduceIte]
      by_cases heqH : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · have heqH_beq : (tL.isSome && (t0 == healEpoch tL)) = true := by
          simpa [beq_iff_eq] using heqH
        simp only [heqH, heqH_beq, ↓reduceIte, StateT.run_bind, run_stateT_lift_r71tx,
          simulateQ_bind, bind_assoc, sim_sampleT_fixed, sim_sampleT_pubFs_run, pure_bind,
          sim_slot_neg_run_r71tx ks _ false _ stLoc hc_neg, StateT.run_pure, simulateQ_pure,
          regSessOptMultiBucket]
        change LeAdd (($ᵗ Pt) >>= _) (($ᵗ Pt) >>= _) (($ᵗ Pt) >>= _)
        refine leAdd_bind ($ᵗ Pt) fun ir _ => ?_
        change LeAdd (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _)
        refine leAdd_bind ($ᵗ (BitVec 256)) fun kSample _ => ?_
        exact hpost _ _ _ none stLoc stM _ _ rfl rfl
          ⟨rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
      · simp only [Bool.not_eq_true] at heqH
        have heqH_beq : (tL.isSome && (t0 == healEpoch tL)) = false := by
          simpa [beq_iff_eq] using heqH
        simp only [heqH, heqH_beq, Bool.false_eq_true, ↓reduceIte]
        by_cases hltH : t0 < healEpoch tL
        · simp only [hltH, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, pure_bind, simulateQ_pure, regSessOptMultiBucket]
          exact hpost _ _ _ none stLoc stM _ _ rfl rfl
            ⟨rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
        · simp only [hltH, decide_false, Bool.not_false, ↓reduceIte, lookupLocalMainSlotF,
            lookupMultiBucketF, StateT.run_bind, StateT.run_get, pure_bind, hfLoc, hfM,
            List.lookup_nil, simulateQ_bind, bind_assoc, sim_slot_neg_run_r71tx ks _ false _ stLoc hc_neg,
            StateT.run_modify, StateT.run_pure, simulateQ_pure, run_stateT_lift_r71tx,
            sim_sampleT_pubFs_run, regSessOptMultiBucket]
          change LeAdd (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _) (($ᵗ (BitVec 256)) >>= _)
          refine leAdd_bind ($ᵗ (BitVec 256)) fun kLookup _ => ?_
          exact hpost _ _ _ none _ _ _ _ rfl rfl
            ⟨rfl, rfl, rfl, rfl, fun t hne => ⟨by simp [hne], by simp [hne], rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩


private def runSideContSt_r71tx {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (oa : OracleComp (Fig8Dom Pt ℓ) Bool)
    (esS : SideESt Pt ℓ) (winEp : Option ℕ) (stP : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) (do
    let (_, es, we) ← (simulateQ (implFSMultiBucketAuth
      (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
      1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL) oa).run (esS, winEp)
    if la then return es.h.lfWin else return mainParOut 3 tL par es we)).run stP

private theorem runSideContSt_eq_r71tx {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (oa : OracleComp (Fig8Dom Pt ℓ) Bool)
    (esS : SideESt Pt ℓ) (winEp : Option ℕ) (tbl : ℕ → SessHSt Pt ℓ) :
    runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par la oa esS winEp (fun _ => false, tbl) =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par la oa esS winEp tbl := rfl


private theorem sim_lift_corruptSender_run_r71tx {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sIdx : ℕ)
    (h : FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (RatchetSenderState (BitVec 256))} {s' : SessHSt Pt ℓ}
    (hcs : ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
      ((liftFSMultiBucket sIdx (corruptSenderQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
          (Ciphertext := ℕ × LibsignalCiphertextWithSalt32))).run h)).run (fun _ => false, tbl) =
    pure ((u, h), (fun _ => false, Function.update tbl sIdx s')) := by
  unfold liftFSMultiBucket corruptSenderQuery
  rw [stateT_lift_run, query_eq_liftM, simulateQ_query]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, query_eq_liftM]
  change (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
    ((id <$> liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩))) >>= fun u => pure (u, h))).run (fun _ => false, tbl) = _
  rw [id_map, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
  rw [StateT.run_bind]
  erw [pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tbl hcs]
  simp


private theorem sendsIn_consec_false_r71tx (P : Party) (t : ℕ) (h : P.sendsIn (t + 1) = true) :
    P.sendsIn t = false := by
  cases P <;> cases t <;> simp [Party.sendsIn] at h ⊢ <;> omega

private theorem sendsIn_of_succ_false_r71tx (P : Party) (t : ℕ) (h : P.sendsIn (t + 1) = false) :
    P.sendsIn t = true := by
  cases P <;> cases t <;> simp [Party.sendsIn] at h ⊢ <;> omega


private theorem safeCh_of_not_postLeak_r71tx {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} {P : Party}
    (hpl : postLeak tL g = false)
    (hadm : lastLeakGuessAdmissible 3 tL (g.epoch P) = true) :
    g.safeCh 3 P = true := by
  unfold GameState.safeCh
  exact healedBy_of_not_postLeak tL g (g.epoch P) hpl hadm

private theorem record_fields_r71tx {St Msg C : Type} (s : GameState St Msg C) (Δ : ℕ) (P : Party)
    (st' : St) (r : Record Msg C) (hidx : r.pos.idx = s.idx P + 1) :
    (s.record Δ P st' r false).st = Function.update s.st P st' ∧
    (s.record Δ P st' r false).epoch = s.epoch ∧
    (s.record Δ P st' r false).idx = Function.update s.idx P (s.idx P + 1) ∧
    (s.record Δ P st' r false).trans = r :: s.trans ∧
    (s.record Δ P st' r false).tL = s.tL ∧
    (s.record Δ P st' r false).win = s.win :=
  ⟨rfl, rfl, congrArg (Function.update s.idx P) hidx, rfl, rfl, rfl⟩

private def vSendTailM_r71tx {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {Γ T Sig SS RS M E CCoins γV σV ssV rsV HS : Type}
    [Inhabited E]
    (hk : Hooks TSpec HS Γ T Sig SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s₁ : VP γV T σV ssV rsV) (m : M) :
    HM TSpec HS (Option (VP γV T σV ssV rsV × (Header T × E))) :=
  match s₁.vS with
  | none => pure (some (s₁, ((s₁.tcur, s₁.curCkaMsg), default)))
  | some v => do
    match ← hk.fsSend ctx P s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m none with
    | none => pure none
    | some (v', e) =>
      pure (some ({ s₁ with vS := some v' }, ((s₁.tcur, s₁.curCkaMsg), e)))

private theorem fsSend_record_coupled_r71tx {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (hrt : SignalRoundTripShort protoSignalCodec) (hℓ : ℓ + 16 < rustLenBound)
    {phase1 : Bool} {rem' : ℕ}
    {actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (hshort : m.1.shortB = true)
    (s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (vp1Loc : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (vp1M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (hLoc1 : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)
    (hM1 : FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (herase1 : eraseSt s₁M = eraseSt s₁Loc)
    (hsends_cur : P.sendsIn (s₁Loc.epoch P) = true)
    (hinv1 : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp
      { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
      { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
      { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
      none tblM tblL) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la
    ∃ vp2Loc vp2M ct hLoc2 hM2 actEp' tblM' tblL',
      simulateQ (keySlotFixedImpl ks) ((vSendTailM_r71tx hkLoc s₁Loc P vp1Loc m).run hLoc1) =
        pure (some (vp2Loc, ct), hLoc2) ∧
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((vSendTailM_r71tx (hkM false) s₁M P vp1M m).run hM1)).run (fun _ => false, tblM) =
        pure ((some (vp2M, ct), hM2), (fun _ => false, tblM')) ∧
      (phase1 = true →
        (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
          ((vSendTailM_r71tx (hkM true) s₁M P vp1M m).run hM1)).run (fun _ => false, tblL) =
          pure ((some (vp2M, ct), hM2), (fun _ => false, tblL'))) ∧
      let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :=
        ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
      CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp'
        { g := s₁Loc.record 3 P vp2Loc recE false, h := hLoc2, abort := false }
        { g := s₁M.record 3 P vp2M recE false, h := hM2, abort := false }
        { g := s₁M.record 3 P vp2M recE false, h := hM2, abort := false }
        none tblM' tblL' := by
  intro hkLoc hkM
  let esLoc1 : LocESt Pt ℓ :=
    { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
  let esM1 : SideESt Pt ℓ :=
    { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
  have hvpL : esLoc1.g.st P = vp1Loc := by simp [esLoc1]
  have hvpM : esM1.g.st P = vp1M := by simp [esM1]
  have htcurL : vp1Loc.tcur = s₁Loc.epoch P := by
    have h := (hinv1.hparty_tcur P).1; simpa [esLoc1] using h
  have htcurM : vp1M.tcur = vp1Loc.tcur := by
    have h := (hinv1.hparty_tcur P).2; simpa [esLoc1, esM1] using h
  have hcurM : vp1M.curCkaMsg = vp1Loc.curCkaMsg := by
    have h := (hinv1.hparty_base P).2.1; simpa [esLoc1, esM1] using h
  have hγM : vp1M.γ = vp1Loc.γ := by
    have h := (hinv1.hparty_base P).1; simpa [esLoc1, esM1] using h
  have hrootM : vp1M.root = vp1Loc.root := by
    have h := (hinv1.hparty_base P).2.2; simpa [esLoc1, esM1] using h
  have hidL : vp1Loc.id = P := by
    have h := (hinv1.hparty_id P).1; simpa [esLoc1] using h
  have hidM : vp1M.id = P := by
    have h := (hinv1.hparty_id P).2; simpa [esM1] using h
  have hsender_ep : Party.senderOf (s₁Loc.epoch P) = P :=
    (eq_senderOf_of_sendsIn hsends_cur).symm
  have hvSP := hinv1.hvS P
  rw [hvpL, hvpM] at hvSP
  cases hvL : vp1Loc.vS with
  | none =>
    rw [hvL, htcurL, hsends_cur] at hvSP
    exact Bool.noConfusion hvSP.2
  | some ss1 =>
    rw [hvL] at hvSP
    rcases hvSP with ⟨ts, _, _, hts_eq, hvM_match⟩
    have hts : ts = s₁Loc.epoch P := by
      rw [← htcurL]; exact hts_eq (by rw [htcurL]; exact hsends_cur)
    subst hts
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let hdr : Header Pt := (vp1Loc.tcur, vp1Loc.curCkaMsg)
    let o := fs.send ss1 hdr m
    cases ha : actEp (s₁Loc.epoch P) with
    | none =>
      rw [ha] at hvM_match
      let vp2Loc := { vp1Loc with vS := some o.1 }
      let vp2M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
        { vp1M with vS := some (Sum.inl o.1) }
      let ct : Header Pt × (ℕ × LibsignalCiphertextWithSalt32) := (hdr, o.2)
      let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :=
        ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
      have hidxM1 : s₁M.idx P = s₁Loc.idx P := by
        have h := congrArg GameState.idx herase1; simpa [eraseSt] using congrFun h P
      rcases record_fields_r71tx s₁Loc 3 P vp2Loc recE rfl with ⟨hrL_st, hrL_ep, hrL_idx, hrL_tr, hrL_tL, hrL_win⟩
      rcases record_fields_r71tx s₁M 3 P vp2M recE (by simp [recE, hidxM1]) with ⟨hrM_st, hrM_ep, hrM_idx, hrM_tr, hrM_tL, hrM_win⟩
      refine ⟨vp2Loc, vp2M, ct, hLoc1, hM1, actEp, tblM, tblL, ?_, ?_, ?_, ?_⟩
      · simp [vSendTailM_r71tx, hvL, hkLoc, hooksLocalMainSlot, fs, hdr, o, vp2Loc, ct]
      · simp [vSendTailM_r71tx, hvM_match, hkM, hooksFSMultiBucketAuth, htcurM, hcurM, fs, hdr, o, vp2M, ct]
      · intro _
        simp [vSendTailM_r71tx, hvM_match, hkM, hooksFSMultiBucketAuth, htcurM, hcurM, fs, hdr, o, vp2M, ct]
      · refine {
          habort_loc := rfl, habort_M := rfl
          hwin_loc := by rw [hrL_win]; exact hinv1.hwin_loc
          hwe := rfl
          herase := eraseSt_record herase1 3 P vp2M vp2Loc recE false
          hep_le := fun Q => hinv1.hep_le Q
          hep_sends := fun Q h => hinv1.hep_sends Q h
          hphase1 := fun hp1 => by
            rcases hinv1.hphase1 hp1 with ⟨hpl, _, hlf, hsc⟩
            exact ⟨hpl, rfl, hlf, hsc⟩
          hphase2 := fun hp2 => by
            rcases hinv1.hphase2 hp2 with ⟨cur, hcur, hlt, hle⟩
            exact ⟨cur, hcur, hlt, hle⟩
          hparty_id := fun Q => by
            rw [hrL_st, hrM_st]
            by_cases hQ : Q = P
            · subst Q; simp [vp2Loc, vp2M, hidL, hidM]
            · simpa [esLoc1, esM1, hQ] using hinv1.hparty_id Q
          hparty_tcur := fun Q => by
            rw [hrL_st, hrM_st, hrL_ep]
            by_cases hQ : Q = P
            · subst Q; simp [vp2Loc, vp2M, htcurL, htcurM]
            · simpa [esLoc1, esM1, hQ] using hinv1.hparty_tcur Q
          hparty_base := fun Q => by
            rw [hrL_st, hrM_st]
            by_cases hQ : Q = P
            · subst Q; simp [vp2Loc, vp2M, hγM, hcurM, hrootM]
            · simpa [esLoc1, esM1, hQ] using hinv1.hparty_base Q
          htcur_le := fun Q => by
            rw [hrL_st]
            by_cases hQ : Q = P
            · subst Q; simpa [esLoc1, vp2Loc] using hinv1.htcur_le P
            · simpa [esLoc1, hQ] using hinv1.htcur_le Q
          hvR_gt := fun Q t ht => by
            rw [hrL_st, hrM_st]
            rw [hrL_st] at ht
            by_cases hQ : Q = P
            · subst Q
              have ht' : (esLoc1.g.st P).tcur < t := by simpa [esLoc1, vp2Loc] using ht
              simpa [esLoc1, esM1, vp2Loc, vp2M] using hinv1.hvR_gt P t ht'
            · have ht' : (esLoc1.g.st Q).tcur < t := by simpa [esLoc1, hQ] using ht
              simpa [esLoc1, esM1, hQ] using hinv1.hvR_gt Q t ht'
          hvS := fun Q => by
            rw [hrL_st, hrM_st]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, vp2Loc, vp2M]
              exact ⟨s₁Loc.epoch P, by rw [htcurL], hsends_cur, fun _ => htcurL.symm, by simp [ha]⟩
            · simpa [esLoc1, esM1, hQ] using hinv1.hvS Q
          hvR := fun Q t => by
            rw [hrL_st, hrM_st]
            by_cases hQ : Q = P
            · subst Q; simpa [esLoc1, esM1, vp2Loc, vp2M] using hinv1.hvR P t
            · simpa [esLoc1, esM1, hQ] using hinv1.hvR Q t
          hcache := fun t => by
            have hst_tcur : ∀ Q, ((s₁Loc.record 3 P vp2Loc recE false).st Q).tcur = (esLoc1.g.st Q).tcur := by
              intro Q; rw [hrL_st]
              by_cases hQ : Q = P
              · subst Q; simp [esLoc1, vp2Loc]
              · simp [esLoc1, hQ]
            have hst_vR : ∀ Q, ((s₁Loc.record 3 P vp2Loc recE false).st Q).vR = (esLoc1.g.st Q).vR := by
              intro Q; rw [hrL_st]
              by_cases hQ : Q = P
              · subst Q; simp [esLoc1, vp2Loc]
              · simp [esLoc1, hQ]
            rcases hinv1.hcache t with ⟨hc1, hc2⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hcM_m⟩
            · exact Or.inl ⟨hc1, hc2⟩
            · refine Or.inr ⟨h1, by rw [hst_tcur]; exact h2, Tc, σc, kVal, hcL, ?_⟩
              cases hat : actEp t with
              | none => rw [hat] at hcM_m; exact hcM_m
              | some pr =>
                rw [hat] at hcM_m
                rcases hcM_m with ⟨hk, hd, hinit⟩
                exact ⟨hk, hd, fun hv => hinit (by rwa [hst_vR] at hv)⟩
          hfuture := fun t ht => by
            have hst_tcur : ((s₁Loc.record 3 P vp2Loc recE false).st (Party.senderOf t)).tcur =
                (esLoc1.g.st (Party.senderOf t)).tcur := by
              rw [hrL_st]
              by_cases hQ : Party.senderOf t = P
              · rw [hQ]; simp [esLoc1, vp2Loc]
              · simp [esLoc1, hQ]
            rw [hst_tcur] at ht
            exact hinv1.hfuture t ht
          hact := fun t0 ss0 rs0 ha0 => by
            have hne_ep : t0 ≠ s₁Loc.epoch P := fun heq => by subst heq; rw [ha] at ha0; cases ha0
            rcases hinv1.hact t0 ss0 rs0 ha0 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
            have hst_tcur : ((s₁Loc.record 3 P vp2Loc recE false).st (Party.senderOf t0)).tcur =
                (esLoc1.g.st (Party.senderOf t0)).tcur := by
              rw [hrL_st]
              by_cases hQ : Party.senderOf t0 = P
              · rw [hQ]; simp [esLoc1, vp2Loc]
              · simp [esLoc1, hQ]
            refine ⟨h1, h2, h3, by rw [hst_tcur]; exact h4, h5, ?_, ?_⟩
            · intro heq_tcur
              rw [hst_tcur] at heq_tcur
              have hne_P : Party.senderOf t0 ≠ P := by
                intro hp; rw [hp] at heq_tcur
                have : (esLoc1.g.st P).tcur = s₁Loc.epoch P := by simpa [esLoc1] using htcurL
                exact hne_ep (this.symm.trans heq_tcur).symm
              rw [hrL_idx, Function.update_of_ne hne_P]
              exact h6 heq_tcur
            · rw [hrL_tr]
              have hfalse : (recE.pos.epoch == t0) = false :=
                beq_false_of_ne (Ne.symm hne_ep)
              simp [hfalse] at h7 ⊢
              exact h7
          hunalloc := hinv1.hunalloc
          htrans := fun r hr => by
            rw [hrL_tr, List.mem_cons] at hr
            have hst_tcur : ∀ Q, ((s₁Loc.record 3 P vp2Loc recE false).st Q).tcur = (esLoc1.g.st Q).tcur := by
              intro Q; rw [hrL_st]
              by_cases hQ : Q = P
              · subst Q; simp [esLoc1, vp2Loc]
              · simp [esLoc1, hQ]
            rcases hr with rfl | hr
            · refine ⟨htcurL.symm, hsender_ep.symm, ?_⟩
              rw [hst_tcur]; simp [recE, esLoc1, htcurL]
            · rcases hinv1.htrans r hr with ⟨ht1, ht2, ht3⟩
              exact ⟨ht1, ht2, by rw [hst_tcur]; exact ht3⟩ }
    | some pairA =>
      rcases pairA with ⟨ssA, rsA⟩
      rw [ha] at hvM_match
      rcases hvM_match with ⟨rfl, hvM_match⟩
      rcases hinv1.hact (s₁Loc.epoch P) ss1 rsA ha with ⟨hhe_ep, hle_ep, hvg_ep, _, hact_inv, hidx_eq, htr_eq⟩
      let sIdx := sIdxMain q tL (s₁Loc.epoch P)
      let bk := (hM1.book sIdx).getD {}
      let vp2Loc := { vp1Loc with vS := some o.1 }
      let vp2M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
        { vp1M with vS := some (Sum.inr sIdx) }
      let ct : Header Pt × (ℕ × LibsignalCiphertextWithSalt32) := (hdr, o.2)
      let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :=
        ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
      let actEp' := Function.update actEp (s₁Loc.epoch P) (some (o.1, rsA))
      have hidxM1 : s₁M.idx P = s₁Loc.idx P := by
        have h := congrArg GameState.idx herase1; simpa [eraseSt] using congrFun h P
      rcases record_fields_r71tx s₁Loc 3 P vp2Loc recE rfl with ⟨hrL_st, hrL_ep, hrL_idx, hrL_tr, hrL_tL, hrL_win⟩
      rcases record_fields_r71tx s₁M 3 P vp2M recE (by simp [recE, hidxM1]) with ⟨hrM_st, hrM_ep, hrM_idx, hrM_tr, hrM_tL, hrM_win⟩
      have hst_tcur : ∀ Q, ((s₁Loc.record 3 P vp2Loc recE false).st Q).tcur = (esLoc1.g.st Q).tcur := by
        intro Q; rw [hrL_st]
        by_cases hQ : Q = P
        · subst Q; simp [esLoc1, vp2Loc]
        · simp [esLoc1, hQ]
      have hstL_vR : ∀ Q, ((s₁Loc.record 3 P vp2Loc recE false).st Q).vR = (esLoc1.g.st Q).vR := by
        intro Q; rw [hrL_st]
        by_cases hQ : Q = P
        · subst Q; simp [esLoc1, vp2Loc]
        · simp [esLoc1, hQ]
      have hstM_vR : ∀ Q, ((s₁M.record 3 P vp2M recE false).st Q).vR = (esM1.g.st Q).vR := by
        intro Q; rw [hrM_st]
        by_cases hQ : Q = P
        · subst Q; simp [esM1, vp2M]
        · simp [esM1, hQ]
      have hidx_cur : s₁Loc.idx P = bk.fsCount := by
        have h := hidx_eq (by simp [hsender_ep, htcurL])
        simpa [esLoc1, hsender_ep] using h
      by_cases hdo_corr : (!(s₁M.safeCh 3 P) && !bk.sCorr) = true
      · have hp1_false : phase1 = false := by
          cases phase1 with
          | false => rfl
          | true =>
            have hpl_f : postLeak tL s₁Loc = false := (hinv1.hphase1 rfl).1
            have hadm : lastLeakGuessAdmissible 3 tL (s₁Loc.epoch P) = true :=
              (Bool.and_eq_true _ _).mp hvg_ep |>.1
            have hsafeL : s₁Loc.safeCh 3 P = true := safeCh_of_not_postLeak_r71tx hpl_f hadm
            have hsafeM : s₁M.safeCh 3 P = true := by rw [eraseSt_safeCh herase1]; exact hsafeL
            simp [hsafeM] at hdo_corr
        subst hp1_false
        rcases activeSessInv_corruptSender C ℓ encT idOf hact_inv with ⟨sM_c, hcs_run, hact_c⟩
        let hM_c := { hM1 with book := Function.update hM1.book sIdx (some { bk with sCorr := true }) }
        let tblM_c := Function.update tblM sIdx sM_c
        have hact_c' : ActiveSessInv C ℓ encT idOf false (ks sIdx) ss1 rsA
            ((hM_c.book sIdx).getD {}) (tblM_c sIdx) (tblL sIdx) := by
          simpa [hM_c, tblM_c] using hact_c
        rcases activeSessInv_transmit C hrt ℓ hℓ encT idOf hact_c' hdr m hshort with
          ⟨sM', sL', htrM_run, _, hact_fin⟩
        let bk_fin : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
          { bk with sCorr := true, fsCount := bk.fsCount + 1, fsTrans := (bk.fsCount + 1, hdr, o.2) :: bk.fsTrans }
        let hM2 := { hM1 with book := Function.update hM1.book sIdx (some bk_fin) }
        let tblM' := Function.update tblM sIdx sM'
        refine ⟨vp2Loc, vp2M, ct, hLoc1, hM2, actEp', tblM', tblL, ?_, ?_, (fun hp1 => Bool.noConfusion hp1), ?_⟩
        · simp [vSendTailM_r71tx, hvL, hkLoc, hooksLocalMainSlot, fs, hdr, o, vp2Loc, ct]
        · simp only [vSendTailM_r71tx, hvM_match, hkM, hooksFSMultiBucketAuth, htcurM, hcurM]
          simp only [StateT.run_bind, StateT.run_get,
            simulateQ_bind, pure_bind, bind_assoc]
          simp only [bk, sIdx] at hdo_corr
          rw [show (!(s₁M.safeCh (2 + 1) P) && !((hM1.book (sIdxMain q tL (s₁Loc.epoch P))).getD {}).sCorr) = true from hdo_corr]
          simp only [↓reduceIte, simulateQ_bind, StateT.run_bind, bind_assoc]
          rw [sim_lift_corruptSender_run_r71tx C ℓ encT idOf sIdx hM1 tblM hcs_run]
          simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
          have htrM_run' : (_root_.CryptoGames.FSAEAD.Thm5.transmitHWith (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 false)
              (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
              (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
              ((hdr, m.1), m.2)).run (tblM_c sIdx) = pure (some o.2, sM') := by
            simpa [tblM_c] using htrM_run
          rw [sim_lift_transmit_run_r71tx C ℓ encT idOf false sIdx hdr m hM_c tblM_c htrM_run']
          simp [pure_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, htcurM, hcurM, hM_c, hM2, tblM_c, tblM', bk_fin, bk, sIdx, vp2M, ct, hdr, o, Function.update_idem]
        · refine {
            habort_loc := rfl, habort_M := rfl
            hwin_loc := by rw [hrL_win]; exact hinv1.hwin_loc
            hwe := rfl
            herase := eraseSt_record herase1 3 P vp2M vp2Loc recE false
            hep_le := fun Q => hinv1.hep_le Q
            hep_sends := fun Q h => hinv1.hep_sends Q h
            hphase1 := fun hp1 => Bool.noConfusion hp1
            hphase2 := fun _ => by
              rcases hinv1.hphase2 rfl with ⟨cur, hcur, hlt, hle⟩
              refine ⟨cur, hcur, hlt, fun t0 ha0 => ?_⟩
              by_cases ht0 : t0 = s₁Loc.epoch P
              · subst ht0; exact hle _ (by simp [ha])
              · simp only [actEp', Function.update_of_ne ht0] at ha0; exact hle t0 ha0
            hparty_id := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, hidL, hidM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_id Q
            hparty_tcur := fun Q => by
              rw [hrL_st, hrM_st, hrL_ep]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, htcurL, htcurM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_tcur Q
            hparty_base := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, hγM, hcurM, hrootM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_base Q
            htcur_le := fun Q => by
              rw [hrL_st]
              by_cases hQ : Q = P
              · subst Q; simpa [esLoc1, vp2Loc] using hinv1.htcur_le P
              · simpa [esLoc1, hQ] using hinv1.htcur_le Q
            hvR_gt := fun Q t ht => by
              rw [hrL_st, hrM_st]; rw [hrL_st] at ht
              by_cases hQ : Q = P
              · subst Q
                have ht' : (esLoc1.g.st P).tcur < t := by simpa [esLoc1, vp2Loc] using ht
                simpa [esLoc1, esM1, vp2Loc, vp2M] using hinv1.hvR_gt P t ht'
              · have ht' : (esLoc1.g.st Q).tcur < t := by simpa [esLoc1, hQ] using ht
                simpa [esLoc1, esM1, hQ] using hinv1.hvR_gt Q t ht'
            hvS := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, vp2Loc, vp2M]
                exact ⟨s₁Loc.epoch P, by rw [htcurL], hsends_cur, fun _ => htcurL.symm,
                  by simp [actEp', sIdx]⟩
              · have hvQ := hinv1.hvS Q
                simp only [Function.update_of_ne hQ]
                simp only [Function.update_of_ne hQ] at hvQ
                cases hvQL : (s₁Loc.st Q).vS with
                | none => rw [hvQL] at hvQ; exact hvQ
                | some ssQ =>
                  rw [hvQL] at hvQ
                  rcases hvQ with ⟨tsQ, hleQ, hsendsQ, heqQ, hmQ⟩
                  have hne_ts : tsQ ≠ s₁Loc.epoch P := by
                    intro heq_ts; subst heq_ts
                    have hQP : Party.senderOf (s₁Loc.epoch P) = Q := (eq_senderOf_of_sendsIn hsendsQ).symm
                    exact hQ (hQP.symm.trans hsender_ep)
                  exact ⟨tsQ, hleQ, hsendsQ, heqQ, by simpa [actEp', hne_ts] using hmQ⟩
            hvR := fun Q t => by
              rw [hstL_vR, hstM_vR, hst_tcur]
              have hvRt := hinv1.hvR Q t
              cases hvRL : (esLoc1.g.st Q).vR t with
              | none => rw [hvRL] at hvRt; exact hvRt
              | some rs =>
                rw [hvRL] at hvRt
                rcases hvRt with ⟨hns_t, hle_t, hm_t⟩
                refine ⟨hns_t, hle_t, ?_⟩
                by_cases ht : t = s₁Loc.epoch P
                · subst ht; rw [ha] at hm_t; simpa [actEp'] using hm_t
                · simpa [actEp', ht] using hm_t
            hcache := fun t => by
              rcases hinv1.hcache t with ⟨hc1, hc2⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hcM_m⟩
              · exact Or.inl ⟨hc1, hc2⟩
              · refine Or.inr ⟨h1, by rw [hst_tcur]; exact h2, Tc, σc, kVal, hcL, ?_⟩
                by_cases ht : t = s₁Loc.epoch P
                · subst ht
                  rw [ha] at hcM_m
                  rcases hcM_m with ⟨hk, hd, hinit⟩
                  simp only [actEp', Function.update_self]
                  exact ⟨hk, hd, fun hv => hinit (by rwa [hstL_vR] at hv)⟩
                · simp only [actEp', Function.update_of_ne ht]
                  cases hat : actEp t with
                  | none => rw [hat] at hcM_m; exact hcM_m
                  | some pr =>
                    rw [hat] at hcM_m
                    rcases hcM_m with ⟨hk, hd, hinit⟩
                    exact ⟨hk, hd, fun hv => hinit (by rwa [hstL_vR] at hv)⟩
            hfuture := fun t ht => by
              rw [hst_tcur] at ht
              have hne_ep : t ≠ s₁Loc.epoch P := by
                intro heq; subst heq
                simp [esLoc1, hsender_ep, htcurL] at ht
              rcases hinv1.hfuture t ht with ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩
              exact ⟨by simp [actEp', hne_ep, hf1], hf2, hf3, hf4, hf5, hf6⟩
            hact := fun t0 ss0 rs0 ha0 => by
              by_cases ht0 : t0 = s₁Loc.epoch P
              · subst ht0
                simp only [actEp', Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha0
                rcases ha0 with ⟨rfl, rfl⟩
                refine ⟨hhe_ep, hle_ep, hvg_ep, by rw [hst_tcur, hsender_ep]; simp [esLoc1, htcurL], ?_, ?_, ?_⟩
                · have hact_f : ActiveSessInv C ℓ encT idOf false (ks sIdx) o.1 rsA bk_fin sM' (tblL sIdx) := by
                    rcases hact_fin with ⟨stR', hi⟩
                    have hbk_eq : { ((hM_c.book sIdx).getD {}) with
                        fsCount := ((hM_c.book sIdx).getD {}).fsCount + 1,
                        fsTrans := (((hM_c.book sIdx).getD {}).fsCount + 1, hdr, o.2) ::
                          ((hM_c.book sIdx).getD {}).fsTrans } = bk_fin := by
                      simp [hM_c, bk_fin, bk, sIdx]
                    rw [hbk_eq] at hi
                    exact ⟨stR', { hi with syncRML := fun h => Bool.noConfusion h }⟩
                  simpa [hM2, tblM', sIdx, bk_fin] using hact_f
                · intro _; rw [hrL_idx, hsender_ep, Function.update_self, hidx_cur]
                  simp [hM2, sIdx, bk_fin]
                · rw [hrL_tr]
                  simp only [hM2, sIdx, Function.update_self, Option.getD_some, bk_fin,
                    List.filter_cons, recE, beq_self_eq_true, ↓reduceIte, List.map_cons, hidx_cur]
                  exact congrArg (_ :: ·) htr_eq
              · simp only [actEp', Function.update_of_ne ht0] at ha0
                rcases hinv1.hact t0 ss0 rs0 ha0 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
                have hne_idx : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                  ht0 (sIdxMain_inj q tL h1 hhe_ep heq)
                refine ⟨h1, h2, h3, by rw [hst_tcur]; exact h4, ?_, ?_, ?_⟩
                · simpa [hM2, tblM', hne_idx] using h5
                · intro heq_tc
                  rw [hst_tcur] at heq_tc
                  have hne_P : Party.senderOf t0 ≠ P := by
                    intro hp; rw [hp] at heq_tc
                    have : (esLoc1.g.st P).tcur = s₁Loc.epoch P := by simpa [esLoc1] using htcurL
                    exact ht0 (this.symm.trans heq_tc).symm
                  rw [hrL_idx, Function.update_of_ne hne_P]
                  simpa [hM2, hne_idx] using h6 heq_tc
                · rw [hrL_tr]
                  have hfalse : (recE.pos.epoch == t0) = false := beq_false_of_ne (Ne.symm ht0)
                  simpa [hM2, hne_idx, hfalse] using h7
            hunalloc := fun sIdx' hlt' hun' => by
              have hne_idx : sIdx' ≠ sIdx := by
                intro heq; subst heq
                have h0 := hun' (s₁Loc.epoch P) hhe_ep rfl
                simp [actEp'] at h0
              rcases hinv1.hunalloc sIdx' hlt' (fun t0 hh0 hs0 => by
                have ht0 : t0 ≠ s₁Loc.epoch P := fun heq => by subst heq; exact hne_idx hs0.symm
                simpa [actEp', ht0] using hun' t0 hh0 hs0) with ⟨hu1, hu2, hu3, _⟩
              exact ⟨hu1, by simp [hM2, hne_idx]; exact hu2, by simp [tblM', hne_idx, hu3],
                fun hp1 => Bool.noConfusion hp1⟩
            htrans := fun r hr => by
              rw [hrL_tr, List.mem_cons] at hr
              rcases hr with rfl | hr
              · refine ⟨htcurL.symm, hsender_ep.symm, ?_⟩
                rw [hst_tcur]; simp [recE, esLoc1, htcurL]
              · rcases hinv1.htrans r hr with ⟨ht1, ht2, ht3⟩
                exact ⟨ht1, ht2, by rw [hst_tcur]; exact ht3⟩ }
      · simp only [Bool.not_eq_true] at hdo_corr
        rcases activeSessInv_transmit C hrt ℓ hℓ encT idOf hact_inv hdr m hshort with
          ⟨sM', sL', htrM_run, htrL_run, hact_fin⟩
        let bk_fin : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
          { bk with fsCount := bk.fsCount + 1, fsTrans := (bk.fsCount + 1, hdr, o.2) :: bk.fsTrans }
        let hM2 := { hM1 with book := Function.update hM1.book sIdx (some bk_fin) }
        let tblM' := Function.update tblM sIdx sM'
        let tblL' := if phase1 then Function.update tblL sIdx sL' else tblL
        refine ⟨vp2Loc, vp2M, ct, hLoc1, hM2, actEp', tblM', tblL', ?_, ?_, ?_, ?_⟩
        · simp [vSendTailM_r71tx, hvL, hkLoc, hooksLocalMainSlot, fs, hdr, o, vp2Loc, ct]
        · simp only [vSendTailM_r71tx, hvM_match, hkM, hooksFSMultiBucketAuth, htcurM, hcurM]
          simp only [StateT.run_bind, StateT.run_get,
            simulateQ_bind, pure_bind, bind_assoc]
          simp only [bk, sIdx] at hdo_corr
          rw [show (!(s₁M.safeCh (2 + 1) P) && !((hM1.book (sIdxMain q tL (s₁Loc.epoch P))).getD {}).sCorr) = false from hdo_corr]
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
            Bool.not_true, simulateQ_bind, StateT.run_bind, bind_assoc]
          rw [sim_lift_transmit_run_r71tx C ℓ encT idOf false sIdx hdr m hM1 tblM htrM_run]
          simp [pure_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, htcurM, hcurM, hM2, tblM', bk_fin, bk, sIdx, vp2M, ct, hdr, o, fs]
        · intro hp1
          have htrL := htrL_run hp1
          simp only [vSendTailM_r71tx, hvM_match, hkM, hooksFSMultiBucketAuth, htcurM, hcurM]
          simp only [StateT.run_bind, StateT.run_get,
            simulateQ_bind, pure_bind, bind_assoc]
          simp only [bk, sIdx] at hdo_corr
          rw [show (!(s₁M.safeCh (2 + 1) P) && !((hM1.book (sIdxMain q tL (s₁Loc.epoch P))).getD {}).sCorr) = false from hdo_corr]
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
            Bool.not_true, simulateQ_bind, StateT.run_bind, bind_assoc]
          rw [sim_lift_transmit_run_r71tx C ℓ encT idOf true sIdx hdr m hM1 tblL htrL]
          simp [pure_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, htcurM, hcurM, hp1, hM2, tblL', bk_fin, bk, sIdx, vp2M, ct, hdr, o, fs]
        · refine {
            habort_loc := rfl, habort_M := rfl
            hwin_loc := by rw [hrL_win]; exact hinv1.hwin_loc
            hwe := rfl
            herase := eraseSt_record herase1 3 P vp2M vp2Loc recE false
            hep_le := fun Q => hinv1.hep_le Q
            hep_sends := fun Q h => hinv1.hep_sends Q h
            hphase1 := fun hp1 => by
              rcases hinv1.hphase1 hp1 with ⟨hpl, _, hlf, hsc⟩
              refine ⟨hpl, rfl, hlf, fun t0 ha0 => ?_⟩
              by_cases ht0 : t0 = s₁Loc.epoch P
              · subst ht0
                have hsc0 := hsc (s₁Loc.epoch P) (by simp [ha])
                simpa [hM2, sIdx, bk_fin, bk] using hsc0
              · simp only [actEp', Function.update_of_ne ht0] at ha0
                have hne_idx : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                  ht0 (sIdxMain_inj q tL (by
                    rcases Option.ne_none_iff_exists'.mp ha0 with ⟨⟨ss0, rs0⟩, ha0'⟩
                    exact (hinv1.hact t0 ss0 rs0 ha0').1) hhe_ep heq)
                simpa [hM2, hne_idx] using hsc t0 ha0
            hphase2 := fun hp2 => by
              rcases hinv1.hphase2 hp2 with ⟨cur, hcur, hlt, hle⟩
              refine ⟨cur, hcur, hlt, fun t0 ha0 => ?_⟩
              by_cases ht0 : t0 = s₁Loc.epoch P
              · subst ht0; exact hle _ (by simp [ha])
              · simp only [actEp', Function.update_of_ne ht0] at ha0; exact hle t0 ha0
            hparty_id := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, hidL, hidM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_id Q
            hparty_tcur := fun Q => by
              rw [hrL_st, hrM_st, hrL_ep]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, htcurL, htcurM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_tcur Q
            hparty_base := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q; simp [vp2Loc, vp2M, hγM, hcurM, hrootM]
              · simpa [esLoc1, esM1, hQ] using hinv1.hparty_base Q
            htcur_le := fun Q => by
              rw [hrL_st]
              by_cases hQ : Q = P
              · subst Q; simpa [esLoc1, vp2Loc] using hinv1.htcur_le P
              · simpa [esLoc1, hQ] using hinv1.htcur_le Q
            hvR_gt := fun Q t ht => by
              rw [hrL_st, hrM_st]; rw [hrL_st] at ht
              by_cases hQ : Q = P
              · subst Q
                have ht' : (esLoc1.g.st P).tcur < t := by simpa [esLoc1, vp2Loc] using ht
                simpa [esLoc1, esM1, vp2Loc, vp2M] using hinv1.hvR_gt P t ht'
              · have ht' : (esLoc1.g.st Q).tcur < t := by simpa [esLoc1, hQ] using ht
                simpa [esLoc1, esM1, hQ] using hinv1.hvR_gt Q t ht'
            hvS := fun Q => by
              rw [hrL_st, hrM_st]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, vp2Loc, vp2M]
                exact ⟨s₁Loc.epoch P, by rw [htcurL], hsends_cur, fun _ => htcurL.symm,
                  by simp [actEp', sIdx]⟩
              · have hvQ := hinv1.hvS Q
                simp only [Function.update_of_ne hQ]
                simp only [Function.update_of_ne hQ] at hvQ
                cases hvQL : (s₁Loc.st Q).vS with
                | none => rw [hvQL] at hvQ; exact hvQ
                | some ssQ =>
                  rw [hvQL] at hvQ
                  rcases hvQ with ⟨tsQ, hleQ, hsendsQ, heqQ, hmQ⟩
                  have hne_ts : tsQ ≠ s₁Loc.epoch P := by
                    intro heq_ts; subst heq_ts
                    have hQP : Party.senderOf (s₁Loc.epoch P) = Q := (eq_senderOf_of_sendsIn hsendsQ).symm
                    exact hQ (hQP.symm.trans hsender_ep)
                  exact ⟨tsQ, hleQ, hsendsQ, heqQ, by simpa [actEp', hne_ts] using hmQ⟩
            hvR := fun Q t => by
              rw [hstL_vR, hstM_vR, hst_tcur]
              have hvRt := hinv1.hvR Q t
              cases hvRL : (esLoc1.g.st Q).vR t with
              | none => rw [hvRL] at hvRt; exact hvRt
              | some rs =>
                rw [hvRL] at hvRt
                rcases hvRt with ⟨hns_t, hle_t, hm_t⟩
                refine ⟨hns_t, hle_t, ?_⟩
                by_cases ht : t = s₁Loc.epoch P
                · subst ht; rw [ha] at hm_t; simpa [actEp'] using hm_t
                · simpa [actEp', ht] using hm_t
            hcache := fun t => by
              rcases hinv1.hcache t with ⟨hc1, hc2⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hcM_m⟩
              · exact Or.inl ⟨hc1, hc2⟩
              · refine Or.inr ⟨h1, by rw [hst_tcur]; exact h2, Tc, σc, kVal, hcL, ?_⟩
                by_cases ht : t = s₁Loc.epoch P
                · subst ht
                  rw [ha] at hcM_m
                  rcases hcM_m with ⟨hk, hd, hinit⟩
                  simp only [actEp', Function.update_self]
                  exact ⟨hk, hd, fun hv => hinit (by rwa [hstL_vR] at hv)⟩
                · simp only [actEp', Function.update_of_ne ht]
                  cases hat : actEp t with
                  | none => rw [hat] at hcM_m; exact hcM_m
                  | some pr =>
                    rw [hat] at hcM_m
                    rcases hcM_m with ⟨hk, hd, hinit⟩
                    exact ⟨hk, hd, fun hv => hinit (by rwa [hstL_vR] at hv)⟩
            hfuture := fun t ht => by
              rw [hst_tcur] at ht
              have hne_ep : t ≠ s₁Loc.epoch P := by
                intro heq; subst heq
                simp [esLoc1, hsender_ep, htcurL] at ht
              rcases hinv1.hfuture t ht with ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩
              exact ⟨by simp [actEp', hne_ep, hf1], hf2, hf3, hf4, hf5, hf6⟩
            hact := fun t0 ss0 rs0 ha0 => by
              by_cases ht0 : t0 = s₁Loc.epoch P
              · subst ht0
                simp only [actEp', Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha0
                rcases ha0 with ⟨rfl, rfl⟩
                refine ⟨hhe_ep, hle_ep, hvg_ep, by rw [hst_tcur, hsender_ep]; simp [esLoc1, htcurL], ?_, ?_, ?_⟩
                · cases phase1 with
                  | false =>
                    have hact_f : ActiveSessInv C ℓ encT idOf false (ks sIdx) o.1 rsA bk_fin sM' (tblL sIdx) := by
                      rcases hact_fin with ⟨stR', hi⟩
                      exact ⟨stR', { hi with syncRML := fun h => Bool.noConfusion h }⟩
                    simpa [hM2, tblM', tblL', sIdx, bk_fin] using hact_f
                  | true =>
                    simpa [hM2, tblM', tblL', sIdx, bk_fin] using hact_fin
                · intro _; rw [hrL_idx, hsender_ep, Function.update_self, hidx_cur]
                  simp [hM2, sIdx, bk_fin]
                · rw [hrL_tr]
                  simp only [hM2, sIdx, Function.update_self, Option.getD_some, bk_fin,
                    List.filter_cons, recE, beq_self_eq_true, ↓reduceIte, List.map_cons, hidx_cur]
                  exact congrArg (_ :: ·) htr_eq
              · simp only [actEp', Function.update_of_ne ht0] at ha0
                rcases hinv1.hact t0 ss0 rs0 ha0 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
                have hne_idx : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                  ht0 (sIdxMain_inj q tL h1 hhe_ep heq)
                refine ⟨h1, h2, h3, by rw [hst_tcur]; exact h4, ?_, ?_, ?_⟩
                · cases phase1 <;> simpa [hM2, tblM', tblL', hne_idx] using h5
                · intro heq_tc
                  rw [hst_tcur] at heq_tc
                  have hne_P : Party.senderOf t0 ≠ P := by
                    intro hp; rw [hp] at heq_tc
                    have : (esLoc1.g.st P).tcur = s₁Loc.epoch P := by simpa [esLoc1] using htcurL
                    exact ht0 (this.symm.trans heq_tc).symm
                  rw [hrL_idx, Function.update_of_ne hne_P]
                  simpa [hM2, hne_idx] using h6 heq_tc
                · rw [hrL_tr]
                  have hfalse : (recE.pos.epoch == t0) = false := beq_false_of_ne (Ne.symm ht0)
                  simpa [hM2, hne_idx, hfalse] using h7
            hunalloc := fun sIdx' hlt' hun' => by
              have hne_idx : sIdx' ≠ sIdx := by
                intro heq; subst heq
                have h0 := hun' (s₁Loc.epoch P) hhe_ep rfl
                simp [actEp'] at h0
              rcases hinv1.hunalloc sIdx' hlt' (fun t0 hh0 hs0 => by
                have ht0 : t0 ≠ s₁Loc.epoch P := fun heq => by subst heq; exact hne_idx hs0.symm
                simpa [actEp', ht0] using hun' t0 hh0 hs0) with ⟨hu1, hu2, hu3, hu4⟩
              exact ⟨hu1, by simp [hM2, hne_idx]; exact hu2, by simp [tblM', hne_idx, hu3],
                fun hp1 => by simp [tblL', hp1, hne_idx, hu4 hp1]⟩
            htrans := fun r hr => by
              rw [hrL_tr, List.mem_cons] at hr
              rcases hr with rfl | hr
              · refine ⟨htcurL.symm, hsender_ep.symm, ?_⟩
                rw [hst_tcur]; simp [recE, esLoc1, htcurL]
              · rcases hinv1.htrans r hr with ⟨ht1, ht2, ht3⟩
                exact ⟨ht1, ht2, by rw [hst_tcur]; exact ht3⟩ }


section Coupling

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
  (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)

private theorem coupledInv_mono_rem_r71tx
    {phase1 : Bool} {rem₁ rem₂ : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ}
    {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (h : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs phase1 rem₁ actEp esLoc esM esL winEp tblM tblL)
    (hle : rem₂ ≤ rem₁) :
    CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs phase1 rem₂ actEp esLoc esM esL winEp tblM tblL :=
  { h with htcur_le := fun P => Nat.le_trans (Nat.add_le_add_left hle _) (h.htcur_le P) }

private theorem coupledInv_set_esL_false_r71tx
    {rem : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ} (esL' : MultiESt_r71tx Pt ℓ)
    {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (h : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem actEp esLoc esM esL winEp tblM tblL) :
    CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem actEp esLoc esM esL' winEp tblM tblL :=
  { h with hphase1 := fun hp => Bool.noConfusion hp }


private theorem epoch_other_eq_of_sendsIn_succ_r71tx
    {phase1 : Bool} {rem : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ}
    {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs phase1 rem actEp esLoc esM esL winEp tblM tblL)
    {P : Party} (hsends : P.sendsIn (esLoc.g.epoch P + 1) = true) :
    esLoc.g.epoch P.other = esLoc.g.epoch P := by
  have hns : P.sendsIn (esLoc.g.epoch P) = false := sendsIn_consec_false_r71tx P _ hsends
  have hge : esLoc.g.epoch P ≤ esLoc.g.epoch P.other := by
    by_contra hlt
    have hlt' : esLoc.g.epoch P.other < esLoc.g.epoch P := by omega
    rw [hinv.hep_sends P hlt'] at hns; cases hns
  have hle : esLoc.g.epoch P.other ≤ esLoc.g.epoch P + 1 := by
    simpa using hinv.hep_le P.other
  by_contra hne
  have heq1 : esLoc.g.epoch P.other = esLoc.g.epoch P + 1 := by omega
  have hlt2 : esLoc.g.epoch P.other.other < esLoc.g.epoch P.other := by
    have ho : P.other.other = P := by cases P <;> rfl
    rw [ho, heq1]; omega
  have hso := hinv.hep_sends P.other hlt2
  rw [heq1, sendsIn_other] at hso
  simp [hsends] at hso

private theorem maxOpt_ge_right_r71tx (o : Option ℕ) (x : ℕ) : x ≤ maxOpt o x := by
  rcases o with _ | y
  · simp [maxOpt]
  · simp [maxOpt]

private theorem maxOpt_ge_some_left_r71tx (y x : ℕ) : y ≤ maxOpt (some y) x := by
  simp [maxOpt]

private theorem ltOpt_mono_right_r71tx (o : Option ℕ) {x y : ℕ} (h : ltOpt o x = true) (hle : x ≤ y) :
    ltOpt o y = true := by
  cases o with
  | none => rfl
  | some v => simp [ltOpt] at h ⊢; omega

private theorem epMgmt_same_none_r71tx
    {gL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {gM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase : eraseSt gM = eraseSt gL) {P : Party} {bad : Bool}
    (hs : P.sendsIn (gL.epoch P + 1) = false) (hq : qep < gL.epoch P) :
    gL.epMgmt 3 qep P bad = none ∧ gM.epMgmt 3 qep P bad = none := by
  have hep : gM.epoch = gL.epoch := eraseSt_epoch herase
  simp [GameState.epMgmt, hep, hs, hq]

private theorem epMgmt_same_some_r71tx
    {gL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {gM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase : eraseSt gM = eraseSt gL) {P : Party} {bad : Bool}
    (hs : P.sendsIn (gL.epoch P + 1) = false) (hq : ¬ qep < gL.epoch P) :
    gL.epMgmt 3 qep P bad = some gL ∧ gM.epMgmt 3 qep P bad = some gM := by
  have hep : gM.epoch = gL.epoch := eraseSt_epoch herase
  simp [GameState.epMgmt, hep, hs, hq]

private theorem epMgmt_new_none_r71tx
    {gL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {gM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase : eraseSt gM = eraseSt gL) {P : Party} {bad : Bool}
    (hs : P.sendsIn (gL.epoch P + 1) = true) (hq : qep < gL.epoch P + 1) :
    gL.epMgmt 3 qep P bad = none ∧ gM.epMgmt 3 qep P bad = none := by
  have hep : gM.epoch = gL.epoch := eraseSt_epoch herase
  simp [GameState.epMgmt, hep, hs, hq]

private theorem epMgmt_new_some_r71tx
    {gL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {gM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase : eraseSt gM = eraseSt gL) {P : Party} {bad : Bool}
    (hs : P.sendsIn (gL.epoch P + 1) = true) (hq : ¬ qep < gL.epoch P + 1) :
    ∃ s₁L s₁M,
      gL.epMgmt 3 qep P bad = some s₁L ∧
      gM.epMgmt 3 qep P bad = some s₁M ∧
      eraseSt s₁M = eraseSt s₁L ∧
      s₁L.st = gL.st ∧ s₁M.st = gM.st ∧
      s₁L.epoch = Function.update gL.epoch P (gL.epoch P + 1) ∧
      s₁L.idx = Function.update gL.idx P 0 ∧
      s₁L.trans = gL.trans ∧ s₁L.win = gL.win ∧
      s₁L.tL = (if bad && !(gL.safeCh 3 P) then some (maxOpt gL.tL (gL.epoch P + 1)) else gL.tL) ∧
      s₁M.tL = s₁L.tL := by
  have hep : gM.epoch = gL.epoch := eraseSt_epoch herase
  have hsc : gM.safeCh 3 P = gL.safeCh 3 P := eraseSt_safeCh herase 3 P
  let s0L := if bad && !(gL.safeCh 3 P) then gL.leak (gL.epoch P + 1) else gL
  let s0M := if bad && !(gM.safeCh 3 P) then gM.leak (gM.epoch P + 1) else gM
  let s₁L := { s0L with epoch := Function.update s0L.epoch P (s0L.epoch P + 1),
                        idx := Function.update s0L.idx P 0 }
  let s₁M := { s0M with epoch := Function.update s0M.epoch P (s0M.epoch P + 1),
                        idx := Function.update s0M.idx P 0 }
  refine ⟨s₁L, s₁M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [GameState.epMgmt, hs, hq, s₁L, s0L]
  · simp [GameState.epMgmt, hep, hs, hq, s₁M, s0M]
  · dsimp only [s₁L, s₁M, s0L, s0M]
    rw [hsc, hep]
    cases (bad && !(gL.safeCh 3 P)) <;>
      (cases gM; cases gL
       dsimp only [eraseSt, GameState.leak] at herase ⊢
       injection herase with _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
       subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
       rfl)
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁M, s0M]; cases (bad && !(gM.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s0L]; cases (bad && !(gL.safeCh 3 P)) <;> rfl
  · dsimp only [s₁L, s₁M, s0L, s0M]
    rw [hsc, hep]
    cases (bad && !(gL.safeCh 3 P)) <;> simp [GameState.leak, eraseSt_tL herase]

private theorem vSend_run_eq_tail_r71tx {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M E CCoins γV σV ssV rsV HS : Type} [Inhabited E]
    (hk : Hooks TSpec HS Γ T Sig SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (r : Option CCoins) (h : HS) :
    (vSend hk ctx P s m none r).run h =
      ((vSendStep1 hk ctx P s r).run h >>= fun p =>
        match p.1 with
        | none => pure (none, p.2)
        | some vp1 => (vSendTailM_r71tx hk ctx P vp1 m).run p.2) := by
  rw [vSend_eq_bind, StateT.run_bind]
  refine bind_congr fun ⟨s₁?, h1⟩ => ?_
  cases s₁? <;> rfl

private theorem midInv_postLeak_r71tx
    {phase1 : Bool} {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ}
    {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL none tblM tblL)
    {P : Party} {bad : Bool} (coins : BitVec 256)
    (hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true)
    {s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase1 : eraseSt s₁M = eraseSt s₁Loc)
    (hstL : s₁Loc.st = esLoc.g.st) (hstM : s₁M.st = esM.g.st)
    (hep1 : s₁Loc.epoch = Function.update esLoc.g.epoch P (esLoc.g.epoch P + 1))
    (hidx1 : s₁Loc.idx = Function.update esLoc.g.idx P 0)
    (htr1 : s₁Loc.trans = esLoc.g.trans) (hwin1 : s₁Loc.win = esLoc.g.win)
    (htL1 : s₁Loc.tL = (if bad && !(esLoc.g.safeCh 3 P) then some (maxOpt esLoc.g.tL (esLoc.g.epoch P + 1)) else esLoc.g.tL))
    (hpl1 : postLeak tL s₁Loc = true) :
    let t0 := esLoc.g.epoch P + 1
    let cOut := (dhScheme Dh).send (esLoc.g.st P).γ coins
    let pIk := (rootPRNG C.F encPt).up (esLoc.g.st P).root cOut.2.2
    let fs := locFS_r71tx C ℓ encT idOf
    let vp1Loc : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) :=
      { esLoc.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := pIk.1, vS := some (fs.initSender pIk.2) }
    let vp1M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
      { esM.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                        root := pIk.1, vS := some (.inl (fs.initSender pIk.2)) }
    let hLoc1 : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt :=
      { esLoc.h with loc := { esLoc.h.loc with cache := Function.update esLoc.h.loc.cache t0 (some (cOut.2.1, pIk.1, pIk.2)) } }
    let hM1 : MultiHSt_r71tx Pt :=
      { esM.h with cache := Function.update esM.h.cache t0 (some (cOut.2.1, pIk.1, pIk.2, none)) }
    CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem' actEp
      { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
      { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
      { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
      none tblM tblL := by
  intro t0 cOut pIk fs vp1Loc vp1M hLoc1 hM1
  have hep_other : esLoc.g.epoch P.other = esLoc.g.epoch P :=
    epoch_other_eq_of_sendsIn_succ_r71tx C encT idOf ℓ q qep tL par ks bs hinv hs_next
  have hep_all : ∀ Q, esLoc.g.epoch Q = esLoc.g.epoch P := by
    intro Q; cases P <;> cases Q <;> first | rfl | exact hep_other
  have htcur_all : ∀ Q, (esLoc.g.st Q).tcur = esLoc.g.epoch P := by
    intro Q; rw [(hinv.hparty_tcur Q).1, hep_all Q]
  have hsender_t0 : Party.senderOf t0 = P := (eq_senderOf_of_sendsIn hs_next).symm
  have hfut_t0 := hinv.hfuture t0 (by rw [htcur_all]; omega)
  have hact_t0 : actEp t0 = none := hfut_t0.1
  let esLoc1 : LocESt Pt ℓ :=
    { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
  let esM1 : MultiESt_r71tx Pt ℓ :=
    { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
  have htcur1 : ∀ Q, (esLoc1.g.st Q).tcur = if Q = P then t0 else (esLoc.g.st Q).tcur := by
    intro Q; by_cases hQ : Q = P
    · subst Q; simp [esLoc1, vp1Loc]
    · simp [esLoc1, hQ, hstL]
  have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ (esLoc1.g.st Q).tcur := by
    intro Q; rw [htcur1 Q]; split_ifs with hQ
    · subst Q; rw [(hinv.hparty_tcur P).1]; omega
    · exact le_rfl
  refine {
    habort_loc := rfl, habort_M := rfl
    hwin_loc := by rw [hwin1]; exact hinv.hwin_loc
    hwe := rfl
    herase := herase1
    hep_le := fun Q => by
      by_cases hQ : Q = P
      · subst Q
        have hne : P.other ≠ P := by cases P <;> decide
        simp [hep1, hne, hep_other]
      · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
        simp [hep1, hQ, hQo, hep_all Q]; omega
    hep_sends := fun Q hlt => by
      by_cases hQ : Q = P
      · subst Q; simpa [hep1, t0] using hs_next
      · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
        simp [hep1, hQ, hQo, hep_all Q] at hlt
    hphase1 := fun hp => Bool.noConfusion hp
    hphase2 := fun _ => by
      cases phase1 with
      | false =>
        rcases hinv.hphase2 rfl with ⟨cur0, htL0, hlt0, hle0⟩
        cases hbad : (bad && !(esLoc.g.safeCh 3 P))
        · refine ⟨cur0, ?_, hlt0, hle0⟩
          change s₁Loc.tL = some cur0
          rw [htL1]; simp [hbad, htL0]
        · refine ⟨maxOpt (some cur0) t0, ?_,
            ltOpt_mono_right_r71tx tL hlt0 (maxOpt_ge_some_left_r71tx cur0 t0),
            fun t' ha' => Nat.le_trans (hle0 t' ha') (maxOpt_ge_some_left_r71tx cur0 t0)⟩
          change s₁Loc.tL = some (maxOpt (some cur0) t0)
          rw [htL1, hbad, htL0]; rfl
      | true =>
        have hpl0 : postLeak tL esLoc.g = false := (hinv.hphase1 rfl).1
        cases hbad : (bad && !(esLoc.g.safeCh 3 P))
        · have : postLeak tL s₁Loc = false := by
            simp only [postLeak, htL1, hbad, Bool.false_eq_true, ↓reduceIte]
            simpa [postLeak] using hpl0
          rw [this] at hpl1; cases hpl1
        · let cur1 := maxOpt esLoc.g.tL t0
          have hs1_tL : s₁Loc.tL = some cur1 := by rw [htL1]; simp [hbad, cur1, t0]
          have hlt1 : ltOpt tL cur1 = true := by simpa [postLeak, hs1_tL] using hpl1
          refine ⟨cur1, hs1_tL, hlt1, fun t' ha' => ?_⟩
          cases ha_eq : actEp t' with
          | none => exact absurd ha_eq ha'
          | some pair =>
            have ht'_le := (hinv.hact t' pair.1 pair.2 ha_eq).2.2.2.1
            rw [htcur_all] at ht'_le
            have ht0_le : t0 ≤ cur1 := maxOpt_ge_right_r71tx esLoc.g.tL t0
            omega
    hparty_id := fun Q => by
      by_cases hQ : Q = P
      · subst Q; simp [vp1Loc, vp1M, (hinv.hparty_id P).1, (hinv.hparty_id P).2]
      · simp [hQ, hstL, hstM, (hinv.hparty_id Q).1, (hinv.hparty_id Q).2]
    hparty_tcur := fun Q => by
      by_cases hQ : Q = P
      · subst Q; simp [vp1Loc, vp1M, hep1, t0]
      · simp [hQ, hstL, hstM, hep1, (hinv.hparty_tcur Q).1, (hinv.hparty_tcur Q).2]
    hparty_base := fun Q => by
      by_cases hQ : Q = P
      · subst Q; simp [vp1Loc, vp1M]
      · simp [hQ, hstL, hstM]
        exact hinv.hparty_base Q
    htcur_le := fun Q => by
      have h0 := hinv.htcur_le Q
      rw [htcur1 Q]; split_ifs with hQ
      · subst Q; rw [(hinv.hparty_tcur P).1] at h0; omega
      · omega
    hvR_gt := fun Q t ht => by
      have ht0' : (esLoc.g.st Q).tcur < t := Nat.lt_of_le_of_lt (htcur_mono Q) ht
      by_cases hQ : Q = P
      · subst Q
        simpa [esLoc1, esM1, vp1Loc, vp1M] using hinv.hvR_gt P t ht0'
      · simpa [esLoc1, esM1, hQ, hstL, hstM] using hinv.hvR_gt Q t ht0'
    hvS := fun Q => by
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self, vp1Loc, vp1M]
        refine ⟨t0, le_rfl, hs_next, fun _ => rfl, ?_⟩
        simp [hact_t0]
      · simp only [Function.update_of_ne hQ, hstL, hstM]
        exact hinv.hvS Q
    hvR := fun Q t => by
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self, vp1Loc, vp1M]
        have h0 := hinv.hvR P t
        cases hv : (esLoc.g.st P).vR t with
        | none => simpa [hv] using h0
        | some rs =>
          simp only [hv] at h0
          refine ⟨h0.1, ?_, h0.2.2⟩
          have hle := h0.2.1; rw [(hinv.hparty_tcur P).1] at hle; omega
      · simp only [Function.update_of_ne hQ, hstL, hstM]
        exact hinv.hvR Q t
    hcache := fun t => by
      by_cases ht : t = t0
      · subst ht
        right
        refine ⟨by omega, ?_, cOut.2.1, pIk.1, pIk.2, ?_, ?_⟩
        · rw [hsender_t0, htcur1 P]; simp
        · simp [hLoc1]
        · simp [hact_t0, hM1]
      · rcases hinv.hcache t with ⟨hcL, hcM⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hrest⟩
        · left; simp [hLoc1, hM1, ht, hcL, hcM]
        · right
          refine ⟨h1, Nat.le_trans h2 (htcur_mono _), Tc, σc, kVal,
            by simp [hLoc1, ht, hcL], ?_⟩
          cases ha : actEp t with
          | none =>
            simp only [ha] at hrest ⊢
            simp [hM1, ht, hrest]
          | some pair =>
            simp only [ha] at hrest ⊢
            rcases hrest with ⟨hk, ⟨kD, hcM⟩, hinit⟩
            refine ⟨hk, ⟨kD, by simp [hM1, ht, hcM]⟩, fun hvr => hinit ?_⟩
            by_cases hR : Party.receiverOf t = P
            · rw [hR] at hvr ⊢; simpa [esLoc1, vp1Loc] using hvr
            · simpa [esLoc1, hR, hstL] using hvr
    hfuture := fun t ht => by
      have ht_old : (esLoc.g.st (Party.senderOf t)).tcur < t :=
        Nat.lt_of_le_of_lt (htcur_mono _) ht
      have hne : t ≠ t0 := by
        intro heq; subst heq
        rw [hsender_t0, htcur1 P] at ht; simp at ht
      rcases hinv.hfuture t ht_old with ⟨ha, hcL, hcM, hfL, hfM, hsM⟩
      exact ⟨ha, by simp [hLoc1, hne, hcL], by simp [hM1, hne, hcM], hfL, hfM, hsM⟩
    hact := fun t' ss0 rs0 ha => by
      have hne : t' ≠ t0 := by intro heq; subst heq; rw [hact_t0] at ha; cases ha
      rcases hinv.hact t' ss0 rs0 ha with ⟨hhe, hqep', hvg, ht'_le, hactI, hcnt, htr_eq⟩
      refine ⟨hhe, hqep', hvg, Nat.le_trans ht'_le (htcur_mono _), ?_, ?_, ?_⟩
      · cases phase1 with
        | false => exact hactI
        | true => exact activeSessInv_to_phase2 C ℓ encT idOf hactI
      · intro htcur_eq
        by_cases hS : Party.senderOf t' = P
        · rw [hS, htcur1 P] at htcur_eq; simp at htcur_eq; exact absurd htcur_eq.symm hne
        · rw [htcur1 (Party.senderOf t')] at htcur_eq; simp only [hS, ↓reduceIte] at htcur_eq
          simp only [hM1, hidx1, Function.update_of_ne hS]
          exact hcnt htcur_eq
      · simp only [hM1, htr1]
        exact htr_eq
    hunalloc := fun sIdx hslt hun => by
      rcases hinv.hunalloc sIdx hslt hun with ⟨hu1, hu2, hu3, _⟩
      exact ⟨hu1, hu2, hu3, fun hp => Bool.noConfusion hp⟩
    htrans := fun r hr => by
      simp only [htr1] at hr
      rcases hinv.htrans r hr with ⟨ht1, ht2, ht3⟩
      exact ⟨ht1, ht2, Nat.le_trans ht3 (htcur_mono _)⟩ }

private theorem midInv_rootPost_phase1_r71tx
    {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ}
    {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true (rem' + 1) actEp esLoc esM esL none tblM tblL)
    {P : Party} (coins : BitVec 256)
    (hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true)
    {s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase1 : eraseSt s₁M = eraseSt s₁Loc)
    (hstL : s₁Loc.st = esLoc.g.st) (hstM : s₁M.st = esM.g.st)
    (hep1 : s₁Loc.epoch = Function.update esLoc.g.epoch P (esLoc.g.epoch P + 1))
    (hidx1 : s₁Loc.idx = Function.update esLoc.g.idx P 0)
    (htr1 : s₁Loc.trans = esLoc.g.trans) (hwin1 : s₁Loc.win = esLoc.g.win)
    (hpl1 : postLeak tL s₁Loc = false)
    {σ' kLoc kM : BitVec 256} {optIdx : Option ℕ}
    {stLoc' : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt}
    {stM' : MultiHSt_r71tx Pt}
    (hroot : RootPost_r71tx q qep tL par ks (esLoc.g.epoch P + 1) esLoc.h stLoc' esM.h stM' kLoc kM optIdx) :
    let t0 := esLoc.g.epoch P + 1
    let cOut := (dhScheme Dh).send (esLoc.g.st P).γ coins
    let fs := locFS_r71tx C ℓ encT idOf
    let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ := match optIdx with
      | none => .inl (fs.initSender kM)
      | some sIdx => .inr sIdx
    let vp1Loc : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) :=
      { esLoc.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := σ', vS := some (fs.initSender kLoc) }
    let vp1M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
      { esM.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                        root := σ', vS := some ssv }
    let hLoc1 : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt :=
      { stLoc' with loc := { stLoc'.loc with cache := Function.update stLoc'.loc.cache t0 (some (cOut.2.1, σ', kLoc)) } }
    let hM1 : MultiHSt_r71tx Pt :=
      { stM' with cache := Function.update stM'.cache t0 (some (cOut.2.1, σ', kM, optIdx)) }
    ∃ actEp1,
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true rem' actEp1
        { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
        { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
        { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
        none tblM tblL := by
  intro t0 cOut fs ssv vp1Loc vp1M hLoc1 hM1
  rcases hroot with ⟨hcL_eq, hcM_eq, hbM_eq, hlf_eq, hf_other, hcases⟩
  rcases hinv.hphase1 rfl with ⟨_, _, hlf0, hsc0⟩
  have hep_other : esLoc.g.epoch P.other = esLoc.g.epoch P :=
    epoch_other_eq_of_sendsIn_succ_r71tx C encT idOf ℓ q qep tL par ks bs hinv hs_next
  have hep_all : ∀ Q, esLoc.g.epoch Q = esLoc.g.epoch P := by
    intro Q; cases P <;> cases Q <;> first | rfl | exact hep_other
  have htcur_all : ∀ Q, (esLoc.g.st Q).tcur = esLoc.g.epoch P := by
    intro Q; rw [(hinv.hparty_tcur Q).1, hep_all Q]
  have hsender_t0 : Party.senderOf t0 = P := (eq_senderOf_of_sendsIn hs_next).symm
  have hfut_t0 := hinv.hfuture t0 (by rw [htcur_all]; omega)
  have hact_t0 : actEp t0 = none := hfut_t0.1
  let esLoc1 : LocESt Pt ℓ :=
    { g := { s₁Loc with st := Function.update s₁Loc.st P vp1Loc }, h := hLoc1, abort := false }
  let esM1 : MultiESt_r71tx Pt ℓ :=
    { g := { s₁M with st := Function.update s₁M.st P vp1M }, h := hM1, abort := false }
  have htcur1 : ∀ Q, (esLoc1.g.st Q).tcur = if Q = P then t0 else (esLoc.g.st Q).tcur := by
    intro Q; by_cases hQ : Q = P
    · subst Q; simp [esLoc1, vp1Loc]
    · simp [esLoc1, hQ, hstL]
  have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ (esLoc1.g.st Q).tcur := by
    intro Q; rw [htcur1 Q]; split_ifs with hQ
    · subst Q; rw [(hinv.hparty_tcur P).1]; omega
    · exact le_rfl
  have hpl_es1 : postLeak tL esLoc1.g = false := by
    simpa [postLeak, esLoc1] using hpl1
  rcases hcases with ⟨hopt_eq, hkM_eq, hus_eq⟩ | ⟨hopt_eq, hhe, hle, hvg, hkL_eq, hus_eq⟩
  · subst hopt_eq; subst kM
    refine ⟨actEp, {
      habort_loc := rfl, habort_M := rfl
      hwin_loc := by rw [hwin1]; exact hinv.hwin_loc
      hwe := rfl
      herase := herase1
      hep_le := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          have hne : P.other ≠ P := by cases P <;> decide
          simp [hep1, hne, hep_other]
        · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
          simp [hep1, hQ, hQo, hep_all Q]; omega
      hep_sends := fun Q hlt => by
        by_cases hQ : Q = P
        · subst Q; simpa [hep1, t0] using hs_next
        · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
          simp [hep1, hQ, hQo, hep_all Q] at hlt
      hphase1 := fun _ => ⟨hpl_es1, rfl, by simp [hM1, hlf_eq, hlf0], fun t' ha' => by
        simp [hM1, hbM_eq, hsc0 t' ha']⟩
      hphase2 := fun hp => Bool.noConfusion hp
      hparty_id := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M, (hinv.hparty_id P).1, (hinv.hparty_id P).2]
        · simp [hQ, hstL, hstM, (hinv.hparty_id Q).1, (hinv.hparty_id Q).2]
      hparty_tcur := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M, hep1, t0]
        · simp [hQ, hstL, hstM, hep1, (hinv.hparty_tcur Q).1, (hinv.hparty_tcur Q).2]
      hparty_base := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M]
        · simp [hQ, hstL, hstM]; exact hinv.hparty_base Q
      htcur_le := fun Q => by
        have h0 := hinv.htcur_le Q
        rw [htcur1 Q]; split_ifs with hQ
        · subst Q; rw [(hinv.hparty_tcur P).1] at h0; omega
        · omega
      hvR_gt := fun Q t ht => by
        have ht0' : (esLoc.g.st Q).tcur < t := Nat.lt_of_le_of_lt (htcur_mono Q) ht
        by_cases hQ : Q = P
        · subst Q; simpa [esLoc1, esM1, vp1Loc, vp1M] using hinv.hvR_gt P t ht0'
        · simpa [esLoc1, esM1, hQ, hstL, hstM] using hinv.hvR_gt Q t ht0'
      hvS := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, vp1Loc, vp1M, ssv]
          exact ⟨t0, le_rfl, hs_next, fun _ => rfl, by simp [hact_t0]⟩
        · simp only [Function.update_of_ne hQ, hstL, hstM]
          exact hinv.hvS Q
      hvR := fun Q t => by
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, vp1Loc, vp1M]
          have h0 := hinv.hvR P t
          cases hv : (esLoc.g.st P).vR t with
          | none => simpa [hv] using h0
          | some rs =>
            simp only [hv] at h0
            refine ⟨h0.1, ?_, h0.2.2⟩
            have hle' := h0.2.1; rw [(hinv.hparty_tcur P).1] at hle'; omega
        · simp only [Function.update_of_ne hQ, hstL, hstM]
          exact hinv.hvR Q t
      hcache := fun t => by
        by_cases ht : t = t0
        · subst ht; right
          refine ⟨by omega, ?_, cOut.2.1, σ', kLoc, by simp [hLoc1, t0], by simp [hact_t0, hM1, t0]⟩
          rw [hsender_t0, htcur1 P]; simp
        · rcases hinv.hcache t with ⟨hcL, hcM⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hrest⟩
          · left; simp [hLoc1, hM1, ht, hcL_eq, hcM_eq, hcL, hcM]
          · right
            refine ⟨h1, Nat.le_trans h2 (htcur_mono _), Tc, σc, kVal,
              by simp [hLoc1, ht, hcL_eq, hcL], ?_⟩
            cases ha : actEp t with
            | none =>
              simp only [ha] at hrest ⊢
              simp [hM1, ht, hcM_eq, hrest]
            | some pair =>
              simp only [ha] at hrest ⊢
              rcases hrest with ⟨hk, ⟨kD, hcM⟩, hinit⟩
              refine ⟨hk, ⟨kD, by simp [hM1, ht, hcM_eq, hcM]⟩, fun hvr => hinit ?_⟩
              by_cases hR : Party.receiverOf t = P
              · rw [hR] at hvr ⊢; simpa [esLoc1, vp1Loc] using hvr
              · simpa [esLoc1, hR, hstL] using hvr
      hfuture := fun t ht => by
        have ht_old : (esLoc.g.st (Party.senderOf t)).tcur < t :=
          Nat.lt_of_le_of_lt (htcur_mono _) ht
        have hne : t ≠ t0 := by
          intro heq; subst heq; rw [hsender_t0, htcur1 P] at ht; simp at ht
        rcases hinv.hfuture t ht_old with ⟨ha, hcL, hcM, hfL, hfM, hsM⟩
        rcases hf_other t hne with ⟨hf1, hf2, hf3⟩
        exact ⟨ha, by simp [hLoc1, hne, hcL_eq, hcL],
          by simp [hM1, hne, hcM_eq, hcM],
          by simp [hLoc1, hf1, hfL],
          by simp [hM1, hf2, hfM],
          by simp [hM1, hf3, hsM]⟩
      hact := fun t' ss0 rs0 ha => by
        have hne : t' ≠ t0 := by intro heq; subst heq; rw [hact_t0] at ha; cases ha
        rcases hinv.hact t' ss0 rs0 ha with ⟨hhe', hqep', hvg', ht'_le, hactI, hcnt, htr_eq⟩
        refine ⟨hhe', hqep', hvg', Nat.le_trans ht'_le (htcur_mono _), ?_, ?_, ?_⟩
        · simpa [esM1, hM1, hbM_eq] using hactI
        · intro htcur_eq
          by_cases hS : Party.senderOf t' = P
          · rw [hS, htcur1 P] at htcur_eq; simp at htcur_eq; exact absurd htcur_eq.symm hne
          · rw [htcur1 (Party.senderOf t')] at htcur_eq; simp only [hS, ↓reduceIte] at htcur_eq
            simp only [hM1, hbM_eq, hidx1, Function.update_of_ne hS]
            exact hcnt htcur_eq
        · simpa [esLoc1, esM1, hM1, hbM_eq, htr1] using htr_eq
      hunalloc := fun sIdx hslt hun => by
        rcases hinv.hunalloc sIdx hslt hun with ⟨hu1, hu2, hu3, hu4⟩
        exact ⟨by simp [hLoc1, hus_eq, hu1], by simp [hM1, hbM_eq, hu2], hu3, hu4⟩
      htrans := fun r hr => by
        simp only [htr1] at hr
        rcases hinv.htrans r hr with ⟨ht1, ht2, ht3⟩
        exact ⟨ht1, ht2, Nat.le_trans ht3 (htcur_mono _)⟩ }⟩
  · subst hopt_eq; subst kLoc
    let sIdx0 := sIdxMain q tL t0
    have hslt0 : sIdx0 < mSessMain q qep tL :=
      sIdxMain_lt_mSessMain q qep tL par t0 (by simp; omega) hvg
    have hun0 : esLoc.h.usedSlot sIdx0 = false ∧ esM.h.book sIdx0 = none ∧
        tblM sIdx0 = hInit (bs sIdx0) (.seed (ks sIdx0)) ∧
        (true = true → tblL sIdx0 = hInit (bs sIdx0) (.seed (ks sIdx0))) := by
      refine hinv.hunalloc sIdx0 hslt0 fun t' hhe' heq_s => ?_
      have ht'_eq : t' = t0 := sIdxMain_inj q tL hhe' hhe heq_s
      subst ht'_eq; exact hact_t0
    rcases hun0 with ⟨_, hb0_none, htblM0, htblL0⟩
    let actEp1 : ActMap_r71tx := Function.update actEp t0
      (some (fs.initSender (ks sIdx0), fs.initReceiver (ks sIdx0)))
    refine ⟨actEp1, {
      habort_loc := rfl, habort_M := rfl
      hwin_loc := by rw [hwin1]; exact hinv.hwin_loc
      hwe := rfl
      herase := herase1
      hep_le := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          have hne : P.other ≠ P := by cases P <;> decide
          simp [hep1, hne, hep_other]
        · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
          simp [hep1, hQ, hQo, hep_all Q]; omega
      hep_sends := fun Q hlt => by
        by_cases hQ : Q = P
        · subst Q; simpa [hep1, t0] using hs_next
        · have hQo : Q.other = P := by cases P <;> cases Q <;> simp_all
          simp [hep1, hQ, hQo, hep_all Q] at hlt
      hphase1 := fun _ => ⟨hpl_es1, rfl, by simp [hM1, hlf_eq, hlf0], fun t' ha' => by
        by_cases ht' : t' = t0
        · subst ht'; simp [hM1, hbM_eq, sIdx0, hb0_none]
        · simp only [actEp1, Function.update_of_ne ht'] at ha'
          simp [hM1, hbM_eq, hsc0 t' ha']⟩
      hphase2 := fun hp => Bool.noConfusion hp
      hparty_id := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M, (hinv.hparty_id P).1, (hinv.hparty_id P).2]
        · simp [hQ, hstL, hstM, (hinv.hparty_id Q).1, (hinv.hparty_id Q).2]
      hparty_tcur := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M, hep1, t0]
        · simp [hQ, hstL, hstM, hep1, (hinv.hparty_tcur Q).1, (hinv.hparty_tcur Q).2]
      hparty_base := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [vp1Loc, vp1M]
        · simp [hQ, hstL, hstM]; exact hinv.hparty_base Q
      htcur_le := fun Q => by
        have h0 := hinv.htcur_le Q
        rw [htcur1 Q]; split_ifs with hQ
        · subst Q; rw [(hinv.hparty_tcur P).1] at h0; omega
        · omega
      hvR_gt := fun Q t ht => by
        have ht0' : (esLoc.g.st Q).tcur < t := Nat.lt_of_le_of_lt (htcur_mono Q) ht
        by_cases hQ : Q = P
        · subst Q; simpa [esLoc1, esM1, vp1Loc, vp1M] using hinv.hvR_gt P t ht0'
        · simpa [esLoc1, esM1, hQ, hstL, hstM] using hinv.hvR_gt Q t ht0'
      hvS := fun Q => by
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, vp1Loc, vp1M, ssv, t0]
          refine ⟨esLoc.g.epoch P + 1, le_rfl, hs_next, fun _ => rfl, ?_⟩
          simp [actEp1, sIdx0, t0]
        · simp only [Function.update_of_ne hQ, hstL, hstM]
          have h0 := hinv.hvS Q
          cases hv : (esLoc.g.st Q).vS with
          | none => simpa [hv] using h0
          | some ss =>
            simp only [hv] at h0
            rcases h0 with ⟨ts, hts_le, hts_sends, hts_eq, hts_m⟩
            have hts_ne : ts ≠ t0 := by rw [htcur_all Q] at hts_le; omega
            refine ⟨ts, hts_le, hts_sends, hts_eq, ?_⟩
            simpa [actEp1, hts_ne] using hts_m
      hvR := fun Q t => by
        by_cases ht : t = t0
        · subst ht
          have hgt0 : (esLoc.g.st Q).tcur < t0 := by rw [htcur_all Q]; omega
          rcases hinv.hvR_gt Q t0 hgt0 with ⟨hvL0, hvM0⟩
          by_cases hQ : Q = P
          · subst Q; simp [vp1Loc, vp1M, hvL0, hvM0]
          · simp [hQ, hstL, hstM, hvL0, hvM0]
        · by_cases hQ : Q = P
          · subst Q
            simp only [Function.update_self, vp1Loc, vp1M]
            have h0 := hinv.hvR P t
            cases hv : (esLoc.g.st P).vR t with
            | none => simpa [hv] using h0
            | some rs =>
              simp only [hv] at h0
              refine ⟨h0.1, ?_, by simpa [actEp1, ht] using h0.2.2⟩
              have hle' := h0.2.1; rw [(hinv.hparty_tcur P).1] at hle'; omega
          · simp only [Function.update_of_ne hQ, hstL, hstM]
            have h0 := hinv.hvR Q t
            cases hv : (esLoc.g.st Q).vR t with
            | none => simpa [hv] using h0
            | some rs =>
              simp only [hv] at h0
              exact ⟨h0.1, h0.2.1, by simpa [actEp1, ht] using h0.2.2⟩
      hcache := fun t => by
        by_cases ht : t = t0
        · subst ht; right
          refine ⟨by omega, ?_, cOut.2.1, σ', ks sIdx0, by simp [hLoc1, sIdx0, t0], ?_⟩
          · rw [hsender_t0, htcur1 P]; simp
          · simp only [actEp1, Function.update_self]
            exact ⟨rfl, ⟨kM, by simp [hM1, t0]⟩, fun _ => rfl⟩
        · rcases hinv.hcache t with ⟨hcL, hcM⟩ | ⟨h1, h2, Tc, σc, kVal, hcL, hrest⟩
          · left; simp [hLoc1, hM1, ht, hcL_eq, hcM_eq, hcL, hcM]
          · right
            refine ⟨h1, Nat.le_trans h2 (htcur_mono _), Tc, σc, kVal,
              by simp [hLoc1, ht, hcL_eq, hcL], ?_⟩
            simp only [actEp1, Function.update_of_ne ht]
            cases ha : actEp t with
            | none =>
              simp only [ha] at hrest ⊢
              simp [hM1, ht, hcM_eq, hrest]
            | some pair =>
              simp only [ha] at hrest ⊢
              rcases hrest with ⟨hk, ⟨kD, hcM⟩, hinit⟩
              refine ⟨hk, ⟨kD, by simp [hM1, ht, hcM_eq, hcM]⟩, fun hvr => hinit ?_⟩
              by_cases hR : Party.receiverOf t = P
              · rw [hR] at hvr ⊢; simpa [esLoc1, vp1Loc] using hvr
              · simpa [esLoc1, hR, hstL] using hvr
      hfuture := fun t ht => by
        have ht_old : (esLoc.g.st (Party.senderOf t)).tcur < t :=
          Nat.lt_of_le_of_lt (htcur_mono _) ht
        have hne : t ≠ t0 := by
          intro heq; subst heq; rw [hsender_t0, htcur1 P] at ht; simp at ht
        rcases hinv.hfuture t ht_old with ⟨ha, hcL, hcM, hfL, hfM, hsM⟩
        rcases hf_other t hne with ⟨hf1, hf2, hf3⟩
        exact ⟨by simp [actEp1, hne, ha],
          by simp [hLoc1, hne, hcL_eq, hcL],
          by simp [hM1, hne, hcM_eq, hcM],
          by simp [hLoc1, hf1, hfL],
          by simp [hM1, hf2, hfM],
          by simp [hM1, hf3, hsM]⟩
      hact := fun t' ss0 rs0 ha => by
        by_cases ht' : t' = t0
        · subst ht'
          simp only [actEp1, Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha
          rcases ha with ⟨rfl, rfl⟩
          refine ⟨hhe, hle, hvg, ?_, ?_, ?_, ?_⟩
          · rw [hsender_t0, htcur1 P]; simp
          · simp only [hM1, hbM_eq, sIdx0, hb0_none, Option.getD_none]
            rw [htblM0, htblL0 rfl]
            exact activeSessInv_init C ℓ encT idOf true (ks sIdx0) (bs sIdx0)
          · intro _
            simp [hM1, hbM_eq, sIdx0, hb0_none, hsender_t0, hidx1]
          · simp only [hM1, hbM_eq, sIdx0, hb0_none, Option.getD_none, htr1]
            have hfilt : esLoc.g.trans.filter (fun r => r.pos.epoch == t0) = [] := by
              rw [List.filter_eq_nil_iff]
              intro r hr
              rcases hinv.htrans r hr with ⟨_, _, hr_le⟩
              rw [htcur_all] at hr_le
              simp only [beq_iff_eq]; omega
            simp [hfilt]
        · simp only [actEp1, Function.update_of_ne ht'] at ha
          rcases hinv.hact t' ss0 rs0 ha with ⟨hhe', hqep', hvg', ht'_le, hactI, hcnt, htr_eq⟩
          refine ⟨hhe', hqep', hvg', Nat.le_trans ht'_le (htcur_mono _), ?_, ?_, ?_⟩
          · simpa [esM1, hM1, hbM_eq] using hactI
          · intro htcur_eq
            by_cases hS : Party.senderOf t' = P
            · rw [hS, htcur1 P] at htcur_eq; simp at htcur_eq; exact absurd htcur_eq.symm ht'
            · rw [htcur1 (Party.senderOf t')] at htcur_eq; simp only [hS, ↓reduceIte] at htcur_eq
              simp only [hM1, hbM_eq, hidx1, Function.update_of_ne hS]
              exact hcnt htcur_eq
          · simpa [esLoc1, esM1, hM1, hbM_eq, htr1] using htr_eq
      hunalloc := fun sIdx hslt hun => by
        have hne_s : sIdx ≠ sIdx0 := by
          intro heq; subst heq
          have h0 := hun t0 hhe rfl
          simp [actEp1] at h0
        have hun_old : ∀ t', healEpoch tL ≤ t' → sIdxMain q tL t' = sIdx → actEp t' = none := by
          intro t' hhe' hs_eq
          have ht'_ne : t' ≠ t0 := by intro heq; subst heq; exact hne_s hs_eq.symm
          have h0 := hun t' hhe' hs_eq
          simpa [actEp1, ht'_ne] using h0
        rcases hinv.hunalloc sIdx hslt hun_old with ⟨hu1, hu2, hu3, hu4⟩
        exact ⟨by simp [hLoc1, hus_eq, sIdx0, t0, hne_s, hu1],
          by simp [hM1, hbM_eq, hu2], hu3, hu4⟩
      htrans := fun r hr => by
        simp only [htr1] at hr
        rcases hinv.htrans r hr with ⟨ht1, ht2, ht3⟩
        exact ⟨ht1, ht2, Nat.le_trans ht3 (htcur_mono _)⟩ }⟩

private theorem runLocCont_transmit_r71tx
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ) (esLoc : LocESt Pt ℓ)
    (habort : esLoc.abort = false) (hwin : esLoc.g.win = false) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par
    runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esLoc none =
    match esLoc.g.epMgmt 3 qep P r.isSome with
    | none => runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) esLoc none
    | some s₁ => (do
      let (res, h') ← simulateQ (keySlotFixedImpl ks) ((vSend hkLoc s₁ P (s₁.st P) m none r).run esLoc.h)
      match res with
      | none =>
        runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) { esLoc with h := h', abort := true } none
      | some (st', ct) =>
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
        runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
          { g := s₁.record 3 P st' recE false, h := h', abort := false } none) := by
  intro hkLoc
  unfold runLocCont
  rw [simulateQ_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
    implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, habort, hwin, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]
  cases hep : esLoc.g.epMgmt 3 qep P r.isSome with
  | none =>
    simp [StateT.run_pure, pure_bind, simulateQ_pure]
  | some s₁ =>
    simp only [StateT.run_bind, run_stateT_lift_r71tx, bind_assoc, pure_bind, simulateQ_bind]
    refine bind_congr fun x => ?_
    rcases x with ⟨res, h'⟩
    cases res with
    | none => simp [StateT.run_set, pure_bind, simulateQ_pure]
    | some pair =>
      rcases pair with ⟨st', ct⟩
      have hes : ({ esLoc with g := s₁.record 3 P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false, h := h' } : LocESt Pt ℓ) =
          { g := s₁.record 3 P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false, h := h', abort := false } := by
        cases esLoc; simp at habort; subst habort; rfl
      simp [StateT.run_set, pure_bind, simulateQ_pure]

private theorem runSideCont_transmit_r71tx (la : Bool)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ) (esS : MultiESt_r71tx Pt ℓ) (tbl : ℕ → SessHSt Pt ℓ)
    (habort : esS.abort = false) (hwin : esS.g.win = false) :
    let hkM := hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 qep true tL par la
    runSideCont C Dh encPt encT idOf ℓ q qep tL par la
      (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esS none tbl =
    match esS.g.epMgmt 3 qep P r.isSome with
    | none => runSideCont C Dh encPt encT idOf ℓ q qep tL par la (k none) esS none tbl
    | some s₁ => (do
      let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
        ((vSend hkM s₁ P (s₁.st P) m none r).run esS.h)).run (fun _ => false, tbl)
      match res with
      | none =>
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par la (k none)
          { esS with h := h', abort := true } none stP'
      | some (st', ct) =>
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par la (k (some ct))
          { g := s₁.record 3 P st' recE false, h := h', abort := false } none stP') := by
  intro hkM
  unfold runSideCont runSideContSt_r71tx
  rw [simulateQ_bind, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
    implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, habort, hwin, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]
  cases hep : esS.g.epMgmt 3 qep P r.isSome with
  | none =>
    simp [StateT.run_pure, pure_bind, simulateQ_pure, simulateQ_bind]
  | some s₁ =>
    simp only [StateT.run_bind, run_stateT_lift_r71tx, bind_assoc, pure_bind, simulateQ_bind, map_bind]
    refine bind_congr fun x => ?_
    rcases x with ⟨⟨res, h'⟩, stP'⟩
    cases res with
    | none => simp [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
    | some pair =>
      rcases pair with ⟨st', ct⟩
      have hes : ({ esS with g := s₁.record 3 P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false, h := h' } : MultiESt_r71tx Pt ℓ) =
          { g := s₁.record 3 P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false, h := h', abort := false } := by
        cases esS; simp at habort; subst habort; rfl
      simp [StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]

private theorem vSend_eq_bind_tailM_r71tx {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M E CCoins γV σV ssV rsV HS : Type} [Inhabited E]
    (hk : Hooks TSpec HS Γ T Sig SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (r : Option CCoins) :
    vSend hk ctx P s m none r =
      (vSendStep1 hk ctx P s r >>= fun p =>
        match p with
        | none => pure none
        | some vp1 => vSendTailM_r71tx hk ctx P vp1 m) := by
  rw [vSend_eq_bind]
  refine bind_congr fun s₁? => ?_
  cases s₁? <;> rfl

attribute [local irreducible] vSendTailM_r71tx in
private theorem vSend_loc_new_none_r71tx
    (s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (h : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)
    (hs : (s₁Loc.st P).id.sendsIn ((s₁Loc.st P).tcur + 1) = true) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par
    simulateQ (keySlotFixedImpl ks) ((vSend hkLoc s₁Loc P (s₁Loc.st P) m none none).run h) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
        simulateQ (keySlotFixedImpl ks)
          ((vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins)).run h)) := by
  intro hkLoc
  have h1 : vSend hkLoc s₁Loc P (s₁Loc.st P) m none none =
      (StateT.lift (sampleT (BitVec 256)) >>= fun coins =>
        vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins)) := by
    rw [vSend_eq_bind_tailM_r71tx]
    conv_rhs => enter [2]; ext coins; rw [vSend_eq_bind_tailM_r71tx]
    dsimp only [vSendStep1, hkLoc, hooksLocalMainSlot]
    simp only [hs, ↓reduceIte, bind_assoc, pure_bind]
  rw [h1, StateT.run_bind, run_stateT_lift_r71tx, simulateQ_bind, simulateQ_bind, sim_sampleT_fixed]
  simp only [simulateQ_pure, bind_assoc, pure_bind]

attribute [local irreducible] vSendTailM_r71tx in
private theorem vSend_multi_new_none_r71tx (la : Bool)
    (s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (h : MultiHSt_r71tx Pt) (stP : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ))
    (hs : (s₁M.st P).id.sendsIn ((s₁M.st P).tcur + 1) = true) :
    let hkM := hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 qep true tL par la
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((vSend hkM s₁M P (s₁M.st P) m none none).run h)).run stP =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
        (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          ((vSend hkM s₁M P (s₁M.st P) m none (some coins)).run h)).run stP) := by
  intro hkM
  have h1 : vSend hkM s₁M P (s₁M.st P) m none none =
      (StateT.lift (sampleT (BitVec 256)) >>= fun coins =>
        vSend hkM s₁M P (s₁M.st P) m none (some coins)) := by
    rw [vSend_eq_bind_tailM_r71tx]
    conv_rhs => enter [2]; ext coins; rw [vSend_eq_bind_tailM_r71tx]
    dsimp only [vSendStep1, hkM, hooksFSMultiBucketAuth]
    simp only [hs, ↓reduceIte, bind_assoc, pure_bind]
  rw [h1, StateT.run_bind, run_stateT_lift_r71tx, simulateQ_bind, StateT.run_bind,
      simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run]
  simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]

attribute [local irreducible] rootLocalMainSlot vSendTailM_r71tx in
private theorem vSend_loc_new_coins_r71tx
    (s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (h : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt)
    (t0 : ℕ) (ht0 : (s₁Loc.st P).tcur + 1 = t0)
    (hs : (s₁Loc.st P).id.sendsIn t0 = true) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par
    let cOut := (dhScheme Dh).send (s₁Loc.st P).γ coins
    simulateQ (keySlotFixedImpl ks) ((vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins)).run h) =
      (do
        let ((σ', kVal), stLoc') ← simulateQ (keySlotFixedImpl ks)
          ((rootLocalMainSlot (rootPRNG C.F encPt) 1 q qep (mSessMain q qep tL)
            tL par t0 (postLeak tL s₁Loc) cOut.2.2 (s₁Loc.st P).root).run h)
        let vp1Loc : VP _ Pt _ _ _ :=
          { s₁Loc.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                            root := σ', vS := some ((locFS_r71tx C ℓ encT idOf).initSender kVal) }
        let hLoc1 := { stLoc' with loc := { stLoc'.loc with cache := Function.update stLoc'.loc.cache t0 (some (cOut.2.1, σ', kVal)) } }
        simulateQ (keySlotFixedImpl ks) ((vSendTailM_r71tx hkLoc s₁Loc P vp1Loc m).run hLoc1)) := by
  intro hkLoc cOut
  have h1 : vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins) =
      (do
        let (σ', kVal) ← rootLocalMainSlot (rootPRNG C.F encPt) 1 q qep (mSessMain q qep tL)
          tL par t0 (postLeak tL s₁Loc) cOut.2.2 (s₁Loc.st P).root
        modify fun (st : LocalMainSlotState Pt (BitVec 256) (BitVec 256) Pt) =>
          { st with loc := { st.loc with cache := Function.update st.loc.cache t0 (some (cOut.2.1, σ', kVal)) } }
        vSendTailM_r71tx hkLoc s₁Loc P
          { s₁Loc.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                            root := σ', vS := some ((locFS_r71tx C ℓ encT idOf).initSender kVal) } m) := by
    rw [vSend_eq_bind_tailM_r71tx]
    dsimp only [vSendStep1, hkLoc, hooksLocalMainSlot, cOut]
    simp only [ht0, hs, ↓reduceIte, bind_assoc, pure_bind]
  rw [h1, StateT.run_bind, simulateQ_bind]
  refine bind_congr fun ⟨⟨σ', kVal⟩, stLoc'⟩ => ?_
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]

attribute [local irreducible] rootFSMultiBucketAuth regSessOptMultiBucket vSendTailM_r71tx in
private theorem vSend_multi_new_coins_r71tx (la : Bool)
    (s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (h : MultiHSt_r71tx Pt) (stP : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ))
    (t0 : ℕ) (ht0 : (s₁M.st P).tcur + 1 = t0)
    (hs : (s₁M.st P).id.sendsIn t0 = true) :
    let hkM := hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 qep true tL par la
    let cOut := (dhScheme Dh).send (s₁M.st P).γ coins
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((vSend hkM s₁M P (s₁M.st P) m none (some coins)).run h)).run stP =
      (do
        let (((σ', kVal, sid), s1), stP1) ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          ((rootFSMultiBucketAuth
            (T := Pt)
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ)
            (E := ℕ × LibsignalCiphertextWithSalt32)
            (rootPRNG C.F encPt) 1 qep tL par t0 (postLeak tL s₁M) cOut.2.2 (s₁M.st P).root).run h)).run stP
        let (optIdx, s2) := regSessOptMultiBucket (q + 1) true tL t0 sid s1
        let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ := (match optIdx with
          | none => .inl ((locFS_r71tx C ℓ encT idOf).initSender kVal)
          | some sIdx => .inr sIdx)
        let vp1M : VP _ Pt _ _ _ :=
          { s₁M.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := σ', vS := some ssv }
        let hM1 := { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
        (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          ((vSendTailM_r71tx hkM s₁M P vp1M m).run hM1)).run stP1) := by
  intro hkM cOut
  have h1 : vSend hkM s₁M P (s₁M.st P) m none (some coins) =
      (do
        let (σ', kVal, sid) ← rootFSMultiBucketAuth
          (T := Pt)
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (M := LibsignalMsgPublicPart × Plain ℓ)
          (E := ℕ × LibsignalCiphertextWithSalt32)
          (rootPRNG C.F encPt) 1 qep tL par t0 (postLeak tL s₁M) cOut.2.2 (s₁M.st P).root
        let (s1 : MultiHSt_r71tx Pt) ← get
        let (optIdx, s2) := regSessOptMultiBucket (q + 1) true tL t0 sid s1
        set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
        let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ := (match optIdx with
          | none => .inl ((locFS_r71tx C ℓ encT idOf).initSender kVal)
          | some sIdx => .inr sIdx)
        vSendTailM_r71tx hkM s₁M P
          { s₁M.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := σ', vS := some ssv } m) := by
    rw [vSend_eq_bind_tailM_r71tx]
    dsimp only [vSendStep1, hkM, hooksFSMultiBucketAuth, cOut]
    simp only [ht0, hs, ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr fun ⟨σ', kVal, sid⟩ => bind_congr fun s1 => ?_
    cases regSessOptMultiBucket (q + 1) true tL t0 sid s1
    rfl
  rw [h1, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun ⟨⟨⟨σ', kVal, sid⟩, s1⟩, stP1⟩ => ?_
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]

attribute [local irreducible] runLocCont runSideCont runSideContSt_r71tx vSendTailM_r71tx in
private theorem vSend_postLeak_coins_leOne_r71tx
    (hrt : SignalRoundTripShort protoSignalCodec) (hℓ : ℓ + 16 < rustLenBound)
    {phase1 : Bool} {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (bad : Bool) (coins : BitVec 256)
    (hshort : m.1.shortB = true)
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ)
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL none tblM tblL)
    (hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true)
    {s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase1 : eraseSt s₁M = eraseSt s₁Loc)
    (hstL : s₁Loc.st = esLoc.g.st) (hstM : s₁M.st = esM.g.st)
    (hep1 : s₁Loc.epoch = Function.update esLoc.g.epoch P (esLoc.g.epoch P + 1))
    (hidx1 : s₁Loc.idx = Function.update esLoc.g.idx P 0)
    (htr1 : s₁Loc.trans = esLoc.g.trans) (hwin1 : s₁Loc.win = esLoc.g.win)
    (htL1 : s₁Loc.tL = (if bad && !(esLoc.g.safeCh 3 P) then some (maxOpt esLoc.g.tL (esLoc.g.epoch P + 1)) else esLoc.g.tL))
    (htLM1 : s₁M.tL = s₁Loc.tL)
    (hpl1 : postLeak tL s₁Loc = true)
    (ih : ∀ u actEp' esLoc' esM' tblM' tblL',
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem' actEp' esLoc' esM' esL none tblM' tblL' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par
    let hkM := hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 qep true tL par false
    LeOne
      (do
        let (res, h') ← simulateQ (keySlotFixedImpl ks) ((vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins)).run esLoc.h)
        match res with
        | none =>
          runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) { esLoc with h := h', abort := true } none
        | some (st', ct) =>
          let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
          runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
            { g := s₁Loc.record 3 P st' recE false, h := h', abort := false } none)
      (do
        let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
          ((vSend hkM s₁M P (s₁M.st P) m none (some coins)).run esM.h)).run (fun _ => false, tblM)
        match res with
        | none =>
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k none)
            { esM with h := h', abort := true } none stP'
        | some (st', ct) =>
          let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k (some ct))
            { g := s₁M.record 3 P st' recE false, h := h', abort := false } none stP') := by
  intro hkLoc hkM
  have ht0L : (s₁Loc.st P).tcur + 1 = esLoc.g.epoch P + 1 := by rw [hstL, (hinv.hparty_tcur P).1]
  have hsL : (s₁Loc.st P).id.sendsIn (esLoc.g.epoch P + 1) = true := by
    rw [hstL, (hinv.hparty_id P).1]; exact hs_next
  have ht0M : (s₁M.st P).tcur + 1 = esLoc.g.epoch P + 1 := by
    rw [hstM, (hinv.hparty_tcur P).2, (hinv.hparty_tcur P).1]
  have hsM : (s₁M.st P).id.sendsIn (esLoc.g.epoch P + 1) = true := by
    rw [hstM, (hinv.hparty_id P).2]; exact hs_next
  rw [vSend_loc_new_coins_r71tx C Dh encPt encT idOf ℓ q qep tL par ks s₁Loc P m coins esLoc.h
        (esLoc.g.epoch P + 1) ht0L hsL,
      vSend_multi_new_coins_r71tx C Dh encPt encT idOf ℓ q qep tL par false s₁M P m coins esM.h
        (fun _ => false, tblM) (esLoc.g.epoch P + 1) ht0M hsM]
  dsimp only
  have hpl1M : postLeak tL s₁M = true := by
    simp only [postLeak, htLM1]; simpa [postLeak] using hpl1
  have hγ_eq : (esM.g.st P).γ = (esLoc.g.st P).γ := (hinv.hparty_base P).1
  have hroot_eq : (esM.g.st P).root = (esLoc.g.st P).root := (hinv.hparty_base P).2.2
  have hinv1 := midInv_postLeak_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hinv coins hs_next
    herase1 hstL hstM hep1 hidx1 htr1 hwin1 htL1 hpl1
  have hsends1 : P.sendsIn (s₁Loc.epoch P) = true := by simpa [hep1] using hs_next
  rcases fsSend_record_coupled_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ P m hshort
    s₁Loc s₁M _ _ _ _ tblM tblL herase1 hsends1 hinv1 with
    ⟨vp2Loc, vp2M, ct, hLoc2, hM2, actEp', tblM', tblL', htailL, htailM, _, hinv2⟩
  simp only [hpl1, hpl1M, rootLocalMainSlot, rootFSMultiBucketAuth, Bool.true_or, ↓reduceIte,
    StateT.run_pure, simulateQ_pure, pure_bind, regSessOptMultiBucket,
    hstL, hstM, hγ_eq, hroot_eq]
  rw [htailL, htailM]
  simp only [pure_bind, runSideContSt_eq_r71tx, eraseSt_epoch herase1, eraseSt_idx herase1]
  exact ih (some ct) actEp' _ _ tblM' tblL'
    (coupledInv_set_esL_false_r71tx C encT idOf ℓ q qep tL par ks bs esL hinv2)

attribute [local irreducible] runLocCont runSideCont runSideContSt_r71tx vSendTailM_r71tx in
private theorem step_transmit_leOne_r71tx
    (hrt : SignalRoundTripShort protoSignalCodec) (hℓ : ℓ + 16 < rustLenBound)
    {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : m.1.shortB = true)
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ)
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih : ∀ u actEp' esLoc' esM' tblM' tblL',
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem' actEp' esLoc' esM' esL none tblM' tblL' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    LeOne
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esM winEp tblM) := by
  obtain rfl := hinv.hwe
  have hwinM : esM.g.win = false := (eraseSt_win hinv.herase).trans hinv.hwin_loc
  rw [runLocCont_transmit_r71tx C Dh encPt encT idOf ℓ q qep tL par ks P m r k esLoc hinv.habort_loc hinv.hwin_loc,
      runSideCont_transmit_r71tx C Dh encPt encT idOf ℓ q qep tL par false P m r k esM tblM hinv.habort_M hwinM]
  dsimp only
  by_cases hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true
  · by_cases hqep : qep < esLoc.g.epoch P + 1
    · rcases epMgmt_new_none_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      exact ih none actEp esLoc esM tblM tblL
        (coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem'))
    · rcases epMgmt_new_some_r71tx ℓ qep hinv.herase hs_next hqep with
        ⟨s₁Loc, s₁M, heL, heM, her1, hstL, hstM, hep1, hidx1, htr1, hwin1, htL1, htLM1⟩
      rw [heL, heM]
      dsimp only
      have hsL1 : (s₁Loc.st P).id.sendsIn ((s₁Loc.st P).tcur + 1) = true := by
        rw [hstL, (hinv.hparty_id P).1, (hinv.hparty_tcur P).1]; exact hs_next
      have hsM1 : (s₁M.st P).id.sendsIn ((s₁M.st P).tcur + 1) = true := by
        rw [hstM, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2, (hinv.hparty_tcur P).1]; exact hs_next
      have hpl1 : postLeak tL s₁Loc = true := by
        rcases hinv.hphase2 rfl with ⟨cur0, htL0, hlt0, _⟩
        cases hbad : (r.isSome && !(esLoc.g.safeCh 3 P))
        · simp [postLeak, htL1, hbad, htL0, hlt0]
        · simp only [postLeak, htL1, hbad, ↓reduceIte, htL0]
          exact ltOpt_mono_right_r71tx tL hlt0 (maxOpt_ge_some_left_r71tx cur0 _)
      cases r with
      | some coins =>
        simp only [Option.isSome_some] at htL1
        exact vSend_postLeak_coins_leOne_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
          P m true coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htL1 htLM1 hpl1 ih
      | none =>
        simp only [Option.isSome_none] at htL1
        rw [vSend_loc_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par ks s₁Loc P m esLoc.h hsL1,
            vSend_multi_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par false s₁M P m esM.h
              (fun _ => false, tblM) hsM1]
        simp only [bind_assoc]
        refine leOne_bind ($ᵗ (BitVec 256)) fun coins _ => ?_
        exact vSend_postLeak_coins_leOne_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
          P m false coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htL1 htLM1 hpl1 ih
  · simp only [Bool.not_eq_true] at hs_next
    by_cases hqep : qep < esLoc.g.epoch P
    · rcases epMgmt_same_none_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      exact ih none actEp esLoc esM tblM tblL
        (coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem'))
    · rcases epMgmt_same_some_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      dsimp only
      rw [vSend_run_eq_tail_r71tx, vSend_run_eq_tail_r71tx]
      have hidL : (esLoc.g.st P).id = P := (hinv.hparty_id P).1
      have htcurL : (esLoc.g.st P).tcur = esLoc.g.epoch P := (hinv.hparty_tcur P).1
      have hidM : (esM.g.st P).id = P := (hinv.hparty_id P).2
      have htcurM : (esM.g.st P).tcur = esLoc.g.epoch P :=
        (hinv.hparty_tcur P).2.trans (hinv.hparty_tcur P).1
      dsimp only [vSendStep1]
      simp only [hidL, htcurL, hidM, htcurM, hs_next, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, pure_bind]
      have hsends_cur : P.sendsIn (esLoc.g.epoch P) = true :=
        sendsIn_of_succ_false_r71tx P (esLoc.g.epoch P) hs_next
      have hesL_id :
          ({ g := { esLoc.g with st := Function.update esLoc.g.st P (esLoc.g.st P) }, h := esLoc.h, abort := false } :
            LocESt Pt ℓ) = esLoc := by
        have hab := hinv.habort_loc
        rcases esLoc with ⟨g, h, ab⟩
        simp at hab; subst hab; cases g; simp
      have hesM_id :
          ({ g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false } :
            MultiESt_r71tx Pt ℓ) = esM := by
        have hab := hinv.habort_M
        rcases esM with ⟨g, h, ab⟩
        simp at hab; subst hab; cases g; simp
      have hinv1 : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem' actEp
          { g := { esLoc.g with st := Function.update esLoc.g.st P (esLoc.g.st P) }, h := esLoc.h, abort := false }
          { g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false }
          { g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false }
          none tblM tblL := by
        rw [hesL_id, hesM_id]
        exact coupledInv_set_esL_false_r71tx C encT idOf ℓ q qep tL par ks bs esM
          (coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem'))
      rcases fsSend_record_coupled_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ P m hshort
        esLoc.g esM.g (esLoc.g.st P) (esM.g.st P) esLoc.h esM.h tblM tblL hinv.herase hsends_cur hinv1 with
        ⟨vp2Loc, vp2M, ct, hLoc2, hM2, actEp', tblM', tblL', htailL, htailM, _, hinv2⟩
      rw [htailL, htailM]
      simp only [pure_bind, runSideContSt_eq_r71tx, eraseSt_epoch hinv.herase, eraseSt_idx hinv.herase]
      exact ih (some ct) actEp' _ _ tblM' tblL'
        (coupledInv_set_esL_false_r71tx C encT idOf ℓ q qep tL par ks bs esL hinv2)

attribute [local irreducible] rootLocalMainSlot rootFSMultiBucketAuth regSessOptMultiBucket
  runLocCont runSideCont runSideContSt_r71tx vSendTailM_r71tx in
private theorem vSend_noLeak_coins_leAdd_r71tx
    (hrt : SignalRoundTripShort protoSignalCodec) (hℓ : ℓ + 16 < rustLenBound)
    {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM : MultiESt_r71tx Pt ℓ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hshort : m.1.shortB = true)
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ)
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true (rem' + 1) actEp esLoc esM esM none tblM tblL)
    (hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true)
    {s₁Loc : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {s₁M : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (herase1 : eraseSt s₁M = eraseSt s₁Loc)
    (hstL : s₁Loc.st = esLoc.g.st) (hstM : s₁M.st = esM.g.st)
    (hep1 : s₁Loc.epoch = Function.update esLoc.g.epoch P (esLoc.g.epoch P + 1))
    (hidx1 : s₁Loc.idx = Function.update esLoc.g.idx P 0)
    (htr1 : s₁Loc.trans = esLoc.g.trans) (hwin1 : s₁Loc.win = esLoc.g.win)
    (htLM1 : s₁M.tL = s₁Loc.tL)
    (hpl1 : postLeak tL s₁Loc = false)
    (ih : ∀ u actEp' esLoc' esM' esL' tblM' tblL',
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71tx C ℓ encT idOf) 1 qep true tL par la
    LeAdd
      (do
        let (res, h') ← simulateQ (keySlotFixedImpl ks) ((vSend hkLoc s₁Loc P (s₁Loc.st P) m none (some coins)).run esLoc.h)
        match res with
        | none =>
          runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) { esLoc with h := h', abort := true } none
        | some (st', ct) =>
          let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
          runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
            { g := s₁Loc.record 3 P st' recE false, h := h', abort := false } none)
      (do
        let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
          ((vSend (hkM false) s₁M P (s₁M.st P) m none (some coins)).run esM.h)).run (fun _ => false, tblM)
        match res with
        | none =>
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k none)
            { esM with h := h', abort := true } none stP'
        | some (st', ct) =>
          let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k (some ct))
            { g := s₁M.record 3 P st' recE false, h := h', abort := false } none stP')
      (do
        let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
          ((vSend (hkM true) s₁M P (s₁M.st P) m none (some coins)).run esM.h)).run (fun _ => false, tblL)
        match res with
        | none =>
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par true (k none)
            { esM with h := h', abort := true } none stP'
        | some (st', ct) =>
          let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
          runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par true (k (some ct))
            { g := s₁M.record 3 P st' recE false, h := h', abort := false } none stP') := by
  intro hkLoc hkM
  let t0 := esLoc.g.epoch P + 1
  have ht0L : (s₁Loc.st P).tcur + 1 = t0 := by rw [hstL, (hinv.hparty_tcur P).1]
  have hsL : (s₁Loc.st P).id.sendsIn t0 = true := by
    rw [hstL, (hinv.hparty_id P).1]; exact hs_next
  have ht0M : (s₁M.st P).tcur + 1 = t0 := by
    rw [hstM, (hinv.hparty_tcur P).2, (hinv.hparty_tcur P).1]
  have hsM : (s₁M.st P).id.sendsIn t0 = true := by
    rw [hstM, (hinv.hparty_id P).2]; exact hs_next
  rw [vSend_loc_new_coins_r71tx C Dh encPt encT idOf ℓ q qep tL par ks s₁Loc P m coins esLoc.h t0 ht0L hsL,
      vSend_multi_new_coins_r71tx C Dh encPt encT idOf ℓ q qep tL par false s₁M P m coins esM.h
        (fun _ => false, tblM) t0 ht0M hsM,
      vSend_multi_new_coins_r71tx C Dh encPt encT idOf ℓ q qep tL par true s₁M P m coins esM.h
        (fun _ => false, tblL) t0 ht0M hsM]
  dsimp only
  have hpl1M : postLeak tL s₁M = false := by
    simp only [postLeak, htLM1]; simpa [postLeak] using hpl1
  have hγ_eq : (esM.g.st P).γ = (esLoc.g.st P).γ := (hinv.hparty_base P).1
  have hroot_eq : (esM.g.st P).root = (esLoc.g.st P).root := (hinv.hparty_base P).2.2
  have hsender_t0 : Party.senderOf t0 = P := (eq_senderOf_of_sendsIn hs_next).symm
  have hfut_t0 := hinv.hfuture t0 (by rw [hsender_t0, (hinv.hparty_tcur P).1]; omega)
  rcases hfut_t0 with ⟨hact_t0, _, _, hfL_t0, hfM_t0, hsesM_t0⟩
  have hun_t0 : validGuessBucketParAuth 1 tL par t0 = true → t0 ≤ qep + 1 →
      esLoc.h.usedSlot (sIdxMain q tL t0) = false := by
    intro hvg hle
    have hh : healedBy tL 3 t0 = true := by
      simp [validGuessBucketParAuth, lastLeakGuessAdmissible] at hvg; exact hvg.1
    have hhe : healEpoch tL ≤ t0 := healedBy_imp_healEpoch_le tL t0 hh
    have hslt : sIdxMain q tL t0 < mSessMain q qep tL :=
      sIdxMain_lt_mSessMain q qep tL par t0 (by simp; omega) hvg
    exact (hinv.hunalloc (sIdxMain q tL t0) hslt fun t' hhe' hs_eq => by
      have ht'_eq : t' = t0 := sIdxMain_inj q tL hhe' hhe hs_eq
      subst ht'_eq; exact hact_t0).1
  let cOut := (dhScheme Dh).send (esLoc.g.st P).γ coins
  simp only [hpl1, hpl1M, hstL, hstM, hγ_eq, hroot_eq, bind_assoc]
  refine root_coupled_leAdd_r71tx C encPt encT idOf ℓ q qep tL par ks
    t0 cOut.2.2 (esLoc.g.st P).root esLoc.h esM.h tblM tblL
    (fun σ' kLoc stLoc' => do
      let vp1Loc : VP _ Pt _ _ _ :=
        { esLoc.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                            root := σ', vS := some ((locFS_r71tx C ℓ encT idOf).initSender kLoc) }
      let hLoc1 := { stLoc' with loc := { stLoc'.loc with cache := Function.update stLoc'.loc.cache t0 (some (cOut.2.1, σ', kLoc)) } }
      let (res, h') ← simulateQ (keySlotFixedImpl ks) ((vSendTailM_r71tx hkLoc s₁Loc P vp1Loc m).run hLoc1)
      match res with
      | none =>
        runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) { esLoc with h := h', abort := true } none
      | some (st', ct) =>
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ct⟩
        runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some ct))
          { g := s₁Loc.record 3 P st' recE false, h := h', abort := false } none)
    (fun σ' kM optIdx s2 stPM' => do
      let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ := (match optIdx with
        | none => .inl ((locFS_r71tx C ℓ encT idOf).initSender kM)
        | some sIdx => .inr sIdx)
      let vp1M : VP _ Pt _ _ _ :=
        { esM.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := σ', vS := some ssv }
      let hM1 := { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kM, optIdx)) }
      let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((vSendTailM_r71tx (hkM false) s₁M P vp1M m).run hM1)).run stPM'
      match res with
      | none =>
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k none)
          { esM with h := h', abort := true } none stP'
      | some (st', ct) =>
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par false (k (some ct))
          { g := s₁M.record 3 P st' recE false, h := h', abort := false } none stP')
    (fun σ' kM optIdx s2 stPL' => do
      let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ := (match optIdx with
        | none => .inl ((locFS_r71tx C ℓ encT idOf).initSender kM)
        | some sIdx => .inr sIdx)
      let vp1M : VP _ Pt _ _ _ :=
        { esM.g.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                          root := σ', vS := some ssv }
      let hM1 := { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kM, optIdx)) }
      let ((res, h'), stP') ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
        ((vSendTailM_r71tx (hkM true) s₁M P vp1M m).run hM1)).run stPL'
      match res with
      | none =>
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par true (k none)
          { esM with h := h', abort := true } none stP'
      | some (st', ct) =>
        let recE : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
        runSideContSt_r71tx C Dh encPt encT idOf ℓ q qep tL par true (k (some ct))
          { g := s₁M.record 3 P st' recE false, h := h', abort := false } none stP')
    hfL_t0 hfM_t0 hsesM_t0 hun_t0 ?_
  intro σ' kLoc kM optIdx stLoc' stM' stPM' stPL' hstPM hstPL hroot
  subst hstPM hstPL
  rcases midInv_rootPost_phase1_r71tx C Dh encT idOf ℓ q qep tL par ks bs hinv coins
    hs_next herase1 hstL hstM hep1 hidx1 htr1 hwin1 hpl1 hroot with ⟨actEp1, hinv1⟩
  have hsends1 : P.sendsIn (s₁Loc.epoch P) = true := by simpa [hep1] using hs_next
  cases optIdx <;>
    (dsimp only [t0, cOut] at hinv1 ⊢
     rcases fsSend_record_coupled_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ P m hshort
       s₁Loc s₁M _ _ _ _ tblM tblL herase1 hsends1 hinv1 with
       ⟨vp2Loc, vp2M, ct, hLoc2, hM2, actEp', tblM', tblL', htailL, htailM, htailLa, hinv2⟩
     rw [htailL, htailM, htailLa rfl]
     simp only [pure_bind, runSideContSt_eq_r71tx, eraseSt_epoch herase1, eraseSt_idx herase1]
     exact ih (some ct) actEp' _ _ _ tblM' tblL' hinv2)

attribute [local irreducible] runLocCont runSideCont runSideContSt_r71tx vSendTailM_r71tx in
private theorem step_transmit_phase1_leAdd_r71tx
    (hrt : SignalRoundTripShort protoSignalCodec) (hℓ : ℓ + 16 < rustLenBound)
    {rem' : ℕ} {actEp : ActMap_r71tx}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71tx Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : m.1.shortB = true)
    (k : Option (Fig8C Pt) → SmAdv_r71tx Pt ℓ)
    (hinv : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih_phase2 : ∀ u actEp' esLoc' esM' tblM' tblL',
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs false rem' actEp' esLoc' esM' esM none tblM' tblL' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM'))
    (ih : ∀ u actEp' esLoc' esM' esL' tblM' tblL',
      CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) :
    LeAdd
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esM winEp tblM)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := SmSpec_r71tx Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= k) esL winEp tblL) := by
  obtain rfl := hinv.hwe
  rcases hinv.hphase1 rfl with ⟨_, hesL, _, _⟩
  subst esL
  have hwinM : esM.g.win = false := (eraseSt_win hinv.herase).trans hinv.hwin_loc
  rw [runLocCont_transmit_r71tx C Dh encPt encT idOf ℓ q qep tL par ks P m r k esLoc hinv.habort_loc hinv.hwin_loc,
      runSideCont_transmit_r71tx C Dh encPt encT idOf ℓ q qep tL par false P m r k esM tblM hinv.habort_M hwinM,
      runSideCont_transmit_r71tx C Dh encPt encT idOf ℓ q qep tL par true P m r k esM tblL hinv.habort_M hwinM]
  dsimp only
  by_cases hs_next : P.sendsIn (esLoc.g.epoch P + 1) = true
  · by_cases hqep : qep < esLoc.g.epoch P + 1
    · rcases epMgmt_new_none_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      exact ih none actEp esLoc esM esM tblM tblL
        (coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem'))
    · rcases epMgmt_new_some_r71tx ℓ qep hinv.herase hs_next hqep with
        ⟨s₁Loc, s₁M, heL, heM, her1, hstL, hstM, hep1, hidx1, htr1, hwin1, htL1, htLM1⟩
      rw [heL, heM]
      dsimp only
      have hsL1 : (s₁Loc.st P).id.sendsIn ((s₁Loc.st P).tcur + 1) = true := by
        rw [hstL, (hinv.hparty_id P).1, (hinv.hparty_tcur P).1]; exact hs_next
      have hsM1 : (s₁M.st P).id.sendsIn ((s₁M.st P).tcur + 1) = true := by
        rw [hstM, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2, (hinv.hparty_tcur P).1]; exact hs_next
      by_cases hpl1 : postLeak tL s₁Loc = true
      · refine leAdd_of_le_main ?_
        cases r with
        | some coins =>
          simp only [Option.isSome_some] at htL1
          exact vSend_postLeak_coins_leOne_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
            P m true coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htL1 htLM1 hpl1 ih_phase2
        | none =>
          simp only [Option.isSome_none] at htL1
          rw [vSend_loc_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par ks s₁Loc P m esLoc.h hsL1,
              vSend_multi_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par false s₁M P m esM.h
                (fun _ => false, tblM) hsM1]
          simp only [bind_assoc]
          refine leOne_bind ($ᵗ (BitVec 256)) fun coins _ => ?_
          exact vSend_postLeak_coins_leOne_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
            P m false coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htL1 htLM1 hpl1 ih_phase2
      · simp only [Bool.not_eq_true] at hpl1
        cases r with
        | some coins =>
          exact vSend_noLeak_coins_leAdd_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
            P m coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htLM1 hpl1 ih
        | none =>
          rw [vSend_loc_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par ks s₁Loc P m esLoc.h hsL1,
              vSend_multi_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par false s₁M P m esM.h
                (fun _ => false, tblM) hsM1,
              vSend_multi_new_none_r71tx C Dh encPt encT idOf ℓ q qep tL par true s₁M P m esM.h
                (fun _ => false, tblL) hsM1]
          simp only [bind_assoc]
          refine leAdd_bind ($ᵗ (BitVec 256)) fun coins _ => ?_
          exact vSend_noLeak_coins_leAdd_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ
            P m coins hshort k hinv hs_next her1 hstL hstM hep1 hidx1 htr1 hwin1 htLM1 hpl1 ih
  · simp only [Bool.not_eq_true] at hs_next
    by_cases hqep : qep < esLoc.g.epoch P
    · rcases epMgmt_same_none_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      exact ih none actEp esLoc esM esM tblM tblL
        (coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem'))
    · rcases epMgmt_same_some_r71tx ℓ qep hinv.herase hs_next hqep with ⟨heL, heM⟩
      rw [heL, heM]
      dsimp only
      rw [vSend_run_eq_tail_r71tx, vSend_run_eq_tail_r71tx, vSend_run_eq_tail_r71tx]
      have hidL : (esLoc.g.st P).id = P := (hinv.hparty_id P).1
      have htcurL : (esLoc.g.st P).tcur = esLoc.g.epoch P := (hinv.hparty_tcur P).1
      have hidM : (esM.g.st P).id = P := (hinv.hparty_id P).2
      have htcurM : (esM.g.st P).tcur = esLoc.g.epoch P :=
        (hinv.hparty_tcur P).2.trans (hinv.hparty_tcur P).1
      dsimp only [vSendStep1]
      simp only [hidL, htcurL, hidM, htcurM, hs_next, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, pure_bind]
      have hsends_cur : P.sendsIn (esLoc.g.epoch P) = true :=
        sendsIn_of_succ_false_r71tx P (esLoc.g.epoch P) hs_next
      have hesL_id :
          ({ g := { esLoc.g with st := Function.update esLoc.g.st P (esLoc.g.st P) }, h := esLoc.h, abort := false } :
            LocESt Pt ℓ) = esLoc := by
        have hab := hinv.habort_loc
        rcases esLoc with ⟨g, h, ab⟩
        simp at hab; subst hab; cases g; simp
      have hesM_id :
          ({ g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false } :
            MultiESt_r71tx Pt ℓ) = esM := by
        have hab := hinv.habort_M
        rcases esM with ⟨g, h, ab⟩
        simp at hab; subst hab; cases g; simp
      have hinv1 : CoupledInv_r71tx C encT idOf ℓ q qep tL par ks bs true rem' actEp
          { g := { esLoc.g with st := Function.update esLoc.g.st P (esLoc.g.st P) }, h := esLoc.h, abort := false }
          { g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false }
          { g := { esM.g with st := Function.update esM.g.st P (esM.g.st P) }, h := esM.h, abort := false }
          none tblM tblL := by
        rw [hesL_id, hesM_id]
        exact coupledInv_mono_rem_r71tx C encT idOf ℓ q qep tL par ks bs hinv (Nat.le_succ rem')
      rcases fsSend_record_coupled_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓ P m hshort
        esLoc.g esM.g (esLoc.g.st P) (esM.g.st P) esLoc.h esM.h tblM tblL hinv.herase hsends_cur hinv1 with
        ⟨vp2Loc, vp2M, ct, hLoc2, hM2, actEp', tblM', tblL', htailL, htailM, htailLa, hinv2⟩
      rw [htailL, htailM, htailLa rfl]
      simp only [pure_bind, runSideContSt_eq_r71tx, eraseSt_epoch hinv.herase, eraseSt_idx hinv.herase]
      exact ih (some ct) actEp' _ _ _ tblM' tblL' hinv2

end Coupling

private theorem coupledInv_phase2_canon_r71tx {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ q qep : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {tL : Option ℕ} {par : Bool} {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {rem' : ℕ}
    {actEp' : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    {esLoc' : LocESt Pt ℓ} {esM' esL' : SideESt Pt ℓ} {tblM' tblL' : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esL' none tblM' tblL') :
    CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' :=
  { hinv with
    hphase1 := fun h => Bool.noConfusion h
    hact := fun t0 ssLoc rsLoc ha =>
      let ⟨h1, h2, h3, h4, ⟨stR, hAt⟩, h6, h7⟩ := hinv.hact t0 ssLoc rsLoc ha
      ⟨h1, h2, h3, h4, ⟨stR, { hAt with syncRML := fun h => Bool.noConfusion h }⟩, h6, h7⟩
    hunalloc := fun sIdx hs hno =>
      let ⟨h1, h2, h3, _⟩ := hinv.hunalloc sIdx hs hno
      ⟨h1, h2, h3, fun h => Bool.noConfusion h⟩ }

end R71Tx

/-- Sub-lemma 1 (`step_transmit_coupled`): Coupled `vSend` / transmit step for `phase1 = false` (`LeOne`) and `phase1 = true` (`LeAdd`). -/
private theorem step_transmit_coupled {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem' : ℕ}
    (P : Party) (pm : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (hshort : pm.1.shortB = true)
    (k : Option (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) → OracleComp (Fig8Dom Pt ℓ) Bool) :
    (∀ {actEp esLoc esM winEp tblM},
      CoupledInv C ℓ q qep encT idOf tL par ks bs false (rem' + 1) actEp esLoc esM esM winEp tblM tblM →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      LeOne
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, pm, r))))))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, pm, r))))))) >>= k)
          esM winEp tblM)) ∧
    (∀ {actEp esLoc esM esL winEp tblM tblL},
      CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      (∀ u actEp' esLoc' esM' esL' tblM' tblL',
        CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
        LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) →
      LeAdd
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, pm, r))))))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, pm, r))))))) >>= k)
          esM winEp tblM)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inl (P, pm, r))))))) >>= k)
          esL winEp tblL)) := by
  have _ := hDh; have _ := hD; have _ := hinj; have _ := hdum
  have hrt : _root_.CryptoGames.LibsignalSession.SignalRoundTripShort protoSignalCodec :=
    _root_.CryptoVerification.LibsignalSession.signalRoundTripShort_proto
  have hℓB : ℓ + 16 < _root_.CryptoGames.LibsignalSession.rustLenBound := by
    unfold _root_.CryptoGames.LibsignalSession.rustLenBound; omega
  refine ⟨fun hinv ih => ?_, fun hinv ih2 ih1 => ?_⟩
  · exact step_transmit_leOne_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓB
      P pm r hshort k hinv fun u actEp' esLoc' esM' tblM' tblL' hinv' =>
        ih u actEp' esLoc' esM' tblM' (coupledInv_phase2_canon_r71tx hinv')
  · exact step_transmit_phase1_leAdd_r71tx C Dh encPt encT idOf ℓ q qep tL par ks bs hrt hℓB
      P pm r hshort k hinv
      (fun u actEp' esLoc' esM' tblM' tblL' hinv' =>
        ih2 u actEp' esLoc' esM' tblM' (coupledInv_phase2_canon_r71tx hinv'))
      ih1

/-! ### Deliver and Corrupt Helpers for `step_deliver_and_corrupt_coupled` -/

private abbrev MultiHSt_r71dc (Pt : Type) :=
  FSMultiBucketAuthState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)

private abbrev ActMap_r71dc :=
  ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))

private abbrev locFS_r71dc {Pt : Type} (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :=
  lFS C protoSignalCodec ℓ encT idOf maxForwardJumps

private theorem activeSessInv_any_to_phase2_r71dc {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL sL' : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL) :
    ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL' :=
  let ⟨stR, h⟩ := hinv
  ⟨stR, { h with syncRML := fun hp1 => Bool.noConfusion hp1 }⟩

private theorem coupledInv_false_swap_r71dc {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ q qep : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {tL : Option ℕ} {par : Bool} {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {rem : ℕ}
    {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL esL' : SideESt Pt ℓ} {winEp : Option ℕ}
    {tblM tblL tblL' : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs false rem actEp esLoc esM esL winEp tblM tblL) :
    CoupledInv C ℓ q qep encT idOf tL par ks bs false rem actEp esLoc esM esL' winEp tblM tblL' :=
  { hinv with
    hphase1 := fun h => Bool.noConfusion h
    hact := fun t0 ss0 rs0 ha =>
      let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hinv.hact t0 ss0 rs0 ha
      ⟨h1, h2, h3, h4, activeSessInv_any_to_phase2_r71dc C ℓ encT idOf h5, h6, h7⟩
    hunalloc := fun sIdx hlt hun =>
      let ⟨hu1, hu2, hu3, _⟩ := hinv.hunalloc sIdx hlt hun
      ⟨hu1, hu2, hu3, fun h => Bool.noConfusion h⟩ }

private theorem ltOpt_mono_r71dc (tL : Option ℕ) {a b : ℕ} (h : ltOpt tL a = true) (hab : a ≤ b) :
    ltOpt tL b = true := by
  cases tL with
  | none => exact h
  | some x => simp only [ltOpt, decide_eq_true_eq] at h ⊢; omega

private theorem postLeak_epMgmt_r71dc {St Msg C : Type} (tL : Option ℕ) (s s₁ : GameState St Msg C)
    (Δ qep : ℕ) (P : Party) (bad : Bool) (hpost : postLeak tL s = true)
    (h : s.epMgmt Δ qep P bad = some s₁) : postLeak tL s₁ = true := by
  unfold GameState.epMgmt GameState.leak at h
  split at h <;> split at h <;> cases h
  · split
    · cases hs : s.tL with
      | none => simp [postLeak, hs] at hpost
      | some cur => simp only [postLeak, hs] at hpost; exact ltOpt_mono_r71dc tL hpost (Nat.le_max_left _ _)
    · exact hpost
  · exact hpost

private theorem postLeak_afterCorr_r71dc {St Msg C : Type} (tL : Option ℕ) (s : GameState St Msg C)
    (P : Party) (hpost : postLeak tL s = true) : postLeak tL (s.afterCorr P) = true := by
  unfold GameState.afterCorr
  cases hs : s.tL with
  | none => simp [postLeak, hs] at hpost
  | some cur => simp only [postLeak, hs] at hpost; exact ltOpt_mono_r71dc tL hpost (Nat.le_max_left _ _)

private theorem slot_eq_loc_of_postLeak_or_halted_r71dc {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ks : ℕ → K)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (g0 : Ctx Γ T Sig SS RS M E) (st0 : LocalMainSlotState T Sig K I) (abort0 : Bool) (we0 : Option ℕ)
    (hPost : (abort0 || g0.win) = true ∨ postLeak tL g0 = true) :
    simulateQ (keySlotFixedImpl ks) (do
      let (_, es, we) ← (simulateQ (implLocalMainSlot
        (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par) Δcka qep fs.maxSkip tL) oa).run
        ({ g := g0, h := st0, abort := abort0 }, we0)
      return mainParOut (2 + Δcka) tL par es we) =
    simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl (do
      let (_, es, we) ← (simulateQ (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
        (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
        Δcka qep fs.maxSkip tL false) oa).run
        ({ g := g0, h := st0.loc, abort := abort0 }, we0)
      return mainParOut (2 + Δcka) tL par es we) := by
  let hkLoc := Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain cka prng fs Δcka qep tL
  let hkSlot := hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par
  induction oa using OracleComp.inductionOn generalizing g0 st0 abort0 we0 with
  | pure _ => simp [simulateQ_pure, StateT.run_pure, mainParOut]
  | query_bind qy k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, simulateQ_bind, simulateQ_bind]
    rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inl n)).run
          ({ g := g0, h := st0, abort := abort0 }, we0) =
          (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl n)) >>=
            fun u => pure (u, ({ g := g0, h := st0, abort := abort0 }, we0))) := by
        simp [implLocalMainSlot, QueryImpl.add_apply_inl]
      have hL : (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
            hkLoc Δcka qep fs.maxSkip tL false (.inl n)).run
          ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n)) >>=
            fun u => pure (u, ({ g := g0, h := st0.loc, abort := abort0 }, we0))) := by
        simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen, QueryImpl.add_apply_inl]
      rw [hS, hL, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        keySlotFixedImpl, _root_.CryptoGames.SM.Construction.AuthL11.lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        simulateQ_pure, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        cases hep : g0.epMgmt (2 + Δcka) qep P r.isSome with
        | none =>
          have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) := by
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp [StateT.run_bind, StateT.run_get, pure_bind, hep]
          have hL : (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) := by
            dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
              QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp [StateT.run_bind, StateT.run_get, pure_bind, hep]
          rw [hS, hL]; simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
        | some s₁ =>
          have hpl1 : postLeak tL s₁ = true := postLeak_epMgmt_r71dc tL g0 s₁ (2 + Δcka) qep P r.isSome hpl0 hep
          have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              ((_root_.CryptoGames.SM.Engine.vSend hkSlot s₁ P (s₁.st P) m none r).run st0 >>= fun (res, h') =>
                match res with
                | none => pure (none, ({ g := g0, h := h', abort := true }, we0))
                | some (st', ct) =>
                  let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
                  pure (some ct, ({ g := s₁.record (2 + Δcka) P st' recE false, h := h', abort := abort0 }, we0))) := by
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hh, Bool.false_eq_true, ↓reduceIte, hep,
              StateT.run_lift, bind_assoc]
            refine bind_congr fun ⟨res, h'⟩ => ?_
            rcases res with _ | ⟨st', ct⟩ <;> simp [StateT.run_set]
          have hL : (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              ((_root_.CryptoGames.SM.Engine.vSend hkLoc s₁ P (s₁.st P) m none r).run st0.loc >>= fun (res, h') =>
                match res with
                | none => pure (none, ({ g := g0, h := h', abort := true }, we0))
                | some (st', ct) =>
                  let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
                  pure (some ct, ({ g := s₁.record (2 + Δcka) P st' recE false, h := h', abort := abort0 }, we0))) := by
            dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
              QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hh, Bool.false_eq_true, ↓reduceIte, hep,
              StateT.run_lift, bind_assoc]
            refine bind_congr fun ⟨res, h'⟩ => ?_
            rcases res with _ | ⟨st', ct⟩ <;> simp [StateT.run_set]
          rw [hS, hL, simulateQ_bind, simulateQ_bind]
          have hvSend : simulateQ (keySlotFixedImpl ks) ((_root_.CryptoGames.SM.Engine.vSend hkSlot s₁ P (s₁.st P) m none r).run st0) =
              (fun z : Option _ × Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.LocalBucketAuthState T Sig K I =>
                (z.1, { st0 with loc := z.2 })) <$>
                simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
                  ((_root_.CryptoGames.SM.Engine.vSend hkLoc s₁ P (s₁.st P) m none r).run st0.loc) := by
            rw [_root_.CryptoGames.SM.Engine.vSend_eq_bind, _root_.CryptoGames.SM.Engine.vSend_eq_bind]
            simp only [StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
            have hstep1 : simulateQ (keySlotFixedImpl ks)
                ((_root_.CryptoGames.SM.Engine.vSendStep1 hkSlot s₁ P (s₁.st P) r).run st0) =
                (fun z : Option _ × Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.LocalBucketAuthState T Sig K I =>
                  (z.1, { st0 with loc := z.2 })) <$>
                  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
                    ((_root_.CryptoGames.SM.Engine.vSendStep1 hkLoc s₁ P (s₁.st P) r).run st0.loc) := by
              unfold _root_.CryptoGames.SM.Engine.vSendStep1
              cases (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1)
              · simp
              · simp only [↓reduceIte, hkSlot, hkLoc, hooksLocalMainSlot,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuth,
                  rootLocalMainSlot,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.rootLocalBucketAuth,
                  hpl1, Bool.true_or]
                cases r with
                | none =>
                  simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
                    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
                    sim_sampleT_fixed,
                    Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot.sim_sampleT_lImpl,
                    map_eq_bind_pure_comp, Function.comp_def]
                | some c =>
                  simp [StateT.run_modify, pure_bind]
            rw [hstep1, map_eq_bind_pure_comp]
            simp only [Function.comp_def, bind_assoc, pure_bind]
            refine bind_congr fun z => ?_
            rcases z with ⟨s1?, loc1⟩
            rcases s1? with _ | s1
            · simp
            · cases hvS : s1.vS
              · simp [hvS]
              · simp [hvS, hkSlot, hkLoc, hooksLocalMainSlot,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuth]
          rw [hvSend, bind_map_left, bind_assoc, bind_assoc]
          refine bind_congr fun z => ?_
          rcases z with ⟨res, loc'⟩
          rcases res with _ | ⟨st', ct⟩
          · dsimp only
            rw [simulateQ_pure, simulateQ_pure, pure_bind, pure_bind]
            exact ih none g0 { st0 with loc := loc' } true we0 (Or.inl rfl)
          · dsimp only
            rw [simulateQ_pure, simulateQ_pure, pure_bind, pure_bind]
            let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            have hpl2 : postLeak tL (s₁.record (2 + Δcka) P st' recE false) = true := by
              simpa [postLeak, GameState.record] using hpl1
            exact ih (some ct) (s₁.record (2 + Δcka) P st' recE false) { st0 with loc := loc' } abort0 we0
              (Or.inr hpl2)
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hh'],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
            ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
            simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl],
          show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
              hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
            ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
            simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
              QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]]
      simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        rcases Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot.deliverE_localMain_pure
          cka prng fs Δcka q qep M_sess tL par (P, c)
          { g := g0, h := st0, abort := abort0 } with ⟨out, g', abort', htL, hdL, hdR⟩
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0, abort := abort' }, we0)) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hdR]; simp,
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0.loc, abort := abort' }, we0)) by
              dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hdL]; simp]
        simp only [pure_bind, simulateQ_pure]
        exact ih out g' st0 abort' we0 (Or.inr (by unfold postLeak at hpl0 ⊢; rw [htL]; exact hpl0))
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
                _root_.CryptoGames.SM.Engine.deliverE, hh'],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, _root_.CryptoGames.SM.Engine.deliverE, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        rcases Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot.injectE_localMain_pure
          cka prng fs Δcka q qep M_sess tL par (P, c)
          { g := g0, h := st0, abort := abort0 } with ⟨out, g', abort', htL, hiL, hiR⟩
        let we' := if !g0.win && g'.win then some c.1.1 else we0
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0, abort := abort' }, we')) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hiR]; simp [we'],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0.loc, abort := abort' }, we')) by
              dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hiL]; simp [we']]
        simp only [pure_bind, simulateQ_pure]
        exact ih out g' st0 abort' we' (Or.inr (by unfold postLeak at hpl0 ⊢; rw [htL]; exact hpl0))
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
                _root_.CryptoGames.SM.Engine.injectE, hh'],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, _root_.CryptoGames.SM.Engine.injectE, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hskip : (abort0 || g0.win || !(g0.corrAllowed P))
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [Bool.or_eq_true] at hskip ⊢; tauto)
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inr P))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              pure (some (realParty (g0.st P) (g0.st P).γ (g0.st P).root (g0.st P).vS (g0.st P).vR),
                ({ g := g0.afterCorr P, h := st0, abort := abort0 }, we0)) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, hkSlot, hooksLocalMainSlot]
              rw [StateT.run_bind, StateT.run_get, pure_bind]; simp [hskip],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inr P))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              pure (some (realParty (g0.st P) (g0.st P).γ (g0.st P).root (g0.st P).vS (g0.st P).vR),
                ({ g := g0.afterCorr P, h := st0.loc, abort := abort0 }, we0)) by
              dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, hkLoc,
                Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain,
                Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuth]
              rw [StateT.run_bind, StateT.run_get, pure_bind]; simp [hskip]]
        simp only [pure_bind, simulateQ_pure]
        exact ih _ (g0.afterCorr P) st0 abort0 we0 (Or.inr (postLeak_afterCorr_r71dc tL g0 P hpl0))
      · have hskip' : (abort0 = true ∨ g0.win = true) ∨ g0.corrAllowed P = false := by
          simpa [Bool.or_eq_true] using hskip
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inr P))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, hskip'],
            show (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen
                hkLoc Δcka qep fs.maxSkip tL false (.inr (.inr P))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.implLocalBucketAuthGen,
                QueryImpl.add_apply_inr, hskip']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost

private theorem halted_exit_leOne_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256)
    (oa : OracleComp (Fig8Dom Pt ℓ) Bool) (esLoc : LocESt Pt ℓ) (esM : SideESt Pt ℓ)
    (winEp : Option ℕ) (tblM : ℕ → SessHSt Pt ℓ)
    (hhalt : (esLoc.abort || esLoc.g.win) = true) (habort : esM.abort = esLoc.abort)
    (herase : eraseSt esM.g = eraseSt esLoc.g) :
    LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks oa esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false oa esM winEp tblM) := by
  unfold runLocCont runSideCont
  have heq := slot_eq_loc_of_postLeak_or_halted_r71dc (dhScheme Dh) (rootPRNG C.F encPt)
    (locFS_r71dc C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par ks
    oa esLoc.g esLoc.h esLoc.abort winEp (Or.inl hhalt)
  change LeOne _ _
  rw [show ({ g := esLoc.g, h := esLoc.h, abort := esLoc.abort } : LocESt Pt ℓ) = esLoc from rfl] at heq
  rw [heq]; simp only [Bool.false_eq_true, ↓reduceIte]
  exact Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt.halted_leOne
    (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.hooksLocalBucketAuthMain
      (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71dc C ℓ encT idOf) 1 qep tL)
    (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71dc C ℓ encT idOf) 1 qep true tL par false)
    1 qep (locFS_r71dc C ℓ encT idOf).maxSkip tL par
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
    (fun n s => pubFsMultiImpl_inl_run _ n s)
    oa { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort } esM winEp (fun _ => false, tblM)
    hhalt habort
    (eraseSt_win herase)
    (_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leaks herase)
    (_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_corrs herase)

private theorem maxOpt_ge_right_r71dc (o : Option ℕ) (x : ℕ) : x ≤ maxOpt o x := by
  cases o <;> simp [maxOpt]

private theorem run_liftH_r71dc {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (_root_.CryptoGames.SM.Engine.liftH x).run es =
      (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem bucketAuthCfg_deliverWin_r71dc {M : Type} (Δ : ℕ) (tL : Option ℕ) :
    (bucketAuthCfg (M := M) Δ tL).deliverWin = false := rfl

private theorem liftFSMultiBucket_inr_run_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ : ℕ)
    (la : Bool) (sIdx : ℕ)
    (q0 : (_root_.CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Domain)
    (h : MultiHSt_r71dc Pt) (tbl : ℕ → SessHSt Pt ℓ) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (.inr q0))).run h)).run (fun _ => false, tbl) =
    (do
      let p ← (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
        (.inr ⟨sIdx, q0⟩)).run (fun _ => false, tbl)
      pure ((p.1, h), p.2)) := by
  unfold Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase.liftFSMultiBucket
  rw [stateT_lift_run, query_eq_liftM, simulateQ_query]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, query_eq_liftM]
  change (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
    ((id <$> liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (.inr ⟨sIdx, q0⟩))) >>= fun u => pure (u, h))).run (fun _ => false, tbl) = _
  rw [id_map, simulateQ_query_bind]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
  simp only [StateT.run_bind, StateT.run_pure, simulateQ_pure]
  rfl

private theorem liftFS_corruptSender_run_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ : ℕ)
    (sIdx : ℕ) (h : MultiHSt_r71dc Pt) (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (RatchetSenderState (BitVec 256))} {s' : SessHSt Pt ℓ}
    (hstep : ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
      ((Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (_root_.CryptoGames.FSAEAD.corruptSenderQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
          (Ciphertext := ℕ × LibsignalCiphertextWithSalt32))).run h)).run (fun _ => false, tbl) =
    pure ((u, h), (fun _ => false, Function.update tbl sIdx s')) := by
  unfold _root_.CryptoGames.FSAEAD.corruptSenderQuery
  rw [liftFSMultiBucket_inr_run_r71dc C encT idOf ℓ false sIdx _ h tbl]
  erw [Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.pubFsMultiImpl_corruptSender_run
    C ℓ encT idOf sIdx tbl hstep, pure_bind]

private theorem liftFS_deliver_some_run_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ : ℕ)
    (la : Bool) (sIdx : ℕ) (hdr : Header Pt)
    (ctPair : ℕ × LibsignalCiphertextWithSalt32) (p : LibsignalMsgPublicPart)
    (hp_pub : lPubOf protoSignalCodec ctPair.2 = some p) (h : MultiHSt_r71dc Pt) (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.deliverH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la) (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((hdr, p), (ctPair.1, ctPair.2))).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (_root_.CryptoGames.FSAEAD.deliverQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) hdr ctPair)).run h)).run (fun _ => false, tbl) =
    pure ((u.map (_root_.CryptoGames.FSAEAD.withPub p), h), (fun _ => false, Function.update tbl sIdx s')) := by
  rcases ctPair with ⟨i, ct⟩
  unfold _root_.CryptoGames.FSAEAD.deliverQuery
  rw [liftFSMultiBucket_inr_run_r71dc C encT idOf ℓ la sIdx _ h tbl]
  erw [Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.pubFsMultiImpl_deliver_some_run
    C ℓ encT idOf la sIdx hdr i ct p hp_pub tbl hstep, pure_bind]

private theorem step_corrupt_postLeak_leOne_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    {phase1 : Bool} {rem' : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (k : Option (Fig8St Pt) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (hcorr : esLoc.g.corrAllowed P = true)
    (hpl_after : postLeak tL (esLoc.g.afterCorr P) = true)
    (ih : ∀ u esLoc' esM' tblM',
      CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp esLoc' esM' esM' none tblM' tblM' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    LeOne
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM winEp tblM) := by
  obtain rfl := hinv.hwe
  have hwinM : esM.g.win = false := by rw [eraseSt_win hinv.herase]; exact hinv.hwin_loc
  have hcorrM : esM.g.corrAllowed P = true := by rw [eraseSt_corrAllowed hinv.herase P]; exact hcorr
  let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root (esLoc.g.st P).vS (esLoc.g.st P).vR
  have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc none =
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some stOut))
        { esLoc with g := esLoc.g.afterCorr P } none := by
    unfold runLocCont; rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implLocalMainSlot, QueryImpl.add_apply_inr, hooksLocalMainSlot]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, StateT.run_get, pure_bind]
    simp [hinv.habort_loc, hinv.hwin_loc, hcorr, stOut]
  rw [hLocStep]
  have hact_false : ∀ t0 ss0 rs0, actEp t0 = some (ss0, rs0) →
      ActiveSessInv C ℓ encT idOf false (ks (sIdxMain q tL t0)) ss0 rs0
        ((esM.h.book (sIdxMain q tL t0)).getD {}) (tblM (sIdxMain q tL t0)) (tblL (sIdxMain q tL t0)) := by
    intro t0 ss0 rs0 ha
    exact activeSessInv_any_to_phase2_r71dc C ℓ encT idOf (hinv.hact t0 ss0 rs0 ha).2.2.2.2.1
  have hvS_step : ∃ (h1 : MultiHSt_r71dc Pt) (tblM1 : ℕ → SessHSt Pt ℓ),
      (((esM.g.st P).vS = (esLoc.g.st P).vS.map Sum.inl ∧ h1 = esM.h ∧ tblM1 = tblM) ∨
        ∃ ss sIdx0 sM', (esLoc.g.st P).vS = some ss ∧ (esM.g.st P).vS = some (.inr sIdx0) ∧
          ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
              StateT (SessHSt Pt ℓ) ProbComp _)).run (tblM sIdx0) = pure (some ss, sM') ∧
          h1 = { esM.h with
                  book := Function.update esM.h.book sIdx0
                    (some { sCorr := true, fsCount := ((esM.h.book sIdx0).getD {}).fsCount,
                            fsTrans := ((esM.h.book sIdx0).getD {}).fsTrans }) } ∧
          tblM1 = Function.update tblM sIdx0 sM') ∧
      h1.cache = esM.h.cache ∧ h1.fTable = esM.h.fTable ∧ h1.sessions = esM.h.sessions ∧
      (∀ t0 ss0 rs0, actEp t0 = some (ss0, rs0) →
        let sIdx := sIdxMain q tL t0
        ActiveSessInv C ℓ encT idOf false (ks sIdx) ss0 rs0 ((h1.book sIdx).getD {}) (tblM1 sIdx) (tblL sIdx) ∧
        ((h1.book sIdx).getD {}).fsCount = ((esM.h.book sIdx).getD {}).fsCount ∧
        ((h1.book sIdx).getD {}).fsTrans = ((esM.h.book sIdx).getD {}).fsTrans) ∧
      (∀ sIdx, sIdx < mSessMain q qep tL →
        (∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp t0 = none) →
        h1.book sIdx = esM.h.book sIdx ∧ tblM1 sIdx = tblM sIdx) := by
    have hvSP := hinv.hvS P
    cases hvL : (esLoc.g.st P).vS with
    | none =>
      rw [hvL] at hvSP; dsimp only at hvSP
      exact ⟨esM.h, tblM, Or.inl ⟨hvSP.1, rfl, rfl⟩, rfl, rfl, rfl,
        fun t0 ss0 rs0 ha => ⟨hact_false t0 ss0 rs0 ha, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
    | some ss =>
      rw [hvL] at hvSP; dsimp only at hvSP
      rcases hvSP with ⟨ts, _, _, _, hvSP⟩
      cases ha0 : actEp ts with
      | none =>
        rw [ha0] at hvSP; dsimp only at hvSP
        exact ⟨esM.h, tblM, Or.inl ⟨hvSP, rfl, rfl⟩, rfl, rfl, rfl,
          fun t0 ss0 rs0 ha => ⟨hact_false t0 ss0 rs0 ha, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
      | some pair =>
        rcases pair with ⟨ssA, rsA⟩
        rw [ha0] at hvSP; dsimp only at hvSP
        rcases hvSP with ⟨hss_eq, hvM_eq⟩
        subst hss_eq
        let sIdx0 := sIdxMain q tL ts
        have hinv0 := hact_false ts ss rsA ha0
        rcases Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt.activeSessInv_corruptSender
          C ℓ encT idOf hinv0 with ⟨sM', hcs, hinv0'⟩
        let bk0 := (esM.h.book sIdx0).getD {}
        let h1 : MultiHSt_r71dc Pt := { esM.h with book := Function.update esM.h.book sIdx0 (some { bk0 with sCorr := true }) }
        let tblM1 := Function.update tblM sIdx0 sM'
        refine ⟨h1, tblM1, Or.inr ⟨ss, sIdx0, sM', rfl, hvM_eq, hcs, rfl, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
        · intro t0 ss0 rs0 ha
          by_cases ht : t0 = ts
          · subst ht; rw [ha0] at ha; cases ha
            refine ⟨by simpa [h1, tblM1, sIdx0, bk0] using hinv0', ?_, ?_⟩ <;> simp [h1, sIdx0, bk0]
          · have hne : sIdxMain q tL t0 ≠ sIdx0 := fun heq =>
              ht (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sIdxMain_inj
                q tL (hinv.hact t0 ss0 rs0 ha).1 (hinv.hact ts ss rsA ha0).1 heq)
            simp [h1, tblM1, hne, hact_false t0 ss0 rs0 ha]
        · intro sIdx hlt hun
          have hne : sIdx ≠ sIdx0 := fun heq => by
            subst heq; have := hun ts (hinv.hact ts ss rsA ha0).1 rfl; rw [ha0] at this; cases this
          simp [h1, tblM1, hne]
  rcases hvS_step with ⟨h1, tblM1, hvS_run, h1_cache, h1_fTable, h1_sess, h1_act, h1_un⟩
  let pInr : ℕ → Bool := fun t => match (esM.g.st P).vR t with | some (.inr _) => true | _ => false
  by_cases hany : ((List.range (q + 1)).any pInr) = true
  · refine leOne_of_lhs_zero ?_
    unfold runLocCont
    have heq := slot_eq_loc_of_postLeak_or_halted_r71dc
      (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71dc C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par ks
      (k (some stOut)) (esLoc.g.afterCorr P) esLoc.h esLoc.abort none (Or.inr hpl_after)
    rw [heq]
    obtain ⟨t, _, ht_inr⟩ := List.any_eq_true.mp hany
    have hvRt := hinv.hvR P t
    cases hvL_t : (esLoc.g.st P).vR t with
    | none => rw [hvL_t] at hvRt; dsimp only [pInr] at ht_inr; rw [hvRt] at ht_inr; cases ht_inr
    | some rs =>
      rw [hvL_t] at hvRt
      rcases hvRt with ⟨hsends_t, htle, hvRt⟩
      cases ha_t : actEp t with
      | none => rw [ha_t] at hvRt; dsimp only [pInr] at ht_inr; rw [hvRt] at ht_inr; cases ht_inr
      | some pair =>
        rcases pair with ⟨ss_t, rs_t⟩
        have hvg : validGuessBucketParAuth 1 tL par t = true := (hinv.hact t ss_t rs_t ha_t).2.2.1
        simp only [validGuessBucketParAuth, Bool.and_eq_true] at hvg
        have hep_ge : t ≤ esLoc.g.epoch P := by rw [← (hinv.hparty_tcur P).1]; exact htle
        have hlt_ep : ltOpt tL (esLoc.g.epoch P) = true :=
          Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.ltOpt_of_healedBy_le tL hvg.1 hep_ge
        have hP_recv : P = Party.receiverOf t := by
          cases hP : P.other.sendsIn t
          · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_t] at hP; cases hP
          · simpa using congrArg Party.other (_root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hP)
        have hmem_corr : (P, esLoc.g.epoch P) ∈ (esLoc.g.afterCorr P).corrs := by
          simp [GameState.afterCorr, GameState.leak]
        exact Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt.cLoc_zero_of_receiver_corr
          (dhScheme Dh) (rootPRNG C.F encPt)
          (locFS_r71dc C ℓ encT idOf) 1 qep tL par P (esLoc.g.epoch P)
          (k (some stOut)) { g := esLoc.g.afterCorr P, h := esLoc.h.loc, abort := esLoc.abort }
          hmem_corr hlt_ep
          (fun tWin hpar => hP_recv.trans
            (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.receiverOf_eq_of_sender_par par hvg.2 hpar))
          none rfl
  · simp only [Bool.not_eq_true] at hany
    have hvR_eq : (fun t => if t < q + 1 then
        match (esM.g.st P).vR t with | some (.inl rs) => some rs | _ => none else none) = (esLoc.g.st P).vR := by
      funext t
      by_cases ht : t < q + 1
      · simp only [ht, ↓reduceIte]
        have hnot : pInr t = false := by
          cases hp : pInr t with
          | false => rfl
          | true =>
            have := List.any_eq_true.mpr ⟨t, List.mem_range.mpr ht, hp⟩
            rw [hany] at this; cases this
        have hvRt := hinv.hvR P t
        cases hvL_t : (esLoc.g.st P).vR t with
        | none => rw [hvL_t] at hvRt; rw [hvRt]
        | some rs =>
          rw [hvL_t] at hvRt
          rcases hvRt with ⟨_, _, hvRt⟩
          cases ha_t : actEp t with
          | none => rw [ha_t] at hvRt; rw [hvRt]
          | some pair =>
            rw [ha_t] at hvRt; dsimp only [pInr] at hnot; rw [hvRt.2] at hnot; cases hnot
      · simp only [ht, ↓reduceIte]
        have ht_gt : (esLoc.g.st P).tcur < t := by have := hinv.htcur_le P; omega
        exact ((hinv.hvR_gt P t ht_gt).1).symm
    have hany_gen : ∀ f : ℕ → Bool,
        (∀ t, f t = match (esM.g.st P).vR t with | some (.inr _) => true | _ => false) →
        (List.range (q + 1)).any f = false := by
      intro f hf; rw [funext hf]; exact hany
    have hstOut_gen : ∀ (vS0 : Option (RatchetSenderState (BitVec 256)))
        (vR' : ℕ → Option (RatchetReceiverState (BitVec 256) (BitVec 256))),
        vS0 = (esLoc.g.st P).vS →
        (∀ t, vR' t = if t < q + 1 then
          match (esM.g.st P).vR t with | some (.inl rs) => some rs | _ => none else none) →
        realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root vS0 vR' = stOut := by
      intro vS0 vR' hvS0 hvR'
      subst hvS0; rw [funext hvR', hvR_eq]
      rcases hinv.hparty_id P with ⟨hidL, hidM⟩
      rcases hinv.hparty_base P with ⟨hγ, hcur, hroot⟩
      simp [realParty, stOut, hidL, hidM, hγ, hcur, hroot, (hinv.hparty_tcur P).2]
    have hMStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM none tblM =
        runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k (some stOut))
          { esM with g := esM.g.afterCorr P, h := h1 } none tblM1 := by
      rw [runSideCont_step]
      have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par false)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
          (.inr (.inr P))).run (esM, none))).run (fun _ => false, tblM) =
        pure ((some stOut, ({ esM with g := esM.g.afterCorr P, h := h1 }, none)),
          (fun _ => false, tblM1)) := by
        dsimp only [implFSMultiBucketAuth, hooksFSMultiBucketAuth]
        simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind,
          hinv.habort_M, hwinM, hcorrM, Bool.not_true, Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, Bool.false_and, stateT_lift_run, simulateQ_bind, bind_assoc]
        rcases hvS_run with ⟨hvM_eq, rfl, rfl⟩ | ⟨ss, sIdx0, sM', hvL_eq, hvM_eq, hcs, rfl, rfl⟩
        · rw [hvM_eq]
          rcases hvL : (esLoc.g.st P).vS with _ | ss <;>
            (simp only [Option.map, StateT.run_pure, simulateQ_pure, pure_bind]
             split_ifs with hif
             · exfalso
               rw [hany_gen _ (fun t => by cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)] at hif
               cases hif
             · simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set, StateT.run_bind]
               rw [hstOut_gen _ _ hvL.symm (fun t => by
                 by_cases ht : t < q + 1 <;> simp only [ht, ↓reduceIte]
                 cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)])
        · rw [hvM_eq]
          simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
          rw [liftFS_corruptSender_run_r71dc C encT idOf ℓ sIdx0 esM.h tblM hcs]
          simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
          split_ifs with hif
          · exfalso
            rw [hany_gen _ (fun t => by cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)] at hif
            cases hif
          · simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set, StateT.run_bind]
            rw [hstOut_gen _ _ hvL_eq.symm (fun t => by
              by_cases ht : t < q + 1 <;> simp only [ht, ↓reduceIte]
              cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)]
      erw [hhead]
      rw [pure_bind]; rfl
    rw [hMStep]
    refine ih (some stOut) { esLoc with g := esLoc.g.afterCorr P }
      { esM with g := esM.g.afterCorr P, h := h1 } tblM1
      (coupledInv_false_swap_r71dc (esL := esL) (tblL := tblL) ?_)
    let cur := maxOpt esLoc.g.tL (max (esLoc.g.epoch .A) (esLoc.g.epoch .B))
    have htL_after : (esLoc.g.afterCorr P).tL = some cur := rfl
    have hlt_cur : ltOpt tL cur = true := by simpa [postLeak, htL_after] using hpl_after
    have hst_afterL : (esLoc.g.afterCorr P).st = esLoc.g.st := rfl
    refine {
      habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
      herase := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hinv.herase P
      hep_le := hinv.hep_le, hep_sends := hinv.hep_sends
      hphase1 := fun h => Bool.noConfusion h
      hphase2 := fun _ => ⟨cur, htL_after, hlt_cur, fun t0 ha => by
        cases ha' : actEp t0 with
        | none => exact absurd ha' ha
        | some pair =>
          have hle := (hinv.hact t0 pair.1 pair.2 ha').2.2.2.1
          rw [(hinv.hparty_tcur (Party.senderOf t0)).1] at hle
          have hm : esLoc.g.epoch (Party.senderOf t0) ≤ max (esLoc.g.epoch .A) (esLoc.g.epoch .B) := by
            cases Party.senderOf t0 <;> simp
          exact hle.trans (hm.trans (maxOpt_ge_right_r71dc _ _))⟩
      hparty_id := hinv.hparty_id, hparty_tcur := hinv.hparty_tcur, hparty_base := hinv.hparty_base
      htcur_le := fun Q => by dsimp only; rw [hst_afterL]; have := hinv.htcur_le Q; omega
      hvR_gt := hinv.hvR_gt, hvS := hinv.hvS, hvR := hinv.hvR
      hcache := by dsimp only; rw [hst_afterL, h1_cache]; exact hinv.hcache
      hfuture := fun t ht => by
        dsimp only at ht ⊢; rw [hst_afterL] at ht
        rcases hinv.hfuture t ht with ⟨h1', h2', h3', h4', h5', h6'⟩
        exact ⟨h1', h2', by simpa [h1_cache] using h3', h4', by simpa [h1_fTable] using h5',
          by simpa [h1_sess] using h6'⟩
      hact := fun t0 ss0 rs0 ha => by
        dsimp only; rw [hst_afterL]
        rcases hinv.hact t0 ss0 rs0 ha with ⟨hh1, hh2, hh3, hh4, _, hh6, hh7⟩
        rcases h1_act t0 ss0 rs0 ha with ⟨ha_inv, hcnt, htr⟩
        exact ⟨hh1, hh2, hh3, hh4, ha_inv, fun ht => (hh6 ht).trans hcnt.symm, htr.trans hh7⟩
      hunalloc := fun sIdx hlt hun => by
        rcases hinv.hunalloc sIdx hlt hun with ⟨hu1, hu2, hu3, _⟩
        rcases h1_un sIdx hlt hun with ⟨hb_eq, htbl_eq⟩
        exact ⟨hu1, hb_eq.trans hu2, htbl_eq.trans hu3, fun h => Bool.noConfusion h⟩
      htrans := hinv.htrans }

private theorem step_corrupt_phase1_noLeak_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    {rem' : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (k : Option (Fig8St Pt) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (hcorr : esLoc.g.corrAllowed P = true)
    (hpl_after : postLeak tL (esLoc.g.afterCorr P) = false)
    (ih : ∀ u esLoc' esM' esL',
      CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp esLoc' esM' esL' none tblM tblL →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL)) :
    LeAdd
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM winEp tblM)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esL winEp tblL) := by
  obtain rfl := hinv.hwe
  rcases hinv.hphase1 rfl with ⟨_, hesL, hlf0, hsc0⟩
  cases hesL
  have hwinM : esM.g.win = false := by rw [eraseSt_win hinv.herase]; exact hinv.hwin_loc
  have hcorrM : esM.g.corrAllowed P = true := by rw [eraseSt_corrAllowed hinv.herase P]; exact hcorr
  let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root (esLoc.g.st P).vS (esLoc.g.st P).vR
  let cur := maxOpt esLoc.g.tL (max (esLoc.g.epoch .A) (esLoc.g.epoch .B))
  have hno_act_le : ∀ t0, t0 ≤ esLoc.g.epoch P → actEp t0 = none := by
    intro t0 hle
    cases ha : actEp t0 with
    | none => rfl
    | some pair =>
      have hvg := (hinv.hact t0 pair.1 pair.2 ha).2.2.1
      simp only [validGuessBucketParAuth, Bool.and_eq_true] at hvg
      have hep_cur : esLoc.g.epoch P ≤ cur := by
        have hm : esLoc.g.epoch P ≤ max (esLoc.g.epoch .A) (esLoc.g.epoch .B) := by cases P <;> simp
        exact hm.trans (maxOpt_ge_right_r71dc _ _)
      have hpl : postLeak tL (esLoc.g.afterCorr P) = true :=
        Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.ltOpt_of_healedBy_le
          tL hvg.1 (hle.trans hep_cur)
      rw [hpl_after] at hpl; cases hpl
  have hvS_eq : (esM.g.st P).vS = ((esLoc.g.st P).vS).map Sum.inl := by
    have hvSP := hinv.hvS P
    cases hvL : (esLoc.g.st P).vS with
    | none => rw [hvL] at hvSP; simp [hvSP.1]
    | some ss =>
      rw [hvL] at hvSP
      rcases hvSP with ⟨ts, hts, _, _, hvSP⟩
      have ha0 : actEp ts = none := hno_act_le ts (by rw [← (hinv.hparty_tcur P).1]; exact hts)
      rw [ha0] at hvSP; simp [hvSP]
  have hvR_M_eq : ∀ t, (esM.g.st P).vR t = ((esLoc.g.st P).vR t).map Sum.inl := by
    intro t
    have hvRt := hinv.hvR P t
    cases hvL_t : (esLoc.g.st P).vR t with
    | none => rw [hvL_t] at hvRt; simp [hvRt]
    | some rs =>
      rw [hvL_t] at hvRt
      rcases hvRt with ⟨_, htle, hvRt⟩
      have ha_t : actEp t = none := hno_act_le t (by rw [← (hinv.hparty_tcur P).1]; exact htle)
      rw [ha_t] at hvRt; simp [hvRt]
  have hany : ((List.range (q + 1)).any
      (fun t => match (esM.g.st P).vR t with | some (.inr _) => true | _ => false)) = false := by
    rw [List.any_eq_false]; intro t _; rw [hvR_M_eq t]; cases (esLoc.g.st P).vR t <;> simp
  have hvR_eq : (fun t => if t < q + 1 then
      match (esM.g.st P).vR t with | some (.inl rs) => some rs | _ => none else none) = (esLoc.g.st P).vR := by
    funext t
    by_cases ht : t < q + 1
    · rw [hvR_M_eq t]; cases (esLoc.g.st P).vR t <;> simp [ht]
    · have ht_gt : (esLoc.g.st P).tcur < t := by have := hinv.htcur_le P; omega
      simp [ht, (hinv.hvR_gt P t ht_gt).1]
  have hany_gen : ∀ f : ℕ → Bool,
      (∀ t, f t = match (esM.g.st P).vR t with | some (.inr _) => true | _ => false) →
      (List.range (q + 1)).any f = false := by
    intro f hf; rw [funext hf]; exact hany
  have hstOut_gen : ∀ (vS0 : Option (RatchetSenderState (BitVec 256)))
      (vR' : ℕ → Option (RatchetReceiverState (BitVec 256) (BitVec 256))),
      vS0 = (esLoc.g.st P).vS →
      (∀ t, vR' t = if t < q + 1 then
        match (esM.g.st P).vR t with | some (.inl rs) => some rs | _ => none else none) →
      realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root vS0 vR' = stOut := by
    intro vS0 vR' hvS0 hvR'
    subst hvS0; rw [funext hvR', hvR_eq]
    rcases hinv.hparty_id P with ⟨hidL, hidM⟩
    rcases hinv.hparty_base P with ⟨hγ, hcur, hroot⟩
    simp [realParty, stOut, hidL, hidM, hγ, hcur, hroot, (hinv.hparty_tcur P).2]
  have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc none =
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k (some stOut))
        { esLoc with g := esLoc.g.afterCorr P } none := by
    unfold runLocCont; rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implLocalMainSlot, QueryImpl.add_apply_inr, hooksLocalMainSlot]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, StateT.run_get, pure_bind]
    simp [hinv.habort_loc, hinv.hwin_loc, hcorr, stOut]
  have hSideStep : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
      runSideCont C Dh encPt encT idOf ℓ q qep tL par la
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM none tbl =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par la (k (some stOut))
        { esM with g := esM.g.afterCorr P } none tbl := by
    intro la tbl
    rw [runSideCont_step]
    have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((implFSMultiBucketAuth
        (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
        1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
        (.inr (.inr P))).run (esM, none))).run (fun _ => false, tbl) =
      pure ((some stOut, ({ esM with g := esM.g.afterCorr P }, none)),
        (fun _ => false, tbl)) := by
      dsimp only [implFSMultiBucketAuth, hooksFSMultiBucketAuth]
      simp only [QueryImpl.add_apply, StateT.run_bind, StateT.run_get, pure_bind,
        hinv.habort_M, hwinM, hcorrM, Bool.not_true, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, Bool.false_and, stateT_lift_run, simulateQ_bind, bind_assoc]
      rw [hvS_eq]
      rcases hvL : (esLoc.g.st P).vS with _ | ss <;>
        (simp only [Option.map, StateT.run_pure, simulateQ_pure, pure_bind]
         split_ifs with hif
         · exfalso
           rw [hany_gen _ (fun t => by cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)] at hif
           cases hif
         · simp only [StateT.run_pure, simulateQ_pure, pure_bind, StateT.run_set, StateT.run_bind]
           rw [hstOut_gen _ _ hvL.symm (fun t => by
             by_cases ht : t < q + 1 <;> simp only [ht, ↓reduceIte]
             cases (esM.g.st P).vR t with | none => rfl | some s => cases s <;> rfl)])
    erw [hhead]
    rw [pure_bind]; rfl
  rw [hLocStep, hSideStep false tblM, hSideStep true tblL]
  have hst_afterL : (esLoc.g.afterCorr P).st = esLoc.g.st := rfl
  exact ih (some stOut) { esLoc with g := esLoc.g.afterCorr P }
    { esM with g := esM.g.afterCorr P } { esM with g := esM.g.afterCorr P } {
      habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
      herase := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hinv.herase P
      hep_le := hinv.hep_le, hep_sends := hinv.hep_sends
      hphase1 := fun _ => ⟨hpl_after, rfl, hlf0, hsc0⟩, hphase2 := fun h => Bool.noConfusion h
      hparty_id := hinv.hparty_id, hparty_tcur := hinv.hparty_tcur, hparty_base := hinv.hparty_base
      htcur_le := fun Q => by dsimp only; rw [hst_afterL]; have := hinv.htcur_le Q; omega
      hvR_gt := hinv.hvR_gt, hvS := hinv.hvS, hvR := hinv.hvR
      hcache := by dsimp only; rw [hst_afterL]; exact hinv.hcache
      hfuture := fun t ht => by dsimp only at ht ⊢; rw [hst_afterL] at ht; exact hinv.hfuture t ht
      hact := fun t0 ss0 rs0 ha => by dsimp only; rw [hst_afterL]; exact hinv.hact t0 ss0 rs0 ha
      hunalloc := hinv.hunalloc, htrans := hinv.htrans }

private theorem ct_beq_iff_r71dc :
    ∀ (c1 c2 : ℕ × LibsignalCiphertextWithSalt32), (c1 == c2) = true ↔ c1 = c2
  | ⟨n1, s1, b1⟩, ⟨n2, s2, b2⟩ => by
    change (n1 == n2 && (s1 == s2 && b1 == b2)) = true ↔ _
    simp [Bool.and_eq_true, beq_iff_eq]

private theorem hdr_beq_iff_r71dc {Pt : Type} [DecidableEq Pt] :
    ∀ (h1 h2 : Header Pt), (h1 == h2) = true ↔ h1 = h2
  | ⟨t1, o1⟩, ⟨t2, o2⟩ => by
    cases o1 <;> cases o2 <;>
      (change (t1 == t2 && _) = true ↔ _; dsimp only [BEq.beq, Option.instBEq, Option.instBEq.beq];
       simp [Bool.and_eq_true])

private theorem beq_hdr_ct_inst_eq_r71dc {Pt : Type} [DecidableEq Pt]
    (p q : Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :
    @BEq.beq (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (@instBEqProd (Header Pt) (ℕ × LibsignalCiphertextWithSalt32) inferInstance instBEqOfDecidableEq)
      p q = (p == q) := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  have hb : @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq p2 q2 = (p2 == q2) := by
    rw [Bool.eq_iff_iff, ct_beq_iff_r71dc]; simp [BEq.beq]
  show (p1 == q1 && @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq p2 q2) =
    (p1 == q1 && p2 == q2)
  rw [hb]

private theorem find_filter_map_trans_r71dc {Pt M : Type} [DecidableEq Pt]
    (L : List (Record M (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (hP : P.other = Party.senderOf c.1.1)
    (htr : ∀ r ∈ L, r.pos.epoch = r.ct.1.1 ∧ r.pos.sender = Party.senderOf r.pos.epoch) :
    ((L.filter (fun r => r.pos.epoch == c.1.1)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2))).find?
      (fun x => x.2 == c) =
    (L.find? (fun r => r.pos.sender == P.other && decide (r.ct = c))).map
      (fun r => (r.pos.idx, r.ct.1, r.ct.2)) := by
  induction L with
  | nil => rfl
  | cons r rs ih =>
    rcases htr r List.mem_cons_self with ⟨hep, hsend⟩
    have ih' := ih (fun r' hr' => htr r' (List.mem_cons_of_mem _ hr'))
    by_cases hct : r.ct = c
    · subst hct
      have h1 : (r.pos.epoch == r.ct.1.1) = true := by simp [hep]
      have h2 : (r.pos.sender == P.other) = true := by simp [hsend, hP, hep]
      have h3 : ((r.ct.1, r.ct.2) == r.ct) = true := by
        change (r.ct.1 == r.ct.1 && r.ct.2 == r.ct.2) = true
        simp [hdr_beq_iff_r71dc, ct_beq_iff_r71dc]
      simp [h1, h2, h3]
    · by_cases he : (r.pos.epoch == c.1.1) = true
      · have hne2 : ((r.ct.1, r.ct.2) == c) = false := by
          change (r.ct.1 == c.1 && r.ct.2 == c.2) = false
          cases hbeq : (r.ct.1 == c.1 && r.ct.2 == c.2) with
          | false => rfl
          | true =>
            simp only [Bool.and_eq_true, hdr_beq_iff_r71dc, ct_beq_iff_r71dc] at hbeq
            exact False.elim (hct (Prod.ext hbeq.1 hbeq.2))
        simp [he, hct, hne2, ih']
      · simp only [Bool.not_eq_true] at he
        simp [he, hct, ih']

private theorem accept_update_idem_r71dc {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : _root_.CryptoGames.SM.Pos) :
    { s.accept P st' pos with st := Function.update (s.accept P st' pos).st P st' } = s.accept P st' pos := by
  have : Function.update (Function.update s.st P st') P st' = Function.update s.st P st' := by
    funext Q; by_cases hQ : Q = P <;> simp [hQ]
  cases s; simp [GameState.accept, GameState.delete, this]

private theorem vRecvStep1_coupled_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    {phase1 : Bool} {rem : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (hbad : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) = false) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71dc C ℓ encT idOf)
      1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71dc C ℓ encT idOf) 1 qep true tL par la
    ((_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (none, esLoc.h) ∧
      ∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (none, esM.h)) ∨
    ((_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (some none, esLoc.h) ∧
      ∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (some none, esM.h)) ∨
    ∃ s1Loc s1M,
      (_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (some (some s1Loc), esLoc.h) ∧
      (∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (some (some s1M), esM.h)) ∧
      (s1Loc.id = P ∧ s1M.id = P) ∧
      (s1Loc.tcur = max (esLoc.g.st P).tcur c.1.1 ∧ s1M.tcur = s1Loc.tcur) ∧
      (c.1.1 = (esLoc.g.st P).tcur + 1 → c.1.1 ≤ (esLoc.g.st P.other).tcur) ∧
      (s1M.γ = s1Loc.γ ∧ s1M.curCkaMsg = s1Loc.curCkaMsg ∧ s1M.root = s1Loc.root) ∧
      (s1Loc.vS = (esLoc.g.st P).vS ∧ s1M.vS = (esM.g.st P).vS) ∧
      (∀ t, s1Loc.tcur < t → s1Loc.vR t = none ∧ s1M.vR t = none) ∧
      (∀ t, t ≠ c.1.1 → s1Loc.vR t = (esLoc.g.st P).vR t ∧ s1M.vR t = (esM.g.st P).vR t) ∧
      (match s1Loc.vR c.1.1 with
        | none => s1M.vR c.1.1 = none
        | some rs => match actEp c.1.1 with
          | none => s1M.vR c.1.1 = some (.inl rs)
          | some (_, rsA) => rs = rsA ∧ s1M.vR c.1.1 = some (.inr (sIdxMain q tL c.1.1))) := by
  intro hkLoc hkM
  rcases hinv.hparty_id P with ⟨hidL, hidM⟩
  have htcurM : (esM.g.st P).tcur = (esLoc.g.st P).tcur := (hinv.hparty_tcur P).2
  rcases hinv.hparty_base P with ⟨hγM, hcurM, hrootM⟩
  rw [hidL, Bool.or_eq_false_iff] at hbad
  rcases hbad with ⟨hsends_c, hle_succ⟩
  simp only [decide_eq_false_iff_not, not_lt] at hle_succ
  have hP_other : Party.senderOf c.1.1 = P.other := by
    cases hPo : P.other.sendsIn c.1.1
    · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
    · exact (_root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo).symm
  have hP_recv : Party.receiverOf c.1.1 = P := by
    simp [Party.receiverOf, hP_other]
  unfold _root_.CryptoGames.SM.Engine.vRecvStep1
  rw [htcurM]
  by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
  · simp only [hnew, ↓reduceIte]
    cases hc2 : c.1.2 with
    | none => right; left; exact ⟨rfl, fun _ => rfl⟩
    | some Tn =>
      dsimp only [hkLoc, hkM, hooksLocalMainSlot, hooksFSMultiBucketAuth]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      have hbeq : (((esLoc.g.st P).tcur + 1 == healEpoch tL)) =
          decide ((esLoc.g.st P).tcur + 1 = healEpoch tL) := Bool.eq_iff_iff.mpr (by simp)
      rcases hinv.hcache ((esLoc.g.st P).tcur + 1) with ⟨hcL, hcM⟩ | ⟨_, hle_send, Tc, σc, kVal, hcL, hcM_match⟩
      · rw [hcL, hcM]; dsimp only
        by_cases hcond : (!(decide (qep + 1 < (esLoc.g.st P).tcur + 1)) &&
            lastLeakGuessAdmissible (2 + 1) tL ((esLoc.g.st P).tcur + 1) &&
            (tL.isSome && decide ((esLoc.g.st P).tcur + 1 = healEpoch tL))) = true
        · left; exact ⟨by simp only [hcond, ↓reduceIte, StateT.run_pure, pure_bind],
            fun _ => by simp only [hbeq, hcond, ↓reduceIte, StateT.run_pure, pure_bind]⟩
        · simp only [Bool.not_eq_true] at hcond
          right; left; exact ⟨by simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind],
            fun _ => by simp only [hbeq, hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]⟩
      · rw [hcL]
        by_cases htc : Tc = Tn
        · subst Tn
          right; right
          have hmax : max (esLoc.g.st P).tcur ((esLoc.g.st P).tcur + 1) = (esLoc.g.st P).tcur + 1 := by omega
          have hle_other : (esLoc.g.st P).tcur + 1 ≤ (esLoc.g.st P.other).tcur := by
            rw [← hnew, hP_other] at hle_send; rw [← hnew]; exact hle_send
          have hvR_none : (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1) = none :=
            (hinv.hvR_gt P ((esLoc.g.st P).tcur + 1) (by omega)).1
          cases ha : actEp ((esLoc.g.st P).tcur + 1) with
          | none =>
            rw [ha] at hcM_match
            let s1Loc := { (esLoc.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esLoc.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some ((locFS_r71dc C ℓ encT idOf).initReceiver kVal)) }
            let s1M := { (esM.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esM.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esM.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some (.inl ((locFS_r71dc C ℓ encT idOf).initReceiver kVal))) }
            refine ⟨s1Loc, s1M, by simp only [↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              fun _ => by simp only [hcM_match, ↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              ⟨hidL, hidM⟩, ⟨hmax.symm, rfl⟩, fun _ => hle_other,
              ⟨by simp [s1Loc, s1M, hγM], hcurM, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
            · intro t ht; have ht' : (esLoc.g.st P).tcur < t := by dsimp [s1Loc] at ht; omega
              have hne : t ≠ (esLoc.g.st P).tcur + 1 := by dsimp [s1Loc] at ht; omega
              simp [s1Loc, s1M, hne, hinv.hvR_gt P t ht']
            · intro t hne; simp [s1Loc, s1M, hne]
            · simp [s1Loc, s1M, ha]
          | some pair =>
            rcases pair with ⟨ssA, rsA⟩
            rw [ha] at hcM_match
            rcases hcM_match with ⟨hk_eq, ⟨kDummy, hcM⟩, hrs_init⟩
            have hrsA : rsA = (locFS_r71dc C ℓ encT idOf).initReceiver kVal :=
              hrs_init (by rw [← hnew, hP_recv, hnew]; exact hvR_none)
            let s1Loc := { (esLoc.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esLoc.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some ((locFS_r71dc C ℓ encT idOf).initReceiver kVal)) }
            let s1M := { (esM.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esM.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esM.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some (.inr (sIdxMain q tL ((esLoc.g.st P).tcur + 1)))) }
            refine ⟨s1Loc, s1M, by simp only [↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              fun _ => by simp only [hcM, ↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              ⟨hidL, hidM⟩, ⟨hmax.symm, rfl⟩, fun _ => hle_other,
              ⟨by simp [s1Loc, s1M, hγM], hcurM, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
            · intro t ht; have ht' : (esLoc.g.st P).tcur < t := by dsimp [s1Loc] at ht; omega
              have hne : t ≠ (esLoc.g.st P).tcur + 1 := by dsimp [s1Loc] at ht; omega
              simp [s1Loc, s1M, hne, hinv.hvR_gt P t ht']
            · intro t hne; simp [s1Loc, s1M, hne]
            · simp [s1Loc, s1M, ha, hrsA.symm]
        · by_cases hcond : (!(decide (qep + 1 < (esLoc.g.st P).tcur + 1)) &&
              lastLeakGuessAdmissible (2 + 1) tL ((esLoc.g.st P).tcur + 1) &&
              (tL.isSome && decide ((esLoc.g.st P).tcur + 1 = healEpoch tL))) = true
          · left; refine ⟨by simp only [htc, ↓reduceIte, hcond, StateT.run_pure, pure_bind], fun _ => ?_⟩
            cases ha : actEp ((esLoc.g.st P).tcur + 1) with
            | none => rw [ha] at hcM_match; simp only [hcM_match, htc, ↓reduceIte, hbeq, hcond, StateT.run_pure, pure_bind]
            | some p => rw [ha] at hcM_match; rcases hcM_match.2.1 with ⟨kDummy, hcM⟩; simp only [hcM, htc, ↓reduceIte, hbeq, hcond, StateT.run_pure, pure_bind]
          · simp only [Bool.not_eq_true] at hcond
            right; left; refine ⟨by simp only [htc, ↓reduceIte, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind], fun _ => ?_⟩
            cases ha : actEp ((esLoc.g.st P).tcur + 1) with
            | none => rw [ha] at hcM_match; simp only [hcM_match, htc, ↓reduceIte, hbeq, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind]
            | some p => rw [ha] at hcM_match; rcases hcM_match.2.1 with ⟨kDummy, hcM⟩; simp only [hcM, htc, ↓reduceIte, hbeq, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind]
  · simp only [hnew, ↓reduceIte]
    have hle_cur : c.1.1 ≤ (esLoc.g.st P).tcur := by omega
    have hmax : max (esLoc.g.st P).tcur c.1.1 = (esLoc.g.st P).tcur := Nat.max_eq_left hle_cur
    right; right
    refine ⟨esLoc.g.st P, esM.g.st P, rfl, fun _ => rfl, ⟨hidL, hidM⟩, ⟨hmax.symm, htcurM⟩,
      False.elim, ⟨hγM, hcurM, hrootM⟩, ⟨rfl, rfl⟩,
      fun t ht => hinv.hvR_gt P t ht, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    have hvRc := hinv.hvR P c.1.1
    cases hvL_c : (esLoc.g.st P).vR c.1.1 with
    | none => rw [hvL_c] at hvRc; exact hvRc
    | some rs => rw [hvL_c] at hvRc; exact hvRc.2.2

private theorem commit_accept_coupled_r71dc {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    {phase1 : Bool} {rem' : ℕ} {actEp actEp' : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ}
    {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ} {hM' : MultiHSt_r71dc Pt}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt) (idxOut : ℕ)
    (hsends_c : P.sendsIn c.1.1 = false) (hle_succ : c.1.1 ≤ (esLoc.g.st P).tcur + 1)
    (s1Loc : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (s1M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (rsLoc' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (rsv' : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hs1_id : s1Loc.id = P ∧ s1M.id = P)
    (hs1_tcur : s1Loc.tcur = max (esLoc.g.st P).tcur c.1.1 ∧ s1M.tcur = s1Loc.tcur)
    (hs1_new : c.1.1 = (esLoc.g.st P).tcur + 1 → c.1.1 ≤ (esLoc.g.st P.other).tcur)
    (hs1_base : s1M.γ = s1Loc.γ ∧ s1M.curCkaMsg = s1Loc.curCkaMsg ∧ s1M.root = s1Loc.root)
    (hs1_vS : s1Loc.vS = (esLoc.g.st P).vS ∧ s1M.vS = (esM.g.st P).vS)
    (hs1_vR_gt : ∀ t, s1Loc.tcur < t → s1Loc.vR t = none ∧ s1M.vR t = none)
    (hs1_vR_ne : ∀ t, t ≠ c.1.1 → s1Loc.vR t = (esLoc.g.st P).vR t ∧ s1M.vR t = (esM.g.st P).vR t)
    (hrsv' : match actEp' c.1.1 with
      | none => actEp c.1.1 = none ∧ rsv' = .inl rsLoc'
      | some (ssA, rsA) => rsLoc' = rsA ∧ rsv' = .inr (sIdxMain q tL c.1.1) ∧
          ∃ rs0, actEp c.1.1 = some (ssA, rs0))
    (hact_ne : ∀ t, t ≠ c.1.1 → actEp' t = actEp t)
    (hhM_base : hM'.cache = esM.h.cache ∧ hM'.fTable = esM.h.fTable ∧ hM'.sessions = esM.h.sessions ∧
      hM'.lfWin = esM.h.lfWin)
    (hact' : ∀ t0 ss0 rs0, actEp' t0 = some (ss0, rs0) →
      let sIdx := sIdxMain q tL t0
      let bk' := (hM'.book sIdx).getD {}
      ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) ss0 rs0 bk' (tblM' sIdx) (tblL' sIdx) ∧
      (phase1 = true → bk'.sCorr = false) ∧
      bk'.fsCount = ((esM.h.book sIdx).getD {}).fsCount ∧
      bk'.fsTrans = (((esLoc.g.accept P { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
        ⟨P.other, c.1.1, idxOut⟩).trans.filter (fun r => r.pos.epoch == t0)).map
        (fun r => (r.pos.idx, r.ct.1, r.ct.2))))
    (hun' : ∀ sIdx, sIdx < mSessMain q qep tL →
      (∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp' t0 = none) →
      hM'.book sIdx = esM.h.book sIdx ∧ tblM' sIdx = tblM sIdx ∧ (phase1 = true → tblL' sIdx = tblL sIdx)) :
    let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, c.1.1, idxOut⟩
    let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
    let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some rsv') }
    CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp'
      { esLoc with g := esLoc.g.accept P stLoc' pos }
      { esM with g := esM.g.accept P stM' pos, h := hM' }
      (if phase1 then { esM with g := esM.g.accept P stM' pos, h := hM' } else esL)
      none tblM' tblL' := by
  intro pos stLoc' stM'
  have hep_P : esLoc.g.epoch P = (esLoc.g.st P).tcur := ((hinv.hparty_tcur P).1).symm
  have hep_Po : esLoc.g.epoch P.other = (esLoc.g.st P.other).tcur := ((hinv.hparty_tcur P.other).1).symm
  have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ ((esLoc.g.accept P stLoc' pos).st Q).tcur := by
    intro Q; dsimp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst Q; simp [stLoc', hs1_tcur.1]
    · simp [hQ]
  have ha_iff : ∀ t0, (actEp' t0 = none) ↔ (actEp t0 = none) := by
    intro t0
    by_cases ht : t0 = c.1.1
    · subst t0
      cases ha' : actEp' c.1.1 with
      | none => rw [ha'] at hrsv'; simp [hrsv'.1]
      | some p => rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨_, ha0⟩; simp [ha0]
    · rw [hact_ne t0 ht]
  refine {
    habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
    herase := by
      have h := hinv.herase
      rcases esM with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      rcases esLoc with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [eraseSt] at h
      injection h; subst_vars; rfl
    hep_le := fun Q => by
      dsimp only [GameState.accept, GameState.delete, pos]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, Function.update_of_ne (Party.other_ne P)]
        by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
        · have := hs1_new hnew; have := hinv.hep_le P; omega
        · have h1 : c.1.1 ≤ esLoc.g.epoch P := by omega
          rw [Nat.max_eq_left h1]; exact hinv.hep_le P
      · have hQo : Q.other = P := by cases Q <;> cases P <;> simp_all
        simp only [Function.update_of_ne hQ, hQo, Function.update_self]
        have hleQ := hinv.hep_le Q; rw [hQo] at hleQ; omega
    hep_sends := fun Q hlt => by
      dsimp only [GameState.accept, GameState.delete, pos] at hlt ⊢
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, Function.update_of_ne (Party.other_ne P)] at hlt ⊢
        by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
        · have := hs1_new hnew; omega
        · have h1 : c.1.1 ≤ esLoc.g.epoch P := by omega
          rw [Nat.max_eq_left h1] at hlt ⊢; exact hinv.hep_sends P hlt
      · have hQo : Q.other = P := by cases Q <;> cases P <;> simp_all
        simp only [Function.update_of_ne hQ, hQo, Function.update_self] at hlt ⊢
        exact hinv.hep_sends Q (by rw [hQo]; omega)
    hphase1 := fun hp1 => by
      rcases hinv.hphase1 hp1 with ⟨hpl0, _, hlf0, _⟩
      refine ⟨hpl0, by simp [hp1], by rw [hhM_base.2.2.2, hlf0], fun t0 ha => ?_⟩
      cases ha' : actEp' t0 with
      | none => exact absurd ha' ha
      | some p => exact (hact' t0 p.1 p.2 ha').2.1 hp1
    hphase2 := fun hp2 => by
      rcases hinv.hphase2 hp2 with ⟨cur, htL_cur, hlt_cur, hle_cur⟩
      exact ⟨cur, htL_cur, hlt_cur, fun t0 ha => hle_cur t0 (fun hn => ha ((ha_iff t0).mpr hn))⟩
    hparty_id := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_id.1, hs1_id.2]
      · simp [hQ, hinv.hparty_id Q]
    hparty_tcur := fun Q => by
      dsimp only [GameState.accept, GameState.delete, pos]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_tcur.1, hs1_tcur.2, hep_P]
      · simp [hQ, hinv.hparty_tcur Q]
    hparty_base := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_base.1, hs1_base.2.1, hs1_base.2.2]
      · simp [hQ, hinv.hparty_base Q]
    htcur_le := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', hs1_tcur.1]
        have := hinv.htcur_le P; omega
      · simp only [Function.update_of_ne hQ]; have := hinv.htcur_le Q; omega
    hvR_gt := fun Q t ht => by
      dsimp only [GameState.accept, GameState.delete] at ht ⊢
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM'] at ht ⊢
        have hne : t ≠ c.1.1 := by rw [hs1_tcur.1] at ht; omega
        simp [hne, hs1_vR_gt t ht]
      · simp only [Function.update_of_ne hQ] at ht ⊢; exact hinv.hvR_gt Q t ht
    hvS := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM', hs1_vS.1, hs1_vS.2, hs1_tcur.1]
        have hvSP := hinv.hvS P
        cases hvL : (esLoc.g.st P).vS with
        | none =>
          rw [hvL] at hvSP; dsimp only at hvSP ⊢
          refine ⟨hvSP.1, ?_⟩
          by_cases hnew : c.1.1 ≤ (esLoc.g.st P).tcur
          · rw [Nat.max_eq_left hnew]; exact hvSP.2
          · rw [show max (esLoc.g.st P).tcur c.1.1 = c.1.1 by omega]; exact hsends_c
        | some ss =>
          rw [hvL] at hvSP; dsimp only at hvSP ⊢
          rcases hvSP with ⟨ts, hts, hsends_ts, hts_eq, hvSP⟩
          have hts_ne : ts ≠ c.1.1 := fun heq => by rw [heq, hsends_c] at hsends_ts; cases hsends_ts
          refine ⟨ts, by omega, hsends_ts, fun hs_max => ?_, ?_⟩
          · by_cases hnew : c.1.1 ≤ (esLoc.g.st P).tcur
            · rw [Nat.max_eq_left hnew] at hs_max ⊢; exact hts_eq hs_max
            · rw [show max (esLoc.g.st P).tcur c.1.1 = c.1.1 by omega] at hs_max
              rw [hsends_c] at hs_max; cases hs_max
          · rw [hact_ne ts hts_ne]; exact hvSP
      · simp only [Function.update_of_ne hQ]
        have hvSQ := hinv.hvS Q
        cases hvL : (esLoc.g.st Q).vS with
        | none => rw [hvL] at hvSQ; dsimp only at hvSQ ⊢; exact hvSQ
        | some ss =>
          rw [hvL] at hvSQ; dsimp only at hvSQ ⊢
          rcases hvSQ with ⟨ts, hts, hsends_ts, hts_eq, hvSQ⟩
          by_cases hts_c : ts = c.1.1
          · subst ts
            refine ⟨c.1.1, hts, hsends_ts, hts_eq, ?_⟩
            cases ha' : actEp' c.1.1 with
            | none => rw [ha'] at hrsv'; rw [hrsv'.1] at hvSQ; exact hvSQ
            | some p =>
              rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨rs0, ha0⟩
              rw [ha0] at hvSQ; exact hvSQ
          · exact ⟨ts, hts, hsends_ts, hts_eq, by rw [hact_ne ts hts_c]; exact hvSQ⟩
    hvR := fun Q t => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM']
        by_cases ht : t = c.1.1
        · subst t; simp only [Function.update_self, hs1_tcur.1]
          refine ⟨hsends_c, Nat.le_max_right _ _, ?_⟩
          cases ha' : actEp' c.1.1 with
          | none => rw [ha'] at hrsv'; exact congrArg some hrsv'.2
          | some p => rw [ha'] at hrsv'; exact ⟨hrsv'.1, congrArg some hrsv'.2.1⟩
        · simp only [Function.update_of_ne ht, hs1_vR_ne t ht, hs1_tcur.1, hact_ne t ht]
          have hvRt := hinv.hvR P t
          cases hvL_t : (esLoc.g.st P).vR t with
          | none => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact hvRt
          | some rs => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact ⟨hvRt.1, hvRt.2.1.trans (Nat.le_max_left _ _), hvRt.2.2⟩
      · simp only [Function.update_of_ne hQ]
        have hvRt := hinv.hvR Q t
        cases hvL_t : (esLoc.g.st Q).vR t with
        | none => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact hvRt
        | some rs =>
          rw [hvL_t] at hvRt; dsimp only at hvRt ⊢
          have hQ_other : Q = P.other := by cases Q <;> cases P <;> simp_all
          have hne : t ≠ c.1.1 := fun heq => by
            rw [heq, hQ_other, _root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hvRt
            exact Bool.noConfusion hvRt.1
          rw [hact_ne t hne]; exact hvRt
    hcache := fun t => by
      rw [hhM_base.1]
      rcases hinv.hcache t with ⟨hcL, hcM⟩ | ⟨ht1, ht_le, Tc, σc, kVal, hcL, hcM_m⟩
      · left; exact ⟨hcL, hcM⟩
      · right; refine ⟨ht1, ht_le.trans (htcur_mono _), Tc, σc, kVal, hcL, ?_⟩
        by_cases ht : t = c.1.1
        · subst t
          have hrecv : Party.receiverOf c.1.1 = P := by
            cases hPo : P.other.sendsIn c.1.1
            · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
            · have := _root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo
              simp [Party.receiverOf, ← this]
          cases ha' : actEp' c.1.1 with
          | none => rw [ha'] at hrsv'; rw [hrsv'.1] at hcM_m; exact hcM_m
          | some p =>
            rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨rs0, ha0⟩
            rw [ha0] at hcM_m
            refine ⟨hcM_m.1, hcM_m.2.1, fun hnone => ?_⟩
            dsimp only [GameState.accept, GameState.delete] at hnone
            rw [hrecv] at hnone; simp [stLoc'] at hnone
        · rw [hact_ne t ht]
          cases ha : actEp t with
          | none => rw [ha] at hcM_m; exact hcM_m
          | some p =>
            rw [ha] at hcM_m
            refine ⟨hcM_m.1, hcM_m.2.1, fun hnone => hcM_m.2.2 ?_⟩
            dsimp only [GameState.accept, GameState.delete] at hnone
            by_cases hR : Party.receiverOf t = P
            · rw [hR] at hnone ⊢
              simp only [Function.update_self, stLoc', Function.update_of_ne ht, (hs1_vR_ne t ht).1] at hnone
              exact hnone
            · simp only [Function.update_of_ne hR] at hnone; exact hnone
    hfuture := fun t ht => by
      have ht0 : (esLoc.g.st (Party.senderOf t)).tcur < t := lt_of_le_of_lt (htcur_mono _) ht
      rcases hinv.hfuture t ht0 with ⟨ha0, hcL, hcM, hfL, hfM, hsM⟩
      exact ⟨(ha_iff t).mpr ha0, hcL, by rw [hhM_base.1, hcM], hfL,
        by rw [hhM_base.2.1, hfM], by rw [hhM_base.2.2.1, hsM]⟩
    hact := fun t0 ss0 rs0 ha' => by
      have ha_ex : ∃ rs_old, actEp t0 = some (ss0, rs_old) := by
        by_cases ht : t0 = c.1.1
        · subst t0; rw [ha'] at hrsv'; exact hrsv'.2.2
        · rw [hact_ne t0 ht] at ha'; exact ⟨rs0, ha'⟩
      rcases ha_ex with ⟨rs_old, ha0⟩
      rcases hinv.hact t0 ss0 rs_old ha0 with ⟨hh1, hh2, hh3, hh4, _, hh6, _⟩
      rcases hact' t0 ss0 rs0 ha' with ⟨ha_inv, _, hcnt, htr⟩
      refine ⟨hh1, hh2, hh3, hh4.trans (htcur_mono (Party.senderOf t0)), ha_inv, fun ht_eq => ?_, htr⟩
      have ht_old : (esLoc.g.st (Party.senderOf t0)).tcur = t0 := by
        have hmono := htcur_mono (Party.senderOf t0)
        dsimp only at ht_eq
        omega
      exact (hh6 ht_old).trans hcnt.symm
    hunalloc := fun sIdx hlt hun => by
      have hun0 : ∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp t0 = none :=
        fun t0 h1 h2 => (ha_iff t0).mp (hun t0 h1 h2)
      rcases hinv.hunalloc sIdx hlt hun0 with ⟨hu1, hu2, hu3, hu4⟩
      rcases hun' sIdx hlt hun with ⟨hb_eq, htm_eq, htl_eq⟩
      exact ⟨hu1, hb_eq.trans hu2, htm_eq.trans hu3, fun hp1 => (htl_eq hp1).trans (hu4 hp1)⟩
    htrans := fun r hr => by
      dsimp only [GameState.accept, GameState.delete] at hr
      rw [List.mem_filter] at hr
      rcases hinv.htrans r hr.1 with ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.trans (htcur_mono _)⟩ }

private theorem deliverE_coupled_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (hD : ∀ k x, C.D k (C.E k x) = x) (hℓ : ℓ < 10 ^ 6)
    {phase1 : Bool} {rem' : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71dc C ℓ encT idOf)
      1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71dc C ℓ encT idOf) 1 qep true tL par la
    ∃ out actEp' esLoc' esM' tblM' tblL',
      (_root_.CryptoGames.SM.Engine.deliverE hkLoc (locFS_r71dc C ℓ encT idOf).maxSkip (bucketAuthCfg 1 tL) (P, c)).run esLoc =
        pure (out, esLoc') ∧
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((_root_.CryptoGames.SM.Engine.deliverE (hkM false) (locFS_r71dc C ℓ encT idOf).maxSkip (bucketAuthCfg 1 tL) (P, c)).run esM)).run
        (fun _ => false, tblM) = pure ((out, esM'), (fun _ => false, tblM')) ∧
      (phase1 = true →
        (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
          ((_root_.CryptoGames.SM.Engine.deliverE (hkM true) (locFS_r71dc C ℓ encT idOf).maxSkip (bucketAuthCfg 1 tL) (P, c)).run esL)).run
          (fun _ => false, tblL) = pure ((out, esM'), (fun _ => false, tblL'))) ∧
      (((esLoc'.abort || esLoc'.g.win) = true ∧ esM'.abort = esLoc'.abort ∧ eraseSt esM'.g = eraseSt esLoc'.g) ∨
        CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp' esLoc' esM'
          (if phase1 then esM' else esL) none tblM' tblL') := by
  intro hkLoc hkM
  have hℓ' : ℓ + 16 < _root_.CryptoGames.LibsignalSession.rustLenBound := by
    unfold _root_.CryptoGames.LibsignalSession.rustLenBound; omega
  have hwinM : esM.g.win = false := by rw [eraseSt_win hinv.herase]; exact hinv.hwin_loc
  have hinT_eq : esM.g.inTransit P.other c = esLoc.g.inTransit P.other c := by
    simp [GameState.inTransit, _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trans hinv.herase]
  have hchall_eq : esM.g.chall = esLoc.g.chall :=
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_chall hinv.herase
  have hinv_rem' : CoupledInv C ℓ q qep encT idOf tL par ks bs phase1 rem' actEp esLoc esM
      (if phase1 then esM else esL) none tblM tblL := {
    habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
    herase := hinv.herase, hep_le := hinv.hep_le, hep_sends := hinv.hep_sends
    hphase1 := fun hp1 => by
      rcases hinv.hphase1 hp1 with ⟨h1, _, h3, h4⟩; exact ⟨h1, by simp [hp1], h3, h4⟩
    hphase2 := hinv.hphase2, hparty_id := hinv.hparty_id, hparty_tcur := hinv.hparty_tcur
    hparty_base := hinv.hparty_base
    htcur_le := fun Q => by have := hinv.htcur_le Q; omega
    hvR_gt := hinv.hvR_gt, hvS := hinv.hvS, hvR := hinv.hvR, hcache := hinv.hcache
    hfuture := hinv.hfuture, hact := hinv.hact, hunalloc := hinv.hunalloc, htrans := hinv.htrans }
  have hesL_eq : phase1 = true → esL = esM := fun hp1 => (hinv.hphase1 hp1).2.1
  have hesLoc_eta : ({ g := esLoc.g, h := esLoc.h } : LocESt Pt ℓ) = esLoc := by
    cases esLoc; simpa using hinv.habort_loc.symm
  have hesM_eta : ({ g := esM.g, h := esM.h } : SideESt Pt ℓ) = esM := by
    cases esM; simpa using hinv.habort_M.symm
  dsimp only [_root_.CryptoGames.SM.Engine.deliverE]
  cases hinT : esLoc.g.inTransit P.other c with
  | none =>
    refine ⟨none, actEp, esLoc, esM, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr hinv_rem'⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, StateT.run_pure, simulateQ_pure]
    · rw [hesL_eq hp1]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, StateT.run_pure, simulateQ_pure]
  | some r =>
    have hr_mem : r ∈ esLoc.g.trans := List.mem_of_find?_eq_some hinT
    have hr_pred := List.find?_some hinT
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
    rcases hr_pred with ⟨hr_sender, hr_ct⟩
    rcases hinv.htrans r hr_mem with ⟨hr_ep, _, _⟩
    have hr_pos : r.pos = ⟨P.other, c.1.1, r.pos.idx⟩ := by
      have hep' : r.pos.epoch = c.1.1 := hr_ep.trans (by rw [hr_ct])
      rcases r with ⟨⟨rs0, re0, ri0⟩, rmsg0, rct0⟩
      dsimp only at hr_sender hep' ⊢
      subst hr_sender; subst hep'; rfl
    by_cases hbad : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) = true
    · have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢
        exact hbad
      refine ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr hinv_rem'⟩
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
          _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
          hbad, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, hesLoc_eta]
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
          _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
          hbadM, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
      · rw [hesL_eq hp1]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
          _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
          hbadM, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
    · simp only [Bool.not_eq_true] at hbad
      have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢
        exact hbad
      have hbad0 := hbad
      rw [(hinv.hparty_id P).1, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hbad0
      rcases hbad0 with ⟨hsends_c, hle_succ⟩
      rcases vRecvStep1_coupled_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs hinv P c hbad with
        ⟨hs1L, hs1M⟩ | ⟨hs1L, hs1M⟩ |
        ⟨s1Loc, s1M, hs1L, hs1M, hid, htcur, hnew, hbase, hvS, hvR_gt, hvR_ne, hvRc⟩
      · change (_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        refine ⟨none, actEp, { esLoc with abort := true }, { esM with abort := true }, tblM, tblL,
          ?_, ?_, fun hp1 => ?_, Or.inl ⟨rfl, rfl, hinv.herase⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbad, hs1L, StateT.run_pure, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbadM, hs1M false, StateT.run_pure, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify, simulateQ_pure]
        · rw [hesL_eq hp1]
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbadM, hs1M true, StateT.run_pure, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify, simulateQ_pure]
      · change (_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        refine ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr hinv_rem'⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbad, hs1L, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, hesLoc_eta]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbadM, hs1M false, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
        · rw [hesL_eq hp1]
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
            _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
            hbadM, hs1M true, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
      · change (_root_.CryptoGames.SM.Engine.vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (_root_.CryptoGames.SM.Engine.vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        cases hvL_c : s1Loc.vR c.1.1 with
        | none =>
          rw [hvL_c] at hvRc
          refine ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr hinv_rem'⟩
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
              Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
              _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
              hbad, hs1L, hvL_c, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, hesLoc_eta]
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
              Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
              _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
              hbadM, hs1M false, hvRc, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
          · rw [hesL_eq hp1]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
              Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
              _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
              hbadM, hs1M true, hvRc, StateT.run_pure, bucketAuthCfg_deliverWin_r71dc, Bool.false_and, simulateQ_pure, hesM_eta]
        | some rsLoc =>
          rw [hvL_c] at hvRc
          cases ha : actEp c.1.1 with
          | none =>
            rw [ha] at hvRc
            cases hrec : (locFS_r71dc C ℓ encT idOf).receive rsLoc c.1 c.2 with
            | none =>
              refine ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr hinv_rem'⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec, StateT.run_pure, pure_bind, bucketAuthCfg_deliverWin_r71dc, Bool.false_and,
                  Bool.false_eq_true, ↓reduceIte, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [hrec, Option.map_none, StateT.run_pure, pure_bind, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, hesM_eta]
              · rw [hesL_eq hp1]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [hrec, Option.map_none, StateT.run_pure, pure_bind, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, hesM_eta]
            | some rim =>
              rcases rim with ⟨rsLoc', idxOut, pmOut⟩
              let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
              let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inl rsLoc')) }
              let out := some (RecvResult.accepted c.1.1 idxOut
                (if esLoc.g.chall.contains r.pos then none else some pmOut))
              refine ⟨out, actEp, { esLoc with g := esLoc.g.accept P stLoc' r.pos },
                { esM with g := esM.g.accept P stM' r.pos }, tblM, tblL, ?_, ?_, fun hp1 => ?_, Or.inr ?_⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot, _root_.CryptoGames.SM.Engine.commitE]
                simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                  run_liftH_r71dc, bind_assoc, accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, stLoc', out]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth, _root_.CryptoGames.SM.Engine.commitE]
                simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  pure_bind, run_liftH_r71dc, bind_assoc, accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, hchall_eq, stM', out, simulateQ_pure]
              · rw [hesL_eq hp1]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth, _root_.CryptoGames.SM.Engine.commitE]
                simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  pure_bind, run_liftH_r71dc, bind_assoc, accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, hchall_eq, stM', out, simulateQ_pure]
              · rw [hr_pos]
                exact commit_accept_coupled_r71dc C encT idOf ℓ q qep tL par ks bs hinv P c r.pos.idx
                  hsends_c hle_succ s1Loc s1M rsLoc' (.inl rsLoc') hid htcur hnew hbase hvS hvR_gt hvR_ne
                  (by rw [ha]; exact ⟨rfl, rfl⟩) (fun _ _ => rfl) ⟨rfl, rfl, rfl, rfl⟩
                  (fun t0 ss0 rs0 ha0 => by
                    rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha_inv, _, htr⟩
                    have hne_ep : r.pos.epoch ≠ t0 := by
                      intro heq; rw [hr_pos] at heq; dsimp only at heq; subst heq; rw [ha] at ha0; cases ha0
                    have hfilt : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, r.pos.idx⟩)).filter
                        (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                      rw [List.filter_comm]; apply List.filter_eq_self.mpr
                      intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                      simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'
                      rw [hr_pos] at hne_ep; exact hne_ep hr'.2
                    refine ⟨ha_inv, fun hp1 => (hinv.hphase1 hp1).2.2.2 t0 (by simp [ha0]), rfl, ?_⟩
                    dsimp only [GameState.accept, GameState.delete]
                    rw [hfilt]; exact htr)
                  (fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩)
          | some pair =>
            rcases pair with ⟨ssA, rsA⟩
            rw [ha] at hvRc
            rcases hvRc with ⟨rfl, hvRc⟩
            let sIdx := sIdxMain q tL c.1.1
            let bk := (esM.h.book sIdx).getD {}
            rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨hh1, _, _, _, ha_inv, _, htr_bk⟩
            have hP_other : P.other = Party.senderOf c.1.1 := by
              cases hPo : P.other.sendsIn c.1.1
              · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
              · exact _root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo
            have hmatch : bk.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = some (r.pos.idx, r.ct.1, r.ct.2) := by
              dsimp only [bk]; rw [htr_bk, find_filter_map_trans_r71dc esLoc.g.trans P (c.1, c.2) hP_other
                (fun r' hr' => ⟨(hinv.htrans r' hr').1, (hinv.htrans r' hr').2.1⟩)]
              change (esLoc.g.inTransit P.other c).map _ = _; rw [hinT]; rfl
            rcases Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt.activeSessInv_deliver
              C hD _root_.CryptoVerification.LibsignalSession.signalRoundTripShort_proto ℓ hℓ' encT idOf
              ha_inv c.1 c.2 hmatch with ⟨p, hpub, hdeliv⟩
            have hmatch_unf : ((esM.h.book (sIdxMain q tL c.1.1)).getD {}).fsTrans.find?
                (fun x => x.2 == (c.1, c.2)) = some (r.pos.idx, r.ct.1, r.ct.2) := hmatch
            cases hrec : (locFS_r71dc C ℓ encT idOf).receive rsLoc c.1 c.2 with
            | none =>
              rw [hrec] at hdeliv
              rcases hdeliv with ⟨sM', sL', hdM, hdL, ha_inv'⟩
              let tblM' := Function.update tblM sIdx sM'
              let tblL' := Function.update tblL sIdx sL'
              refine ⟨some .rejected, actEp, esLoc, esM, tblM', tblL', ?_, ?_, fun hp1 => ?_, Or.inr ?_⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec, StateT.run_pure, pure_bind, bucketAuthCfg_deliverWin_r71dc, Bool.false_and,
                  Bool.false_eq_true, ↓reduceIte, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind, sIdx, bk,
                  beq_hdr_ct_inst_eq_r71dc, hmatch_unf,
                  Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
                  Bool.not_true, simulateQ_bind, bind_assoc]
                rw [liftFS_deliver_some_run_r71dc C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblM hdM]
                simp only [pure_bind, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, StateT.run_pure, simulateQ_pure,
                  bucketAuthCfg_deliverWin_r71dc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, tblM', sIdx, hesM_eta]
              · rw [hesL_eq hp1]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind, sIdx, bk,
                  beq_hdr_ct_inst_eq_r71dc, hmatch_unf,
                  Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
                  Bool.not_true, simulateQ_bind, bind_assoc]
                rw [liftFS_deliver_some_run_r71dc C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblL (hdL hp1)]
                simp only [pure_bind, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, StateT.run_pure, simulateQ_pure,
                  bucketAuthCfg_deliverWin_r71dc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, tblL', sIdx, hesM_eta]
              · refine { hinv_rem' with
                  hact := fun t0 ss0 rs0 ha0 => by
                    by_cases ht : t0 = c.1.1
                    · subst t0; rw [ha] at ha0; cases ha0
                      rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨h1, h2, h3, h4, _, h6, h7⟩
                      refine ⟨h1, h2, h3, h4, ?_, h6, h7⟩
                      simpa [tblM', tblL', sIdx, bk] using ha_inv'
                    · have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                        ht (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sIdxMain_inj
                          q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                      simpa [tblM', tblL', hne] using hinv.hact t0 ss0 rs0 ha0
                  hunalloc := fun sIdx' hlt hun => by
                    have hne : sIdx' ≠ sIdx := fun heq => by
                      subst heq; have := hun c.1.1 hh1 rfl; rw [ha] at this; cases this
                    rcases hinv.hunalloc sIdx' hlt hun with ⟨hu1, hu2, hu3, hu4⟩
                    exact ⟨hu1, hu2, by simp [tblM', hne, hu3], fun hp1 => by simp [tblL', hne, hu4 hp1]⟩ }
            | some rim =>
              rcases rim with ⟨rsLoc', idxOut, pmOut⟩
              rw [hrec] at hdeliv
              rcases hdeliv with ⟨hidx_eq, sM', sL', hdM, hdL, hpm1, ha_inv'⟩
              change r.pos.idx = idxOut at hidx_eq
              have hpm_eq : (p, pmOut.2) = pmOut := by cases pmOut; dsimp only at hpm1; subst hpm1; rfl
              let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                { bk with fsTrans := bk.fsTrans.filter (·.1 != r.pos.idx) }
              let hM' : MultiHSt_r71dc Pt := { esM.h with book := Function.update esM.h.book sIdx (some bk') }
              let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
              let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inr sIdx)) }
              let actEp' := Function.update actEp c.1.1 (some (ssA, rsLoc'))
              let tblM' := Function.update tblM sIdx sM'
              let tblL' := Function.update tblL sIdx sL'
              let out := some (RecvResult.accepted c.1.1 idxOut
                (if esLoc.g.chall.contains r.pos then none else some pmOut))
              refine ⟨out, actEp', { esLoc with g := esLoc.g.accept P stLoc' r.pos },
                { esM with g := esM.g.accept P stM' r.pos, h := hM' }, tblM', tblL',
                ?_, ?_, fun hp1 => ?_, Or.inr ?_⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.or_self, Bool.false_eq_true, ↓reduceIte, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot, _root_.CryptoGames.SM.Engine.commitE]
                simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                  run_liftH_r71dc, bind_assoc, accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, stLoc', out]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth, _root_.CryptoGames.SM.Engine.commitE]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind, sIdx, bk,
                  beq_hdr_ct_inst_eq_r71dc, hmatch_unf,
                  Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
                  Bool.not_true, simulateQ_bind, bind_assoc]
                rw [liftFS_deliver_some_run_r71dc C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblM hdM]
                simp only [pure_bind, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, hpm_eq, hidx_eq,
                  StateT.run_bind, StateT.run_get,
                  StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71dc, bind_assoc,
                  Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.getD_some,
                  accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc, hchall_eq, hM', bk', stM', tblM', out, sIdx, bk]
              · rw [hesL_eq hp1]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hinT_eq, hinT, run_liftH_r71dc, bind_assoc,
                  _root_.CryptoGames.SM.Engine.vRecv_eq_bind,
                  hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth, _root_.CryptoGames.SM.Engine.commitE]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind, sIdx, bk,
                  beq_hdr_ct_inst_eq_r71dc, hmatch_unf,
                  Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
                  Bool.not_true, simulateQ_bind, bind_assoc]
                rw [liftFS_deliver_some_run_r71dc C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblL (hdL hp1)]
                simp only [pure_bind, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, hpm_eq, hidx_eq,
                  StateT.run_bind, StateT.run_get,
                  StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71dc, bind_assoc,
                  Option.isNone_some, Bool.true_and, Bool.false_and, Bool.false_eq_true,
                  ↓reduceIte, Option.getD_some, accept_update_idem_r71dc, bucketAuthCfg_deliverWin_r71dc,
                  hchall_eq, hM', bk', stM', tblL', out, sIdx, bk]
              · rw [hr_pos]
                exact commit_accept_coupled_r71dc C encT idOf ℓ q qep tL par ks bs hinv P c r.pos.idx
                  hsends_c hle_succ s1Loc s1M rsLoc' (.inr sIdx) hid htcur hnew hbase hvS hvR_gt hvR_ne
                  (by simp [actEp', sIdx, ha]) (fun t ht => by simp [actEp', ht])
                  ⟨rfl, rfl, rfl, rfl⟩
                  (fun t0 ss0 rs0 ha0 => by
                    by_cases ht : t0 = c.1.1
                    · subst t0; simp only [actEp', Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha0
                      rcases ha0 with ⟨rfl, rfl⟩
                      have hfilt_eq : (((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, r.pos.idx⟩)).filter
                          (fun r' => r'.pos.epoch == c.1.1)).map (fun r' => (r'.pos.idx, r'.ct.1, r'.ct.2))) =
                          bk.fsTrans.filter (·.1 != r.pos.idx) := by
                        rw [htr_bk, List.filter_map, List.filter_comm]
                        congr 1; apply List.filter_congr
                        intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                        rcases hinv.htrans r' hr'.1 with ⟨_, hsend', _⟩
                        rw [hr'.2, ← hP_other] at hsend'
                        rcases r' with ⟨⟨rs', re', ri'⟩, rm', rct'⟩
                        rcases hr' with ⟨_, rfl⟩
                        dsimp only [Function.comp_def] at hsend' ⊢
                        subst hsend'; rw [Bool.eq_iff_iff]; simp [bne_iff_ne]
                      refine ⟨?_, fun hp1 => by simp [hM', bk', sIdx, bk, (hinv.hphase1 hp1).2.2.2 c.1.1 (by simp [ha])],
                        by simp [hM', bk', sIdx, bk], by simpa [hM', bk', sIdx, GameState.accept, GameState.delete] using hfilt_eq.symm⟩
                      simpa [hM', bk', tblM', tblL', sIdx, bk] using ha_inv'
                    · simp only [actEp', Function.update_of_ne ht] at ha0
                      have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                        ht (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sIdxMain_inj
                          q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                      rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha0_inv, _, htr0⟩
                      have hfilt0 : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, r.pos.idx⟩)).filter
                          (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                        rw [List.filter_comm]; apply List.filter_eq_self.mpr
                        intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                        simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'; exact ht hr'.2.symm
                      refine ⟨?_, fun hp1 => by simp [hM', hne, (hinv.hphase1 hp1).2.2.2 t0 (by simp [ha0])],
                        by simp [hM', hne], ?_⟩
                      · simpa [hM', tblM', tblL', hne] using ha0_inv
                      · simp only [hM', Function.update_of_ne hne, GameState.accept, GameState.delete, hfilt0, htr0])
                  (fun sIdx' hlt hun => by
                    have hne : sIdx' ≠ sIdx := fun heq => by
                      subst heq; have := hun c.1.1 hh1 rfl; simp [actEp'] at this
                    exact ⟨by simp [hM', hne], by simp [tblM', hne], fun _ => by simp [tblL', hne]⟩)

private theorem step_deliver_leOne_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (hD : ∀ k x, C.D k (C.E k x) = x) (hℓ : ℓ < 10 ^ 6)
    {rem' : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs false (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih : ∀ u actEp' esLoc' esM' tblM',
      CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    LeOne
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM winEp tblM) := by
  obtain rfl := hinv.hwe
  rcases deliverE_coupled_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs hD hℓ hinv P c with
    ⟨out, actEp', esLoc', esM', tblM', _, hdelLoc, hdelM, _, hpost⟩
  have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esLoc none =
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' none := by
    unfold runLocCont; rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hdelLoc,
      StateT.run_set, StateT.run_pure, simulateQ_pure]
  have hMStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM none tblM =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k out) esM' none tblM' := by
    unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
    rw [hdelM]
    simp only [pure_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
  rw [hLocStep, hMStep]
  rcases hpost with ⟨hhalt, hab, her⟩ | hinv'
  · exact halted_exit_leOne_r71dc
      C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' esM' none tblM' hhalt hab her
  · exact ih out actEp' esLoc' esM' tblM' (coupledInv_false_swap_r71dc hinv')

private theorem step_deliver_leAdd_r71dc {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (hD : ∀ k x, C.D k (C.E k x) = x) (hℓ : ℓ < 10 ^ 6)
    {rem' : ℕ} {actEp : ActMap_r71dc}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih : ∀ u actEp' esLoc' esM' esL' tblM' tblL',
      CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) :
    LeAdd
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM winEp tblM)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esL winEp tblL) := by
  obtain rfl := hinv.hwe
  rcases deliverE_coupled_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs hD hℓ hinv P c with
    ⟨out, actEp', esLoc', esM', tblM', tblL', hdelLoc, hdelM, hdelL, hpost⟩
  have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esLoc none =
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' none := by
    unfold runLocCont; rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hdelLoc,
      StateT.run_set, StateT.run_pure, simulateQ_pure]
  have hMStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esM none tblM =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k out) esM' none tblM' := by
    unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
    rw [hdelM]
    simp only [pure_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
  have hLStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par true
      (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr (P, c)))))) >>= k) esL none tblL =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k out) esM' none tblL' := by
    unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
    rw [hdelL rfl]
    simp only [pure_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
  rw [hLocStep, hMStep, hLStep]
  rcases hpost with ⟨hhalt, hab, her⟩ | hinv'
  · exact leAdd_of_le_main
      (halted_exit_leOne_r71dc
        C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' esM' none tblM' hhalt hab her)
  · exact ih out actEp' esLoc' esM' esM' tblM' tblL' hinv'

/-- Sub-lemma 2 (`step_deliver_and_corrupt_coupled`): Coupled `deliverE` (`.inr (.inl (.inl (.inr x)))`)
and `corrE` (`.inr (.inr P)`, when `corrAllowed P = true`) steps for `phase1 = false` (`LeOne`)
and `phase1 = true` (`LeAdd`). The `corrE` half is proved in `BucketFSAuthBridgeHopSimInv.lean`. -/
private theorem step_deliver_and_corrupt_coupled {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem' : ℕ} :
    ((∀ (x : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
        (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
        {actEp esLoc esM winEp tblM},
      CoupledInv C ℓ q qep encT idOf tL par ks bs false (rem' + 1) actEp esLoc esM esM winEp tblM tblM →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      LeOne
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr x))))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr x))))) >>= k)
          esM winEp tblM)) ∧
     (∀ (x : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
        (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
        {actEp esLoc esM esL winEp tblM tblL},
      CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      (∀ u actEp' esLoc' esM' esL' tblM' tblL',
        CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
        LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) →
      LeAdd
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr x))))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr x))))) >>= k)
          esM winEp tblM)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inr x))))) >>= k)
          esL winEp tblL))) ∧
    ((∀ (P : Party) (k : Option (Fig8St Pt) → OracleComp (Fig8Dom Pt ℓ) Bool)
        {actEp esLoc esM winEp tblM},
      CoupledInv C ℓ q qep encT idOf tL par ks bs false (rem' + 1) actEp esLoc esM esM winEp tblM tblM →
      esLoc.g.corrAllowed P = true →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      LeOne
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k)
          esM winEp tblM)) ∧
     (∀ (P : Party) (k : Option (Fig8St Pt) → OracleComp (Fig8Dom Pt ℓ) Bool)
        {actEp esLoc esM esL winEp tblM tblL},
      CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL →
      esLoc.g.corrAllowed P = true →
      (∀ u actEp' esLoc' esM' tblM',
        CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
        LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) →
      (∀ u actEp' esLoc' esM' esL' tblM' tblL',
        CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
        LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
          (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) →
      LeAdd
        (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k)
          esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k)
          esM winEp tblM)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k)
          esL winEp tblL))) := by
  have _ := hDh; have _ := hinj; have _ := hdum
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro ⟨P, c⟩ k actEp esLoc esM winEp tblM hinv ih
    exact step_deliver_leOne_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs hD hℓ P c k hinv ih
  · intro ⟨P, c⟩ k actEp esLoc esM esL winEp tblM tblL hinv _ ih
    exact step_deliver_leAdd_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs hD hℓ P c k hinv ih
  · intro P k actEp esLoc esM winEp tblM hinv hcorr ih
    rcases hinv.hphase2 rfl with ⟨cur, htL, hlt, _⟩
    have hpl : postLeak tL esLoc.g = true := by simp [postLeak, htL, hlt]
    have hpl_after : postLeak tL (esLoc.g.afterCorr P) = true :=
      postLeak_afterCorr_r71dc
        tL esLoc.g P hpl
    exact step_corrupt_postLeak_leOne_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs P k hinv
      hcorr hpl_after (fun u esLoc' esM' tblM' hinv' => ih u actEp esLoc' esM' tblM' hinv')
  · intro P k actEp esLoc esM esL winEp tblM tblL hinv hcorr hphase2 ih
    by_cases hpl_after : postLeak tL (esLoc.g.afterCorr P) = true
    · exact leAdd_of_le_main
        (step_corrupt_postLeak_leOne_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs P k hinv
          hcorr hpl_after (fun u esLoc' esM' tblM' hinv' => hphase2 u actEp esLoc' esM' tblM' hinv'))
    · simp only [Bool.not_eq_true] at hpl_after
      exact step_corrupt_phase1_noLeak_r71dc C Dh encPt encT idOf ℓ q qep tL par ks bs P k hinv
        hcorr hpl_after (fun u esLoc' esM' esL' hinv' => ih u actEp esLoc' esM' esL' tblM tblL hinv')

/-! ### Inject Helpers for `step_inject_phase2_leOne` and `step_inject_phase1_leAdd` -/

private theorem CoupledInv_set_esL_tblL_false_r71inj {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ q qep : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {tL : Option ℕ} {par : Bool} {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {rem : ℕ}
    {actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    {esLoc : LocESt Pt ℓ} {esM esL esL' : SideESt Pt ℓ} {winEp : Option ℕ}
    {tblM tblL tblL' : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs false rem actEp esLoc esM esL winEp tblM tblL) :
    CoupledInv C ℓ q qep encT idOf tL par ks bs false rem actEp esLoc esM esL' winEp tblM tblL' :=
  { hinv with
    hphase1 := fun h => Bool.noConfusion h
    hact := fun t0 ssLoc rsLoc ha =>
      let ⟨h1, h2, h3, h4, ⟨stR, ha_inv⟩, h6, h7⟩ := hinv.hact t0 ssLoc rsLoc ha
      ⟨h1, h2, h3, h4, ⟨stR, { ha_inv with syncRML := fun h => Bool.noConfusion h }⟩, h6, h7⟩
    hunalloc := fun sIdx hlt hun =>
      let ⟨u1, u2, u3, _⟩ := hinv.hunalloc sIdx hlt hun
      ⟨u1, u2, u3, fun h => Bool.noConfusion h⟩ }

private theorem ltOpt_mono_r71inj (tL : Option ℕ) {a b : ℕ} (h : ltOpt tL a = true) (hab : a ≤ b) :
    ltOpt tL b = true := by
  cases tL with
  | none => exact h
  | some x => simp only [ltOpt, decide_eq_true_eq] at h ⊢; omega

private theorem postLeak_epMgmt_r71inj {St Msg C : Type} (tL : Option ℕ) (s s₁ : GameState St Msg C)
    (Δ qep : ℕ) (P : Party) (bad : Bool) (hpost : postLeak tL s = true)
    (h : s.epMgmt Δ qep P bad = some s₁) : postLeak tL s₁ = true := by
  unfold GameState.epMgmt GameState.leak at h
  split at h <;> split at h <;> cases h
  · split
    · cases hs : s.tL with
      | none => simp [postLeak, hs] at hpost
      | some cur => simp only [postLeak, hs] at hpost; exact ltOpt_mono_r71inj tL hpost (Nat.le_max_left _ _)
    · exact hpost
  · exact hpost

private theorem postLeak_afterCorr_r71inj {St Msg C : Type} (tL : Option ℕ) (s : GameState St Msg C)
    (P : Party) (hpost : postLeak tL s = true) : postLeak tL (s.afterCorr P) = true := by
  unfold GameState.afterCorr
  cases hs : s.tL with
  | none => simp [postLeak, hs] at hpost
  | some cur => simp only [postLeak, hs] at hpost; exact ltOpt_mono_r71inj tL hpost (Nat.le_max_left _ _)

private theorem slot_eq_loc_of_postLeak_or_halted_r71inj {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) (ks : ℕ → K)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (g0 : Ctx Γ T Sig SS RS M E) (st0 : LocalMainSlotState T Sig K I) (abort0 : Bool) (we0 : Option ℕ)
    (hPost : (abort0 || g0.win) = true ∨ postLeak tL g0 = true) :
    simulateQ (keySlotFixedImpl ks) (do
      let (_, es, we) ← (simulateQ (implLocalMainSlot
        (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par) Δcka qep fs.maxSkip tL) oa).run
        ({ g := g0, h := st0, abort := abort0 }, we0)
      return mainParOut (2 + Δcka) tL par es we) =
    simulateQ lImpl (do
      let (_, es, we) ← (simulateQ (implLocalBucketAuthGen
        (hooksLocalBucketAuthMain cka prng fs Δcka qep tL) Δcka qep fs.maxSkip tL false) oa).run
        ({ g := g0, h := st0.loc, abort := abort0 }, we0)
      return mainParOut (2 + Δcka) tL par es we) := by
  let hkLoc := hooksLocalBucketAuthMain cka prng fs Δcka qep tL
  let hkSlot := hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par
  induction oa using OracleComp.inductionOn generalizing g0 st0 abort0 we0 with
  | pure _ => simp [simulateQ_pure, StateT.run_pure, mainParOut]
  | query_bind qy k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc, simulateQ_bind, simulateQ_bind]
    rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inl n)).run
          ({ g := g0, h := st0, abort := abort0 }, we0) =
          (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl n)) >>=
            fun u => pure (u, ({ g := g0, h := st0, abort := abort0 }, we0))) := by
        simp [implLocalMainSlot, QueryImpl.add_apply_inl]
      have hL : (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inl n)).run
          ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
          (liftM (OracleSpec.query (spec := unifSpec + nilSpec) (.inl n)) >>=
            fun u => pure (u, ({ g := g0, h := st0.loc, abort := abort0 }, we0))) := by
        simp [implLocalBucketAuthGen, QueryImpl.add_apply_inl]
      rw [hS, hL, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        keySlotFixedImpl, lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        simulateQ_pure, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        cases hep : g0.epMgmt (2 + Δcka) qep P r.isSome with
        | none =>
          have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) := by
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp [StateT.run_bind, StateT.run_get, pure_bind, hep]
          have hL : (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) := by
            dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp [StateT.run_bind, StateT.run_get, pure_bind, hep]
          rw [hS, hL]; simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
        | some s₁ =>
          have hpl1 : postLeak tL s₁ = true := postLeak_epMgmt_r71inj tL g0 s₁ (2 + Δcka) qep P r.isSome hpl0 hep
          have hS : (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              ((vSend hkSlot s₁ P (s₁.st P) m none r).run st0 >>= fun (res, h') =>
                match res with
                | none => pure (none, ({ g := g0, h := h', abort := true }, we0))
                | some (st', ct) =>
                  let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
                  pure (some ct, ({ g := s₁.record (2 + Δcka) P st' recE false, h := h', abort := abort0 }, we0))) := by
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hh, Bool.false_eq_true, ↓reduceIte, hep,
              StateT.run_lift, bind_assoc]
            refine bind_congr fun ⟨res, h'⟩ => ?_
            rcases res with _ | ⟨st', ct⟩ <;> simp [StateT.run_set]
          have hL : (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false
              (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              ((vSend hkLoc s₁ P (s₁.st P) m none r).run st0.loc >>= fun (res, h') =>
                match res with
                | none => pure (none, ({ g := g0, h := h', abort := true }, we0))
                | some (st', ct) =>
                  let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
                  pure (some ct, ({ g := s₁.record (2 + Δcka) P st' recE false, h := h', abort := abort0 }, we0))) := by
            dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hh, Bool.false_eq_true, ↓reduceIte, hep,
              StateT.run_lift, bind_assoc]
            refine bind_congr fun ⟨res, h'⟩ => ?_
            rcases res with _ | ⟨st', ct⟩ <;> simp [StateT.run_set]
          rw [hS, hL, simulateQ_bind, simulateQ_bind]
          have hvSend : simulateQ (keySlotFixedImpl ks) ((vSend hkSlot s₁ P (s₁.st P) m none r).run st0) =
              (fun z : Option _ × LocalBucketAuthState T Sig K I => (z.1, { st0 with loc := z.2 })) <$>
                simulateQ lImpl ((vSend hkLoc s₁ P (s₁.st P) m none r).run st0.loc) := by
            rw [vSend_eq_bind, vSend_eq_bind]
            simp only [StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
            have hstep1 : simulateQ (keySlotFixedImpl ks) ((vSendStep1 hkSlot s₁ P (s₁.st P) r).run st0) =
                (fun z : Option _ × LocalBucketAuthState T Sig K I => (z.1, { st0 with loc := z.2 })) <$>
                  simulateQ lImpl ((vSendStep1 hkLoc s₁ P (s₁.st P) r).run st0.loc) := by
              unfold vSendStep1
              cases (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1)
              · simp
              · simp only [↓reduceIte, hkSlot, hkLoc, hooksLocalMainSlot, hooksLocalBucketAuthMain,
                  hooksLocalBucketAuth, rootLocalMainSlot, rootLocalBucketAuth, hpl1, Bool.true_or]
                cases r with
                | none =>
                  simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
                    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
                    sim_sampleT_fixed, sim_sampleT_lImpl, map_eq_bind_pure_comp, Function.comp_def]
                | some c =>
                  simp [StateT.run_modify, pure_bind]
            rw [hstep1, map_eq_bind_pure_comp]
            simp only [Function.comp_def, bind_assoc, pure_bind]
            refine bind_congr fun z => ?_
            rcases z with ⟨s1?, loc1⟩
            rcases s1? with _ | s1
            · simp
            · cases hvS : s1.vS
              · simp [hvS]
              · simp [hvS, hkSlot, hkLoc, hooksLocalMainSlot, hooksLocalBucketAuthMain, hooksLocalBucketAuth]
          rw [hvSend, bind_map_left, bind_assoc, bind_assoc]
          refine bind_congr fun z => ?_
          rcases z with ⟨res, loc'⟩
          rcases res with _ | ⟨st', ct⟩
          · dsimp only
            rw [simulateQ_pure, simulateQ_pure, pure_bind, pure_bind]
            exact ih none g0 { st0 with loc := loc' } true we0 (Or.inl rfl)
          · dsimp only
            rw [simulateQ_pure, simulateQ_pure, pure_bind, pure_bind]
            let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            have hpl2 : postLeak tL (s₁.record (2 + Δcka) P st' recE false) = true := by
              simpa [postLeak, GameState.record] using hpl1
            exact ih (some ct) (s₁.record (2 + Δcka) P st' recE false) { st0 with loc := loc' } abort0 we0
              (Or.inr hpl2)
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hh'],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
            ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
            simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl],
          show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
            ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
            simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]]
      simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        rcases deliverE_localMain_pure cka prng fs Δcka q qep M_sess tL par (P, c)
          { g := g0, h := st0, abort := abort0 } with ⟨out, g', abort', htL, hdL, hdR⟩
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0, abort := abort' }, we0)) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hdR]; simp,
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0.loc, abort := abort' }, we0)) by
              dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hdL]; simp]
        simp only [pure_bind, simulateQ_pure]
        exact ih out g' st0 abort' we0 (Or.inr (by unfold postLeak at hpl0 ⊢; rw [htL]; exact hpl0))
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hh'],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inl (.inr (P, c)))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hh : (abort0 || g0.win)
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [hh])
        rcases injectE_localMain_pure cka prng fs Δcka q qep M_sess tL par (P, c)
          { g := g0, h := st0, abort := abort0 } with ⟨out, g', abort', htL, hiL, hiR⟩
        let we' := if !g0.win && g'.win then some c.1.1 else we0
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0, abort := abort' }, we')) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hiR]; simp [we'],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (out, ({ g := g', h := st0.loc, abort := abort' }, we')) by
              dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
              rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift, hiL]; simp [we']]
        simp only [pure_bind, simulateQ_pure]
        exact ih out g' st0 abort' we' (Or.inr (by unfold postLeak at hpl0 ⊢; rw [htL]; exact hpl0))
      · have hh' : abort0 = true ∨ g0.win = true := by simpa [Bool.or_eq_true] using hh
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hh'],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inl (.inr (P, c))))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hh']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost
    · cases hskip : (abort0 || g0.win || !(g0.corrAllowed P))
      · have hpl0 : postLeak tL g0 = true := hPost.resolve_left (by simp [Bool.or_eq_true] at hskip ⊢; tauto)
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inr P))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) =
              pure (some (realParty (g0.st P) (g0.st P).γ (g0.st P).root (g0.st P).vS (g0.st P).vR),
                ({ g := g0.afterCorr P, h := st0, abort := abort0 }, we0)) by
              dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, hkSlot, hooksLocalMainSlot]
              rw [StateT.run_bind, StateT.run_get, pure_bind]; simp [hskip],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inr P))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) =
              pure (some (realParty (g0.st P) (g0.st P).γ (g0.st P).root (g0.st P).vS (g0.st P).vR),
                ({ g := g0.afterCorr P, h := st0.loc, abort := abort0 }, we0)) by
              dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, hkLoc, hooksLocalBucketAuthMain, hooksLocalBucketAuth]
              rw [StateT.run_bind, StateT.run_get, pure_bind]; simp [hskip]]
        simp only [pure_bind, simulateQ_pure]
        exact ih _ (g0.afterCorr P) st0 abort0 we0 (Or.inr (postLeak_afterCorr_r71inj tL g0 P hpl0))
      · have hskip' : (abort0 = true ∨ g0.win = true) ∨ g0.corrAllowed P = false := by
          simpa [Bool.or_eq_true] using hskip
        rw [show (implLocalMainSlot hkSlot Δcka qep fs.maxSkip tL (.inr (.inr P))).run
              ({ g := g0, h := st0, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0, abort := abort0 }, we0)) by
              simp [implLocalMainSlot, QueryImpl.add_apply_inr, hskip'],
            show (implLocalBucketAuthGen hkLoc Δcka qep fs.maxSkip tL false (.inr (.inr P))).run
              ({ g := g0, h := st0.loc, abort := abort0 }, we0) = pure (none, ({ g := g0, h := st0.loc, abort := abort0 }, we0)) by
              simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, hskip']]
        simp only [pure_bind, simulateQ_pure]; exact ih none g0 st0 abort0 we0 hPost

private abbrev SmSpec_r71inj (Pt : Type) (ℓ : ℕ) :=
  unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

private abbrev SmAdv_r71inj (Pt : Type) (ℓ : ℕ) := OracleComp (SmSpec_r71inj Pt ℓ) Bool

private abbrev MultiHSt_r71inj (Pt : Type) :=
  FSMultiBucketAuthState Pt CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.ChainKey Pt
    (ℕ × LibsignalCiphertextWithSalt32)


private abbrev MultiESt_r71inj (Pt : Type) (ℓ : ℕ) :=
  EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
    (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) (MultiHSt_r71inj Pt)

private abbrev ActMap_r71inj :=
  ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))

private abbrev locFS_r71inj {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :=
  lFS C protoSignalCodec ℓ encT idOf maxForwardJumps

section InjectR71

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
  (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)

private abbrev CoupledInv_r71inj {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (ℓ q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) :=
  CoupledInv (Pt := Pt) C ℓ q qep encT idOf tL par ks bs

private theorem halted_exit_leOne_r71inj
    (oa : SmAdv_r71inj Pt ℓ) (esLoc : LocESt Pt ℓ) (esM : MultiESt_r71inj Pt ℓ)
    (winEp : Option ℕ) (tblM : ℕ → SessHSt Pt ℓ)
    (hhalt : (esLoc.abort || esLoc.g.win) = true) (habort : esM.abort = esLoc.abort)
    (herase : _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esM.g =
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esLoc.g) :
    LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks oa esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false oa esM winEp tblM) := by
  unfold runLocCont runSideCont
  have heq := slot_eq_loc_of_postLeak_or_halted_r71inj (dhScheme Dh) (rootPRNG C.F encPt)
    (locFS_r71inj C ℓ encT idOf) 1 q qep (mSessMain q qep tL) tL par ks
    oa esLoc.g esLoc.h esLoc.abort winEp (Or.inl hhalt)
  change LeOne _ _
  rw [show ({ g := esLoc.g, h := esLoc.h, abort := esLoc.abort } : LocESt Pt ℓ) = esLoc from rfl] at heq
  rw [heq]; simp only [Bool.false_eq_true, ↓reduceIte]
  exact halted_leOne
    (hooksLocalBucketAuthMain (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71inj C ℓ encT idOf) 1 qep tL)
    (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71inj C ℓ encT idOf) 1 qep true tL par false)
    1 qep (locFS_r71inj C ℓ encT idOf).maxSkip tL par
    (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
    (fun n s => pubFsMultiImpl_inl_run _ n s)
    oa { g := esLoc.g, h := esLoc.h.loc, abort := esLoc.abort } esM winEp (fun _ => false, tblM)
    hhalt habort
    (_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_win herase)
    (_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leaks herase)
    (_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_corrs herase)

private theorem run_liftH_r71inj {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (_root_.CryptoGames.SM.Engine.liftH x).run es =
      (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem liftFSMultiBucket_inr_run_r71inj (la : Bool) (sIdx : ℕ)
    (q0 : (_root_.CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Domain)
    (h : MultiHSt_r71inj Pt) (tbl : ℕ → SessHSt Pt ℓ) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (.inr q0))).run h)).run (fun _ => false, tbl) =
    (do
      let p ← (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))
        (.inr ⟨sIdx, q0⟩)).run (fun _ => false, tbl)
      pure ((p.1, h), p.2)) := by
  unfold BucketFSAuthShallowBase.liftFSMultiBucket
  rw [stateT_lift_run]
  simp only [query_eq_liftM, id_map, map_eq_bind_pure_comp, Function.comp_def, bind_pure,
    simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind,
    StateT.run_pure]
  erw [id_map, simulateQ_query, id_map]
  rfl

private theorem liftFS_corruptSender_run_r71inj (sIdx : ℕ) (h : MultiHSt_r71inj Pt) (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (RatchetSenderState (BitVec 256))} {s' : SessHSt Pt ℓ}
    (hstep : ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
      ((BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (_root_.CryptoGames.FSAEAD.corruptSenderQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
          (Ciphertext := ℕ × LibsignalCiphertextWithSalt32))).run h)).run (fun _ => false, tbl) =
    pure ((u, h), (fun _ => false, Function.update tbl sIdx s')) := by
  unfold _root_.CryptoGames.FSAEAD.corruptSenderQuery
  rw [liftFSMultiBucket_inr_run_r71inj C encT idOf ℓ false sIdx _ h tbl]
  erw [pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tbl hstep, pure_bind]

private theorem liftFS_inject_none_run_r71inj (la : Bool) (sIdx : ℕ) (hdr : Header Pt)
    (ctPair : ℕ × LibsignalCiphertextWithSalt32) (hp_none : lPubOf protoSignalCodec ctPair.2 = none)
    (h : MultiHSt_r71inj Pt) (tbl : ℕ → SessHSt Pt ℓ) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (_root_.CryptoGames.FSAEAD.injectQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) hdr ctPair)).run h)).run (fun _ => false, tbl) =
    pure ((some .rejected, h), (fun _ => false, tbl)) := by
  rcases ctPair with ⟨i, ct⟩
  unfold _root_.CryptoGames.FSAEAD.injectQuery
  rw [liftFSMultiBucket_inr_run_r71inj C encT idOf ℓ la sIdx _ h tbl]
  erw [pubFsMultiImpl_inject_none_run C ℓ encT idOf la sIdx hdr i ct hp_none tbl, pure_bind]

private theorem liftFS_inject_some_run_r71inj (la : Bool) (sIdx : ℕ) (hdr : Header Pt)
    (ctPair : ℕ × LibsignalCiphertextWithSalt32) (p : LibsignalMsgPublicPart)
    (hp_pub : lPubOf protoSignalCodec ctPair.2 = some p) (h : MultiHSt_r71inj Pt) (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (_root_.CryptoGames.FSAEAD.Thm5.injectH (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la) (_root_.CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp))
        ((hdr, p), (ctPair.1, ctPair.2))).run (tbl sIdx) = pure (u, s')) :
    (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((BucketFSAuthShallowBase.liftFSMultiBucket sIdx
        (_root_.CryptoGames.FSAEAD.injectQuery
          (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) hdr ctPair)).run h)).run (fun _ => false, tbl) =
    pure ((u.map (withPub p), h), (fun _ => false, Function.update tbl sIdx s')) := by
  rcases ctPair with ⟨i, ct⟩
  unfold _root_.CryptoGames.FSAEAD.injectQuery
  rw [liftFSMultiBucket_inr_run_r71inj C encT idOf ℓ la sIdx _ h tbl]
  erw [pubFsMultiImpl_inject_some_run C ℓ encT idOf la sIdx hdr i ct p hp_pub tbl hstep, pure_bind]

private theorem ct_beq_iff_local_r71inj :
    ∀ (c1 c2 : ℕ × LibsignalCiphertextWithSalt32), (c1 == c2) = true ↔ c1 = c2
  | ⟨n1, s1, b1⟩, ⟨n2, s2, b2⟩ => by
    change (n1 == n2 && (s1 == s2 && b1 == b2)) = true ↔ _
    simp [Bool.and_eq_true, beq_iff_eq]

private theorem hdr_beq_iff_local_r71inj :
    ∀ (h1 h2 : Header Pt), (h1 == h2) = true ↔ h1 = h2
  | ⟨t1, o1⟩, ⟨t2, o2⟩ => by
    cases o1 <;> cases o2 <;>
      (change (t1 == t2 && _) = true ↔ _; dsimp only [BEq.beq, Option.instBEq, Option.instBEq.beq];
       simp [Bool.and_eq_true])

private theorem beq_hdr_ct_inst_eq_r71inj
    (p q : Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :
    @BEq.beq (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (@instBEqProd (Header Pt) (ℕ × LibsignalCiphertextWithSalt32) inferInstance instBEqOfDecidableEq)
      p q = (p == q) := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  have hb : @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq p2 q2 = (p2 == q2) := by
    rw [Bool.eq_iff_iff, ct_beq_iff_local_r71inj]; simp [BEq.beq]
  show (p1 == q1 && @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq p2 q2) =
    (p1 == q1 && p2 == q2)
  rw [hb]

private theorem find_filter_map_trans_r71inj {M : Type}
    (L : List (Record M (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (hP : P.other = Party.senderOf c.1.1)
    (htr : ∀ r ∈ L, r.pos.epoch = r.ct.1.1 ∧ r.pos.sender = Party.senderOf r.pos.epoch) :
    ((L.filter (fun r => r.pos.epoch == c.1.1)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2))).find?
      (fun x => x.2 == c) =
    (L.find? (fun r => r.pos.sender == P.other && decide (r.ct = c))).map
      (fun r => (r.pos.idx, r.ct.1, r.ct.2)) := by
  induction L with
  | nil => rfl
  | cons r rs ih =>
    rcases htr r List.mem_cons_self with ⟨hep, hsend⟩
    have ih' := ih (fun r' hr' => htr r' (List.mem_cons_of_mem _ hr'))
    by_cases hct : r.ct = c
    · subst hct
      have h1 : (r.pos.epoch == r.ct.1.1) = true := by simp [hep]
      have h2 : (r.pos.sender == P.other) = true := by simp [hsend, hP, hep]
      have h3 : ((r.ct.1, r.ct.2) == r.ct) = true := by
        change (r.ct.1 == r.ct.1 && r.ct.2 == r.ct.2) = true
        simp [hdr_beq_iff_local_r71inj, ct_beq_iff_local_r71inj]
      simp [h1, h2, h3]
    · by_cases he : (r.pos.epoch == c.1.1) = true
      · have hne2 : ((r.ct.1, r.ct.2) == c) = false := by
          change (r.ct.1 == c.1 && r.ct.2 == c.2) = false
          cases hbeq : (r.ct.1 == c.1 && r.ct.2 == c.2) with
          | false => rfl
          | true =>
            simp only [Bool.and_eq_true, hdr_beq_iff_local_r71inj, ct_beq_iff_local_r71inj] at hbeq
            exact False.elim (hct (Prod.ext hbeq.1 hbeq.2))
        simp [he, hct, hne2, ih']
      · simp only [Bool.not_eq_true] at he
        simp [he, hct, ih']

private theorem accept_update_idem_r71inj {St Msg C : Type} (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    { s.accept P st' pos with st := Function.update (s.accept P st' pos).st P st' } = s.accept P st' pos := by
  have : Function.update (Function.update s.st P st') P st' = Function.update s.st P st' := by
    funext Q; by_cases hQ : Q = P <;> simp [hQ]
  cases s; simp [GameState.accept, GameState.delete, this]

private theorem vRecvStep1_coupled_r71inj {phase1 : Bool} {rem : ℕ} {actEp : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs phase1 rem actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt)
    (hbad : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) = false) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71inj C ℓ encT idOf)
      1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71inj C ℓ encT idOf) 1 qep true tL par la
    ((vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (none, esLoc.h) ∧
      ∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (none, esM.h)) ∨
    ((vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (some none, esLoc.h) ∧
      ∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (some none, esM.h)) ∨
    ∃ s1Loc s1M,
      (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = pure (some (some s1Loc), esLoc.h) ∧
      (∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = pure (some (some s1M), esM.h)) ∧
      (s1Loc.id = P ∧ s1M.id = P) ∧
      (s1Loc.tcur = max (esLoc.g.st P).tcur c.1.1 ∧ s1M.tcur = s1Loc.tcur) ∧
      (c.1.1 = (esLoc.g.st P).tcur + 1 → c.1.1 ≤ (esLoc.g.st P.other).tcur) ∧
      (s1M.γ = s1Loc.γ ∧ s1M.curCkaMsg = s1Loc.curCkaMsg ∧ s1M.root = s1Loc.root) ∧
      (s1Loc.vS = (esLoc.g.st P).vS ∧ s1M.vS = (esM.g.st P).vS) ∧
      (∀ t, s1Loc.tcur < t → s1Loc.vR t = none ∧ s1M.vR t = none) ∧
      (∀ t, t ≠ c.1.1 → s1Loc.vR t = (esLoc.g.st P).vR t ∧ s1M.vR t = (esM.g.st P).vR t) ∧
      (match s1Loc.vR c.1.1 with
        | none => s1M.vR c.1.1 = none
        | some rs => match actEp c.1.1 with
          | none => s1M.vR c.1.1 = some (.inl rs)
          | some (_, rsA) => rs = rsA ∧ s1M.vR c.1.1 = some (.inr (sIdxMain q tL c.1.1))) := by
  intro hkLoc hkM
  rcases hinv.hparty_id P with ⟨hidL, hidM⟩
  have htcurM : (esM.g.st P).tcur = (esLoc.g.st P).tcur := (hinv.hparty_tcur P).2
  rcases hinv.hparty_base P with ⟨hγM, hcurM, hrootM⟩
  rw [hidL, Bool.or_eq_false_iff] at hbad
  rcases hbad with ⟨hsends_c, hle_succ⟩
  simp only [decide_eq_false_iff_not, not_lt] at hle_succ
  have hP_other : Party.senderOf c.1.1 = P.other := by
    cases hPo : P.other.sendsIn c.1.1
    · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
    · exact (_root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo).symm
  have hP_recv : Party.receiverOf c.1.1 = P := by
    simp [Party.receiverOf, hP_other]
  unfold vRecvStep1
  rw [htcurM]
  by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
  · simp only [hnew, ↓reduceIte]
    cases hc2 : c.1.2 with
    | none => right; left; exact ⟨rfl, fun _ => rfl⟩
    | some Tn =>
      dsimp only [hkLoc, hkM, hooksLocalMainSlot, hooksFSMultiBucketAuth]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      have hbeq : (((esLoc.g.st P).tcur + 1 == healEpoch tL)) =
          decide ((esLoc.g.st P).tcur + 1 = healEpoch tL) := Bool.eq_iff_iff.mpr (by simp)
      rcases hinv.hcache ((esLoc.g.st P).tcur + 1) with ⟨hcL, hcM⟩ | ⟨_, hle_send, Tc, σc, kVal, hcL, hcM_match⟩
      · rw [hcL, hcM]; dsimp only
        by_cases hcond : (!(decide (qep + 1 < (esLoc.g.st P).tcur + 1)) &&
            lastLeakGuessAdmissible (2 + 1) tL ((esLoc.g.st P).tcur + 1) &&
            (tL.isSome && decide ((esLoc.g.st P).tcur + 1 = healEpoch tL))) = true
        · left; exact ⟨by simp only [hcond, ↓reduceIte, StateT.run_pure, pure_bind],
            fun _ => by simp only [hbeq, hcond, ↓reduceIte, StateT.run_pure, pure_bind]⟩
        · simp only [Bool.not_eq_true] at hcond
          right; left; exact ⟨by simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind],
            fun _ => by simp only [hbeq, hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]⟩
      · rw [hcL]
        by_cases htc : Tc = Tn
        · subst Tn
          right; right
          have hmax : max (esLoc.g.st P).tcur ((esLoc.g.st P).tcur + 1) = (esLoc.g.st P).tcur + 1 := by omega
          have hle_other : (esLoc.g.st P).tcur + 1 ≤ (esLoc.g.st P.other).tcur := by
            rw [← hnew, hP_other] at hle_send; rw [← hnew]; exact hle_send
          have hvR_none : (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1) = none :=
            (hinv.hvR_gt P ((esLoc.g.st P).tcur + 1) (by omega)).1
          cases ha : actEp ((esLoc.g.st P).tcur + 1) with
          | none =>
            rw [ha] at hcM_match
            let s1Loc := { (esLoc.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esLoc.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some ((locFS_r71inj C ℓ encT idOf).initReceiver kVal)) }
            let s1M := { (esM.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esM.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esM.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some (.inl ((locFS_r71inj C ℓ encT idOf).initReceiver kVal))) }
            refine ⟨s1Loc, s1M, by simp only [↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              fun _ => by simp only [hcM_match, ↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              ⟨hidL, hidM⟩, ⟨hmax.symm, rfl⟩, fun _ => hle_other,
              ⟨by simp [s1Loc, s1M, hγM], hcurM, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
            · intro t ht; have ht' : (esLoc.g.st P).tcur < t := by dsimp [s1Loc] at ht; omega
              have hne : t ≠ (esLoc.g.st P).tcur + 1 := by dsimp [s1Loc] at ht; omega
              simp [s1Loc, s1M, hne, hinv.hvR_gt P t ht']
            · intro t hne; simp [s1Loc, s1M, hne]
            · simp [s1Loc, s1M, ha]
          | some pair =>
            rcases pair with ⟨ssA, rsA⟩
            rw [ha] at hcM_match
            rcases hcM_match with ⟨hk_eq, ⟨kDummy, hcM⟩, hrs_init⟩
            have hrsA : rsA = (locFS_r71inj C ℓ encT idOf).initReceiver kVal :=
              hrs_init (by rw [← hnew, hP_recv, hnew]; exact hvR_none)
            let s1Loc := { (esLoc.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esLoc.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esLoc.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some ((locFS_r71inj C ℓ encT idOf).initReceiver kVal)) }
            let s1M := { (esM.g.st P) with
              tcur := (esLoc.g.st P).tcur + 1, γ := ((dhScheme Dh).receive (esM.g.st P).γ Tc).1,
              root := σc,
              vR := Function.update (esM.g.st P).vR ((esLoc.g.st P).tcur + 1)
                (some (.inr (sIdxMain q tL ((esLoc.g.st P).tcur + 1)))) }
            refine ⟨s1Loc, s1M, by simp only [↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              fun _ => by simp only [hcM, ↓reduceIte, StateT.run_pure, pure_bind]; rfl,
              ⟨hidL, hidM⟩, ⟨hmax.symm, rfl⟩, fun _ => hle_other,
              ⟨by simp [s1Loc, s1M, hγM], hcurM, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
            · intro t ht; have ht' : (esLoc.g.st P).tcur < t := by dsimp [s1Loc] at ht; omega
              have hne : t ≠ (esLoc.g.st P).tcur + 1 := by dsimp [s1Loc] at ht; omega
              simp [s1Loc, s1M, hne, hinv.hvR_gt P t ht']
            · intro t hne; simp [s1Loc, s1M, hne]
            · simp [s1Loc, s1M, ha, hrsA.symm]
        · by_cases hcond : (!(decide (qep + 1 < (esLoc.g.st P).tcur + 1)) &&
              lastLeakGuessAdmissible (2 + 1) tL ((esLoc.g.st P).tcur + 1) &&
              (tL.isSome && decide ((esLoc.g.st P).tcur + 1 = healEpoch tL))) = true
          · left; refine ⟨by simp only [htc, ↓reduceIte, hcond, StateT.run_pure, pure_bind], fun _ => ?_⟩
            cases ha : actEp ((esLoc.g.st P).tcur + 1) with
            | none => rw [ha] at hcM_match; simp only [hcM_match, htc, ↓reduceIte, hbeq, hcond, StateT.run_pure, pure_bind]
            | some p => rw [ha] at hcM_match; rcases hcM_match.2.1 with ⟨kDummy, hcM⟩; simp only [hcM, htc, ↓reduceIte, hbeq, hcond, StateT.run_pure, pure_bind]
          · simp only [Bool.not_eq_true] at hcond
            right; left; refine ⟨by simp only [htc, ↓reduceIte, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind], fun _ => ?_⟩
            cases ha : actEp ((esLoc.g.st P).tcur + 1) with
            | none => rw [ha] at hcM_match; simp only [hcM_match, htc, ↓reduceIte, hbeq, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind]
            | some p => rw [ha] at hcM_match; rcases hcM_match.2.1 with ⟨kDummy, hcM⟩; simp only [hcM, htc, ↓reduceIte, hbeq, hcond, Bool.false_eq_true, StateT.run_pure, pure_bind]
  · simp only [hnew, ↓reduceIte]
    have hle_cur : c.1.1 ≤ (esLoc.g.st P).tcur := by omega
    have hmax : max (esLoc.g.st P).tcur c.1.1 = (esLoc.g.st P).tcur := Nat.max_eq_left hle_cur
    right; right
    refine ⟨esLoc.g.st P, esM.g.st P, rfl, fun _ => rfl, ⟨hidL, hidM⟩, ⟨hmax.symm, htcurM⟩,
      False.elim, ⟨hγM, hcurM, hrootM⟩, ⟨rfl, rfl⟩,
      fun t ht => hinv.hvR_gt P t ht, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    have hvRc := hinv.hvR P c.1.1
    cases hvL_c : (esLoc.g.st P).vR c.1.1 with
    | none => rw [hvL_c] at hvRc; exact hvRc
    | some rs => rw [hvL_c] at hvRc; exact hvRc.2.2

private theorem commit_accept_coupled_r71inj {phase1 : Bool} {rem' : ℕ} {actEp actEp' : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ}
    {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ} {hM' : MultiHSt_r71inj Pt}
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs phase1 (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt) (idxOut : ℕ)
    (hsends_c : P.sendsIn c.1.1 = false) (hle_succ : c.1.1 ≤ (esLoc.g.st P).tcur + 1)
    (s1Loc : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (s1M : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (rsLoc' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (rsv' : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hs1_id : s1Loc.id = P ∧ s1M.id = P)
    (hs1_tcur : s1Loc.tcur = max (esLoc.g.st P).tcur c.1.1 ∧ s1M.tcur = s1Loc.tcur)
    (hs1_new : c.1.1 = (esLoc.g.st P).tcur + 1 → c.1.1 ≤ (esLoc.g.st P.other).tcur)
    (hs1_base : s1M.γ = s1Loc.γ ∧ s1M.curCkaMsg = s1Loc.curCkaMsg ∧ s1M.root = s1Loc.root)
    (hs1_vS : s1Loc.vS = (esLoc.g.st P).vS ∧ s1M.vS = (esM.g.st P).vS)
    (hs1_vR_gt : ∀ t, s1Loc.tcur < t → s1Loc.vR t = none ∧ s1M.vR t = none)
    (hs1_vR_ne : ∀ t, t ≠ c.1.1 → s1Loc.vR t = (esLoc.g.st P).vR t ∧ s1M.vR t = (esM.g.st P).vR t)
    (hrsv' : match actEp' c.1.1 with
      | none => actEp c.1.1 = none ∧ rsv' = .inl rsLoc'
      | some (ssA, rsA) => rsLoc' = rsA ∧ rsv' = .inr (sIdxMain q tL c.1.1) ∧
          ∃ rs0, actEp c.1.1 = some (ssA, rs0))
    (hact_ne : ∀ t, t ≠ c.1.1 → actEp' t = actEp t)
    (hhM_base : hM'.cache = esM.h.cache ∧ hM'.fTable = esM.h.fTable ∧ hM'.sessions = esM.h.sessions ∧
      hM'.lfWin = esM.h.lfWin)
    (hact' : ∀ t0 ss0 rs0, actEp' t0 = some (ss0, rs0) →
      let sIdx := sIdxMain q tL t0
      let bk' := (hM'.book sIdx).getD {}
      ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) ss0 rs0 bk' (tblM' sIdx) (tblL' sIdx) ∧
      (phase1 = true → bk'.sCorr = false) ∧
      bk'.fsCount = ((esM.h.book sIdx).getD {}).fsCount ∧
      bk'.fsTrans = (((esLoc.g.accept P { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
        ⟨P.other, c.1.1, idxOut⟩).trans.filter (fun r => r.pos.epoch == t0)).map
        (fun r => (r.pos.idx, r.ct.1, r.ct.2))))
    (hun' : ∀ sIdx, sIdx < mSessMain q qep tL →
      (∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp' t0 = none) →
      hM'.book sIdx = esM.h.book sIdx ∧ tblM' sIdx = tblM sIdx ∧ (phase1 = true → tblL' sIdx = tblL sIdx)) :
    let pos : Pos := ⟨P.other, c.1.1, idxOut⟩
    let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
    let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some rsv') }
    CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs phase1 rem' actEp'
      { esLoc with g := esLoc.g.accept P stLoc' pos }
      { esM with g := esM.g.accept P stM' pos, h := hM' }
      (if phase1 then { esM with g := esM.g.accept P stM' pos, h := hM' } else esL)
      none tblM' tblL' := by
  intro pos stLoc' stM'
  have hep_P : esLoc.g.epoch P = (esLoc.g.st P).tcur := ((hinv.hparty_tcur P).1).symm
  have hep_Po : esLoc.g.epoch P.other = (esLoc.g.st P.other).tcur := ((hinv.hparty_tcur P.other).1).symm
  have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ ((esLoc.g.accept P stLoc' pos).st Q).tcur := by
    intro Q; dsimp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst Q; simp [stLoc', hs1_tcur.1]
    · simp [hQ]
  have ha_iff : ∀ t0, (actEp' t0 = none) ↔ (actEp t0 = none) := by
    intro t0
    by_cases ht : t0 = c.1.1
    · subst t0
      cases ha' : actEp' c.1.1 with
      | none => rw [ha'] at hrsv'; simp [hrsv'.1]
      | some p => rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨_, ha0⟩; simp [ha0]
    · rw [hact_ne t0 ht]
  refine {
    habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
    herase := by
      have h := hinv.herase
      rcases esM with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      rcases esLoc with ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt] at h
      injection h; subst_vars; rfl
    hep_le := fun Q => by
      dsimp only [GameState.accept, GameState.delete, pos]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, Function.update_of_ne (Party.other_ne P)]
        by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
        · have := hs1_new hnew; have := hinv.hep_le P; omega
        · have h1 : c.1.1 ≤ esLoc.g.epoch P := by omega
          rw [Nat.max_eq_left h1]; exact hinv.hep_le P
      · have hQo : Q.other = P := by cases Q <;> cases P <;> simp_all
        simp only [Function.update_of_ne hQ, hQo, Function.update_self]
        have hleQ := hinv.hep_le Q; rw [hQo] at hleQ; omega
    hep_sends := fun Q hlt => by
      dsimp only [GameState.accept, GameState.delete, pos] at hlt ⊢
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, Function.update_of_ne (Party.other_ne P)] at hlt ⊢
        by_cases hnew : c.1.1 = (esLoc.g.st P).tcur + 1
        · have := hs1_new hnew; omega
        · have h1 : c.1.1 ≤ esLoc.g.epoch P := by omega
          rw [Nat.max_eq_left h1] at hlt ⊢; exact hinv.hep_sends P hlt
      · have hQo : Q.other = P := by cases Q <;> cases P <;> simp_all
        simp only [Function.update_of_ne hQ, hQo, Function.update_self] at hlt ⊢
        exact hinv.hep_sends Q (by rw [hQo]; omega)
    hphase1 := fun hp1 => by
      rcases hinv.hphase1 hp1 with ⟨hpl0, _, hlf0, _⟩
      refine ⟨hpl0, by simp [hp1], by rw [hhM_base.2.2.2, hlf0], fun t0 ha => ?_⟩
      cases ha' : actEp' t0 with
      | none => exact absurd ha' ha
      | some p => exact (hact' t0 p.1 p.2 ha').2.1 hp1
    hphase2 := fun hp2 => by
      rcases hinv.hphase2 hp2 with ⟨cur, htL_cur, hlt_cur, hle_cur⟩
      exact ⟨cur, htL_cur, hlt_cur, fun t0 ha => hle_cur t0 (fun hn => ha ((ha_iff t0).mpr hn))⟩
    hparty_id := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_id.1, hs1_id.2]
      · simp [hQ, hinv.hparty_id Q]
    hparty_tcur := fun Q => by
      dsimp only [GameState.accept, GameState.delete, pos]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_tcur.1, hs1_tcur.2, hep_P]
      · simp [hQ, hinv.hparty_tcur Q]
    hparty_base := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp [stLoc', stM', hs1_base.1, hs1_base.2.1, hs1_base.2.2]
      · simp [hQ, hinv.hparty_base Q]
    htcur_le := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', hs1_tcur.1]
        have := hinv.htcur_le P; omega
      · simp only [Function.update_of_ne hQ]; have := hinv.htcur_le Q; omega
    hvR_gt := fun Q t ht => by
      dsimp only [GameState.accept, GameState.delete] at ht ⊢
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM'] at ht ⊢
        have hne : t ≠ c.1.1 := by rw [hs1_tcur.1] at ht; omega
        simp [hne, hs1_vR_gt t ht]
      · simp only [Function.update_of_ne hQ] at ht ⊢; exact hinv.hvR_gt Q t ht
    hvS := fun Q => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM', hs1_vS.1, hs1_vS.2, hs1_tcur.1]
        have hvSP := hinv.hvS P
        cases hvL : (esLoc.g.st P).vS with
        | none =>
          rw [hvL] at hvSP; dsimp only at hvSP ⊢
          refine ⟨hvSP.1, ?_⟩
          by_cases hnew : c.1.1 ≤ (esLoc.g.st P).tcur
          · rw [Nat.max_eq_left hnew]; exact hvSP.2
          · rw [show max (esLoc.g.st P).tcur c.1.1 = c.1.1 by omega]; exact hsends_c
        | some ss =>
          rw [hvL] at hvSP; dsimp only at hvSP ⊢
          rcases hvSP with ⟨ts, hts, hsends_ts, hts_eq, hvSP⟩
          have hts_ne : ts ≠ c.1.1 := fun heq => by rw [heq, hsends_c] at hsends_ts; cases hsends_ts
          refine ⟨ts, by omega, hsends_ts, fun hs_max => ?_, ?_⟩
          · by_cases hnew : c.1.1 ≤ (esLoc.g.st P).tcur
            · rw [Nat.max_eq_left hnew] at hs_max ⊢; exact hts_eq hs_max
            · rw [show max (esLoc.g.st P).tcur c.1.1 = c.1.1 by omega] at hs_max
              rw [hsends_c] at hs_max; cases hs_max
          · rw [hact_ne ts hts_ne]; exact hvSP
      · simp only [Function.update_of_ne hQ]
        have hvSQ := hinv.hvS Q
        cases hvL : (esLoc.g.st Q).vS with
        | none => rw [hvL] at hvSQ; dsimp only at hvSQ ⊢; exact hvSQ
        | some ss =>
          rw [hvL] at hvSQ; dsimp only at hvSQ ⊢
          rcases hvSQ with ⟨ts, hts, hsends_ts, hts_eq, hvSQ⟩
          by_cases hts_c : ts = c.1.1
          · subst ts
            refine ⟨c.1.1, hts, hsends_ts, hts_eq, ?_⟩
            cases ha' : actEp' c.1.1 with
            | none => rw [ha'] at hrsv'; rw [hrsv'.1] at hvSQ; exact hvSQ
            | some p =>
              rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨rs0, ha0⟩
              rw [ha0] at hvSQ; exact hvSQ
          · exact ⟨ts, hts, hsends_ts, hts_eq, by rw [hact_ne ts hts_c]; exact hvSQ⟩
    hvR := fun Q t => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hQ : Q = P
      · subst Q; simp only [Function.update_self, stLoc', stM']
        by_cases ht : t = c.1.1
        · subst t; simp only [Function.update_self, hs1_tcur.1]
          refine ⟨hsends_c, Nat.le_max_right _ _, ?_⟩
          cases ha' : actEp' c.1.1 with
          | none => rw [ha'] at hrsv'; exact congrArg some hrsv'.2
          | some p => rw [ha'] at hrsv'; exact ⟨hrsv'.1, congrArg some hrsv'.2.1⟩
        · simp only [Function.update_of_ne ht, hs1_vR_ne t ht, hs1_tcur.1, hact_ne t ht]
          have hvRt := hinv.hvR P t
          cases hvL_t : (esLoc.g.st P).vR t with
          | none => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact hvRt
          | some rs => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact ⟨hvRt.1, hvRt.2.1.trans (Nat.le_max_left _ _), hvRt.2.2⟩
      · simp only [Function.update_of_ne hQ]
        have hvRt := hinv.hvR Q t
        cases hvL_t : (esLoc.g.st Q).vR t with
        | none => rw [hvL_t] at hvRt; dsimp only at hvRt ⊢; exact hvRt
        | some rs =>
          rw [hvL_t] at hvRt; dsimp only at hvRt ⊢
          have hQ_other : Q = P.other := by cases Q <;> cases P <;> simp_all
          have hne : t ≠ c.1.1 := fun heq => by
            rw [heq, hQ_other, _root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hvRt
            exact Bool.noConfusion hvRt.1
          rw [hact_ne t hne]; exact hvRt
    hcache := fun t => by
      rw [hhM_base.1]
      rcases hinv.hcache t with ⟨hcL, hcM⟩ | ⟨ht1, ht_le, Tc, σc, kVal, hcL, hcM_m⟩
      · left; exact ⟨hcL, hcM⟩
      · right; refine ⟨ht1, ht_le.trans (htcur_mono _), Tc, σc, kVal, hcL, ?_⟩
        by_cases ht : t = c.1.1
        · subst t
          have hrecv : Party.receiverOf c.1.1 = P := by
            cases hPo : P.other.sendsIn c.1.1
            · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
            · have := _root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo
              simp [Party.receiverOf, ← this]
          cases ha' : actEp' c.1.1 with
          | none => rw [ha'] at hrsv'; rw [hrsv'.1] at hcM_m; exact hcM_m
          | some p =>
            rw [ha'] at hrsv'; rcases hrsv'.2.2 with ⟨rs0, ha0⟩
            rw [ha0] at hcM_m
            refine ⟨hcM_m.1, hcM_m.2.1, fun hnone => ?_⟩
            dsimp only [GameState.accept, GameState.delete] at hnone
            rw [hrecv] at hnone; simp [stLoc'] at hnone
        · rw [hact_ne t ht]
          cases ha : actEp t with
          | none => rw [ha] at hcM_m; exact hcM_m
          | some p =>
            rw [ha] at hcM_m
            refine ⟨hcM_m.1, hcM_m.2.1, fun hnone => hcM_m.2.2 ?_⟩
            dsimp only [GameState.accept, GameState.delete] at hnone
            by_cases hR : Party.receiverOf t = P
            · rw [hR] at hnone ⊢
              simp only [Function.update_self, stLoc', Function.update_of_ne ht, (hs1_vR_ne t ht).1] at hnone
              exact hnone
            · simp only [Function.update_of_ne hR] at hnone; exact hnone
    hfuture := fun t ht => by
      have ht0 : (esLoc.g.st (Party.senderOf t)).tcur < t := lt_of_le_of_lt (htcur_mono _) ht
      rcases hinv.hfuture t ht0 with ⟨ha0, hcL, hcM, hfL, hfM, hsM⟩
      exact ⟨(ha_iff t).mpr ha0, hcL, by rw [hhM_base.1, hcM], hfL,
        by rw [hhM_base.2.1, hfM], by rw [hhM_base.2.2.1, hsM]⟩
    hact := fun t0 ss0 rs0 ha' => by
      have ha_ex : ∃ rs_old, actEp t0 = some (ss0, rs_old) := by
        by_cases ht : t0 = c.1.1
        · subst t0; rw [ha'] at hrsv'; exact hrsv'.2.2
        · rw [hact_ne t0 ht] at ha'; exact ⟨rs0, ha'⟩
      rcases ha_ex with ⟨rs_old, ha0⟩
      rcases hinv.hact t0 ss0 rs_old ha0 with ⟨hh1, hh2, hh3, hh4, _, hh6, _⟩
      rcases hact' t0 ss0 rs0 ha' with ⟨ha_inv, _, hcnt, htr⟩
      refine ⟨hh1, hh2, hh3, hh4.trans (htcur_mono (Party.senderOf t0)), ha_inv, fun ht_eq => ?_, htr⟩
      have ht_old : (esLoc.g.st (Party.senderOf t0)).tcur = t0 := by
        have hmono := htcur_mono (Party.senderOf t0)
        dsimp only at ht_eq
        omega
      exact (hh6 ht_old).trans hcnt.symm
    hunalloc := fun sIdx hlt hun => by
      have hun0 : ∀ t0, healEpoch tL ≤ t0 → sIdxMain q tL t0 = sIdx → actEp t0 = none :=
        fun t0 h1 h2 => (ha_iff t0).mp (hun t0 h1 h2)
      rcases hinv.hunalloc sIdx hlt hun0 with ⟨hu1, hu2, hu3, hu4⟩
      rcases hun' sIdx hlt hun with ⟨hb_eq, htm_eq, htl_eq⟩
      exact ⟨hu1, hb_eq.trans hu2, htm_eq.trans hu3, fun hp1 => (htl_eq hp1).trans (hu4 hp1)⟩
    htrans := fun r hr => by
      dsimp only [GameState.accept, GameState.delete] at hr
      rw [List.mem_filter] at hr
      rcases hinv.htrans r hr.1 with ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.trans (htcur_mono _)⟩ }

private theorem bucketAuthCfg_injectFull_r71inj {M : Type} (tL : Option ℕ) (t' : ℕ) :
    (bucketAuthCfg (M := M) 1 tL).injectFull t' = lastLeakGuessAdmissible 3 tL t' := rfl

private theorem eraseSt_win_true_r71inj {St₁ St₂ Msg C : Type} {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (her : _root_.CryptoGames.SM.Construction.AuthL11.eraseSt g₁ =
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt g₂) :
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt { g₁ with win := true } =
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt { g₂ with win := true } := by
  cases g₁; cases g₂
  dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt] at her ⊢
  injection her with _ h2 h3 h4 h5 h6 h7 h8 h9 _ h11 h12
  congr 1

private theorem injectE_phase2_coupled_r71inj
    {rem' : ℕ} {actEp : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs false (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71inj C ℓ encT idOf)
      1 q qep (mSessMain q qep tL) tL par
    let hkM := hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71inj C ℓ encT idOf) 1 qep true tL par false
    ∃ out actEp' esLoc' esM' tblM',
      (injectE hkLoc 3 qep (bucketAuthCfg 1 tL) (P, c)).run esLoc = pure (out, esLoc') ∧
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((injectE hkM 3 qep (bucketAuthCfg 1 tL) (P, c)).run esM)).run
        (fun _ => false, tblM) = pure ((out, esM'), (fun _ => false, tblM')) ∧
      esM'.g.win = esLoc'.g.win ∧
      (((esLoc'.abort || esLoc'.g.win) = true ∧ esM'.abort = esLoc'.abort ∧
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esM'.g =
            _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esLoc'.g) ∨
        (esLoc'.g.win = false ∧
          CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs false rem' actEp' esLoc' esM' esL none tblM' tblL)) := by
  intro hkLoc hkM
  have hwinM : esM.g.win = false := by
    rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_win hinv.herase]; exact hinv.hwin_loc
  have hinT_eq : esM.g.inTransit P.other c = esLoc.g.inTransit P.other c := by
    simp [GameState.inTransit, _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trans hinv.herase]
  have hsafe_eq : esM.g.safeInj 3 = esLoc.g.safeInj 3 :=
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hinv.herase 3
  have htL_eq : esM.g.tL = esLoc.g.tL :=
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_tL hinv.herase
  have hesLoc_eta : ({ g := esLoc.g, h := esLoc.h } : LocESt Pt ℓ) = esLoc := by
    cases esLoc; simpa using hinv.habort_loc.symm
  have hesM_eta : ({ g := esM.g, h := esM.h } : MultiESt_r71inj Pt ℓ) = esM := by
    cases esM; simpa using hinv.habort_M.symm
  have hinv_rem' : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs false rem' actEp esLoc esM esL none tblM tblL := {
    habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
    herase := hinv.herase, hep_le := hinv.hep_le, hep_sends := hinv.hep_sends
    hphase1 := fun h => Bool.noConfusion h, hphase2 := hinv.hphase2
    hparty_id := hinv.hparty_id, hparty_tcur := hinv.hparty_tcur, hparty_base := hinv.hparty_base
    htcur_le := fun Q => by have := hinv.htcur_le Q; omega
    hvR_gt := hinv.hvR_gt, hvS := hinv.hvS, hvR := hinv.hvR, hcache := hinv.hcache
    hfuture := hinv.hfuture, hact := hinv.hact, hunalloc := hinv.hunalloc, htrans := hinv.htrans }
  dsimp only [injectE]
  by_cases hguard : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj 3)) = true
  · have hguardM : ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj 3)) = true := by
      rw [hinT_eq, hsafe_eq]; exact hguard
    refine ⟨none, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
        Bool.false_or, Bool.or_assoc, hguard, ↓reduceIte, StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
        Bool.false_or, Bool.or_assoc, hguardM, ↓reduceIte, StateT.run_pure, simulateQ_pure]
  · simp only [Bool.not_eq_true] at hguard
    have hguardM : ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj 3)) = false := by
      rw [hinT_eq, hsafe_eq]; exact hguard
    have hinT : esLoc.g.inTransit P.other c = none := by
      cases h : esLoc.g.inTransit P.other c with
      | none => rfl
      | some _ => simp [h] at hguard
    by_cases hbad : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) = true
    · have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢; exact hbad
      refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
        Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
          Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
          vRecv_eq_bind, hbad, StateT.run_pure, hesLoc_eta]
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
          Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
          vRecv_eq_bind, hbadM, StateT.run_pure, simulateQ_pure, hesM_eta]
    · simp only [Bool.not_eq_true] at hbad
      have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢; exact hbad
      have hbad0 := hbad
      rw [(hinv.hparty_id P).1, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hbad0
      rcases hbad0 with ⟨hsends_c, hle_succ⟩
      rcases vRecvStep1_coupled_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs hinv P c hbad with
        ⟨hs1L, hs1M⟩ | ⟨hs1L, hs1M⟩ |
        ⟨s1Loc, s1M, hs1L, hs1M, hid, htcur, hnew, hbase, hvS, hvR_gt, hvR_ne, hvRc⟩
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        have hs1M0 : (vRecvStep1 hkM esM.g P (esM.g.st P) c).run esM.h = pure (none, esM.h) := hs1M false
        refine ⟨none, actEp, { esLoc with abort := true }, { esM with abort := true }, tblM,
          ?_, ?_, hwinM.trans hinv.hwin_loc.symm, Or.inl ⟨rfl, rfl, hinv.herase⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbad, hs1L, StateT.run_pure, abortE, StateT.run_modify]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbadM, hs1M0, StateT.run_pure, abortE, StateT.run_modify, simulateQ_pure]
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        have hs1M0 : (vRecvStep1 hkM esM.g P (esM.g.st P) c).run esM.h = pure (some none, esM.h) := hs1M false
        refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
          Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbad, hs1L, StateT.run_pure, hesLoc_eta]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbadM, hs1M0, StateT.run_pure, simulateQ_pure, hesM_eta]
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        have hs1M0 : (vRecvStep1 hkM esM.g P (esM.g.st P) c).run esM.h = pure (some (some s1M), esM.h) := hs1M false
        cases hvL_c : s1Loc.vR c.1.1 with
        | none =>
          rw [hvL_c] at hvRc
          refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
            Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
              Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
              vRecv_eq_bind, hbad, hs1L, hvL_c, StateT.run_pure, hesLoc_eta]
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
              Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
              vRecv_eq_bind, hbadM, hs1M0, hvRc, StateT.run_pure, simulateQ_pure, hesM_eta]
        | some rsLoc =>
          rw [hvL_c] at hvRc
          cases ha : actEp c.1.1 with
          | none =>
            rw [ha] at hvRc
            cases hrec : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 with
            | none =>
              refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec, StateT.run_pure, pure_bind, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M0, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [hrec, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure, hesM_eta]
            | some rim =>
              rcases rim with ⟨rsLoc', idxOut, pmOut⟩
              by_cases hqep_gt : qep + 1 < c.1.1
              · refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                  Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                    Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbad, hs1L, hvL_c]
                  dsimp only [hkLoc, hooksLocalMainSlot]
                  simp only [hrec, StateT.run_pure, pure_bind, hqep_gt, ↓reduceIte, hesLoc_eta]
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                    Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbadM, hs1M0, hvRc]
                  dsimp only [hkM, hooksFSMultiBucketAuth]
                  simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, ↓reduceIte,
                    simulateQ_pure, hesM_eta]
              · let pos : Pos := ⟨P.other, c.1.1, idxOut⟩
                have htriv_eq : esM.g.trivial 3 pos = esLoc.g.trivial 3 pos :=
                  _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hinv.herase 3 pos
                by_cases htriv : esLoc.g.trivial 3 pos = true
                · have htrivM : esM.g.trivial 3 pos = true := htriv_eq.trans htriv
                  let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
                  let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inl rsLoc')) }
                  refine ⟨some (.accepted c.1.1 idxOut (some pmOut)), actEp,
                    { esLoc with g := esLoc.g.accept P stLoc' pos },
                    { esM with g := esM.g.accept P stM' pos }, tblM, ?_, ?_,
                    hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_⟩⟩
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                      Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbad, hs1L, hvL_c]
                    dsimp only [hkLoc, hooksLocalMainSlot, commitE]
                    simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                      hqep_gt, ↓reduceIte, pos, htriv, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, stLoc']
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M0, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                    simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                      pure_bind, hqep_gt, ↓reduceIte, pos, htrivM, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, simulateQ_pure, stM']
                  · exact commit_accept_coupled_r71inj (actEp' := actEp) (tblM' := tblM) (tblL' := tblL) (hM' := esM.h)
                      C encT idOf ℓ q qep tL par ks bs hinv P c idxOut
                      hsends_c hle_succ s1Loc s1M rsLoc' (.inl rsLoc') hid htcur hnew hbase hvS hvR_gt hvR_ne
                      (by rw [ha]; exact ⟨rfl, rfl⟩) (fun _ _ => rfl) ⟨rfl, rfl, rfl, rfl⟩
                      (fun t0 ss0 rs0 ha0 => by
                        rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha_inv, _, htr⟩
                        have hne_ep : c.1.1 ≠ t0 := fun heq => by subst heq; rw [ha] at ha0; cases ha0
                        have hfilt : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                            (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                          rw [List.filter_comm]; apply List.filter_eq_self.mpr
                          intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                          simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'; exact hne_ep hr'.2
                        refine ⟨ha_inv, fun hp1 => Bool.noConfusion hp1, rfl, ?_⟩
                        dsimp only [GameState.accept, GameState.delete]; rw [hfilt]; exact htr)
                      (fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩)
                · simp only [Bool.not_eq_true] at htriv
                  have htrivM : esM.g.trivial 3 pos = false := htriv_eq.trans htriv
                  by_cases hinjF : (bucketAuthCfg (M := LibsignalMsgPublicPart × Plain ℓ) 1 tL).injectFull c.1.1 = true
                  · refine ⟨some .rejected, actEp, { esLoc with g := { esLoc.g with win := true } },
                      { esM with g := { esM.g with win := true } }, tblM, ?_, ?_, rfl,
                      Or.inl ⟨by simp, hinv.habort_M.trans hinv.habort_loc.symm, eraseSt_win_true_r71inj hinv.herase⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot]
                      simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                        hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htriv, hinjF]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M0, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                        pure_bind, hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htrivM, hinjF, simulateQ_pure]
                  · simp only [Bool.not_eq_true] at hinjF
                    refine ⟨some .rejected, actEp, esLoc, esM, tblM, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                      Or.inr ⟨hinv.hwin_loc, hinv_rem'⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot]
                      simp only [hrec, StateT.run_pure, pure_bind, hqep_gt, Bool.false_eq_true, ↓reduceIte,
                        pos, htriv, hinjF, hesLoc_eta]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M0, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, Bool.false_eq_true,
                        ↓reduceIte, pos, htrivM, hinjF, simulateQ_pure, hesM_eta]
          | some pair =>
            rcases pair with ⟨ssA, rsA⟩
            rw [ha] at hvRc
            rcases hvRc with ⟨rfl, hvRc⟩
            let sIdx := sIdxMain q tL c.1.1
            let bk := (esM.h.book sIdx).getD {}
            rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨hh1, hqep_le, hvg, _, ha_inv, _, htr_bk⟩
            have hqep_gt : ¬ (qep + 1 < c.1.1) := by omega
            have hinjF : (bucketAuthCfg (M := LibsignalMsgPublicPart × Plain ℓ) 1 tL).injectFull c.1.1 = true := by
              simp only [bucketAuthCfg_injectFull_r71inj]
              simp only [validGuessBucketParAuth, Bool.and_eq_true] at hvg
              exact hvg.1
            have hP_other : P.other = Party.senderOf c.1.1 := by
              cases hPo : P.other.sendsIn c.1.1
              · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
              · exact _root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo
            have hmatch : bk.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := by
              dsimp only [bk]; rw [htr_bk, find_filter_map_trans_r71inj esLoc.g.trans P (c.1, c.2) hP_other
                (fun r' hr' => ⟨(hinv.htrans r' hr').1, (hinv.htrans r' hr').2.1⟩)]
              change (esLoc.g.inTransit P.other c).map _ = _; rw [hinT]; rfl
            have hmatch_unf : ((esM.h.book (sIdxMain q tL c.1.1)).getD {}).fsTrans.find?
                (fun x => x.2 == (c.1, c.2)) = none := hmatch
            rcases hinv.hphase2 rfl with ⟨cur, htL_cur, _, hle_cur⟩
            have hheal_M : healedBy esM.g.tL (2 + 1) c.1.1 = false := by
              have hc_le : c.1.1 ≤ cur := hle_cur c.1.1 (by simp [ha])
              rw [htL_eq, htL_cur]; simp [healedBy]; omega
            have hcs_step : ∃ (h1 : MultiHSt_r71inj Pt) (tblM1 : ℕ → SessHSt Pt ℓ),
                ((((esM.h.book (sIdxMain q tL c.1.1)).getD {}).sCorr = true ∧ h1 = esM.h ∧ tblM1 = tblM) ∨
                 (((esM.h.book (sIdxMain q tL c.1.1)).getD {}).sCorr = false ∧
                  ∃ sM_cs,
                    ((_root_.CryptoGames.FSAEAD.Thm5.corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
                      StateT (SessHSt Pt ℓ) ProbComp _)).run (tblM (sIdxMain q tL c.1.1)) = pure (some ssA, sM_cs) ∧
                    h1 = { esM.h with book := Function.update esM.h.book sIdx (some { bk with sCorr := true }) } ∧
                    tblM1 = Function.update tblM sIdx sM_cs)) ∧
                h1.cache = esM.h.cache ∧ h1.fTable = esM.h.fTable ∧ h1.sessions = esM.h.sessions ∧
                h1.lfWin = esM.h.lfWin ∧
                ((h1.book sIdx).getD {}).sCorr = true ∧
                ((h1.book sIdx).getD {}).fsCount = bk.fsCount ∧
                ((h1.book sIdx).getD {}).fsTrans = bk.fsTrans ∧
                ActiveSessInv C ℓ encT idOf false (ks sIdx) ssA rsLoc ((h1.book sIdx).getD {})
                  (tblM1 sIdx) (tblL sIdx) ∧
                (∀ sIdx', sIdx' ≠ sIdx → h1.book sIdx' = esM.h.book sIdx' ∧ tblM1 sIdx' = tblM sIdx') := by
              cases hsc : bk.sCorr with
              | true =>
                exact ⟨esM.h, tblM, Or.inl ⟨rfl, rfl, rfl⟩,
                  rfl, rfl, rfl, rfl, hsc, rfl, rfl, ha_inv, fun _ _ => ⟨rfl, rfl⟩⟩
              | false =>
                rcases activeSessInv_corruptSender C ℓ encT idOf ha_inv with ⟨sM_cs, hcs, ha_cs⟩
                let h1 : MultiHSt_r71inj Pt := { esM.h with book := Function.update esM.h.book sIdx (some { bk with sCorr := true }) }
                let tblM1 := Function.update tblM sIdx sM_cs
                exact ⟨h1, tblM1, Or.inr ⟨rfl, sM_cs, hcs, rfl, rfl⟩,
                  rfl, rfl, rfl, rfl, by simp [h1, sIdx, bk], by simp [h1, sIdx, bk],
                  by simp [h1, sIdx, bk], by simpa [h1, tblM1, sIdx, bk] using ha_cs,
                  fun sIdx' hne => ⟨by simp [h1, hne], by simp [tblM1, hne]⟩⟩
            rcases hcs_step with ⟨h1, tblM1, hcs_cases, h1_cache, h1_fTable, h1_sess, h1_lf,
              h1_sc, h1_cnt, h1_tr, ha_inv1, h1_ne⟩
            have h1_match : ((h1.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := by
              rw [h1_tr]; exact hmatch
            have h1_match_unf : ((h1.book (sIdxMain q tL c.1.1)).getD {}).fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := h1_match
            cases hpub : lPubOf protoSignalCodec c.2.2 with
            | none =>
              have hrec_none : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 = none := by
                dsimp only [locFS_r71inj]; rw [lFS_receive_eq, hpub]
              have hesM1_eta : ({ g := esM.g, h := h1 } : MultiESt_r71inj Pt ℓ) = { esM with h := h1 } := by
                cases esM; simpa using hinv.habort_M.symm
              refine ⟨some .rejected, actEp, esLoc, { esM with h := h1 }, tblM1, ?_, ?_,
                hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_⟩⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec_none, StateT.run_pure, pure_bind, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M0, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                rcases hcs_cases with ⟨hsc_unf, hh1_def, htbl1_def⟩ | ⟨hsc_unf, sM_cs, hcs, hh1_def, htbl1_def⟩
                · simp only [← hh1_def, ← htbl1_def] at *
                  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_bind, bind_assoc,
                    beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
                  rw [liftFS_inject_none_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 hpub h1 tblM1]
                  simp only [pure_bind, StateT.run_pure, simulateQ_pure, hesM1_eta]
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind, bind_assoc,
                    beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                    Bool.true_and, ↓reduceIte]
                  rw [liftFS_corruptSender_run_r71inj C encT idOf ℓ (sIdxMain q tL c.1.1) esM.h tblM hcs]
                  simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    simulateQ_pure, simulateQ_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                    ← hh1_def, ← htbl1_def, bk, sIdx]
                  rw [liftFS_inject_none_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 hpub h1 tblM1]
                  simp only [pure_bind, StateT.run_pure, simulateQ_pure, hesM1_eta]
              · refine { hinv_rem' with
                  hphase1 := fun hp1 => Bool.noConfusion hp1
                  hcache := fun t => by rw [h1_cache]; exact hinv.hcache t
                  hfuture := fun t ht => by rw [h1_cache, h1_fTable, h1_sess]; exact hinv.hfuture t ht
                  hact := fun t0 ss0 rs0 ha0 => by
                    by_cases ht : t0 = c.1.1
                    · subst t0; rw [ha] at ha0; cases ha0
                      rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨a1, a2, a3, a4, _, a6, a7⟩
                      exact ⟨a1, a2, a3, a4, ha_inv1, fun heq => (a6 heq).trans h1_cnt.symm, h1_tr.trans a7⟩
                    · have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                        ht (sIdxMain_inj q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                      rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                      simpa [hb_ne, ht_ne] using hinv.hact t0 ss0 rs0 ha0
                  hunalloc := fun sIdx' hlt hun => by
                    have hne : sIdx' ≠ sIdx := fun heq => by
                      subst heq; have := hun c.1.1 hh1 rfl; rw [ha] at this; cases this
                    rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                    rcases hinv.hunalloc sIdx' hlt hun with ⟨u1, u2, u3, u4⟩
                    exact ⟨u1, hb_ne.trans u2, ht_ne.trans u3, u4⟩ }
            | some p =>
              have hinj2 := activeSessInv_inject_phase2 C ℓ encT idOf ha_inv1 h1_sc c.1 c.2 h1_match p hpub
              cases hrec : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 with
              | none =>
                dsimp only [locFS_r71inj] at hrec; rw [hrec] at hinj2
                rcases hinj2 with ⟨sM', hiM, ha_inv2⟩
                let tblM' := Function.update tblM1 sIdx sM'
                have hesM1_eta : ({ g := esM.g, h := h1 } : MultiESt_r71inj Pt ℓ) = { esM with h := h1 } := by
                  cases esM; simpa using hinv.habort_M.symm
                refine ⟨some .rejected, actEp, esLoc, { esM with h := h1 }, tblM', ?_, ?_,
                  hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_⟩⟩
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                    Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbad, hs1L, hvL_c]
                  dsimp only [hkLoc, hooksLocalMainSlot]
                  simp only [locFS_r71inj, hrec, StateT.run_pure, pure_bind, hesLoc_eta]
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                    Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbadM, hs1M0, hvRc]
                  dsimp only [hkM, hooksFSMultiBucketAuth]
                  rcases hcs_cases with ⟨hsc_unf, hh1_def, htbl1_def⟩ | ⟨hsc_unf, sM_cs, hcs, hh1_def, htbl1_def⟩
                  · simp only [← hh1_def, ← htbl1_def] at *
                    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_bind, bind_assoc,
                      beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                      Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
                    rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                    simp only [pure_bind, Option.map_some, withPub, StateT.run_pure,
                      simulateQ_pure, tblM', sIdx, hesM1_eta]
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind, bind_assoc,
                      beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                      Bool.true_and, ↓reduceIte]
                    rw [liftFS_corruptSender_run_r71inj C encT idOf ℓ (sIdxMain q tL c.1.1) esM.h tblM hcs]
                    simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                      simulateQ_pure, simulateQ_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                      ← hh1_def, ← htbl1_def, bk, sIdx]
                    rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                    simp only [pure_bind, Option.map_some, withPub, StateT.run_pure,
                      simulateQ_pure, tblM', sIdx, hesM1_eta]
                · refine { hinv_rem' with
                    hphase1 := fun hp1 => Bool.noConfusion hp1
                    hcache := fun t => by rw [h1_cache]; exact hinv.hcache t
                    hfuture := fun t ht => by rw [h1_cache, h1_fTable, h1_sess]; exact hinv.hfuture t ht
                    hact := fun t0 ss0 rs0 ha0 => by
                      by_cases ht : t0 = c.1.1
                      · subst t0; rw [ha] at ha0; cases ha0
                        rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨a1, a2, a3, a4, _, a6, a7⟩
                        exact ⟨a1, a2, a3, a4, by simpa [tblM', sIdx] using ha_inv2,
                          fun heq => (a6 heq).trans h1_cnt.symm, h1_tr.trans a7⟩
                      · have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                          ht (sIdxMain_inj q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                        rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                        simpa [tblM', hne, hb_ne, ht_ne] using hinv.hact t0 ss0 rs0 ha0
                    hunalloc := fun sIdx' hlt hun => by
                      have hne : sIdx' ≠ sIdx := fun heq => by
                        subst heq; have := hun c.1.1 hh1 rfl; rw [ha] at this; cases this
                      rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                      rcases hinv.hunalloc sIdx' hlt hun with ⟨u1, u2, u3, u4⟩
                      exact ⟨u1, hb_ne.trans u2, by simp [tblM', hne, ht_ne, u3], u4⟩ }
              | some rim =>
                rcases rim with ⟨rsLoc', idxOut, pmOut⟩
                dsimp only [locFS_r71inj] at hrec; rw [hrec] at hinj2
                rcases hinj2 with ⟨sM', hiM, hpm1, ha_inv2⟩
                have hpm_eq : (p, pmOut.2) = pmOut := by cases pmOut; dsimp only at hpm1; subst hpm1; rfl
                let bk2 : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                  { (h1.book sIdx).getD {} with fsTrans := ((h1.book sIdx).getD {}).fsTrans.filter (·.1 != idxOut) }
                let h2 : MultiHSt_r71inj Pt := { h1 with book := Function.update h1.book sIdx (some bk2) }
                let tblM' := Function.update tblM1 sIdx sM'
                let pos : Pos := ⟨P.other, c.1.1, idxOut⟩
                have htriv_eq : esM.g.trivial 3 pos = esLoc.g.trivial 3 pos :=
                  _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hinv.herase 3 pos
                by_cases htriv : esLoc.g.trivial 3 pos = true
                · have htrivM : esM.g.trivial 3 pos = true := htriv_eq.trans htriv
                  let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
                  let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inr sIdx)) }
                  let actEp' := Function.update actEp c.1.1 (some (ssA, rsLoc'))
                  refine ⟨some (.accepted c.1.1 idxOut (some pmOut)), actEp',
                    { esLoc with g := esLoc.g.accept P stLoc' pos },
                    { esM with g := esM.g.accept P stM' pos, h := h2 }, tblM', ?_, ?_,
                    hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_⟩⟩
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                      Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbad, hs1L, hvL_c]
                    dsimp only [hkLoc, hooksLocalMainSlot, commitE]
                    simp only [locFS_r71inj, hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                      hqep_gt, ↓reduceIte, pos, htriv, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, stLoc']
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M0, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                    rcases hcs_cases with ⟨hsc_unf, hh1_def, htbl1_def⟩ | ⟨hsc_unf, sM_cs, hcs, hh1_def, htbl1_def⟩
                    · simp only [← hh1_def, ← htbl1_def] at *
                      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_bind, bind_assoc,
                        beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                        Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind, StateT.run_get,
                        StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71inj, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none, hqep_gt, pos, htrivM,
                        accept_update_idem_r71inj, h2, bk2, stM', tblM', sIdx]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind, bind_assoc,
                        beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                        Bool.true_and, ↓reduceIte]
                      rw [liftFS_corruptSender_run_r71inj C encT idOf ℓ (sIdxMain q tL c.1.1) esM.h tblM hcs]
                      simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                        simulateQ_pure, simulateQ_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                        ← hh1_def, ← htbl1_def, bk, sIdx]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind, StateT.run_get,
                        StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71inj, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none, hqep_gt, pos, htrivM,
                        accept_update_idem_r71inj, h2, bk2, stM', tblM', sIdx]
                  · exact commit_accept_coupled_r71inj (actEp' := actEp') (tblM' := tblM') (tblL' := tblL) (hM' := h2)
                      C encT idOf ℓ q qep tL par ks bs hinv P c idxOut
                      hsends_c hle_succ s1Loc s1M rsLoc' (.inr sIdx) hid htcur hnew hbase hvS hvR_gt hvR_ne
                      (by simp [actEp', sIdx, ha]) (fun t ht => by simp [actEp', ht])
                      ⟨h1_cache, h1_fTable, h1_sess, h1_lf⟩
                      (fun t0 ss0 rs0 ha0 => by
                        by_cases ht : t0 = c.1.1
                        · subst t0; simp only [actEp', Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha0
                          rcases ha0 with ⟨rfl, rfl⟩
                          have hfilt_eq : (((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                              (fun r' => r'.pos.epoch == c.1.1)).map (fun r' => (r'.pos.idx, r'.ct.1, r'.ct.2))) =
                              bk.fsTrans.filter (·.1 != idxOut) := by
                            rw [htr_bk, List.filter_map, List.filter_comm]
                            congr 1; apply List.filter_congr
                            intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                            rcases hinv.htrans r' hr'.1 with ⟨_, hsend', _⟩
                            rw [hr'.2, ← hP_other] at hsend'
                            rcases r' with ⟨⟨rs', re', ri'⟩, rm', rct'⟩
                            rcases hr' with ⟨_, rfl⟩
                            dsimp only [Function.comp_def] at hsend' ⊢
                            subst hsend'; rw [Bool.eq_iff_iff]; simp [bne_iff_ne]
                          refine ⟨?_, fun hp1 => Bool.noConfusion hp1,
                            by simp [h2, bk2, sIdx, h1_cnt, bk],
                            by simpa [h2, bk2, sIdx, h1_tr, GameState.accept, GameState.delete] using hfilt_eq.symm⟩
                          simpa [h2, bk2, tblM', sIdx] using ha_inv2
                        · simp only [actEp', Function.update_of_ne ht] at ha0
                          have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                            ht (sIdxMain_inj q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                          rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                          rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha0_inv, _, htr0⟩
                          have hfilt0 : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                              (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                            rw [List.filter_comm]; apply List.filter_eq_self.mpr
                            intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                            simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'; exact ht hr'.2.symm
                          refine ⟨?_, fun hp1 => Bool.noConfusion hp1, by simp [h2, hne, hb_ne], ?_⟩
                          · simpa [h2, tblM', hne, hb_ne, ht_ne] using ha0_inv
                          · simp only [h2, Function.update_of_ne hne, hb_ne, GameState.accept, GameState.delete, hfilt0, htr0])
                      (fun sIdx' hlt hun => by
                        have hne : sIdx' ≠ sIdx := fun heq => by
                          subst heq; have := hun c.1.1 hh1 rfl; simp [actEp'] at this
                        rcases h1_ne _ hne with ⟨hb_ne, ht_ne⟩
                        exact ⟨by simp [h2, hne, hb_ne], by simp [tblM', hne, ht_ne], fun hp1 => Bool.noConfusion hp1⟩)
                · simp only [Bool.not_eq_true] at htriv
                  have htrivM : esM.g.trivial 3 pos = false := htriv_eq.trans htriv
                  refine ⟨some .rejected, actEp, { esLoc with g := { esLoc.g with win := true } },
                    { esM with g := { esM.g with win := true }, h := h2 }, tblM', ?_, ?_, rfl,
                    Or.inl ⟨by simp, hinv.habort_M.trans hinv.habort_loc.symm, eraseSt_win_true_r71inj hinv.herase⟩⟩
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                      Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbad, hs1L, hvL_c]
                    dsimp only [hkLoc, hooksLocalMainSlot]
                    simp only [locFS_r71inj, hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                      hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htriv, hinjF]
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M0, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth]
                    rcases hcs_cases with ⟨hsc_unf, hh1_def, htbl1_def⟩ | ⟨hsc_unf, sM_cs, hcs, hh1_def, htbl1_def⟩
                    · simp only [← hh1_def, ← htbl1_def] at *
                      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_bind, bind_assoc,
                        beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                        Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind, StateT.run_get,
                        StateT.run_modify, StateT.run_pure, simulateQ_pure, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none, hqep_gt, pos, htrivM,
                        hinjF, h2, bk2, tblM', sIdx]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind, bind_assoc,
                        beq_hdr_ct_inst_eq_r71inj, hmatch_unf, Option.isNone_none, hheal_M, Bool.not_false, hsc_unf,
                        Bool.true_and, ↓reduceIte]
                      rw [liftFS_corruptSender_run_r71inj C encT idOf ℓ (sIdxMain q tL c.1.1) esM.h tblM hcs]
                      simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                        simulateQ_pure, simulateQ_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                        ← hh1_def, ← htbl1_def, bk, sIdx]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub h1 tblM1 hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind, StateT.run_get,
                        StateT.run_modify, StateT.run_pure, simulateQ_pure, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none, hqep_gt, pos, htrivM,
                        hinjF, h2, bk2, tblM', sIdx]

private theorem step_inject_phase2_leOne_r71inj
    {rem' : ℕ} {actEp : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → SmAdv_r71inj Pt ℓ)
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs false (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih : ∀ u actEp' esLoc' esM' tblM' tblL',
      CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs false rem' actEp' esLoc' esM' esL none tblM' tblL' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    LeOne
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esM winEp tblM) := by
  obtain rfl := hinv.hwe
  have hwinM : esM.g.win = false := by
    rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_win hinv.herase]; exact hinv.hwin_loc
  rcases injectE_phase2_coupled_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs hinv P c with
    ⟨out, actEp', esLoc', esM', tblM', hinjLoc, hinjM, hwin_eq, hpost⟩
  let winEp' : Option ℕ := if esLoc'.g.win then some c.1.1 else none
  have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
      (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esLoc none =
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' winEp' := by
    unfold runLocCont; rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hinjLoc,
      hinv.hwin_loc, Bool.not_false, Bool.true_and, StateT.run_set, StateT.run_pure, winEp']
  have hMStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
      (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esM none tblM =
      runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k out) esM' winEp' tblM' := by
    unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
    rw [hinjM]
    simp only [pure_bind, hwinM, Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true,
      hwin_eq, StateT.run_set, StateT.run_pure, simulateQ_pure, winEp']
  rw [hLocStep, hMStep]
  rcases hpost with ⟨hhalt, hab, her⟩ | ⟨hwin_false, hinv'⟩
  · exact halted_exit_leOne_r71inj C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' esM' winEp' tblM' hhalt hab her
  · have hwe' : winEp' = none := by simp [winEp', hwin_false]
    rw [hwe']
    exact ih out actEp' esLoc' esM' tblM' tblL hinv'

private theorem injectE_phase1_coupled_r71inj
    {rem' : ℕ} {actEp : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (P : Party) (c : Fig8C Pt) :
    let hkLoc := hooksLocalMainSlot (dhScheme Dh) (rootPRNG C.F encPt) (locFS_r71inj C ℓ encT idOf)
      1 q qep (mSessMain q qep tL) tL par
    let hkM := fun la => hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
      (locFS_r71inj C ℓ encT idOf) 1 qep true tL par la
    (∃ hL' tblL',
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
        ((injectE (hkM true) 3 qep (bucketAuthCfg 1 tL) (P, c)).run esL)).run
        (fun _ => false, tblL) = pure ((none, { esM with h := hL', abort := true }), (fun _ => false, tblL')) ∧
      hL'.lfWin = true) ∨
    (∃ out actEp' esLoc' esM' tblM' tblL',
      (injectE hkLoc 3 qep (bucketAuthCfg 1 tL) (P, c)).run esLoc = pure (out, esLoc') ∧
      (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
        ((injectE (hkM false) 3 qep (bucketAuthCfg 1 tL) (P, c)).run esM)).run
        (fun _ => false, tblM) = pure ((out, esM'), (fun _ => false, tblM')) ∧
      esM'.g.win = esLoc'.g.win ∧
      (((esLoc'.abort || esLoc'.g.win) = true ∧ esM'.abort = esLoc'.abort ∧
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esM'.g =
            _root_.CryptoGames.SM.Construction.AuthL11.eraseSt esLoc'.g) ∨
        (esLoc'.g.win = false ∧
          (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
            ((injectE (hkM true) 3 qep (bucketAuthCfg 1 tL) (P, c)).run esL)).run
            (fun _ => false, tblL) = pure ((out, esM'), (fun _ => false, tblL')) ∧
          CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs true rem' actEp' esLoc' esM' esM' none tblM' tblL'))) := by
  intro hkLoc hkM
  rcases hinv.hphase1 rfl with ⟨hpl_false, hesL_eq, hlf0, hsc0⟩
  have hwinM : esM.g.win = false := by
    rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_win hinv.herase]; exact hinv.hwin_loc
  have hinT_eq : esM.g.inTransit P.other c = esLoc.g.inTransit P.other c := by
    simp [GameState.inTransit, _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trans hinv.herase]
  have hsafe_eq : esM.g.safeInj 3 = esLoc.g.safeInj 3 :=
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hinv.herase 3
  have htL_eq : esM.g.tL = esLoc.g.tL :=
    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_tL hinv.herase
  have hesLoc_eta : ({ g := esLoc.g, h := esLoc.h } : LocESt Pt ℓ) = esLoc := by
    cases esLoc; simpa using hinv.habort_loc.symm
  have hesM_eta : ({ g := esM.g, h := esM.h } : MultiESt_r71inj Pt ℓ) = esM := by
    cases esM; simpa using hinv.habort_M.symm
  have hinv_rem' : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs true rem' actEp esLoc esM esM none tblM tblL := {
    habort_loc := hinv.habort_loc, habort_M := hinv.habort_M, hwin_loc := hinv.hwin_loc, hwe := rfl
    herase := hinv.herase, hep_le := hinv.hep_le, hep_sends := hinv.hep_sends
    hphase1 := fun _ => ⟨hpl_false, rfl, hlf0, hsc0⟩, hphase2 := fun h => Bool.noConfusion h
    hparty_id := hinv.hparty_id, hparty_tcur := hinv.hparty_tcur, hparty_base := hinv.hparty_base
    htcur_le := fun Q => by have := hinv.htcur_le Q; omega
    hvR_gt := hinv.hvR_gt, hvS := hinv.hvS, hvR := hinv.hvR, hcache := hinv.hcache
    hfuture := hinv.hfuture, hact := hinv.hact, hunalloc := hinv.hunalloc, htrans := hinv.htrans }
  dsimp only [injectE]
  by_cases hguard : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj 3)) = true
  · have hguardM : ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj 3)) = true := by
      rw [hinT_eq, hsafe_eq]; exact hguard
    refine Or.inr ⟨none, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
      Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
        Bool.false_or, Bool.or_assoc, hguard, ↓reduceIte, StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
        Bool.false_or, Bool.or_assoc, hguardM, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    · rw [hesL_eq]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
        Bool.false_or, Bool.or_assoc, hguardM, ↓reduceIte, StateT.run_pure, simulateQ_pure]
  · simp only [Bool.not_eq_true] at hguard
    have hguardM : ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj 3)) = false := by
      rw [hinT_eq, hsafe_eq]; exact hguard
    have hinT : esLoc.g.inTransit P.other c = none := by
      cases h : esLoc.g.inTransit P.other c with
      | none => rfl
      | some _ => simp [h] at hguard
    by_cases hbad : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) = true
    · have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢; exact hbad
      refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
        Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
          Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
          vRecv_eq_bind, hbad, StateT.run_pure, hesLoc_eta]
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
          Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
          vRecv_eq_bind, hbadM, StateT.run_pure, simulateQ_pure, hesM_eta]
      · rw [hesL_eq]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
          Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
          vRecv_eq_bind, hbadM, StateT.run_pure, simulateQ_pure, hesM_eta]
    · simp only [Bool.not_eq_true] at hbad
      have hbadM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
        simp only [(hinv.hparty_id P).1, (hinv.hparty_id P).2, (hinv.hparty_tcur P).2] at hbad ⊢; exact hbad
      have hbad0 := hbad
      rw [(hinv.hparty_id P).1, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hbad0
      rcases hbad0 with ⟨hsends_c, hle_succ⟩
      rcases vRecvStep1_coupled_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs hinv P c hbad with
        ⟨hs1L, hs1M⟩ | ⟨hs1L, hs1M⟩ |
        ⟨s1Loc, s1M, hs1L, hs1M, hid, htcur, hnew, hbase, hvS, hvR_gt, hvR_ne, hvRc⟩
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        refine Or.inr ⟨none, actEp, { esLoc with abort := true }, { esM with abort := true }, tblM, tblL,
          ?_, ?_, hwinM.trans hinv.hwin_loc.symm, Or.inl ⟨rfl, rfl, hinv.herase⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbad, hs1L, StateT.run_pure, abortE, StateT.run_modify]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbadM, hs1M false, StateT.run_pure, abortE, StateT.run_modify, simulateQ_pure]
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
          Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
            Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbad, hs1L, StateT.run_pure, hesLoc_eta]
        · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbadM, hs1M false, StateT.run_pure, simulateQ_pure, hesM_eta]
        · rw [hesL_eq]
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
            Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
            vRecv_eq_bind, hbadM, hs1M true, StateT.run_pure, simulateQ_pure, hesM_eta]
      · change (vRecvStep1 hkLoc esLoc.g P (esLoc.g.st P) c).run esLoc.h = _ at hs1L
        change ∀ la, (vRecvStep1 (hkM la) esM.g P (esM.g.st P) c).run esM.h = _ at hs1M
        cases hvL_c : s1Loc.vR c.1.1 with
        | none =>
          rw [hvL_c] at hvRc
          refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
            Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
              Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
              vRecv_eq_bind, hbad, hs1L, hvL_c, StateT.run_pure, hesLoc_eta]
          · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
              Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
              vRecv_eq_bind, hbadM, hs1M false, hvRc, StateT.run_pure, simulateQ_pure, hesM_eta]
          · rw [hesL_eq]
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
              Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj,
              vRecv_eq_bind, hbadM, hs1M true, hvRc, StateT.run_pure, simulateQ_pure, hesM_eta]
        | some rsLoc =>
          rw [hvL_c] at hvRc
          cases ha : actEp c.1.1 with
          | none =>
            rw [ha] at hvRc
            cases hrec : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 with
            | none =>
              refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec, StateT.run_pure, pure_bind, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [hrec, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure, hesM_eta]
              · rw [hesL_eq]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [hrec, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure, hesM_eta]
            | some rim =>
              rcases rim with ⟨rsLoc', idxOut, pmOut⟩
              by_cases hqep_gt : qep + 1 < c.1.1
              · refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                  Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                    Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbad, hs1L, hvL_c]
                  dsimp only [hkLoc, hooksLocalMainSlot]
                  simp only [hrec, StateT.run_pure, pure_bind, hqep_gt, ↓reduceIte, hesLoc_eta]
                · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                    Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbadM, hs1M false, hvRc]
                  dsimp only [hkM, hooksFSMultiBucketAuth]
                  simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, ↓reduceIte,
                    simulateQ_pure, hesM_eta]
                · rw [hesL_eq]
                  simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                    Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                    vRecv_eq_bind, hbadM, hs1M true, hvRc]
                  dsimp only [hkM, hooksFSMultiBucketAuth]
                  simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, ↓reduceIte,
                    simulateQ_pure, hesM_eta]
              · let pos : Pos := ⟨P.other, c.1.1, idxOut⟩
                have htriv_eq : esM.g.trivial 3 pos = esLoc.g.trivial 3 pos :=
                  _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hinv.herase 3 pos
                by_cases htriv : esLoc.g.trivial 3 pos = true
                · have htrivM : esM.g.trivial 3 pos = true := htriv_eq.trans htriv
                  let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
                  let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inl rsLoc')) }
                  refine Or.inr ⟨some (.accepted c.1.1 idxOut (some pmOut)), actEp,
                    { esLoc with g := esLoc.g.accept P stLoc' pos },
                    { esM with g := esM.g.accept P stM' pos }, tblM, tblL, ?_, ?_,
                    hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_, ?_⟩⟩
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                      Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbad, hs1L, hvL_c]
                    dsimp only [hkLoc, hooksLocalMainSlot, commitE]
                    simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                      hqep_gt, ↓reduceIte, pos, htriv, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, stLoc']
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M false, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                    simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                      pure_bind, hqep_gt, ↓reduceIte, pos, htrivM, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, simulateQ_pure, stM']
                  · rw [hesL_eq]
                    simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M true, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                    simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                      pure_bind, hqep_gt, ↓reduceIte, pos, htrivM, run_liftH_r71inj, bind_assoc,
                      accept_update_idem_r71inj, simulateQ_pure, stM']
                  · exact commit_accept_coupled_r71inj (actEp' := actEp) (tblM' := tblM) (tblL' := tblL) (hM' := esM.h)
                      C encT idOf ℓ q qep tL par ks bs hinv P c idxOut
                      hsends_c hle_succ s1Loc s1M rsLoc' (.inl rsLoc') hid htcur hnew hbase hvS hvR_gt hvR_ne
                      (by rw [ha]; exact ⟨rfl, rfl⟩) (fun _ _ => rfl) ⟨rfl, rfl, rfl, rfl⟩
                      (fun t0 ss0 rs0 ha0 => by
                        rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha_inv, _, htr⟩
                        have hne_ep : c.1.1 ≠ t0 := fun heq => by subst heq; rw [ha] at ha0; cases ha0
                        have hfilt : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                            (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                          rw [List.filter_comm]; apply List.filter_eq_self.mpr
                          intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                          simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'; exact hne_ep hr'.2
                        refine ⟨ha_inv, fun _ => hsc0 t0 (by simp [ha0]), rfl, ?_⟩
                        dsimp only [GameState.accept, GameState.delete]; rw [hfilt]; exact htr)
                      (fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩)
                · simp only [Bool.not_eq_true] at htriv
                  have htrivM : esM.g.trivial 3 pos = false := htriv_eq.trans htriv
                  by_cases hinjF : (bucketAuthCfg (M := LibsignalMsgPublicPart × Plain ℓ) 1 tL).injectFull c.1.1 = true
                  · refine Or.inr ⟨some .rejected, actEp, { esLoc with g := { esLoc.g with win := true } },
                      { esM with g := { esM.g with win := true } }, tblM, tblL, ?_, ?_, rfl,
                      Or.inl ⟨by simp, hinv.habort_M.trans hinv.habort_loc.symm, eraseSt_win_true_r71inj hinv.herase⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot]
                      simp only [hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                        hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htriv, hinjF]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M false, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [hrec, Option.map_some, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                        pure_bind, hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htrivM, hinjF, simulateQ_pure]
                  · simp only [Bool.not_eq_true] at hinjF
                    refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_, hwinM.trans hinv.hwin_loc.symm,
                      Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot]
                      simp only [hrec, StateT.run_pure, pure_bind, hqep_gt, Bool.false_eq_true, ↓reduceIte,
                        pos, htriv, hinjF, hesLoc_eta]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M false, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, Bool.false_eq_true,
                        ↓reduceIte, pos, htrivM, hinjF, simulateQ_pure, hesM_eta]
                    · rw [hesL_eq]
                      simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M true, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [hrec, Option.map_some, StateT.run_pure, pure_bind, hqep_gt, Bool.false_eq_true,
                        ↓reduceIte, pos, htrivM, hinjF, simulateQ_pure, hesM_eta]
          | some pair =>
            rcases pair with ⟨ssA, rsA⟩
            rw [ha] at hvRc
            rcases hvRc with ⟨rfl, hvRc⟩
            let sIdx := sIdxMain q tL c.1.1
            let bk := (esM.h.book sIdx).getD {}
            rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨hh1, hqep_le, hvg, _, ha_inv, _, htr_bk⟩
            have hqep_gt : ¬ (qep + 1 < c.1.1) := by omega
            have hvg_adm : lastLeakGuessAdmissible 3 tL c.1.1 = true := by
              simp only [validGuessBucketParAuth, Bool.and_eq_true] at hvg; exact hvg.1
            have hinjF : (bucketAuthCfg (M := LibsignalMsgPublicPart × Plain ℓ) 1 tL).injectFull c.1.1 = true :=
              hvg_adm
            have hvg_heal : healedBy tL 3 c.1.1 = true := hvg_adm
            have hheal_M : healedBy esM.g.tL (2 + 1) c.1.1 = true := by
              rw [htL_eq]; exact healedBy_of_not_postLeak tL esLoc.g c.1.1 hpl_false hvg_heal
            have hP_other : P.other = Party.senderOf c.1.1 := by
              cases hPo : P.other.sendsIn c.1.1
              · rw [_root_.CryptoGames.SM.Construction.AuthL11.sendsIn_other, hsends_c] at hPo; cases hPo
              · exact _root_.CryptoGames.SM.Construction.AuthL11.eq_senderOf_of_sendsIn hPo
            have hmatch : bk.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none := by
              dsimp only [bk]; rw [htr_bk, find_filter_map_trans_r71inj esLoc.g.trans P (c.1, c.2) hP_other
                (fun r' hr' => ⟨(hinv.htrans r' hr').1, (hinv.htrans r' hr').2.1⟩)]
              change (esLoc.g.inTransit P.other c).map _ = _; rw [hinT]; rfl
            have hmatch_unf : ((esM.h.book (sIdxMain q tL c.1.1)).getD {}).fsTrans.find?
                (fun x => x.2 == (c.1, c.2)) = none := hmatch
            have hsc_false : ((esM.h.book (sIdxMain q tL c.1.1)).getD {}).sCorr = false :=
              hsc0 c.1.1 (by simp [ha])
            cases hpub : lPubOf protoSignalCodec c.2.2 with
            | none =>
              have hrec_none : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 = none := by
                dsimp only [locFS_r71inj]; rw [lFS_receive_eq, hpub]
              refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM, tblL, ?_, ?_,
                hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_, hinv_rem'⟩⟩
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                  Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbad, hs1L, hvL_c]
                dsimp only [hkLoc, hooksLocalMainSlot]
                simp only [hrec_none, StateT.run_pure, pure_bind, hesLoc_eta]
              · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M false, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                  hmatch_unf, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                  Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  simulateQ_bind, bind_assoc]
                rw [liftFS_inject_none_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 hpub esM.h tblM]
                simp only [pure_bind, StateT.run_pure, simulateQ_pure, hesM_eta]
              · rw [hesL_eq]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                  hmatch_unf, Option.isNone_none, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                  Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  simulateQ_bind, bind_assoc]
                rw [liftFS_inject_none_run_r71inj C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 hpub esM.h tblL]
                simp only [pure_bind, StateT.run_pure, simulateQ_pure, hesM_eta]
            | some p =>
              rcases activeSessInv_inject_phase1 C ℓ encT idOf ha_inv c.1 c.2 hmatch p hpub with
                ⟨msg, sL', _, hlt_cnt, hiL⟩ | hinj1
              · have hlt_unf : ((esM.h.book (sIdxMain q tL c.1.1)).getD {}).fsCount < c.2.1 := hlt_cnt
                refine Or.inl ⟨{ esM.h with lfWin := true }, Function.update tblL sIdx sL', ?_, rfl⟩
                rw [hesL_eq]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                  Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                  vRecv_eq_bind, hbadM, hs1M true, hvRc]
                dsimp only [hkM, hooksFSMultiBucketAuth]
                simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                  hmatch_unf, Option.isNone_none, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                  Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  simulateQ_bind, bind_assoc]
                rw [liftFS_inject_some_run_r71inj C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblL hiL]
                simp only [pure_bind, Option.map_some, withPub, StateT.run_bind, StateT.run_get,
                  StateT.run_modify, StateT.run_pure, simulateQ_pure, sIdx,
                  hsc_false, Bool.not_false, decide_eq_true_eq, hlt_unf,
                  Bool.true_and, Bool.and_self, ↓reduceIte, abortE]
              · cases hrec : (locFS_r71inj C ℓ encT idOf).receive rsLoc c.1 c.2 with
                | none =>
                  dsimp only [locFS_r71inj] at hrec; rw [hrec] at hinj1
                  rcases hinj1 with ⟨sM', sL', hiM, hiL, ha_inv'⟩
                  let tblM' := Function.update tblM sIdx sM'
                  let tblL' := Function.update tblL sIdx sL'
                  refine Or.inr ⟨some .rejected, actEp, esLoc, esM, tblM', tblL', ?_, ?_,
                    hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_, ?_⟩⟩
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                      Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbad, hs1L, hvL_c]
                    dsimp only [hkLoc, hooksLocalMainSlot]
                    simp only [locFS_r71inj, hrec, StateT.run_pure, pure_bind, hesLoc_eta]
                  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M false, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth]
                    simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                      hmatch_unf, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                      Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                      simulateQ_bind, bind_assoc]
                    rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblM hiM]
                    simp only [pure_bind, Option.map_some, withPub, StateT.run_pure,
                      simulateQ_pure, tblM', sIdx, hesM_eta]
                  · rw [hesL_eq]
                    simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                      Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                      vRecv_eq_bind, hbadM, hs1M true, hvRc]
                    dsimp only [hkM, hooksFSMultiBucketAuth]
                    simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                      hmatch_unf, Option.isNone_none, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                      Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                      simulateQ_bind, bind_assoc]
                    rw [liftFS_inject_some_run_r71inj C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblL hiL]
                    simp only [pure_bind, Option.map_some, withPub, StateT.run_pure,
                      simulateQ_pure, tblL', sIdx, hesM_eta]
                  · refine { hinv_rem' with
                      hact := fun t0 ss0 rs0 ha0 => by
                        by_cases ht : t0 = c.1.1
                        · subst t0; rw [ha] at ha0; cases ha0
                          rcases hinv.hact c.1.1 ssA rsLoc ha with ⟨a1, a2, a3, a4, _, a6, a7⟩
                          exact ⟨a1, a2, a3, a4, by simpa [tblM', tblL', sIdx, bk] using ha_inv', a6, a7⟩
                        · have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                            ht (sIdxMain_inj q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                          simpa [tblM', tblL', hne] using hinv.hact t0 ss0 rs0 ha0
                      hunalloc := fun sIdx' hlt hun => by
                        have hne : sIdx' ≠ sIdx := fun heq => by
                          subst heq; have := hun c.1.1 hh1 rfl; rw [ha] at this; cases this
                        rcases hinv.hunalloc sIdx' hlt hun with ⟨u1, u2, u3, u4⟩
                        exact ⟨u1, u2, by simp [tblM', hne, u3], fun hp1 => by simp [tblL', hne, u4 hp1]⟩ }
                | some rim =>
                  rcases rim with ⟨rsLoc', idxOut, pmOut⟩
                  dsimp only [locFS_r71inj] at hrec; rw [hrec] at hinj1
                  rcases hinj1 with ⟨sM', sL', hiM, hiL, hinj_cnt, hpm1, ha_inv'⟩
                  have hpm_eq : (p, pmOut.2) = pmOut := by cases pmOut; dsimp only at hpm1; subst hpm1; rfl
                  have hle_cnt : idxOut ≤ bk.fsCount := hinj_cnt hsc_false
                  have hlt_false : ¬ (((esM.h.book (sIdxMain q tL c.1.1)).getD {}).fsCount < idxOut) := by
                    dsimp only [bk, sIdx] at hle_cnt; omega
                  let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                    { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) }
                  let hM' : MultiHSt_r71inj Pt := { esM.h with book := Function.update esM.h.book sIdx (some bk') }
                  let tblM' := Function.update tblM sIdx sM'
                  let tblL' := Function.update tblL sIdx sL'
                  let pos : Pos := ⟨P.other, c.1.1, idxOut⟩
                  have htriv_eq : esM.g.trivial 3 pos = esLoc.g.trivial 3 pos :=
                    _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hinv.herase 3 pos
                  by_cases htriv : esLoc.g.trivial 3 pos = true
                  · have htrivM : esM.g.trivial 3 pos = true := htriv_eq.trans htriv
                    let stLoc' := { s1Loc with vR := Function.update s1Loc.vR c.1.1 (some rsLoc') }
                    let stM' := { s1M with vR := Function.update s1M.vR c.1.1 (some (.inr sIdx)) }
                    let actEp' := Function.update actEp c.1.1 (some (ssA, rsLoc'))
                    refine Or.inr ⟨some (.accepted c.1.1 idxOut (some pmOut)), actEp',
                      { esLoc with g := esLoc.g.accept P stLoc' pos },
                      { esM with g := esM.g.accept P stM' pos, h := hM' }, tblM', tblL', ?_, ?_,
                      hwinM.trans hinv.hwin_loc.symm, Or.inr ⟨hinv.hwin_loc, ?_, ?_⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot, commitE]
                      simp only [locFS_r71inj, hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                        hqep_gt, ↓reduceIte, pos, htriv, run_liftH_r71inj, bind_assoc,
                        accept_update_idem_r71inj, stLoc']
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M false, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                      simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                        hmatch_unf, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                        simulateQ_bind, bind_assoc]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblM hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind,
                        StateT.run_get, StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71inj,
                        ↓reduceIte, Option.map_none, Option.getD_none,
                        hqep_gt, pos, htrivM, accept_update_idem_r71inj, hM', bk', stM', tblM', sIdx, bk]
                    · rw [hesL_eq]
                      simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M true, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth, commitE]
                      simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                        hmatch_unf, Option.isNone_none, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                        simulateQ_bind, bind_assoc]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ true (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblL hiL]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind,
                        StateT.run_get, StateT.run_modify, StateT.run_pure, simulateQ_pure, run_liftH_r71inj,
                        hsc_false, Bool.not_false,
                        hlt_false, decide_false,
                        Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none,
                        hqep_gt, pos, htrivM, accept_update_idem_r71inj, hM', bk', stM', tblL', sIdx, bk]
                    · exact commit_accept_coupled_r71inj (actEp' := actEp') (tblM' := tblM') (tblL' := tblL') (hM' := hM')
                        C encT idOf ℓ q qep tL par ks bs hinv P c idxOut
                        hsends_c hle_succ s1Loc s1M rsLoc' (.inr sIdx) hid htcur hnew hbase hvS hvR_gt hvR_ne
                        (by simp [actEp', sIdx, ha]) (fun t ht => by simp [actEp', ht])
                        ⟨rfl, rfl, rfl, rfl⟩
                        (fun t0 ss0 rs0 ha0 => by
                          by_cases ht : t0 = c.1.1
                          · subst t0; simp only [actEp', Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha0
                            rcases ha0 with ⟨rfl, rfl⟩
                            have hfilt_eq : (((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                                (fun r' => r'.pos.epoch == c.1.1)).map (fun r' => (r'.pos.idx, r'.ct.1, r'.ct.2))) =
                                bk.fsTrans.filter (·.1 != idxOut) := by
                              rw [htr_bk, List.filter_map, List.filter_comm]
                              congr 1; apply List.filter_congr
                              intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                              rcases hinv.htrans r' hr'.1 with ⟨_, hsend', _⟩
                              rw [hr'.2, ← hP_other] at hsend'
                              rcases r' with ⟨⟨rs', re', ri'⟩, rm', rct'⟩
                              rcases hr' with ⟨_, rfl⟩
                              dsimp only [Function.comp_def] at hsend' ⊢
                              subst hsend'; rw [Bool.eq_iff_iff]; simp [bne_iff_ne]
                            refine ⟨?_, fun _ => by simp [hM', bk', sIdx, bk, hsc_false],
                              by simp [hM', bk', sIdx, bk],
                              by simpa [hM', bk', sIdx, GameState.accept, GameState.delete] using hfilt_eq.symm⟩
                            simpa [hM', bk', tblM', tblL', sIdx, bk] using ha_inv'
                          · simp only [actEp', Function.update_of_ne ht] at ha0
                            have hne : sIdxMain q tL t0 ≠ sIdx := fun heq =>
                              ht (sIdxMain_inj q tL (hinv.hact t0 ss0 rs0 ha0).1 hh1 heq)
                            rcases hinv.hact t0 ss0 rs0 ha0 with ⟨_, _, _, _, ha0_inv, _, htr0⟩
                            have hfilt0 : ((esLoc.g.trans.filter (fun r' => r'.pos != ⟨P.other, c.1.1, idxOut⟩)).filter
                                (fun r' => r'.pos.epoch == t0)) = esLoc.g.trans.filter (fun r' => r'.pos.epoch == t0) := by
                              rw [List.filter_comm]; apply List.filter_eq_self.mpr
                              intro r' hr'; rw [List.mem_filter, beq_iff_eq] at hr'
                              simp only [bne_iff_ne, ne_eq]; intro hp; rw [hp] at hr'; exact ht hr'.2.symm
                            refine ⟨?_, fun _ => by simp [hM', hne, hsc0 t0 (by simp [ha0])], by simp [hM', hne], ?_⟩
                            · simpa [hM', tblM', tblL', hne] using ha0_inv
                            · simp only [hM', Function.update_of_ne hne, GameState.accept, GameState.delete, hfilt0, htr0])
                        (fun sIdx' hlt hun => by
                          have hne : sIdx' ≠ sIdx := fun heq => by
                            subst heq; have := hun c.1.1 hh1 rfl; simp [actEp'] at this
                          exact ⟨by simp [hM', hne], by simp [tblM', hne], fun _ => by simp [tblL', hne]⟩)
                  · simp only [Bool.not_eq_true] at htriv
                    have htrivM : esM.g.trivial 3 pos = false := htriv_eq.trans htriv
                    refine Or.inr ⟨some .rejected, actEp, { esLoc with g := { esLoc.g with win := true } },
                      { esM with g := { esM.g with win := true }, h := hM' }, tblM', tblL', ?_, ?_, rfl,
                      Or.inl ⟨by simp, hinv.habort_M.trans hinv.habort_loc.symm, eraseSt_win_true_r71inj hinv.herase⟩⟩
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_loc, hinv.hwin_loc,
                        Bool.false_or, Bool.or_assoc, hguard, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbad, hs1L, hvL_c]
                      dsimp only [hkLoc, hooksLocalMainSlot]
                      simp only [locFS_r71inj, hrec, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
                        hqep_gt, Bool.false_eq_true, ↓reduceIte, pos, htriv, hinjF]
                    · simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.habort_M, hwinM,
                        Bool.false_or, Bool.or_assoc, hguardM, Bool.false_eq_true, ↓reduceIte, run_liftH_r71inj, bind_assoc,
                        vRecv_eq_bind, hbadM, hs1M false, hvRc]
                      dsimp only [hkM, hooksFSMultiBucketAuth]
                      simp only [StateT.run_bind, StateT.run_get, pure_bind, beq_hdr_ct_inst_eq_r71inj,
                        hmatch_unf, hheal_M, Bool.not_true, Bool.and_false, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                        simulateQ_bind, bind_assoc]
                      rw [liftFS_inject_some_run_r71inj C encT idOf ℓ false (sIdxMain q tL c.1.1) c.1 c.2 p hpub esM.h tblM hiM]
                      simp only [pure_bind, Option.map_some, withPub, hpm_eq, StateT.run_bind,
                        StateT.run_get, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                        Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none,
                        hqep_gt, pos, htrivM, hinjF, hM', bk', tblM', sIdx, bk]

private theorem step_inject_phase1_leAdd_r71inj
    {rem' : ℕ} {actEp : ActMap_r71inj}
    {esLoc : LocESt Pt ℓ} {esM esL : MultiESt_r71inj Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (P : Party) (c : Fig8C Pt)
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → SmAdv_r71inj Pt ℓ)
    (hinv : CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (ih : ∀ u actEp' esLoc' esM' esL' tblM' tblL',
      CoupledInv_r71inj C encT idOf ℓ q qep tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) :
    LeAdd
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esM winEp tblM)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esL winEp tblL) := by
  obtain rfl := hinv.hwe
  have hesL_eq : esL = esM := (hinv.hphase1 rfl).2.1
  have hwinM : esM.g.win = false := by
    rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_win hinv.herase]; exact hinv.hwin_loc
  rcases injectE_phase1_coupled_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs hinv P c with
    ⟨hL', tblL', hinjL, hlf_true⟩ |
    ⟨out, actEp', esLoc', esM', tblM', tblL', hinjLoc, hinjM, hwin_eq, hpost⟩
  · have hLStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esL none tblL =
        runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k none)
          { esM with h := hL', abort := true } none tblL' := by
      unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
      rw [hinjL]
      rw [hesL_eq]
      simp only [pure_bind, hwinM, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_set, StateT.run_pure, simulateQ_pure]
    rw [hLStep]
    exact lfWin_exit_leAdd C Dh encPt encT idOf ℓ q qep tL par (k none)
      { esM with h := hL', abort := true } none tblL' rfl hlf_true
  · let winEp' : Option ℕ := if esLoc'.g.win then some c.1.1 else none
    have hLocStep : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esLoc none =
        runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k out) esLoc' winEp' := by
      unfold runLocCont; rw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hinjLoc,
        hinv.hwin_loc, Bool.not_false, Bool.true_and, StateT.run_set, StateT.run_pure, winEp']
    have hMStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esM none tblM =
        runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k out) esM' winEp' tblM' := by
      unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
      rw [hinjM]
      simp only [pure_bind, hwinM, Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true,
        hwin_eq, StateT.run_set, StateT.run_pure, simulateQ_pure, winEp']
    rw [hLocStep, hMStep]
    rcases hpost with ⟨hhalt, hab, her⟩ | ⟨hwin_false, hinjL, hinv'⟩
    · exact leAdd_of_le_main (halted_exit_leOne_r71inj C Dh encPt encT idOf ℓ q qep tL par ks
        (k out) esLoc' esM' winEp' tblM' hhalt hab her)
    · have hwe' : winEp' = none := by simp [winEp', hwin_false]
      have hLStep : runSideCont C Dh encPt encT idOf ℓ q qep tL par true
          (liftM (OracleSpec.query (spec := SmSpec_r71inj Pt ℓ) (.inr (.inl (.inr (P, c))))) >>= k) esL none tblL =
          runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k out) esM' none tblL' := by
        unfold runSideCont; rw [simulateQ_bind, simulateQ_query_bind]
        dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
          implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
        rw [hinjL]
        rw [hesL_eq]
        have hwinM'_false : esM'.g.win = false := hwin_eq.trans hwin_false
        simp only [pure_bind, hwinM, hwinM'_false, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, simulateQ_pure]
      rw [hwe', hLStep]
      exact ih out actEp' esLoc' esM' esM' tblM' tblL' hinv'

end InjectR71

/-- Sub-lemma 3 (`step_inject_phase2_leOne`): Coupled `injectE` step for `phase1 = false` proving `LeOne`. -/
private theorem step_inject_phase2_leOne {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem' : ℕ}
    {actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    {esLoc : LocESt Pt ℓ} {esM : SideESt Pt ℓ} {winEp : Option ℕ} {tblM : ℕ → SessHSt Pt ℓ}
    (x : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs false (rem' + 1) actEp esLoc esM esM winEp tblM tblM)
    (ih : ∀ u actEp' esLoc' esM' tblM',
      CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')) :
    LeOne
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inr x)))) >>= k)
        esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inr x)))) >>= k)
        esM winEp tblM) := by
  let _ := (PLift.up hDh, PLift.up hD, PLift.up hinj, PLift.up hdum, PLift.up hℓ)
  rcases x with ⟨P, c⟩
  exact step_inject_phase2_leOne_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs P c k hinv
    fun u actEp' esLoc' esM' tblM' _ hinv' =>
      ih u actEp' esLoc' esM' tblM' (CoupledInv_set_esL_tblL_false_r71inj hinv')

/-- Sub-lemma 4 (`step_inject_phase1_leAdd`): Coupled `injectE` step for `phase1 = true` proving `LeAdd`. -/
private theorem step_inject_phase1_leAdd {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem' : ℕ}
    {actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256))}
    {esLoc : LocESt Pt ℓ} {esM esL : SideESt Pt ℓ} {winEp : Option ℕ} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (x : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (k : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → OracleComp (Fig8Dom Pt ℓ) Bool)
    (hinv : CoupledInv C ℓ q qep encT idOf tL par ks bs true (rem' + 1) actEp esLoc esM esL winEp tblM tblL)
    (hphase2 : ∀ u actEp' esLoc' esM' tblM',
      CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM'))
    (ih : ∀ u actEp' esLoc' esM' esL' tblM' tblL',
      CoupledInv C ℓ q qep encT idOf tL par ks bs true rem' actEp' esLoc' esM' esL' none tblM' tblL' →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM')
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true (k u) esL' none tblL')) :
    LeAdd
      (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inr x)))) >>= k)
        esLoc winEp)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par false
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inr x)))) >>= k)
        esM winEp tblM)
      (runSideCont C Dh encPt encT idOf ℓ q qep tL par true
        (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inr x)))) >>= k)
        esL winEp tblL) := by
  rcases x with ⟨P, c⟩
  let _ := (PLift.up hDh, PLift.up hD, PLift.up hinj, PLift.up hdum, PLift.up hℓ, PLift.up hphase2)
  exact step_inject_phase1_leAdd_r71inj C Dh encPt encT idOf ℓ q qep tL par ks bs P c k hinv ih

/-! ## 2. Adversary Induction (`LeOne` for `phase1 = false`, `LeAdd` for `phase1 = true`) -/

private theorem phase2_coupling_leOne {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (oa : OracleComp (Fig8Dom Pt ℓ) Bool) :
    ∀ (rem : ℕ)
      (actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256)))
      (esLoc : LocESt Pt ℓ) (esM : SideESt Pt ℓ) (winEp : Option ℕ) (tblM : ℕ → SessHSt Pt ℓ),
      oa.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) rem →
      oa.IsQueryBoundP (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 →
      CoupledInv C ℓ q qep encT idOf tL par ks bs false rem actEp esLoc esM esM winEp tblM tblM →
      LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks oa esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false oa esM winEp tblM) := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro rem actEp esLoc esM winEp tblM _ _ hinv
    rcases hinv.hwe with rfl
    refine leOne_of_lhs_zero ?_
    unfold runLocCont mainParOut
    simp
  | query_bind qy k ih =>
    intro rem actEp esLoc esM winEp tblM hoa hSend hinv
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ :=
      badSendMsg_query_bind_step (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) qy k hSend
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inl n)) >>= k) esLoc winEp =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc winEp) := by
        rw [runLocCont_step]
        dsimp only [implLocalMainSlot, QueryImpl.add_apply_inl, keySlotFixedImpl]
        simp only [stateT_lift_run, query_eq_liftM, simulateQ_bind, simulateQ_query, simulateQ_pure,
          OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.ofLift_apply, bind_assoc, pure_bind]
        rfl
      have hSide : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inl n)) >>= k) esM winEp tblM =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM winEp tblM) := by
        rw [runSideCont_step]
        have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
          ((implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par false)
            1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
            (.inl n)).run (esM, winEp))).run (fun _ => false, tblM) =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            pure ((u, (esM, winEp)), (fun _ => false, tblM))) := by
          dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
          rw [stateT_lift_run, query_eq_liftM, simulateQ_query_bind]
          dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
          simp only [simulateQ_pure, StateT.run_bind, StateT.run_pure,
            pubFsMultiImpl_inl_run, bind_assoc, pure_bind]
        erw [hhead]
        simp only [bind_assoc, pure_bind, map_bind]
        rfl
      rw [hLoc, hSide]
      exact leOne_bind _ fun u _ => ih u rem actEp esLoc esM winEp tblM (hmx u) (hSendMx u) hinv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < rem := hq0.resolve_left (by decide)
      obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
      rcases t_sm with (((⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P
      · have hshort : pm.1.shortB = true :=
          atomicShortPubB_imp_shortB
            (by simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg] using hBad)
        exact (step_transmit_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs
          P pm r hshort k).1 hinv fun u actEp' esLoc' esM' tblM' hinv' =>
            ih u rem' actEp' esLoc' esM' none tblM' (by simpa using hmx u) (hSendMx u) hinv'
      · have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
            (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) >>= k)
            esLoc winEp =
            runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) esLoc winEp := by
          rw [runLocCont_step]
          dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hSide : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
            (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) >>= k)
            esM winEp tblM =
            runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k none) esM winEp tblM := by
          rw [runSideCont_step]
          have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
            ((implFSMultiBucketAuth
              (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par false)
              1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
              (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esM, winEp))).run (fun _ => false, tblM) =
            pure ((none, (esM, winEp)), (fun _ => false, tblM)) := by
            dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_pure, simulateQ_pure]
          erw [hhead]
          rw [pure_bind]; rfl
        rw [hLoc, hSide]
        exact ih none rem' actEp esLoc esM winEp tblM (by simpa using hmx none) (hSendMx none)
          (hinv.mono_rem (Nat.le_succ rem'))
      · exact (step_deliver_and_corrupt_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs).1.1
          x k hinv fun u actEp' esLoc' esM' tblM' hinv' =>
            ih u rem' actEp' esLoc' esM' none tblM' (by simpa using hmx u) (hSendMx u) hinv'
      · exact step_inject_phase2_leOne C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs
          x k hinv fun u actEp' esLoc' esM' tblM' hinv' =>
            ih u rem' actEp' esLoc' esM' none tblM' (by simpa using hmx u) (hSendMx u) hinv'
      · by_cases hcorr : esLoc.g.corrAllowed P = true
        · exact (step_deliver_and_corrupt_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs).2.1
            P k hinv hcorr fun u actEp' esLoc' esM' tblM' hinv' =>
              ih u rem' actEp' esLoc' esM' none tblM' (by simpa using hmx u) (hSendMx u) hinv'
        · simp only [Bool.not_eq_true] at hcorr
          have hwinM : esM.g.win = false := by rw [eraseSt_win hinv.herase]; exact hinv.hwin_loc
          have hcorrM : esM.g.corrAllowed P = false := by rw [eraseSt_corrAllowed hinv.herase P]; exact hcorr
          have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
              (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc winEp =
              runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) esLoc winEp := by
            rw [runLocCont_step]
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr]
            simp [hinv.habort_loc, hinv.hwin_loc, hcorr]
          have hSide : runSideCont C Dh encPt encT idOf ℓ q qep tL par false
              (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM winEp tblM =
              runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k none) esM winEp tblM := by
            rw [runSideCont_step]
            have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
              ((implFSMultiBucketAuth
                (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par false)
                1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
                (.inr (.inr P))).run (esM, winEp))).run (fun _ => false, tblM) =
              pure ((none, (esM, winEp)), (fun _ => false, tblM)) := by
              dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr]
              simp [hinv.habort_M, hwinM, hcorrM]
            erw [hhead]
            rw [pure_bind]; rfl
          rw [hLoc, hSide]
          exact ih none rem' actEp esLoc esM winEp tblM (by simpa using hmx none) (hSendMx none)
            (hinv.mono_rem (Nat.le_succ rem'))

private theorem phase1_coupling_leAdd {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (oa : OracleComp (Fig8Dom Pt ℓ) Bool) :
    ∀ (rem : ℕ)
      (actEp : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256)))
      (esLoc : LocESt Pt ℓ) (esM esL : SideESt Pt ℓ) (winEp : Option ℕ) (tblM tblL : ℕ → SessHSt Pt ℓ),
      oa.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) rem →
      oa.IsQueryBoundP (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 →
      CoupledInv C ℓ q qep encT idOf tL par ks bs true rem actEp esLoc esM esL winEp tblM tblL →
      LeAdd (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks oa esLoc winEp)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par false oa esM winEp tblM)
        (runSideCont C Dh encPt encT idOf ℓ q qep tL par true oa esL winEp tblL) := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro rem actEp esLoc esM esL winEp tblM tblL _ _ hinv
    rcases hinv.hwe with rfl
    refine leAdd_of_lhs_zero ?_
    unfold runLocCont mainParOut
    simp
  | query_bind qy k ih =>
    intro rem actEp esLoc esM esL winEp tblM tblL hoa hSend hinv
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ :=
      badSendMsg_query_bind_step (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) qy k hSend
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
          (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inl n)) >>= k) esLoc winEp =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc winEp) := by
        rw [runLocCont_step]
        dsimp only [implLocalMainSlot, QueryImpl.add_apply_inl, keySlotFixedImpl]
        simp only [stateT_lift_run, query_eq_liftM, simulateQ_bind, simulateQ_query, simulateQ_pure,
          OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.ofLift_apply, bind_assoc, pure_bind]
        rfl
      have hSide : ∀ (la : Bool) (esS : SideESt Pt ℓ) (tbl : ℕ → SessHSt Pt ℓ),
          runSideCont C Dh encPt encT idOf ℓ q qep tL par la
            (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inl n)) >>= k) esS winEp tbl =
            ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
              runSideCont C Dh encPt encT idOf ℓ q qep tL par la (k u) esS winEp tbl) := by
        intro la esS tbl
        rw [runSideCont_step]
        have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          ((implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
            1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
            (.inl n)).run (esS, winEp))).run (fun _ => false, tbl) =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            pure ((u, (esS, winEp)), (fun _ => false, tbl))) := by
          dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
          rw [stateT_lift_run, query_eq_liftM, simulateQ_query_bind]
          dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
          simp only [simulateQ_pure, StateT.run_bind, StateT.run_pure,
            pubFsMultiImpl_inl_run, bind_assoc, pure_bind]
        erw [hhead]
        simp only [bind_assoc, pure_bind, map_bind]
        rfl
      rw [hLoc, hSide false esM tblM, hSide true esL tblL]
      exact leAdd_bind _ fun u _ => ih u rem actEp esLoc esM esL winEp tblM tblL (hmx u) (hSendMx u) hinv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < rem := hq0.resolve_left (by decide)
      obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
      have hP2 : ∀ u actEp' esLoc' esM' tblM',
          CoupledInv C ℓ q qep encT idOf tL par ks bs false rem' actEp' esLoc' esM' esM' none tblM' tblM' →
          LeOne (runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k u) esLoc' none)
            (runSideCont C Dh encPt encT idOf ℓ q qep tL par false (k u) esM' none tblM') :=
        fun u actEp' esLoc' esM' tblM' hinv' =>
          phase2_coupling_leOne C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs
            (k u) rem' actEp' esLoc' esM' none tblM' (by simpa using hmx u) (hSendMx u) hinv'
      rcases t_sm with (((⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P
      · have hshort : pm.1.shortB = true :=
          atomicShortPubB_imp_shortB
            (by simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg] using hBad)
        exact (step_transmit_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs
          P pm r hshort k).2 hinv hP2 fun u actEp' esLoc' esM' esL' tblM' tblL' hinv' =>
            ih u rem' actEp' esLoc' esM' esL' none tblM' tblL' (by simpa using hmx u) (hSendMx u) hinv'
      · have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
            (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) >>= k)
            esLoc winEp =
            runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) esLoc winEp := by
          rw [runLocCont_step]
          dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        have hSide : ∀ (la : Bool) (esS : SideESt Pt ℓ) (tbl : ℕ → SessHSt Pt ℓ),
            runSideCont C Dh encPt encT idOf ℓ q qep tL par la
              (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) >>= k)
              esS winEp tbl =
              runSideCont C Dh encPt encT idOf ℓ q qep tL par la (k none) esS winEp tbl := by
          intro la esS tbl
          rw [runSideCont_step]
          have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
              (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
            ((implFSMultiBucketAuth
              (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
              1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
              (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esS, winEp))).run (fun _ => false, tbl) =
            pure ((none, (esS, winEp)), (fun _ => false, tbl)) := by
            dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
            simp only [StateT.run_pure, simulateQ_pure]
          erw [hhead]
          rw [pure_bind]; rfl
        rw [hLoc, hSide false esM tblM, hSide true esL tblL]
        exact ih none rem' actEp esLoc esM esL winEp tblM tblL (by simpa using hmx none) (hSendMx none)
          (hinv.mono_rem (Nat.le_succ rem'))
      · exact (step_deliver_and_corrupt_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs).1.2
          x k hinv hP2 fun u actEp' esLoc' esM' esL' tblM' tblL' hinv' =>
            ih u rem' actEp' esLoc' esM' esL' none tblM' tblL' (by simpa using hmx u) (hSendMx u) hinv'
      · exact step_inject_phase1_leAdd C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs
          x k hinv hP2 fun u actEp' esLoc' esM' esL' tblM' tblL' hinv' =>
            ih u rem' actEp' esLoc' esM' esL' none tblM' tblL' (by simpa using hmx u) (hSendMx u) hinv'
      · by_cases hcorr : esLoc.g.corrAllowed P = true
        · exact (step_deliver_and_corrupt_coupled C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep tL par ks bs).2.2
            P k hinv hcorr hP2 fun u actEp' esLoc' esM' esL' tblM' tblL' hinv' =>
              ih u rem' actEp' esLoc' esM' esL' none tblM' tblL' (by simpa using hmx u) (hSendMx u) hinv'
        · simp only [Bool.not_eq_true] at hcorr
          rcases hinv.hphase1 rfl with ⟨_, hesL, _, _⟩
          subst esL
          have hwinM : esM.g.win = false := by rw [eraseSt_win hinv.herase]; exact hinv.hwin_loc
          have hcorrM : esM.g.corrAllowed P = false := by rw [eraseSt_corrAllowed hinv.herase P]; exact hcorr
          have hLoc : runLocCont C Dh encPt encT idOf ℓ q qep tL par ks
              (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esLoc winEp =
              runLocCont C Dh encPt encT idOf ℓ q qep tL par ks (k none) esLoc winEp := by
            rw [runLocCont_step]
            dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr]
            simp [hinv.habort_loc, hinv.hwin_loc, hcorr]
          have hSide : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
              runSideCont C Dh encPt encT idOf ℓ q qep tL par la
                (liftM (OracleSpec.query (spec := Fig8Dom Pt ℓ) (.inr (.inr P))) >>= k) esM winEp tbl =
                runSideCont C Dh encPt encT idOf ℓ q qep tL par la (k none) esM winEp tbl := by
            intro la tbl
            rw [runSideCont_step]
            have hhead : (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
              ((implFSMultiBucketAuth
                (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
                1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL
                (.inr (.inr P))).run (esM, winEp))).run (fun _ => false, tbl) =
              pure ((none, (esM, winEp)), (fun _ => false, tbl)) := by
              dsimp only [implFSMultiBucketAuth, QueryImpl.add_apply_inr]
              simp [hinv.habort_M, hwinM, hcorrM]
            erw [hhead]
            rw [pure_bind]; rfl
          rw [hLoc, hSide false tblM, hSide true tblL]
          exact ih none rem' actEp esLoc esM esM winEp tblM tblL (by simpa using hmx none) (hSendMx none)
            (hinv.mono_rem (Nat.le_succ rem'))

/-! ## 3. Initial State Coupling -/

private theorem mkParties_coupledInv_unalloc {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (γA γB : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ0 k0 : BitVec 256)
    (fTblLoc : ℕ → List (Pt × BitVec 256)) (fTblM : ℕ → List (Pt × BitVec 256))
    (hfLoc : ∀ t, 0 < t → fTblLoc t = []) (hfM : ∀ t, 0 < t → fTblM t = []) :
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let pLoc := mkParties (T := Pt) γA γB σ0 (fs.initSender k0) (fs.initReceiver k0)
    let pM := mkParties (T := Pt) γA γB σ0
      (Sum.inl (fs.initSender k0) : RatchetSenderState (BitVec 256) ⊕ ℕ)
      (Sum.inl (fs.initReceiver k0) : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    let gLoc : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
      { st := (fun P => match P with | .A => pLoc.1 | .B => pLoc.2), b := false }
    let gM : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
      { st := (fun P => match P with | .A => pM.1 | .B => pM.2), b := false }
    let esLoc : LocESt Pt ℓ :=
      { g := gLoc, h := { loc := { fTable := fTblLoc }, usedSlot := fun _ => false }, abort := false }
    let esM : SideESt Pt ℓ :=
      { g := gM, h := { fTable := fTblM }, abort := false }
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    CoupledInv C ℓ q qep encT idOf tL par ks bs true q (fun _ => none) esLoc esM esM none tbl0 tbl0 := by
  intro fs pLoc pM gLoc gM esLoc esM tbl0
  refine {
    habort_loc := rfl
    habort_M := rfl
    hwin_loc := rfl
    hwe := rfl
    herase := rfl
    hep_le := fun Q => by cases Q <;> simp [esLoc, gLoc]
    hep_sends := fun Q h => by exfalso; cases Q <;> simp [esLoc, gLoc] at h
    hphase1 := fun _ => ⟨rfl, rfl, rfl, fun t0 ha => (ha rfl).elim⟩
    hphase2 := fun h => Bool.noConfusion h
    hparty_id := fun P => by cases P <;> exact ⟨rfl, rfl⟩
    hparty_tcur := fun P => by cases P <;> exact ⟨rfl, rfl⟩
    hparty_base := fun P => by cases P <;> exact ⟨rfl, rfl, rfl⟩
    htcur_le := fun P => by cases P <;> simp [esLoc, gLoc, pLoc, mkParties]
    hvR_gt := fun P t ht => by
      cases P <;> simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties] at ht ⊢ <;> omega
    hvS := fun P => by
      cases P
      · simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties, Party.sendsIn]
      · dsimp only [esLoc, esM, gLoc, gM, pLoc, pM, mkParties]
        exact ⟨0, le_rfl, by simp [Party.sendsIn], fun _ => rfl, rfl⟩
    hvR := fun P t => by
      cases P
      · by_cases ht0 : t = 0 <;>
          simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties, ht0, Party.sendsIn]
      · simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties]
    hcache := fun _ => Or.inl ⟨rfl, rfl⟩
    hfuture := fun t ht => by
      have hpos : 0 < t := by
        rcases hp : Party.senderOf t with _ | _ <;> simp [esLoc, gLoc, pLoc, mkParties, hp] at ht <;> exact ht
      exact ⟨rfl, rfl, rfl, hfLoc t hpos, hfM t hpos, rfl⟩
    hact := fun _ _ _ ha => by cases ha
    hunalloc := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩
    htrans := fun _ hr => by simp [esLoc, gLoc] at hr
  }

private theorem mkParties_coupledInv_alloc0 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (ℓ q qep : ℕ) (par : Bool) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (hvg0 : validGuessBucketParAuth 1 none par 0 = true)
    (γA γB : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ0 kDummy : BitVec 256) (lam : Pt) :
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let pLoc := mkParties (T := Pt) γA γB σ0 (fs.initSender (ks 0)) (fs.initReceiver (ks 0))
    let pM := mkParties (T := Pt) γA γB σ0
      (Sum.inr 0 : RatchetSenderState (BitVec 256) ⊕ ℕ)
      (Sum.inr 0 : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    let gLoc : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
      { st := (fun P => match P with | .A => pLoc.1 | .B => pLoc.2), b := false }
    let gM : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
      { st := (fun P => match P with | .A => pM.1 | .B => pM.2), b := false }
    let esLoc : LocESt Pt ℓ :=
      { g := gLoc
        h := { loc := { fTable := Function.update (fun _ => []) 0 [(lam, ks 0)] }
               usedSlot := Function.update (fun _ => false) 0 true }
        abort := false }
    let esM : SideESt Pt ℓ :=
      { g := gM
        h := { fTable := Function.update (fun _ => []) 0 [(lam, kDummy)]
               sessions := Function.update (fun _ => []) 0 [lam] }
        abort := false }
    let actEp0 : ℕ → Option (RatchetSenderState (BitVec 256) × RatchetReceiverState (BitVec 256) (BitVec 256)) :=
      fun t => if t = 0 then some (fs.initSender (ks 0), fs.initReceiver (ks 0)) else none
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    CoupledInv C ℓ q qep encT idOf none par ks bs true q actEp0 esLoc esM esM none tbl0 tbl0 := by
  intro fs pLoc pM gLoc gM esLoc esM actEp0 tbl0
  refine {
    habort_loc := rfl
    habort_M := rfl
    hwin_loc := rfl
    hwe := rfl
    herase := rfl
    hep_le := fun Q => by cases Q <;> simp [esLoc, gLoc]
    hep_sends := fun Q h => by exfalso; cases Q <;> simp [esLoc, gLoc] at h
    hphase1 := fun _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    hphase2 := fun h => Bool.noConfusion h
    hparty_id := fun P => by cases P <;> exact ⟨rfl, rfl⟩
    hparty_tcur := fun P => by cases P <;> exact ⟨rfl, rfl⟩
    hparty_base := fun P => by cases P <;> exact ⟨rfl, rfl, rfl⟩
    htcur_le := fun P => by cases P <;> simp [esLoc, gLoc, pLoc, mkParties]
    hvR_gt := fun P t ht => by
      cases P <;> simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties] at ht ⊢ <;> omega
    hvS := fun P => by
      cases P
      · simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties, Party.sendsIn]
      · dsimp only [esLoc, esM, gLoc, gM, pLoc, pM, mkParties]
        exact ⟨0, le_rfl, by simp [Party.sendsIn], fun _ => rfl, by simp [actEp0, sIdxMain, healEpoch]⟩
    hvR := fun P t => by
      cases P
      · by_cases ht0 : t = 0 <;>
          simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties, actEp0, sIdxMain, healEpoch, ht0, Party.sendsIn]
      · simp [esLoc, esM, gLoc, gM, pLoc, pM, mkParties]
    hcache := fun _ => Or.inl ⟨rfl, rfl⟩
    hfuture := fun t ht => by
      have hne : t ≠ 0 := by
        rcases hp : Party.senderOf t with _ | _ <;> simp [esLoc, gLoc, pLoc, mkParties, hp] at ht <;> omega
      exact ⟨by simp [actEp0, hne], rfl, rfl,
        by simp [esLoc, hne], by simp [esM, hne], by simp [esM, hne]⟩
    hact := fun t0 ssLoc rsLoc ha => by
      by_cases ht0 : t0 = 0
      · subst ht0
        simp only [actEp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at ha
        rcases ha with ⟨rfl, rfl⟩
        refine ⟨by simp [healEpoch], Nat.zero_le _, hvg0, by simp [esLoc, gLoc, pLoc, mkParties],
          ?_, fun _ => rfl, rfl⟩
        simpa [sIdxMain, healEpoch, esM, tbl0] using
          activeSessInv_init C ℓ encT idOf true (ks 0) (bs 0)
      · simp [actEp0, ht0] at ha
    hunalloc := fun sIdx _ hun => by
      have hne0 : sIdx ≠ 0 := by
        intro h0
        subst h0
        have := hun 0 (by simp [healEpoch]) (by simp [sIdxMain, healEpoch])
        simp [actEp0] at this
      exact ⟨by simp [esLoc, hne0], rfl, rfl, fun _ => rfl⟩
    htrans := fun _ hr => by simp [esLoc, gLoc] at hr
  }

/-! ## 4. Glue Theorem (`localAuthBucketMainPar_le_multiSessRealWinProb_split`) -/

attribute [local irreducible] redFSAuthMultiBucketShallow in
private theorem advBr_offRange
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (multiSessPubToAD protoSignalCodec
      ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
          true la tL par).eval (fun _ => A) ())).IsQueryBoundP
      (fun t => sessOffRange (mSessMain q qep tL) t = true) 0 := by
  refine multiSessPubToAD_offRange protoSignalCodec
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        true la tL par).eval (fun _ => A) ()) (mSessMain q qep tL) ?_
  refine isQueryBoundP_sessOffRange_of_ge_zero (mSessMain q qep tL) _ fun idx hidx => ?_
  exact (redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero ℓ Pt C Dh encPt encT idOf lam
    q B0 qep true la tL par A hq idx (Or.inl (by dsimp [mSessMain] at hidx; rwa [Nat.mul_comm] at hidx))).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx

private theorem localAuthBucketMainSlot_eq_init {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (ℓ q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ks : ℕ → BitVec 256) (A : OracleComp (Fig8Dom Pt ℓ) Bool) :
    simulateQ (keySlotFixedImpl ks)
      (localAuthBucketMainSlot (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 q qep (mSessMain q qep tL) tL par A) =
    (do
      let kr ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let kc ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let p ← simulateQ (keySlotFixedImpl ks)
        ((rootLocalMainSlot (rootPRNG C.F encPt) 1 q qep (mSessMain q qep tL) tL par 0 false lam
          ((rootPRNG C.F encPt).init kr)).run {})
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let pLoc := mkParties (T := Pt) ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) p.1.1
        (fs.initSender p.1.2) (fs.initReceiver p.1.2)
      let g : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
        { st := (fun P => match P with | .A => pLoc.1 | .B => pLoc.2), b := false }
      runLocCont C Dh encPt encT idOf ℓ q qep tL par ks A { g, h := p.2 } none) := by
  unfold localAuthBucketMainSlot initLocalMainSlot runLocCont mainParOut
  simp only [StateT.run_bind, StateT.run_pure, stateT_lift_run, bind_assoc, pure_bind]
  rw [simulateQ_bind, sim_sampleT_fixed (α := BitVec 256) ks]; refine bind_congr fun kr => ?_
  rw [simulateQ_bind, sim_sampleT_fixed (α := BitVec 256) ks]; refine bind_congr fun kc => ?_
  rw [simulateQ_bind]; rfl

private theorem redFSAuthMultiBucket_eq_init {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (ℓ q qep : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool) (tbl0 : ℕ → SessHSt Pt ℓ)
    (A : OracleComp (Fig8Dom Pt ℓ) Bool) :
    Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
        (redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep true la tL par A)).run
        (fun _ => false, tbl0) =
    (do
      let kr ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let kc ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let p ← (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          ((rootFSMultiBucketAuth (rootPRNG C.F encPt) 1 qep tL par 0 false lam
            ((rootPRNG C.F encPt).init kr)).run {})).run (fun _ => false, tbl0)
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let r := regSessOptMultiBucket (q + 1) true tL 0 p.1.1.2.2 p.1.2
      let ssv0 : RatchetSenderState (BitVec 256) ⊕ ℕ := match r.1 with
        | none => .inl (fs.initSender p.1.1.2.1)
        | some sIdx => .inr sIdx
      let rsv0 : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ := match r.1 with
        | none => .inl (fs.initReceiver p.1.1.2.1)
        | some sIdx => .inr sIdx
      let pM := mkParties (T := Pt) ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) p.1.1.1 ssv0 rsv0
      let g0 : Ctx _ Pt _ _ _ (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
        { st := (fun P => match P with | .A => pM.1 | .B => pM.2), b := false }
      Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) (do
        let (_, es, we) ← (simulateQ (implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) 1 qep true tL par la)
          1 qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip true tL) A).run
          ({ g := g0, h := r.2, abort := false }, none)
        if la then return es.h.lfWin else return mainParOut 3 tL par es we)).run p.2) := by
  unfold redFSAuthMultiBucket initFSMultiBucketAuth mainParOut
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    stateT_lift_run, ↓reduceIte, bind_assoc, pure_bind]
  rw [simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256)]
  simp only [bind_assoc, pure_bind, map_bind]
  refine bind_congr fun kr => ?_
  rw [simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256)]
  simp only [bind_assoc, pure_bind, map_bind]
  refine bind_congr fun kc => ?_
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  refine bind_congr fun p => ?_
  congr 1; congr 1; congr 1
  refine bind_congr fun ⟨_, es, we⟩ => ?_
  cases la <;> cases we <;> rfl

attribute [local irreducible] redFSAuthMultiBucketShallow in
theorem localAuthBucketMainPar_le_multiSessRealWinProb_split
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
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
            true la tL par).eval (fun _ => A) ())
    𝒟[localAuthBucketMainPar (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf AdvBr false +
        multiSessRealWinProb C ℓ encT idOf AdvBr true := by
  intro AdvBr
  let M_sess := mSessMain q qep tL
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  have hA_q : A.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q := by
    refine hq.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hSendOk : A.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 := by
    refine hsh.of_imp fun t ht => ?_
    rcases t with _ | ((((_ | _) | _) | _) | _) <;> exact ht
  have hoff : ∀ la, (AdvBr la).IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0 :=
    fun la => advBr_offRange ℓ Pt C Dh encPt encT idOf lam q B0 qep la tL par A hq
  rw [localAuthBucketMainPar_eq_eager_ks cka prng fs lam (0 : BitVec 256) 1 q qep M_sess tL par A]
  suffices hK : ∀ (ks : ℕ → BitVec 256) (bs : ℕ → Bool),
      LeAdd
        (simulateQ (keySlotFixedImpl ks) (localAuthBucketMainSlot cka prng fs lam 1 q qep M_sess tL par A))
        (Prod.fst <$> (simulateQ (sessLift (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
            (AdvBr false)).run (fun i => hInit (bs i) (.seed (ks i))))
        (Prod.fst <$> (simulateQ (sessLift (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
            (AdvBr true)).run (fun i => hInit (bs i) (.seed (ks i)))) by
    have hStep : LeAdd
        (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
          simulateQ (keySlotFixedImpl ks) (localAuthBucketMainSlot cka prng fs lam 1 q qep M_sess tL par A))
        (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
            Prod.fst <$> (simulateQ (sessLift (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
                (AdvBr false)).run (fun i => hInit (bs i) (.seed (ks i))))
        (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
          sampleVec ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
            Prod.fst <$> (simulateQ (sessLift (fsImpl (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
                (AdvBr true)).run (fun i => hInit (bs i) (.seed (ks i)))) :=
      leAdd_bind _ fun ks _ => leAdd_bind_dummy_loc _ fun bs _ => hK ks bs
    exact hStep.trans (add_le_add
      (multiFsEager_le_real (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps M_sess (0 : BitVec 256)
        false (AdvBr false) (hoff false))
      (multiFsEager_le_real (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps M_sess (0 : BitVec 256)
        true (AdvBr true) (hoff true)))
  intro ks bs
  let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
  have hSideEq : ∀ la : Bool,
      Prod.fst <$> (simulateQ (sessLift (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          (AdvBr la)).run tbl0 =
      Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
          (redFSAuthMultiBucket (q + 1) cka prng fs lam 1 qep true la tL par A)).run
          (fun _ => false, tbl0) := by
    intro la
    dsimp only [AdvBr]
    rw [redFSAuthMultiBucket_main_atomic_eq ℓ Pt C Dh encPt encT idOf lam q B0 qep hB0 la tL par A hq hsh,
      simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl]
  rw [hSideEq false, hSideEq true,
    localAuthBucketMainSlot_eq_init C Dh encPt encT idOf lam ℓ q qep tL par ks A,
    redFSAuthMultiBucket_eq_init C Dh encPt encT idOf lam ℓ q qep false tL par tbl0 A,
    redFSAuthMultiBucket_eq_init C Dh encPt encT idOf lam ℓ q qep true tL par tbl0 A]
  refine leAdd_bind _ fun kr _ => leAdd_bind _ fun kc _ => ?_
  cases tL with
  | some l =>
    have hltH : 0 < healEpoch (some l) := by simp [healEpoch]
    have hneH : ¬(0 = healEpoch (some l)) := by simp [healEpoch]
    have hvgF : validGuessBucketParAuth 1 (some l) par 0 = false := by
      simp [validGuessBucketParAuth, lastLeakGuessAdmissible, healedBy]
    dsimp only [rootLocalMainSlot, rootFSMultiBucketAuth]
    simp only [hvgF, hltH, hneH, Option.isSome_some, beq_iff_eq, Bool.false_eq_true, Bool.true_and,
      Bool.or_false, not_true_eq_false, ↓reduceIte, Nat.not_lt_zero, decide_false,
      regSessOptMultiBucket, StateT.run_pure, simulateQ_pure, pure_bind]
    exact phase1_coupling_leAdd C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep (some l) par ks bs
      A q (fun _ => none) _ _ _ none tbl0 tbl0 hA_q hSendOk
      (mkParties_coupledInv_unalloc C encT idOf ℓ q qep (some l) par ks bs
        (cka.initA kc) (cka.initB kc)
        ((prng.up (prng.init kr) lam).1) ((prng.up (prng.init kr) lam).2)
        (fun _ => []) (fun _ => []) (fun _ _ => rfl) (fun _ _ => rfl))
  | none =>
    have hMPos : decide (0 < mSessMain q qep none) = true := by
      rw [decide_eq_true_eq]; dsimp [mSessMain, healEpoch]
      exact Nat.mul_pos (Nat.succ_pos q) (Nat.succ_pos (qep + 1))
    by_cases hvg0 : validGuessBucketParAuth 1 none par 0 = true
    · have hSlot0 : simulateQ (keySlotFixedImpl ks)
          ((sampleOrSlot (T := Pt) (Sig := BitVec 256) (K := BitVec 256) (I := Pt)
            (mSessMain q qep none) true 0).run {}) =
          pure (ks 0, { usedSlot := Function.update (fun _ => false) 0 true }) := by
        have h1 : (sampleOrSlot (T := Pt) (Sig := BitVec 256) (K := BitVec 256) (I := Pt)
            (mSessMain q qep none) true 0).run {} =
            ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec (BitVec 256))) (.inr ⟨0, ()⟩)) :
                OracleComp (unifSpec + multiSessSpec (keySlotSpec (BitVec 256))) _) >>=
              fun k => Pure.pure ((k : BitVec 256), { usedSlot := Function.update (fun _ => false) 0 true })) := by
          simp only [sampleOrSlot, hMPos, Bool.and_self, Bool.not_false, ↓reduceIte,
            StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]; rfl
        rw [h1]; erw [simulateQ_query_bind]; rfl
      dsimp only [rootLocalMainSlot, rootFSMultiBucketAuth, lookupLocalMainSlotF, lookupMultiBucketF]
      simp only [hvg0, Option.isSome_none, Bool.false_eq_true, Bool.false_and, Bool.or_false,
        Bool.not_false, Nat.not_lt_zero, decide_false, not_false_eq_true, ↓reduceIte,
        sIdxMain, healEpoch, Nat.sub_self, Nat.mul_zero, List.lookup_nil,
        StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure,
        stateT_lift_run, bind_assoc, pure_bind]
      rw [simulateQ_bind, hSlot0,
        simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256),
        simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256)]
      simp only [simulateQ_pure, StateT.run_pure, regSessOptMultiBucket, regSessMultiBucket,
        List.not_mem_nil, List.length_nil, Nat.add_zero, ↓reduceIte, bind_assoc, pure_bind, map_bind]
      refine leAdd_bind_dummy_loc _ fun kDummy _ => ?_
      exact phase1_coupling_leAdd C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep none par ks bs
        A q _ _ _ _ none tbl0 tbl0 hA_q hSendOk
        (mkParties_coupledInv_alloc0 C encT idOf ℓ q qep par ks bs hvg0
          (cka.initA kc) (cka.initB kc) ((prng.up (prng.init kr) lam).1) kDummy lam)
    · simp only [Bool.not_eq_true] at hvg0
      dsimp only [rootLocalMainSlot, rootFSMultiBucketAuth, lookupLocalMainSlotF, lookupMultiBucketF,
        sampleOrSlot]
      simp only [hvg0, Option.isSome_none, Bool.false_eq_true, Bool.false_and, Bool.or_false,
        Bool.not_false, healEpoch, Nat.not_lt_zero,
        decide_false, not_false_eq_true, ↓reduceIte, List.lookup_nil,
        StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure,
        stateT_lift_run, bind_assoc, pure_bind]
      rw [simulateQ_bind, sim_sampleT_fixed (α := BitVec 256) ks,
        simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256),
        simulateQ_bind, StateT.run_bind, sim_sampleT_pubFs_run (α := BitVec 256)]
      simp only [simulateQ_pure, StateT.run_pure, regSessOptMultiBucket, bind_assoc, pure_bind, map_bind]
      refine leAdd_bind _ fun kSample _ => ?_
      exact phase1_coupling_leAdd C Dh hDh hD encPt encT hinj hdum idOf ℓ hℓ q qep none par ks bs
        A q (fun _ => none) _ _ _ none tbl0 tbl0 hA_q hSendOk
        (mkParties_coupledInv_unalloc C encT idOf ℓ q qep none par ks bs
          (cka.initA kc) (cka.initB kc)
          ((prng.up (prng.init kr) lam).1) kSample
          (Function.update (fun _ => []) 0 [(lam, kSample)])
          (Function.update (fun _ => []) 0 [(lam, kSample)])
          (fun t ht => by simp [Nat.ne_of_gt ht])
          (fun t ht => by simp [Nat.ne_of_gt ht]))

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSplit
