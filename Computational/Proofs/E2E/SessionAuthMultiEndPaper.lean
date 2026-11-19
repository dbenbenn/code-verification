/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.E2E.SessionAuthWireEnd
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.SM.GameProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.E2E.SpkHop1A
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.ReductionDsl.SM.Theorem1
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow
import Computational.Proofs.SessionCostedFig8.Bundles
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Multi-Session Ideal-Cutoff (`multiSessEndWinProb = 0`) Proofs for `DeliverForgePaper`

Proves that at the ideal FS-AEAD hopping endpoint (`Thm5.hp cut cut la`, with
`cut = authHopCutoff maxForwardJumps qR la` and `min (2 * q) (q + 2) ≤ qR`), all three
multi-session Stage-2 `DeliverForgePaper` FS-AEAD reductions output `true` with probability `0`:
1. `multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero` (`B1` and `B2`)
2. `multiSessEndWinProb_redFSAuthDFPaperMulti_eq_zero` (single-epoch Stage-2)
3. `multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero` (`(tL, par)`-bucket Stage-2, `2 ≤ Δbucket`)-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEnd

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM.Construction (
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessPubFsAdv multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_isQueryBoundP_sessQueryAt)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessEndWinProb)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGen)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  fwd lazyInit lazyInit_run_none' lazyInit_run_some'
  sessLift sessLift_inl sessLift_inr sessLiftCore multiSessSpec)
open Computational.Proofs.E2E.SessionAuthMultiPot (
  redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
  redFSAuthDFPaperMulti_sess_isQueryBoundP
  redFSAuthDFPaperMultiBucket_sess_isQueryBoundP)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames.SM.Construction (
  Header Mode FSMultiState FSMultiDFBucketState FSMultiBook
  liftFSMulti liftFSMultiDFBucket lookupMultiF lookupMultiDFBucketF
  regSessMulti regSessOptMulti regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMulti rootFSMultiDFBucketPaper hooksFSMulti hooksFSMultiDFBucketPaper
  initFSMultiRaw initFSMultiDFBucketPaper runFSMultiDFPaper
  inStage2BucketGen bucketAuthCfgGen postLeakDFBucket)
open _root_.CryptoGames.SM.Engine (
  VP EState Hooks liftH abortE vSend vRecv commitE
  transmitE challE deliverE injectE coinsE authOut)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  deliverForgeE corrEPaper corrEPaperBucket corrEShiftedPaper
  transmitEBucket challEBucket implEDFPaper implEDFShiftedPaperGen
  implEDFPaperBucketRaw implEDFPaperBucket engRunDFPaperBucket withWinEpDF authOutBucket)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionWire (
  hpIdeal kind_hpIdeal sessQueryAt allSessions_hp_eq_hpIdeal_main allSessions_hp_eq_hpIdeal_la)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalCiphertextWithSalt32 lIdeal lAeadR lChainPRG lPubOf)
open _root_.CryptoGames.FSAEAD.Thm5 (
  HState HSt DG decIdx encIdxWith genUpTo receiveH
  transmitHWith challengeHWith corruptSenderH corruptReceiverH deliverH injectH
  getH getH_run onH modifyH modifyH_run hInit)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (
  mem_support_genUpTo mem_support_encIdx mem_support_senderKey
  mem_support_receiveH_none mem_support_receiveH_some)
open _root_.CryptoGames.SM.Construction.AuthL11 (evalDist_bind_eq_zero)


open _root_.CryptoGames.FSAEAD (ReceiveResult withPub)
open _root_.CryptoGames.FSAEAD.Thm5 (Slot)
open _root_.CryptoGames.SM (Config GameState Pos Record healedBy)
open _root_.CryptoGames.SM.Construction (PartyState mkParties)
open _root_.CryptoGames.SM.Engine (Ctx Policy)

section PaperMultiEndZero

set_option linter.unusedSimpArgs false
variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## 1. `la = true`: `hooksFSMulti` & `implEDFPaper` Preserve `lfWin = false` -/

private theorem pubQuery_any_eq_hs_la
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    {Sig K I : Type}
    (hs : FSMultiState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32)) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2 = hs)
      ((liftFSMulti sIdx
        (query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256) (Header Pt)
          (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) (Sum.inr q₀))).run hs) := by
  rw [query_eq_liftM, ← lift_inr_query_eq, liftFSMulti_run_query_eq]
  exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => PubLaSafe.pure rfl

private theorem hooksFSMulti_fsRecv_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (mo : Mode) (gMain : Bool)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (t0 : ℕ)
    (rsv : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlf : hs.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo gMain true).fsRecv
        ctx P t0 rsv hdr e rec).run hs) := by
  dsimp only [hooksFSMulti]
  cases rsv with
  | inl rs =>
    (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
  | inr sIdx =>
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    generalize hmatch : List.find? _ ((hs.book sIdx).getD {}).fsTrans = matched
    cases matched with
    | some m0 =>
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_true, Option.isSome_some]
      refine PubLaSafe.bind
        (pubQuery_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inr (hdr, e))) hs) ?_
      rintro ⟨res, hs₁⟩ rfl
      cases res with
      | none => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
      | some rr =>
        cases rr with
        | rejected => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
        | accepted idx mo' =>
          simp only [StateT.run_bind, StateT.run_get, pure_bind,
            Option.isNone_some, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_modify]
          cases mo' <;> cases rec <;> (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
    | none =>
      by_cases hguard : (!(healedBy ctx.tL (2 + Δcka) t0) && !((hs.book sIdx).getD {}).sCorr) = true
      · simp only [Option.isNone_none, Bool.true_and, hguard, ↓reduceIte,
          StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_false]
        apply PubLaSafe.pure; exact hlf
      · have hgf : (!(healedBy ctx.tL (2 + Δcka) t0) && !((hs.book sIdx).getD {}).sCorr) = false :=
          Bool.not_eq_true _ |>.mp hguard
        simp only [Option.isNone_none, Bool.true_and, hgf, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_true, Option.isSome_none]
        erw [liftFSMulti_run_query_eq]
        refine PubLaSafe.bind
          (pubQuery_inject_not_accepted_la C ℓ encT idOf N sIdx hdr e hs) ?_
        rintro ⟨res, hs₁⟩ ⟨rfl, hnotacc⟩
        cases res with
        | none => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
        | some rr =>
          cases rr with
          | rejected => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
          | accepted idx mo' => exact False.elim (hnotacc idx mo' rfl)

private theorem hooksFSMulti_nonRecv_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (mo : Mode) (gMain : Bool)
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlf : hs.lfWin = false) :
    (∀ ctx P t0 γ σr r,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo gMain true).startSend
          ctx P t0 γ σr r).run hs)) ∧
    (∀ ctx P t0 γ σr Tn,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo gMain true).startRecv
          ctx P t0 γ σr Tn).run hs)) ∧
    (∀ ctx P t0 ssv hdr m pair,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo gMain true).fsSend
          ctx P t0 ssv hdr m pair).run hs)) ∧
    (∀ ctx P vp,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo gMain true).reveal
          ctx P vp).run hs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx P t0 γ σr r
    dsimp only [hooksFSMulti]
    have hbody : ∀ (coins : BitVec 256),
        PubLaSafe C ℓ encT idOf N (fun p : _ × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) => p.2.lfWin = false)
          ((do
            let c := (dhScheme Dh).send γ coins
            let (σ', k, sid) ← rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) mo t0 c.2.2 σr
            let optIdx ← regSessOptMulti sid
            modify fun (s : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) => { s with cache := Function.update s.cache t0 (some (c.2.1, σ', k, optIdx)) }
            let ssv : CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ := match optIdx with
              | none => .inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k)
              | some sIdx => .inr sIdx
            return some (c.1, c.2.1, σ', ssv)).run hs) := by
      intro coins
      rw [StateT.run_bind]
      have hrt : PubLaSafe C ℓ encT idOf N (fun p : (BitVec 256 × BitVec 256 × Option Pt) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) => p.2.lfWin = false) ((rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) mo t0 ((dhScheme Dh).send γ coins).2.2 σr).run hs) := by
        unfold rootFSMulti
        split_ifs
        · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
        · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
          exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
            PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
              by (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
        · simp only [StateT.run_bind, lookupMultiF, StateT.run_get, pure_bind]
          cases hs.table.lookup ((dhScheme Dh).send γ coins).2.2 with
          | some k => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
          | none =>
            simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
            exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
              by simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]; apply PubLaSafe.pure; exact hlf
        · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
          exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
            by (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
        · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
      refine PubLaSafe.bind hrt fun ⟨⟨σ', k, sid⟩, hs₂⟩ hlf₂ => ?_
      rw [StateT.run_bind]
      refine PubLaSafe.bind (P := fun p => p.2.lfWin = false) ?_ fun ⟨_, hs₃⟩ hlf₃ => ?_
      · cases sid with
        | none => (simp only [regSessOptMulti, StateT.run_pure]; apply PubLaSafe.pure; exact hlf₂)
        | some ik =>
          simp only [regSessOptMulti, regSessMulti, StateT.run_map, map_eq_bind_pure_comp,
            StateT.run_bind, StateT.run_get, pure_bind]
          split_ifs
          · (simp only [StateT.run_pure, bind_pure_comp, map_pure]; apply PubLaSafe.pure; exact hlf₂)
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
            apply PubLaSafe.pure; exact hlf₂
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
        apply PubLaSafe.pure; exact hlf₃
    cases r with
    | some c =>
      rw [StateT.run_bind, StateT.run_pure, pure_bind]
      exact hbody c
    | none =>
      simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
      exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun coins _ => hbody coins
  · intro ctx P t0 γ σr Tn
    dsimp only [hooksFSMulti]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    have hnone_branch : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        ((if gMain = true then pure (some none)
          else if (mo.auth && decide (t0 = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let kk := (dhScheme Dh).receive γ Tn
              let __x ← lookupMultiF kk.2
              let sIdx ← regSessMulti kk.2
              pure (some (some (kk.1, ((CryptoGames.Ratchet.rootPRNG C.F encPt).up σr kk.2).1,
                (Sum.inr sIdx : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))))
          else pure (some none)).run hs) := by
      split_ifs
      · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
      · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
      · simp only [StateT.run_bind, lookupMultiF, StateT.run_get, pure_bind]
        refine PubLaSafe.bind (P := fun p => p.2.lfWin = false) ?_ fun ⟨_, hs₁⟩ hlf₁ => ?_
        · cases hs.table.lookup ((dhScheme Dh).receive γ Tn).2 with
          | some _ => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
          | none =>
            simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
            exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
              by simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]; apply PubLaSafe.pure; exact hlf
        · simp only [StateT.run_bind, regSessMulti, StateT.run_get, pure_bind]
          split_ifs
          · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf₁)
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
            apply PubLaSafe.pure; exact hlf₁
      · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
    cases hcache : hs.cache t0 with
    | none => simpa only [hcache] using hnone_branch
    | some val =>
      rcases val with ⟨Tc, σc, k, optIdx⟩
      by_cases hTc : Tc = Tn
      · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure]
        apply PubLaSafe.pure; exact hlf
      · simpa only [hcache, hTc, ↓reduceIte] using hnone_branch
  · intro ctx P t0 ssv hdr m pair
    dsimp only [hooksFSMulti]
    cases ssv with
    | inl _ => (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
    | inr sIdx =>
      rw [StateT.run_bind, StateT.run_get, pure_bind]
      simp only [↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_false, ↓reduceIte]
        apply PubLaSafe.pure; exact hlf
      · simp only [StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases pair with
        | some pm =>
          refine PubLaSafe.bind
            (pubQuery_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inl (.inl (.inl (.inr (hdr, pm.1, pm.2)))))) hs) ?_
          rintro ⟨e?, _⟩ rfl
          cases e? <;>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
            (apply PubLaSafe.pure; exact hlf)
        | none =>
          refine PubLaSafe.bind
            (pubQuery_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inl (.inl (.inl (.inl (hdr, m)))))) hs) ?_
          rintro ⟨e?, _⟩ rfl
          cases e? <;>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
            (apply PubLaSafe.pure; exact hlf)
  · intro ctx P vp
    dsimp only [hooksFSMulti]
    cases vp.vS with
    | none =>
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      split_ifs <;> (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
    | some ssv =>
      cases ssv with
      | inl _ =>
        simp only [StateT.run_bind, StateT.run_pure, pure_bind]
        split_ifs <;> (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact hlf)
      | inr _ =>
        simp only [↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind]
        apply PubLaSafe.pure; exact hlf

private theorem liftH_run_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Vγ T VR VSg VRg M E HS α : Type}
    (x : _root_.CryptoGames.SM.Engine.HM tspec HS α)
    (es : EState (VP Vγ T VR VSg VRg) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem implEDFPaper_step_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka qep : ℕ) (mo : Mode) (q_in : _) (es : _) (hlf : es.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
      ((implEDFPaper
        (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo false true)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy q_in).run es) := by
  have hvSend : ∀ s₁ P vp m pair r
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((liftH (vSend (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo false true)
          s₁ P vp m pair r)).run es₀) := by
    intro s₁ P vp m pair r es₀ hlf₀
    rw [liftH_run_eq]
    refine PubLaSafe.bind (P := fun p => p.2.lfWin = false) ?_ fun ⟨_, _⟩ hlf_vs =>
      PubLaSafe.pure hlf_vs
    unfold vSend
    by_cases hsIn : vp.id.sendsIn (vp.tcur + 1) = true
    · simp only [hsIn, ↓reduceIte, pure_bind]
      rw [StateT.run_bind]
      refine PubLaSafe.bind
        ((hooksFSMulti_nonRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false es₀.h hlf₀).1
          s₁ P (vp.tcur + 1) vp.γ vp.root r) fun ⟨res, hs₁⟩ hlf₁ => ?_
      cases res with
      | none => dsimp only; simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
      | some out =>
        rcases out with ⟨γ', T', σ', ss⟩
        dsimp only
        rw [StateT.run_bind]
        refine PubLaSafe.bind
          ((hooksFSMulti_nonRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false hs₁ hlf₁).2.2.1
            s₁ P (vp.tcur + 1) ss (vp.tcur + 1, some T') m pair) fun ⟨res2, _⟩ hlf₂ => ?_
        cases res2 <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
    · have hsIn_f : vp.id.sendsIn (vp.tcur + 1) = false := Bool.not_eq_true _ |>.mp hsIn
      simp only [hsIn_f, Bool.false_eq_true, ↓reduceIte, pure_bind]
      cases vp.vS with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀
      | some v =>
        rw [StateT.run_bind]
        refine PubLaSafe.bind
          ((hooksFSMulti_nonRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false es₀.h hlf₀).2.2.1
            s₁ P vp.tcur v (vp.tcur, vp.curCkaMsg) m pair) fun ⟨res2, _⟩ hlf₂ => ?_
        cases res2 <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
  have hvRecv : ∀ s₁ P vp c rec
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((liftH (vRecv (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo false true)
          s₁ P vp c rec)).run es₀) := by
    intro s₁ P vp c rec es₀ hlf₀
    rw [liftH_run_eq]
    refine PubLaSafe.bind (P := fun p => p.2.lfWin = false) ?_ fun ⟨_, _⟩ hlf_vr =>
      PubLaSafe.pure hlf_vr
    unfold vRecv
    simp only [StateT.run_bind]
    by_cases hg0 : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
    · simp only [hg0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf₀
    · simp only [Bool.not_eq_true _ |>.mp hg0, Bool.false_eq_true, ↓reduceIte]
      by_cases hg1 : (c.1.1 : ℕ) = vp.tcur + 1
      · simp only [hg1, ↓reduceIte]
        cases c.1.2 with
        | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hlf₀
        | some Tn =>
          simp only [bind_assoc]
          rw [StateT.run_bind]
          refine PubLaSafe.bind
            ((hooksFSMulti_nonRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false es₀.h hlf₀).2.1
              s₁ P _ vp.γ vp.root Tn) fun ⟨res, hs₁⟩ hlf₁ => ?_
          cases res with
          | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hlf₁
          | some inner =>
            cases inner with
            | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hlf₁
            | some triple =>
              rcases triple with ⟨γ', σ', rsv⟩
              simp only [pure_bind, Function.update_self]
              rw [StateT.run_bind]
              refine PubLaSafe.bind
                (hooksFSMulti_fsRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false
                  s₁ P _ rsv _ _ rec hs₁ hlf₁) fun ⟨res2, _⟩ hlf₂ => ?_
              cases res2 with
              | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂
              | some r_in => cases r_in <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
      · simp only [hg1, ↓reduceIte, pure_bind]
        cases vp.vR c.1.1 with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀
        | some v =>
          rw [StateT.run_bind]
          refine PubLaSafe.bind
            (hooksFSMulti_fsRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false
              s₁ P c.1.1 v c.1 c.2 rec es₀.h hlf₀) fun ⟨res, _⟩ hlf₂ => ?_
          cases res with
          | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂
          | some r_in => cases r_in <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
  rcases q_in with n | ((q14 | P) | ⟨P, c, c'⟩)
  · simp only [implEDFPaper, QueryImpl.add_apply, coinsE, stateT_lift_run]
    exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => PubLaSafe.pure hlf
  · rcases q14 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩)
    · simp only [implEDFPaper, QueryImpl.add_apply, transmitE, StateT.run_bind,
        StateT.run_get, pure_bind]
      by_cases h0 : (es.abort || es.g.win) = true
      · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
        cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | some s₁ =>
          by_cases h1 : mo.policy.leakDoom es.g s₁ = true
          · simp only [h1, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact PubLaSafe.pure hlf
          · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
            refine PubLaSafe.bind (hvSend s₁ P (s₁.st P) m none r es hlf) fun ⟨res, _⟩ hlf₁ => ?_
            cases res <;>
              (simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
               exact PubLaSafe.pure hlf₁)
    · simp only [implEDFPaper, QueryImpl.add_apply, challE, StateT.run_bind,
        StateT.run_get, pure_bind]
      by_cases h0 : (es.abort || es.g.win) = true
      · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
        cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | some s₁ =>
          by_cases h1 : (!(s₁.safeCh (2 + Δcka) P) || !((mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P))) = true
          · simp only [h1, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : mo.policy.leakDoom es.g s₁ = true
            · simp only [h2, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
              exact PubLaSafe.pure hlf
            · simp only [Bool.not_eq_true _ |>.mp h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
              refine PubLaSafe.bind (hvSend s₁ P (s₁.st P) _ (some (m₀, m₁)) r es hlf)
                fun ⟨res, _⟩ hlf₁ => ?_
              cases res <;>
                (simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
                 exact PubLaSafe.pure hlf₁)
    · simp only [implEDFPaper, QueryImpl.add_apply, deliverE, StateT.run_bind,
        StateT.run_get, pure_bind]
      by_cases h0 : (es.abort || es.g.win) = true
      · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
        cases es.g.inTransit P.other c with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | some r =>
          rw [StateT.run_bind]
          refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c (some r) es hlf)
            fun ⟨res, _⟩ hlf₁ => ?_
          cases res with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact PubLaSafe.pure hlf₁
          | some r_in =>
            cases r_in with
            | none =>
              by_cases hm : ((mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).deliverWin && es.g.mustBeCorrect maxForwardJumps P r) = true
              · simp only [hm, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
                exact PubLaSafe.pure hlf₁
              · simp only [Bool.not_eq_true _ |>.mp hm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
                exact PubLaSafe.pure hlf₁
            | some _ =>
              simp only [commitE, liftH_run_eq, hooksFSMulti, StateT.run_bind, StateT.run_pure,
                pure_bind, StateT.run_modify]
              exact PubLaSafe.pure hlf₁
    · simp only [implEDFPaper, QueryImpl.add_apply, injectE, StateT.run_bind,
        StateT.run_get, pure_bind]
      by_cases h0 : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
      · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c none es hlf)
          fun ⟨res, _⟩ hlf₁ => ?_
        cases res with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact PubLaSafe.pure hlf₁
        | some r_in =>
          cases r_in with
          | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            by_cases h1 : qep + 1 < t'
            · simp only [h1, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf₁
            · simp only [h1, ↓reduceIte]
              by_cases h2 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · simp only [h2, ↓reduceIte, commitE, liftH_run_eq, hooksFSMulti, StateT.run_bind,
                  StateT.run_pure, pure_bind, StateT.run_modify]
                exact PubLaSafe.pure hlf₁
              · simp only [Bool.not_eq_true _ |>.mp h2, Bool.false_eq_true, ↓reduceIte]
                by_cases h3 : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull t' = true
                · simp only [h3, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
                  exact PubLaSafe.pure hlf₁
                · simp only [Bool.not_eq_true _ |>.mp h3, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
                  exact PubLaSafe.pure hlf₁
  · simp only [implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases h0 : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
    · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
      · simp only [h1, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
        exact PubLaSafe.pure hlf
      · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          liftH_run_eq, bind_assoc]
        refine PubLaSafe.bind
          ((hooksFSMulti_nonRecv_lfWin_la C ℓ Dh encPt encT idOf N Δcka mo false es.h hlf).2.2.2
            es.g P (es.g.st P)) fun ⟨res, _⟩ hlf₁ => ?_
        cases res <;>
          (simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure]
           exact PubLaSafe.pure hlf₁)
  · simp only [implEDFPaper, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases h0 : (es.abort || es.g.win) = true
    · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
      cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some r =>
        by_cases h0b : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [h0b, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [Bool.not_eq_true _ |>.mp h0b, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c' none es hlf)
            fun ⟨res, _⟩ hlf₁ => ?_
          cases res with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact PubLaSafe.pure hlf₁
          | some r_in =>
            cases r_in with
            | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
            | some quad =>
              rcases quad with ⟨st', t', i', m'⟩
              by_cases h1 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp only [h1, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf₁
              · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte]
                by_cases h2 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
                · simp only [h2, ↓reduceIte, commitE, liftH_run_eq, hooksFSMulti, StateT.run_bind,
                    StateT.run_pure, pure_bind, StateT.run_modify]
                  exact PubLaSafe.pure hlf₁
                · simp only [Bool.not_eq_true _ |>.mp h2, Bool.false_eq_true, ↓reduceIte]
                  by_cases h3 : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull t' = true
                  · simp only [h3, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
                    exact PubLaSafe.pure hlf₁
                  · simp only [Bool.not_eq_true _ |>.mp h3, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
                    exact PubLaSafe.pure hlf₁

private theorem redFSAuthDFPaperMulti_la_true_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (N Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N true
      (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep true tL t A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hinit : PubLaSafe C ℓ encT idOf N (fun es => es.h.lfWin = false)
      (initFSMultiRaw (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, t⟩ false) := by
    unfold initFSMultiRaw
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kr _ => ?_
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kc _ => ?_
    have hroot : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        ((rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) ⟨true, tL, t⟩ 0 lam
          ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr)).run {}) := by
      unfold rootFSMulti
      split_ifs
      · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact rfl)
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
          PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
            by (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact rfl)
      · simp only [StateT.run_bind, lookupMultiF, StateT.run_get, pure_bind, List.lookup_nil,
          stateT_lift_run, bind_assoc]
        exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
          by simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]; apply PubLaSafe.pure; exact rfl
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ =>
          by (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact rfl)
      · (simp only [StateT.run_pure]; apply PubLaSafe.pure; exact rfl)
    refine PubLaSafe.bind hroot fun ⟨⟨σ, k, sid⟩, h₁⟩ hlf₁ => ?_
    have hreg : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        ((regSessOptMulti sid).run h₁) := by
      cases sid with
      | none => (simp only [regSessOptMulti, StateT.run_pure]; apply PubLaSafe.pure; exact hlf₁)
      | some ik =>
        dsimp only [regSessOptMulti, regSessMulti]
        simp only [StateT.run_map, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, Function.comp_apply, Prod.map]
        split_ifs <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure] <;>
          (apply PubLaSafe.pure; exact hlf₁)
    refine PubLaSafe.bind hreg fun ⟨_, _⟩ hlf₂ => by apply PubLaSafe.pure; exact hlf₂
  have hsim : ∀ (oa : OracleComp _ Bool) es₀ (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((simulateQ (implEDFPaper
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false true)
          (2 + Δcka) qep maxForwardJumps (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy)
          oa).run es₀) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure _ =>
      intro es₀ hlf₀
      (simp only [simulateQ_pure, StateT.run_pure]; apply PubLaSafe.pure; exact hlf₀)
    | query_bind q_in _ ih =>
      intro es₀ hlf₀
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      refine PubLaSafe.bind
        (implEDFPaper_step_lfWin_la C ℓ Dh encPt encT idOf N Δcka qep ⟨true, tL, t⟩ q_in es₀ hlf₀)
        fun ⟨ans, es₁⟩ hlf₁ => ih ans es₁ hlf₁
  have hred : PubLaSafe C ℓ encT idOf N (fun b => b = false)
      (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep true tL t A) := by
    unfold redFSAuthDFPaperMulti runFSMultiDFPaper
    rw [bind_assoc]
    refine PubLaSafe.bind hinit fun es₀ hlf₀ => ?_
    refine PubLaSafe.bind (hsim A es₀ hlf₀) fun ⟨_, _⟩ hlf => ?_
    simp only [↓reduceIte]
    apply PubLaSafe.pure; exact hlf
  intro w hw
  exact (hred (fun _ => false) (fun _ => none) (fun _ _ h => by simp at h) w hw).1

/-! ## 2. `la = false`: `hpIdeal N false` Step Lemmas & `liftFSMulti` Support Bridges -/

private theorem genUpTo_preserves_meta {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    (G : ℕ → PRGScheme CK (CK × MK)) (P : CryptoGames.FSAEAD.Thm5.Params) (i : ℕ)
    (s s' : HSt CK MK AD M C) (u : Unit)
    (hmem : (u, s') ∈ support ((CryptoGames.FSAEAD.Thm5.genUpTo (m := ProbComp) G P (DG G) i).run s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.ended = s.1.ended ∧
    s'.1.inTransit = s.1.inTransit := by
  unfold CryptoGames.FSAEAD.Thm5.genUpTo at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  generalize (i - s.1.keys.length) = n at hmem
  induction n generalizing s with
  | zero =>
    simp only [CryptoGames.FSAEAD.Thm5.genN, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [CryptoGames.FSAEAD.Thm5.genN, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨_, s_mid⟩, hstep, htail⟩
    have hmid : s_mid.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
        s_mid.1.lastSentIdx = s.1.lastSentIdx ∧
        s_mid.1.ended = s.1.ended ∧
        s_mid.1.inTransit = s.1.inTransit := by
      unfold CryptoGames.FSAEAD.Thm5.genStep at hstep
      cases hsl : s.2 <;> simp only [StateT.run_mk, hsl] at hstep
      · split_ifs at hstep <;>
          simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hstep
        · rcases hstep with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
        · rcases hstep with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hstep
        rcases hstep with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
      · split_ifs at hstep <;>
          simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hstep
        · rcases hstep with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
        · rcases hstep with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
    have hrec := ih s_mid htail
    exact ⟨hrec.1.trans hmid.1, hrec.2.1.trans hmid.2.1,
      hrec.2.2.1.trans hmid.2.2.1, hrec.2.2.2.trans hmid.2.2.2⟩

private theorem injectH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ)
    (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C) (res : Option (ReceiveResult M))
    (hmem : (res, s') ∈ support ((injectH (m := ProbComp) ae G maxSkip (hpIdeal N false) (DG G) none q).run s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.ended = s.1.ended ∧
    (∀ r' ∈ s'.1.inTransit, r' ∈ s.1.inTransit) ∧
    (∀ i' mo', res = some (.accepted i' mo') →
      i' = q.2.1 ∧ s.1.isCompromised i' = true) ∧
    ((∀ i' mo', res ≠ some (.accepted i' mo')) → s'.1.inTransit = s.1.inTransit) := by
  unfold injectH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ h => h, by intro _ _ h; simp at h, fun _ => rfl⟩
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨ro, s₁⟩, hro, hs'⟩
    have hpres : s₁.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
        s₁.1.lastSentIdx = s.1.lastSentIdx ∧ s₁.1.ended = s.1.ended ∧
        s₁.1.inTransit = s.1.inTransit ∧
        (∀ i' m', ro = some (i', m') → i' = q.2.1 ∧ s.1.isCompromised i' = true) := by
      unfold receiveH at hro
      simp only [StateT.run_bind, getH_run, pure_bind] at hro
      split_ifs at hro
      · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hro
        rcases hro with ⟨⟨mo0, s₂⟩, hdec, hfin⟩
        by_cases hc : s.1.isCompromised q.2.1 = false
        · rw [decIdx_hpIdeal_none ae N false q.2.1 q.1 q.2.2 s hc] at hdec
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec hfin
          rcases hdec with ⟨rfl, rfl⟩; rcases hfin with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
        · simp only [Bool.not_eq_false] at hc
          have hdec_meta : s₂.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
              s₂.1.lastSentIdx = s.1.lastSentIdx ∧ s₂.1.ended = s.1.ended ∧
              s₂.1.inTransit = s.1.inTransit := by
            unfold decIdx at hdec
            simp only [StateT.run_bind, getH_run, pure_bind] at hdec
            (split at hdec <;> try split at hdec) <;>
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                MonadAttach.mem_support_bind, modifyH_run, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec
            · rcases hdec with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
            · contradiction
            · rcases hdec with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
          cases hmo : mo0 <;>
            simp only [hmo, StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
          · rcases hfin with ⟨rfl, rfl⟩
            exact ⟨hdec_meta.1, hdec_meta.2.1, hdec_meta.2.2.1, hdec_meta.2.2.2,
              by intro _ _ h; simp at h⟩
          · rcases hfin with ⟨⟨rfl, _⟩, rfl⟩
            refine ⟨hdec_meta.1, hdec_meta.2.1, hdec_meta.2.2.1, hdec_meta.2.2.2,
              fun i' _ hi => ?_⟩
            injection hi with hpair; injection hpair with hi_eq _
            exact ⟨hi_eq.symm, hi_eq ▸ hc⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
        rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
        rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
      · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hro
        rcases hro with ⟨⟨_, s₂⟩, hgen, hrest⟩
        have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) q.2.1 s s₂ _ hgen
        simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hrest
        rcases hrest with ⟨⟨mo0, s₃⟩, hdec, hfin⟩
        by_cases hc : s.1.isCompromised q.2.1 = false
        · have hc₂ : s₂.1.isCompromised q.2.1 = false := by
            simpa [HState.isCompromised, hgen_pres.1] using hc
          rw [decIdx_hpIdeal_none ae N false q.2.1 q.1 q.2.2 s₂ hc₂] at hdec
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec hfin
          rcases hdec with ⟨rfl, rfl⟩; rcases hfin with ⟨rfl, rfl⟩
          exact ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
            by intro _ _ h; simp at h⟩
        · simp only [Bool.not_eq_false] at hc
          have hdec_meta : s₃.1.senderCorruptedAt = s₂.1.senderCorruptedAt ∧
              s₃.1.lastSentIdx = s₂.1.lastSentIdx ∧ s₃.1.ended = s₂.1.ended ∧
              s₃.1.inTransit = s₂.1.inTransit := by
            unfold decIdx at hdec
            simp only [StateT.run_bind, getH_run, pure_bind] at hdec
            (split at hdec <;> try split at hdec) <;>
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                MonadAttach.mem_support_bind, modifyH_run, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec
            · rcases hdec with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
            · contradiction
            · rcases hdec with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
          cases hmo : mo0 <;>
            simp only [hmo, StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
          · rcases hfin with ⟨rfl, rfl⟩
            exact ⟨hdec_meta.1.trans hgen_pres.1, hdec_meta.2.1.trans hgen_pres.2.1,
              hdec_meta.2.2.1.trans hgen_pres.2.2.1, hdec_meta.2.2.2.trans hgen_pres.2.2.2,
              by intro _ _ h; simp at h⟩
          · rcases hfin with ⟨⟨rfl, _⟩, rfl⟩
            refine ⟨hdec_meta.1.trans hgen_pres.1, hdec_meta.2.1.trans hgen_pres.2.1,
              hdec_meta.2.2.1.trans hgen_pres.2.2.1, hdec_meta.2.2.2.trans hgen_pres.2.2.2,
              fun i' _ hi => ?_⟩
            injection hi with hpair; injection hpair with hi_eq _
            exact ⟨hi_eq.symm, hi_eq ▸ hc⟩
    cases ro with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs'
      rcases hs' with ⟨rfl, rfl⟩
      exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, fun _ h => hpres.2.2.2.1 ▸ h,
        by intro _ _ h; simp at h, fun _ => hpres.2.2.2.1⟩
    | some im =>
      rcases im with ⟨i', m'⟩
      have him := hpres.2.2.2.2 i' m' rfl
      simp only [hpIdeal, Bool.false_and, Bool.or_false, StateT.run_bind, modifyH_run, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        HState.removeFromTransit] at hs'
      rcases hs' with ⟨rfl, ⟨rfl, _⟩⟩
      refine ⟨hpres.1, hpres.2.1, hpres.2.2.1, ?_, ?_, ?_⟩
      · intro r' hr'
        rw [List.mem_filter] at hr'
        exact hpres.2.2.2.1 ▸ hr'.1
      · intro i₀ _ hacc
        injection hacc with hacc'
        injection hacc' with hi₀ _
        exact ⟨hi₀ ▸ him.1, hi₀ ▸ him.2⟩
      · intro hnotacc
        exact False.elim (hnotacc i' (some m') rfl)

private theorem deliverH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ)
    (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C) (res : Option (ReceiveResult M))
    (hct_idx : ∀ r ∈ s.1.inTransit, r.ct.1 = r.idx)
    (hmem : (res, s') ∈ support ((deliverH (m := ProbComp) ae G maxSkip (hpIdeal N false) (DG G) none q).run s)) :
    (res = none ∧ s' = s) ∨
    ∃ r_fs ∈ s.1.inTransit,
      r_fs.ad = q.1 ∧ r_fs.ct = q.2 ∧
      s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
      s'.1.lastSentIdx = s.1.lastSentIdx ∧
      s'.1.ended = s.1.ended ∧
      ((res = some .rejected ∧ s'.1.inTransit = s.1.inTransit) ∨
       (∃ mo', res = some (.accepted r_fs.idx mo') ∧
         s'.1.inTransit = s.1.inTransit.filter (·.idx != r_fs.idx))) := by
  unfold deliverH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact Or.inl ⟨hmem.1, hmem.2⟩
  · cases hfind : s.1.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
    | none =>
      simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact Or.inl ⟨hmem.1, hmem.2⟩
    | some r_fs =>
      have hr_mem : r_fs ∈ s.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      simp only [hfind, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨ro, s₁⟩, hro, hs'⟩
      have hidx_eq : q.2.1 = r_fs.idx := by rw [← hr_pred.2, hct_idx r_fs hr_mem]
      have hpres : s₁.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
          s₁.1.lastSentIdx = s.1.lastSentIdx ∧ s₁.1.ended = s.1.ended ∧
          s₁.1.inTransit = s.1.inTransit ∧
          (ro = none ∨ ro = some (r_fs.idx, r_fs.msg)) := by
        unfold receiveH at hro
        simp only [StateT.run_bind, getH_run, pure_bind, decIdx] at hro
        split_ifs at hro
        · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨rfl, ⟨rfl, _⟩⟩
          exact ⟨rfl, rfl, rfl, rfl, Or.inr (by simp [hidx_eq])⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
        · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hro
          rcases hro with ⟨⟨_, s₂⟩, hgen, hfin⟩
          have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) q.2.1 s s₂ _ hgen
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, exists_eq_left] at hfin
          have hro_eq := congrArg Prod.fst hfin
          have hs₁_eq := congrArg Prod.snd hfin
          subst hs₁_eq; subst hro_eq
          exact ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
            Or.inr (by simp [hidx_eq])⟩
      refine Or.inr ⟨r_fs, hr_mem, hr_pred.1, hr_pred.2, ?_⟩
      rcases hpres.2.2.2.2 with rfl | rfl
      · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hs'
        rcases hs' with ⟨rfl, ⟨rfl, _⟩⟩
        exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, Or.inl ⟨rfl, hpres.2.2.2.1⟩⟩
      · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, HState.removeFromTransit] at hs'
        rcases hs' with ⟨rfl, ⟨rfl, _⟩⟩
        exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, Or.inr ⟨_, rfl, by rw [hpres.2.2.2.1]⟩⟩

private theorem transmitHWith_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (N : ℕ)
    (q : AD × M) (s s' : HSt CK MK AD M C) (res : Option (ℕ × C))
    (hend : s.1.ended = false)
    (hmem : (res, s') ∈ support ((transmitHWith (m := ProbComp) ideal ae G (hpIdeal N false) (DG G) none q).run s)) :
    ∃ rawCt,
      res = some (s.1.lastSentIdx + 1, rawCt) ∧
      s'.1.ended = false ∧
      s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
      s'.1.lastSentIdx = s.1.lastSentIdx + 1 ∧
      s'.1.inTransit = ⟨s.1.lastSentIdx + 1, q.1, q.2, (s.1.lastSentIdx + 1, rawCt)⟩ :: s.1.inTransit := by
  unfold transmitHWith at hmem
  simp only [StateT.run_bind, getH_run, pure_bind, hend, Bool.false_eq_true, ↓reduceIte,
    MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨_, s₁⟩, hgen, ⟨rawCt, s₂⟩, henc, hfin⟩
  have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) (s.1.lastSentIdx + 1) s s₁ _ hgen
  have henc_pres : s₂.1.ended = s₁.1.ended ∧ s₂.1.senderCorruptedAt = s₁.1.senderCorruptedAt ∧
      s₂.1.lastSentIdx = s₁.1.lastSentIdx ∧ s₂.1.inTransit = s₁.1.inTransit := by
    unfold CryptoGames.FSAEAD.Thm5.encIdxWith at henc
    simp only [StateT.run_bind, getH_run, pure_bind] at henc
    split at henc
    · simp only [CryptoGames.FSAEAD.Thm5.sampleH, StateT.run_monadLift, monadLift_self,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at henc
      rcases henc with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
    · contradiction
    · split at henc
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at henc
        rcases henc with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
      · simp only [CryptoGames.FSAEAD.Thm5.sampleH, StateT.run_monadLift, monadLift_self,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at henc
        rcases henc with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, exists_eq_left] at hfin
  have hres_eq := congrArg Prod.fst hfin
  have hs'_eq := congrArg Prod.snd hfin
  subst hs'_eq
  exact ⟨rawCt, hres_eq, henc_pres.1.trans (hgen_pres.2.2.1.trans hend),
    henc_pres.2.1.trans hgen_pres.1, rfl, by rw [henc_pres.2.2.2, hgen_pres.2.2.2]⟩

private theorem corruptSenderH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (G : ℕ → PRGScheme CK (CK × MK)) (N : ℕ)
    (s s' : HSt CK MK AD M C) (res : Option (CryptoGames.FSAEAD.RatchetSenderState CK))
    (hend : s.1.ended = false)
    (hmem : (res, s') ∈ support ((corruptSenderH (m := ProbComp) G (hpIdeal N false) ()).run s)) :
    res.isSome = true ∧
    s'.1.ended = false ∧
    s'.1.senderCorruptedAt = some (s.1.senderCorruptedAt.getD s.1.lastSentIdx) ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.inTransit = s.1.inTransit := by
  unfold corruptSenderH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hpIdeal, Bool.false_eq_true, ↓reduceIte,
    MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨w, s₁⟩, hsk, hfin⟩
  have hsk_pres : s₁.1 = s.1 := by
    unfold CryptoGames.FSAEAD.Thm5.senderKey at hsk
    simp only [StateT.run_bind, getH_run, pure_bind] at hsk
    split at hsk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsk
      exact congrArg Prod.fst hsk.2
    · unfold CryptoGames.FSAEAD.Thm5.reveal at hsk
      cases hsl : s.2 <;> simp only [StateT.run_mk, hsl, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsk
      · rcases hsk with ⟨_, _, _, rfl⟩; rfl
      · exact congrArg Prod.fst hsk.2
      · rcases hsk with ⟨_, _, _, rfl⟩; rfl
  simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, exists_eq_left] at hfin
  have hres_eq := congrArg Prod.fst hfin
  have hs'_eq := congrArg Prod.snd hfin
  subst hs'_eq; subst hres_eq
  simp [hsk_pres, hend]

private theorem runPubIdeal_bind_eq {α β : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (x : OracleComp (PubMultiSpec Pt ℓ) α)
    (f : α → OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    runPubIdeal C ℓ encT idOf N la (x >>= f) rc σ =
    (runPubIdeal C ℓ encT idOf N la x rc σ >>= fun v =>
      runPubIdeal C ℓ encT idOf N la (f v.1.1) v.1.2 v.2) := by
  simp [runPubIdeal, simulateQ_bind, StateT.run_bind]

private theorem runPubIdeal_liftFSMulti_transmit_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    {β : Type} (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ℕ × LibsignalCiphertextWithSalt32) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) → OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMulti sIdx (CryptoGames.FSAEAD.transmitQuery hdr pm)).run hs >>= k) rc σ)) :
    ∃ u ∈ support
      ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false))
        (.inl (.inl (.inl (.inl (.inl ((hdr, pm.1), pm.2))))))).run (σ sIdx)),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (u.1, hs))
        rc (Function.update σ sIdx u.2)) := by
  rw [runPubIdeal_bind_eq] at hw
  erw [liftFSMulti_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inl (.inl (hdr, pm)))))) hs rc σ] at hw
  rw [pubTag_tr_eq C ℓ encT idOf N false sIdx hdr pm (rc sIdx) σ] at hw
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hw
  rcases hw with ⟨u, hu, hwu⟩
  exact ⟨u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwu⟩

private theorem runPubIdeal_liftFSMulti_corruptSender_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) {β : Type} (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMulti sIdx CryptoGames.FSAEAD.corruptSenderQuery).run hs >>= k) rc σ)) :
    ∃ u ∈ support
      ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false))
        (.inl (.inl (.inl (.inr ()))))).run (σ sIdx)),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (u.1, hs))
        rc (Function.update σ sIdx u.2)) := by
  rw [runPubIdeal_bind_eq] at hw
  erw [liftFSMulti_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inr ())))) hs rc σ] at hw
  rw [pubTag_cs_eq C ℓ encT idOf N false sIdx () (rc sIdx) σ] at hw
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hw
  rcases hw with ⟨u, hu, hwu⟩
  exact ⟨u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwu⟩

private theorem runPubIdeal_liftFSMulti_deliver_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {β : Type} (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMulti sIdx (CryptoGames.FSAEAD.deliverQuery hdr e)).run hs >>= k) rc σ)) :
    (lPubOf protoSignalCodec e.2 = none ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (none, hs)) rc σ)) ∨
    (∃ p, lPubOf protoSignalCodec e.2 = some p ∧
      ∃ u ∈ support
        ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false))
          (.inl (.inr ((hdr, p), e)))).run (σ sIdx)),
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          (k (u.1.map (_root_.CryptoGames.FSAEAD.withPub p), hs))
          rc (Function.update σ sIdx u.2))) := by
  rw [runPubIdeal_bind_eq] at hw
  erw [liftFSMulti_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inr (hdr, e))) hs rc σ] at hw
  rw [pubTag_dl_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hw
  cases hp : lPubOf protoSignalCodec e.2 with
  | none =>
    simp only [hp, StateT.run_pure, bind_assoc, pure_bind] at hw
    exact Or.inl ⟨rfl, by simpa only [Function.update_eq_self] using hw⟩
  | some p =>
    simp only [hp, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨u, hu, hwu⟩
    exact Or.inr ⟨p, rfl, u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwu⟩

private theorem runPubIdeal_liftFSMulti_inject_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {β : Type} (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMulti sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs >>= k) rc σ)) :
    (lPubOf protoSignalCodec e.2 = none ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (k ((if rc sIdx then none else some .rejected), hs)) rc σ)) ∨
    (∃ p, lPubOf protoSignalCodec e.2 = some p ∧
      ∃ u ∈ support
        ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false))
          (.inr ((hdr, p), e))).run (σ sIdx)),
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          (k (u.1.map (_root_.CryptoGames.FSAEAD.withPub p), hs))
          rc (Function.update σ sIdx u.2))) := by
  rw [runPubIdeal_bind_eq] at hw
  erw [liftFSMulti_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inr (hdr, e)) hs rc σ] at hw
  rw [pubTag_ij_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hw
  cases hp : lPubOf protoSignalCodec e.2 with
  | none =>
    simp only [hp, StateT.run_pure, bind_assoc, pure_bind] at hw
    exact Or.inl ⟨rfl, by simpa only [Function.update_eq_self] using hw⟩
  | some p =>
    simp only [hp, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨u, hu, hwu⟩
    exact Or.inr ⟨p, rfl, u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwu⟩

private def SessPinOpt {ℓ : ℕ} (t : ℕ)
    (es : EState
      (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))) :
    Option ℕ → Prop
  | none => ∀ P, (es.g.st P).vR t = none
  | some s₀ =>
    (∀ P v, (es.g.st P).vR t = some v → v = .inr s₀) ∧
    (0 < t → ∃ Tc σc k,
      es.h.cache t = some (Tc, σc, k, some s₀) ∧
      (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).curCkaMsg = some Tc) ∧
      (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.1.2 = some Tc))

private theorem SessPinOpt.congr_cache {ℓ : ℕ} {t : ℕ}
    {es : EState
      (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))}
    {hs' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {sSend : Option ℕ}
    (h : SessPinOpt t es sSend) (hc : hs'.cache = es.h.cache) :
    SessPinOpt t { es with h := hs' } sSend := by
  cases sSend with
  | none => exact h
  | some s₀ => simpa only [SessPinOpt, hc] using h

private structure MainActiveInv {ℓ : ℕ}
    (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : EState
      (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop where
  habort : es.abort = false
  hwin : es.g.win = false
  hid : ∀ P, (es.g.st P).id = P
  htcur : ∀ P, (es.g.st P).tcur = es.g.epoch P
  hcache_t : ∀ Tc σc k optIdx, es.h.cache t = some (Tc, σc, k, optIdx) → ∃ sIdx, optIdx = some sIdx
  hcache_ne : ∀ t' Tc σc k optIdx, t' ≠ t → es.h.cache t' = some (Tc, σc, k, optIdx) → optIdx = none
  hvR_t : ∀ P v, (es.g.st P).vR t = some v → ∃ sIdx, v = .inr sIdx
  hvR_ne : ∀ P t' v, t' ≠ t → (es.g.st P).vR t' = some v → ∃ rs, v = .inl rs
  htrans_wf : ∀ r ∈ es.g.trans,
    r.pos.epoch = r.ct.1.1 ∧
    r.pos.sender = Party.senderOf r.pos.epoch ∧
    r.pos.epoch ≤ es.g.epoch r.pos.sender ∧
    (r.pos.epoch = es.g.epoch r.pos.sender → r.pos.idx ≤ es.g.idx r.pos.sender) ∧
    (r.pos.epoch = t → r.ct.2.1 = r.pos.idx)
  hsess : ∃ sSend : Option ℕ,
    (match sSend with
    | none =>
      es.g.epoch (Party.senderOf t) < t ∧
      (∀ P sIdx, (es.g.st P).vS ≠ some (.inr sIdx)) ∧
      (∀ sIdx st, σ sIdx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0)
    | some s₀ =>
      t ≤ es.g.epoch (Party.senderOf t) ∧
      (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
      (∀ P sIdx, (es.g.st P).vS = some (.inr sIdx) →
        P = Party.senderOf t ∧ sIdx = s₀ ∧
        ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
          es.g.epoch (Party.senderOf t) = t ∧
          ((σ s₀ = none ∧ es.g.idx (Party.senderOf t) = 0) ∨
            ∃ st, σ s₀ = some st ∧ st.1.lastSentIdx = es.g.idx (Party.senderOf t)))) ∧
      (∀ sIdx st, sIdx ≠ s₀ → σ sIdx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
      (σ s₀ = none → ∀ r ∈ es.g.trans, r.pos.epoch ≠ t) ∧
      (∀ st, σ s₀ = some st →
        st.1.ended = false ∧
        (∀ r_fs ∈ st.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st.1.lastSentIdx) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st.1.lastSentIdx) ∧
        (healedBy es.g.tL (2 + Δcka) t = true →
          st.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
          st.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)))) ∧
    SessPinOpt t es sSend

private def MainInv {ℓ : ℕ}
    (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : EState
      (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  es.abort = true ∨ MainActiveInv Δcka tL t es σ

private theorem authOut_eq_false_of_mainInv {ℓ : ℕ}
    {Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))}
    {σ : ℕ → Option (IdealHSt Pt ℓ)}
    (hinv : MainInv Δcka tL t es σ) :
    authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es = false := by
  rcases hinv with hab | hact
  · simp [authOut, hab]
  · simp [authOut, Mode.policy, hact.habort, hact.hwin]

/-- Pure coin-only `PubMultiSpec` computations leave `(rc, σ)` unchanged in `runPubIdeal`. -/
private def CoinOnly {α : Type} (P : α → Prop)
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (x : OracleComp (PubMultiSpec Pt ℓ) α) : Prop :=
  ∀ rc σ, ∀ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
    P z.1.1 ∧ z.1.2 = rc ∧ z.2 = σ

private theorem CoinOnly.pure {α : Type} {P : α → Prop} {a : α} (ha : P a)
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ} :
    CoinOnly P C ℓ encT idOf N (pure a) := by
  intro rc σ z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact ⟨ha, rfl, rfl⟩

private theorem CoinOnly.bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {x : OracleComp (PubMultiSpec Pt ℓ) α} {f : α → OracleComp (PubMultiSpec Pt ℓ) β}
    (hx : CoinOnly P C ℓ encT idOf N x) (hf : ∀ a, P a → CoinOnly Q C ℓ encT idOf N (f a)) :
    CoinOnly Q C ℓ encT idOf N (x >>= f) := by
  intro rc σ z hz
  simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  rcases hx rc σ w hw with ⟨hp, hrc, hσ⟩
  rcases hf w.1.1 hp w.1.2 w.2 z hzw with ⟨hq, hrc', hσ'⟩
  exact ⟨hq, hrc'.trans hrc, hσ'.trans hσ⟩

private theorem lift_inl_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₁.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₁.Range q₀)) =
      query (spec := s₁ + s₂) (Sum.inl q₀) := by
  rw [query_eq_liftM]; rfl

private theorem CoinOnly.sampleT {T₀ : Type} [SampleableType T₀]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ) :
    CoinOnly (fun _ : T₀ => True) C ℓ encT idOf N
      (CryptoGames.SM.Construction.sampleT T₀) := by
  unfold CryptoGames.SM.Construction.sampleT
  rw [← liftComp_eq_liftM]
  induction ($ᵗ T₀ : ProbComp T₀) using OracleComp.inductionOn with
  | pure a =>
    intro rc σ z hz
    simp only [liftComp_pure, runPubIdeal, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact ⟨trivial, rfl, rfl⟩
  | query_bind t0 r ih =>
    intro rc σ z hz
    rw [liftComp_bind, liftComp_liftM_query, lift_inl_query_eq] at hz
    simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
      simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨u, _, hzu⟩
    exact ih u rc σ z hzu

private theorem initFSMultiRaw_mainInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (N Δcka : ℕ) (tL : Option ℕ) (t : ℕ) :
    CoinOnly (fun es => MainInv Δcka tL t es (fun _ => none)) C ℓ encT idOf N
      (initFSMultiRaw (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, t⟩ false) := by
  unfold initFSMultiRaw
  refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun kr _ => ?_
  refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun kc _ => ?_
  have hrt : CoinOnly
      (fun p : (BitVec 256 × BitVec 256 × Option Pt) ×
          FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) =>
        p.2.cache = (fun _ => none) ∧ p.2.sessions = [] ∧
        ((t = 0 ∧ p.1.2.2.isSome = true) ∨ (0 < t ∧ p.1.2.2 = none)))
      C ℓ encT idOf N
      ((rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) ⟨true, tL, t⟩ 0 lam
        ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr)).run {}) := by
    unfold rootFSMulti
    by_cases ht0 : t = 0
    · subst ht0
      simp only [Mode.tStar, lt_self_iff_false, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
          CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
            by (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, rfl, Or.inl ⟨trivial, rfl⟩⟩)
      · rw [StateT.run_bind]
        unfold lookupMultiF
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        dsimp only
        simp only [List.lookup_nil, StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ => by
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          apply CoinOnly.pure; exact ⟨rfl, rfl, Or.inl ⟨trivial, rfl⟩⟩
    · have hpos : 0 < t := Nat.pos_of_ne_zero ht0
      have hne : ¬ (0 = t) := by omega
      simp only [Mode.tStar, Nat.not_lt_zero, hne, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
          by (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, rfl, Or.inr ⟨hpos, rfl⟩⟩)
      · (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, rfl, Or.inr ⟨hpos, rfl⟩⟩)
  refine CoinOnly.bind hrt fun ⟨⟨σr, k, sid⟩, h₁⟩ ⟨hc₁, hs₁, hsid⟩ => ?_
  dsimp only at hc₁ hs₁ hsid
  rcases hsid with ⟨rfl, hsome⟩ | ⟨hpos, rfl⟩
  · rcases Option.isSome_iff_exists.mp hsome with ⟨ik, rfl⟩
    dsimp only [regSessOptMulti, regSessMulti]
    simp only [StateT.run_map, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get,
      hs₁, List.not_mem_nil, ↓reduceIte, StateT.run_set, StateT.run_pure, List.length_nil,
      bind_assoc, pure_bind, Function.comp_apply, Prod.map]
    apply CoinOnly.pure; refine (Or.inr ?_)
    refine {
      habort := rfl
      hwin := rfl
      hid := fun P => by cases P <;> rfl
      htcur := fun P => by cases P <;> rfl
      hcache_t := fun _ _ _ _ h => by simp [hc₁] at h
      hcache_ne := fun _ _ _ _ _ _ h => by simp [hc₁] at h
      hvR_t := fun P v hv => by
        cases P <;> simp [mkParties] at hv
        exact ⟨0, hv.symm⟩
      hvR_ne := fun P t' v hne hv => by
        cases P <;> simp [mkParties, hne] at hv
      htrans_wf := fun _ hr => by simp at hr
      hsess := ⟨some 0, ⟨le_rfl, fun _ => rfl, ?_, fun _ _ _ h => by simp at h,
        fun _ _ hr => by simp at hr, fun _ h => by simp at h⟩,
        ⟨fun P v hv => by cases P <;> simp [mkParties] at hv; exact hv.symm,
         fun h => by omega⟩⟩
    }
    · intro P sIdx hvS
      cases P <;> simp [mkParties] at hvS
      subst hvS
      exact ⟨rfl, rfl, fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  · dsimp only [regSessOptMulti]; simp only [StateT.run_pure, pure_bind]
    apply CoinOnly.pure; refine (Or.inr ?_)
    refine {
      habort := rfl
      hwin := rfl
      hid := fun P => by cases P <;> rfl
      htcur := fun P => by cases P <;> rfl
      hcache_t := fun _ _ _ _ h => by simp [hc₁] at h
      hcache_ne := fun _ _ _ _ _ _ h => by simp [hc₁] at h
      hvR_t := fun P v hv => by cases P <;> simp [mkParties, Nat.ne_of_gt hpos] at hv
      hvR_ne := fun P t' v _ hv => by
        cases P <;> simp [mkParties] at hv
        exact ⟨_, hv.2.symm⟩
      htrans_wf := fun _ hr => by simp at hr
      hsess := ⟨none, ⟨hpos,
        fun P sIdx => by cases P <;> simp [mkParties],
        fun _ _ h => by simp at h⟩,
        fun P => by cases P <;> simp [mkParties, Nat.ne_of_gt hpos]⟩
    }

/-- Helper for `[ISSUE-13b]` lazy `corruptSenderQuery` inside `hooksFSMulti.fsRecv` (`la = false`):
when `healedBy es.g.tL (2 + Δcka) t = false` and `sIdx` is pinned to the active target session `s₀`,
running `liftFSMulti sIdx corruptSenderQuery` preserves `MainActiveInv Δcka tL t es` on the updated
session map `Function.update σ sIdx (some st₁)`. -/
private theorem corruptSender_fsRecv_step_mainActiveInv
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t sIdx : ℕ)
    (es : EState
      (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : MainActiveInv Δcka tL t es σ)
    (hnot_heal : healedBy es.g.tL (2 + Δcka) t = false)
    (hsafe_or_pin :
      healedBy es.g.tL (2 + Δcka) t = true ∨
      (∃ P, (es.g.st P).vR t = some (.inr sIdx)) ∨
      (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
        ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))
    {β : Type} (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (k_cont : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMulti sIdx CryptoGames.FSAEAD.corruptSenderQuery).run hs >>= k_cont) rc σ)) :
    ∃ ss_out st₁,
      MainActiveInv Δcka tL t es (Function.update σ sIdx (some st₁)) ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (k_cont (some ss_out, hs)) rc (Function.update σ sIdx (some st₁))) := by
  rcases hact.hsess with ⟨none | s₀, hs_inv, hpin⟩
  · rcases hsafe_or_pin with hheal | ⟨P, hvR⟩ | ⟨_, ⟨r_hdr, hr_mem, hr_ep⟩, _⟩
    · rw [hnot_heal] at hheal; cases hheal
    · rw [hpin P] at hvR; cases hvR
    · have hwf := hact.htrans_wf r_hdr hr_mem
      have hle := hwf.2.2.1; rw [hwf.2.1, hr_ep] at hle; have := hs_inv.1; omega
  · have hsIdx_eq : sIdx = s₀ := by
      rcases hsafe_or_pin with hheal | ⟨P, hvR⟩ | ⟨hpos, _, Tc, σc, k, hcache⟩
      · rw [hnot_heal] at hheal; cases hheal
      · exact Sum.inr.inj (hpin.1 P (.inr sIdx) hvR)
      · rcases hpin.2 hpos with ⟨Tc', σc', k', hcache', _⟩
        rw [hcache] at hcache'
        injection hcache' with hq
        exact Option.some.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hq).2).2).2
    subst hsIdx_eq
    rcases runPubIdeal_liftFSMulti_corruptSender_support C ℓ encT idOf N sIdx hs k_cont
        rc σ w hw with ⟨u, hu, hwu⟩
    have hcs_body : ∀ (st₀ : IdealHSt Pt ℓ)
        (v0 : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) × IdealHSt Pt ℓ),
        u = (v0.1, some v0.2) →
        st₀.1.ended = false →
        (σ sIdx = none → st₀.1.lastSentIdx = 0 ∧ ∀ r0 ∈ es.g.trans, r0.pos.epoch ≠ t) →
        (∀ st_ex, σ sIdx = some st_ex → st₀ = st_ex) →
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
        (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos.idx ≤ st₀.1.lastSentIdx) →
        (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos ∉ es.g.comp →
          st₀.1.isCompromised r0.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r0.pos.idx → (r_fs.ad.1, r_fs.ct) = r0.ct)) →
        v0 ∈ support ((corruptSenderH (m := ProbComp) (lChainPRG C.F) (hpIdeal N false) ()).run st₀) →
        ∃ ss_out st₁,
          MainActiveInv Δcka tL t es (Function.update σ sIdx (some st₁)) ∧
          w ∈ support (runPubIdeal C ℓ encT idOf N false
            (k_cont (some ss_out, hs)) rc (Function.update σ sIdx (some st₁))) := by
      intro st₀ v0 hu_eq hend₀ hif_none hif_some hit₀ hidx₀ hunc₀ hu_cs
      rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ v0.2 v0.1 hend₀ hu_cs with
        ⟨hsome_res, hend₁, hsc₁, hls₁, hit₁⟩
      rcases Option.isSome_iff_exists.mp hsome_res with ⟨ss_out, hu1⟩
      have hwu' : w ∈ support (runPubIdeal C ℓ encT idOf N false
          (k_cont (some ss_out, hs)) rc (Function.update σ sIdx (some v0.2))) := by
        simpa only [hu_eq, hu1] using hwu
      refine ⟨ss_out, v0.2, ?_, hwu'⟩
      refine {
        habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
        hcache_t := hact.hcache_t, hcache_ne := hact.hcache_ne,
        hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
        hsess := ⟨some sIdx, ⟨hs_inv.1, hs_inv.2.1, ?_, ?_, by intro h; simp at h, ?_⟩, hpin⟩
      }
      · intro Q idx hvSQ
        rcases hs_inv.2.2.1 Q idx hvSQ with ⟨rfl, rfl, hsendQ⟩
        refine ⟨rfl, rfl, fun hsIn => ?_⟩
        rcases hsendQ hsIn with ⟨hep_t, ⟨hnone, hidx0⟩ | ⟨st_ex, hsome, hls_ex⟩⟩
        · exact ⟨hep_t, Or.inr ⟨v0.2, by simp, hls₁.trans ((hif_none hnone).1.trans hidx0.symm)⟩⟩
        · have heq_st := hif_some st_ex hsome; subst heq_st
          exact ⟨hep_t, Or.inr ⟨v0.2, by simp, hls₁.trans hls_ex⟩⟩
      · intro idx st hne_idx hst_j
        rw [Function.update_of_ne hne_idx] at hst_j
        exact hs_inv.2.2.2.1 idx st hne_idx hst_j
      · intro st hst
        simp only [Function.update_self, Option.some.injEq] at hst; subst hst
        refine ⟨hend₁, ?_, fun r0 hr0 hep0 => by rw [hls₁]; exact hidx₀ r0 hr0 hep0,
          (fun hh : healedBy es.g.tL (2 + Δcka) t = true => Bool.noConfusion (hnot_heal.symm.trans hh)), ?_⟩
        · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
        · intro r0 hr0 hep0 hnc0
          rcases hunc₀ r0 hr0 hep0 hnc0 with ⟨hc_f, hct_m⟩
          have hle_ls := hidx₀ r0 hr0 hep0
          refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (by rw [← hit₁]; exact hr_fs)⟩
          cases hsc0 : st₀.1.senderCorruptedAt with
          | none => simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
          | some j0 => simpa [HState.isCompromised, hsc₁, hsc0] using hc_f
    have hσ0_cases : σ sIdx = none ∨ ∃ st₀, σ sIdx = some st₀ := by
      cases σ sIdx with
      | none => exact Or.inl rfl
      | some st₀ => exact Or.inr ⟨st₀, rfl⟩
    rcases hσ0_cases with hσ0 | ⟨st₀, hσ0⟩
    · rw [hσ0] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, hvu⟩
      exact hcs_body (hInit b .unknown) v0 hvu rfl (fun _ => ⟨rfl, hs_inv.2.2.2.2.1 hσ0⟩)
        (fun _ h => by rw [hσ0] at h; cases h) (by simp [hInit])
        (fun r0 hr0 hep0 => (hs_inv.2.2.2.2.1 hσ0 r0 hr0 hep0).elim)
        (fun r0 hr0 hep0 _ => (hs_inv.2.2.2.2.1 hσ0 r0 hr0 hep0).elim) hv0
    · rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      have h5 := hs_inv.2.2.2.2.2 st₀ hσ0
      exact hcs_body st₀ v0 hvu h5.1 (fun h => by rw [hσ0] at h; cases h)
        (fun _ h => Option.some.inj (hσ0.symm.trans h)) h5.2.1 h5.2.2.1 h5.2.2.2.2 hv0

/-- Post-state companion for `hooksFSMulti.fsRecv` (`la = false`) on `.inr sIdx`:
either aborts (`none`), rejects (`some none`) while preserving `MainActiveInv.hsess` on `es.g`,
or accepts at `sIdx = s₀` (`some s₀` witness of `hact.hsess`) with `inTransit` a sublist of `st₀.1.inTransit`
(and filtered by `r_fs.idx` when `healedBy = true`). -/
private theorem fsRecv_inr_step_post
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t sIdx : ℕ) (P : Party)
    (es : _) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : MainActiveInv Δcka tL t es σ)
    (hsafe_or_pin :
      healedBy es.g.tL (2 + Δcka) t = true ∨
      (∃ P, (es.g.st P).vR t = some (.inr sIdx)) ∨
      (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
        ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (hs₁ : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (w : ((Option (Option ((CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).fsRecv
        es.g P t (.inr sIdx) hdr e rec).run hs₁) rc σ)) :
    w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧
      ∀ hs', hs'.cache = es.h.cache → MainActiveInv Δcka tL t { es with h := hs' } w.2) ∨
    (∃ i' m' s₀, ∃ (st₀ st' : IdealHSt Pt ℓ),
      w.1.1.1 = some (some (.inr s₀, i', m')) ∧
      w.1.1.2.cache = hs₁.cache ∧
      sIdx = s₀ ∧
      SessPinOpt t es (some s₀) ∧
      t ≤ es.g.epoch (Party.senderOf t) ∧
      (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
      (∀ Q idx, (es.g.st Q).vS = some (.inr idx) →
        Q = Party.senderOf t ∧ idx = s₀ ∧
        ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
          es.g.epoch (Party.senderOf t) = t ∧
          st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
      (∀ idx st, idx ≠ s₀ → σ idx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
      (st₀.1.ended = false ∧
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
        (healedBy es.g.tL (2 + Δcka) t = true →
          st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
      w.2 = Function.update σ s₀ (some st') ∧
      st'.1.ended = false ∧
      st'.1.lastSentIdx = st₀.1.lastSentIdx ∧
      st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
      (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
      ((∃ r_fs ∈ st₀.1.inTransit, r_fs.idx = i' ∧ r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
          st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx)) ∨
        (healedBy es.g.tL (2 + Δcka) t = false ∧
          ∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx = i' → r.pos ∈ es.g.comp))) := by
  -- Preserve `MainActiveInv` when `σ_cur` updates at `sIdx` without changing `(ended, senderCorruptedAt, inTransit, lastSentIdx)`
  have hrej_pres : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), MainActiveInv Δcka tL t es σ_cur →
      ∀ st₀ st',
      (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt →
      st'.1.lastSentIdx = st₀.1.lastSentIdx →
      st'.1.ended = st₀.1.ended →
      st'.1.inTransit = st₀.1.inTransit →
      ∀ hs', hs'.cache = es.h.cache →
        MainActiveInv Δcka tL t { es with h := hs' } (Function.update σ_cur sIdx (some st')) := by
    intro σ_cur hact_cur st₀ st' hst₀ hsc hls hend hit hs' hcache
    refine {
      habort := hact_cur.habort
      hwin := hact_cur.hwin
      hid := hact_cur.hid
      htcur := hact_cur.htcur
      hcache_t := fun Tc σc k optIdx hc => hact_cur.hcache_t Tc σc k optIdx (hcache ▸ hc)
      hcache_ne := fun t' Tc σc k optIdx hne hc => hact_cur.hcache_ne t' Tc σc k optIdx hne (hcache ▸ hc)
      hvR_t := hact_cur.hvR_t
      hvR_ne := hact_cur.hvR_ne
      htrans_wf := hact_cur.htrans_wf
      hsess := ?_
    }
    rcases hact_cur.hsess with ⟨none | s₀, hs, hpin⟩
    · refine ⟨none, ⟨hs.1, hs.2.1, fun j st hj => ?_⟩, hpin.congr_cache hcache⟩
      by_cases heq : j = sIdx
      · subst heq; simp only [Function.update_self, Option.some.injEq] at hj; subst hj
        rcases hst₀ with hsome | ⟨_, b, rfl⟩
        · rcases hs.2.2 j st₀ hsome with ⟨he, hc, hi, hl⟩
          exact ⟨hend.trans he, hsc.trans hc, hit.trans hi, hls.trans hl⟩
        · exact ⟨hend, hsc, hit, hls⟩
      · rw [Function.update_of_ne heq] at hj; exact hs.2.2 j st hj
    · refine ⟨some s₀, ⟨hs.1, hs.2.1, ?_, ?_, ?_, ?_⟩, hpin.congr_cache hcache⟩
      · intro Q idx hvS
        rcases hs.2.2.1 Q idx hvS with ⟨hQ, hidx, hsend⟩
        refine ⟨hQ, hidx, fun hsIn => ?_⟩
        rcases hsend hsIn with ⟨hep, ⟨hnone, hidx0⟩ | ⟨st, hsome, hl⟩⟩
        · refine ⟨hep, ?_⟩
          by_cases heq : s₀ = sIdx
          · subst heq
            rcases hst₀ with hsome | ⟨_, b, rfl⟩
            · rw [hnone] at hsome; cases hsome
            · exact Or.inr ⟨st', by simp, hls.trans hidx0.symm⟩
          · exact Or.inl ⟨by simp [Function.update_of_ne heq, hnone], hidx0⟩
        · refine ⟨hep, ?_⟩
          by_cases heq : s₀ = sIdx
          · subst heq
            rcases hst₀ with hsome' | ⟨hnone, _⟩
            · rw [hsome] at hsome'; injection hsome' with hst_eq; subst hst_eq
              exact Or.inr ⟨st', by simp, hls.trans hl⟩
            · rw [hsome] at hnone; cases hnone
          · exact Or.inr ⟨st, by simp [Function.update_of_ne heq, hsome], hl⟩
      · intro j st hj_ne hj
        by_cases heq : j = sIdx
        · subst heq; simp only [Function.update_self, Option.some.injEq] at hj; subst hj
          rcases hst₀ with hsome | ⟨_, b, rfl⟩
          · rcases hs.2.2.2.1 j st₀ hj_ne hsome with ⟨he, hc, hi, hl⟩
            exact ⟨hend.trans he, hsc.trans hc, hit.trans hi, hls.trans hl⟩
          · exact ⟨hend, hsc, hit, hls⟩
        · rw [Function.update_of_ne heq] at hj; exact hs.2.2.2.1 j st hj_ne hj
      · intro hnone
        by_cases heq : s₀ = sIdx
        · subst heq; simp at hnone
        · rw [Function.update_of_ne heq] at hnone; exact hs.2.2.2.2.1 hnone
      · intro st hst
        by_cases heq : s₀ = sIdx
        · subst heq; simp only [Function.update_self, Option.some.injEq] at hst; subst hst
          rcases hst₀ with hsome | ⟨hnone, b, rfl⟩
          · rw [hsc, hls, hend, hit]
            have h5 := hs.2.2.2.2.2 st₀ hsome
            refine ⟨h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, fun r hr hep hnc => ?_⟩
            have hr5 := h5.2.2.2.2 r hr hep hnc
            exact ⟨by simpa [HState.isCompromised, hsc] using hr5.1, hr5.2⟩
          · have hno_t := hs.2.2.2.2.1 hnone
            refine ⟨hend, by simp [hit, hInit], fun r hr hep => (hno_t r hr hep).elim,
              fun _ => ⟨hsc, by simp [hit, hInit]⟩,
              fun r hr hep _ => (hno_t r hr hep).elim⟩
        · rw [Function.update_of_ne heq] at hst; exact hs.2.2.2.2.2 st hst
  have hunchanged : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), MainActiveInv Δcka tL t es σ_cur →
      ∀ hs', hs'.cache = es.h.cache →
      MainActiveInv Δcka tL t { es with h := hs' } σ_cur := fun σ_cur hact_cur hs' hcache => {
    habort := hact_cur.habort, hwin := hact_cur.hwin, hid := hact_cur.hid, htcur := hact_cur.htcur,
    hcache_t := fun Tc σc k optIdx hc => hact_cur.hcache_t Tc σc k optIdx (hcache ▸ hc),
    hcache_ne := fun t' Tc σc k optIdx hne hc => hact_cur.hcache_ne t' Tc σc k optIdx hne (hcache ▸ hc),
    hvR_t := hact_cur.hvR_t, hvR_ne := hact_cur.hvR_ne, htrans_wf := hact_cur.htrans_wf,
    hsess := by
      rcases hact_cur.hsess with ⟨sSend, hs, hpin⟩
      exact ⟨sSend, hs, hpin.congr_cache hcache⟩
  }
  -- Active session `sIdx` must be `some s₀` with `σ_cur s₀ = some st₀` whenever `inTransit ≠ []` or `isCompromised = true`:
  have hmust_s₀ : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), MainActiveInv Δcka tL t es σ_cur →
      (∀ idx, idx ≠ sIdx → σ_cur idx = σ idx) →
      ∀ st₀,
      (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ((∃ r_fs, r_fs ∈ st₀.1.inTransit) ∨ (∃ i', st₀.1.isCompromised i' = true)) →
      ∃ s₀, sIdx = s₀ ∧ SessPinOpt t es (some s₀) ∧
        t ≤ es.g.epoch (Party.senderOf t) ∧
        (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
        (∀ Q idx, (es.g.st Q).vS = some (.inr idx) →
          Q = Party.senderOf t ∧ idx = s₀ ∧
          ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
            es.g.epoch (Party.senderOf t) = t ∧
            st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
        (∀ idx st, idx ≠ s₀ → σ idx = some st →
          st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
          st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
        (st₀.1.ended = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
          (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
          (healedBy es.g.tL (2 + Δcka) t = true →
            st₀.1.senderCorruptedAt = none ∧
            (∀ r_fs ∈ st₀.1.inTransit,
              ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
          (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
            st₀.1.isCompromised r.pos.idx = false ∧
            (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) := by
    intro σ_cur hact_cur hσ_ne st₀ hst₀ hact_ev
    rcases hst₀ with hsome | ⟨_, b, rfl⟩
    · rcases hact_cur.hsess with ⟨none | s₀, hs, hpin⟩
      · rcases hs.2.2 sIdx st₀ hsome with ⟨_, hsc, hit, _⟩
        rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
        · simp [hit] at hr
        · rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc i'] at hc; cases hc
      · by_cases heq : sIdx = s₀
        · subst heq
          refine ⟨sIdx, rfl, hpin, hs.1, hs.2.1, fun Q idx hvS => ?_, ?_, hs.2.2.2.2.2 st₀ hsome⟩
          · rcases hs.2.2.1 Q idx hvS with ⟨hQ, hidx, hsend⟩
            refine ⟨hQ, hidx, fun hsIn => ?_⟩
            rcases hsend hsIn with ⟨hep, ⟨hnone, _⟩ | ⟨st_s, hst_s, hls_s⟩⟩
            · rw [hsome] at hnone; cases hnone
            · rw [hsome] at hst_s; injection hst_s with hst_eq; subst hst_eq
              exact ⟨hep, hls_s⟩
          · intro idx st hne hst
            exact hs.2.2.2.1 idx st hne ((hσ_ne idx hne).trans hst)
        · rcases hs.2.2.2.1 sIdx st₀ heq hsome with ⟨_, hsc, hit, _⟩
          rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
          · simp [hit] at hr
          · rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc i'] at hc; cases hc
    · rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
      · simp [hInit] at hr
      · simp [hInit, HState.isCompromised] at hc
  have hct_idx_at : ∀ st₀,
      (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx := by
    intro st₀ hst₀
    rcases hst₀ with hsome | ⟨_, b, rfl⟩
    · rcases hact.hsess with ⟨none | s₀, hs, _⟩
      · rcases hs.2.2 sIdx st₀ hsome with ⟨_, _, hit, _⟩; simp [hit]
      · by_cases heq : sIdx = s₀
        · subst heq; exact fun r hr => ((hs.2.2.2.2.2 st₀ hsome).2.1 r hr).1
        · rcases hs.2.2.2.1 sIdx st₀ heq hsome with ⟨_, _, hit, _⟩; simp [hit]
    · simp [hInit]
  dsimp only [hooksFSMulti] at hw
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hw
  dsimp only at hw
  generalize hmatch : List.find? _ ((hs₁.book sIdx).getD {}).fsTrans = matched at hw
  cases matched with
  | some m0 =>
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_true, Option.isSome_some] at hw
    rcases runPubIdeal_liftFSMulti_deliver_support C ℓ encT idOf N sIdx hdr e hs₁ _ rc σ w hw with
      ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
    · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw_none
      subst hw_none; exact Or.inl rfl
    · have hdl_body : ∀ (st₀ : IdealHSt Pt ℓ)
          (v0 : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ)) × IdealHSt Pt ℓ),
          u = (v0.1, some v0.2) →
          (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
          v0 ∈ support ((deliverH (m := ProbComp) (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
            none ((hdr, p), e)).run st₀) →
          (w.1.1.1 = none ∨
            (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧
              ∀ hs', hs'.cache = es.h.cache → MainActiveInv Δcka tL t { es with h := hs' } w.2) ∨
            (∃ i' m' s₀, ∃ (st₀ st' : IdealHSt Pt ℓ),
              w.1.1.1 = some (some (.inr s₀, i', m')) ∧
              w.1.1.2.cache = hs₁.cache ∧
              sIdx = s₀ ∧
              SessPinOpt t es (some s₀) ∧
              t ≤ es.g.epoch (Party.senderOf t) ∧
              (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
              (∀ Q idx, (es.g.st Q).vS = some (.inr idx) →
                Q = Party.senderOf t ∧ idx = s₀ ∧
                ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
                  es.g.epoch (Party.senderOf t) = t ∧
                  st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
              (∀ idx st, idx ≠ s₀ → σ idx = some st →
                st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
                st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
              (st₀.1.ended = false ∧
                (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
                (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
                (healedBy es.g.tL (2 + Δcka) t = true →
                  st₀.1.senderCorruptedAt = none ∧
                  (∀ r_fs ∈ st₀.1.inTransit,
                    ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
                (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
                  st₀.1.isCompromised r.pos.idx = false ∧
                  (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
              w.2 = Function.update σ s₀ (some st') ∧
              st'.1.ended = false ∧
              st'.1.lastSentIdx = st₀.1.lastSentIdx ∧
              st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
              (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
              ((∃ r_fs ∈ st₀.1.inTransit, r_fs.idx = i' ∧ r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
                  st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx)) ∨
                (healedBy es.g.tL (2 + Δcka) t = false ∧
                  ∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx = i' → r.pos ∈ es.g.comp)))) := by
        intro st₀ v0 hu_eq hst₀ hu_dl
        rw [hu_eq] at hwu
        rcases deliverH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e) st₀ v0.2 v0.1
            (hct_idx_at st₀ hst₀) hu_dl with ⟨hu1, hu2⟩ |
            ⟨r_fs, hr_fs, had, hct, hsc, hls, hend, ⟨hu1, hit⟩ | ⟨mo', hu1, hit_f⟩⟩
        · simp only [hu1, Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hwu
          subst hwu; exact Or.inl rfl
        · simp only [hu1, Option.map_some, withPub, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hwu
          subst hwu
          exact Or.inr (Or.inl ⟨rfl, rfl, hrej_pres σ hact st₀ v0.2 hst₀ hsc hls hend hit⟩)
        · rcases hmust_s₀ σ hact (fun _ _ => rfl) st₀ hst₀ (Or.inl ⟨r_fs, hr_fs⟩) with
            ⟨s₀, rfl, hpin₀, hle, heqvS, hvS, hne, h5₀⟩
          simp only [hu1, Option.map_some, withPub, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_modify] at hwu
          have hsub : ∀ r' ∈ v0.2.1.inTransit, r' ∈ st₀.1.inTransit := by
            intro r' hr'; rw [hit_f, List.mem_filter] at hr'; exact hr'.1
          cases mo' with
          | none =>
            cases rec with
            | none =>
              simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu; exact Or.inl rfl
            | some r_rec =>
              simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu
              exact Or.inr (Or.inr ⟨r_fs.idx, r_rec.msg, sIdx, st₀, v0.2, rfl, rfl, rfl, hpin₀, hle, heqvS, hvS, hne,
                h5₀, rfl, hend.trans h5₀.1,
                hls, hsc, hsub, Or.inl ⟨r_fs, hr_fs, rfl, congrArg Prod.fst had, hct, hit_f⟩⟩)
          | some m_raw =>
            simp only [Option.map_some, StateT.run_pure, runPubIdeal, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hwu
            subst hwu
            exact Or.inr (Or.inr ⟨r_fs.idx, (p, m_raw), sIdx, st₀, v0.2, rfl, rfl, rfl, hpin₀, hle, heqvS, hvS, hne,
              h5₀, rfl, hend.trans h5₀.1,
              hls, hsc, hsub, Or.inl ⟨r_fs, hr_fs, rfl, congrArg Prod.fst had, hct, hit_f⟩⟩)
      cases hσ0 : σ sIdx with
      | none =>
        rw [hσ0] at hu
        simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
        rcases hu with ⟨b, _, v0, hv0, hvu⟩
        exact hdl_body (hInit b .unknown) v0 hvu (Or.inr ⟨hσ0, b, rfl⟩) hv0
      | some st₀ =>
        rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
        rcases hu with ⟨v0, hv0, hvu⟩
        simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
        exact hdl_body st₀ v0 hvu (Or.inl hσ0) hv0
  | none =>
    have hij_tail : ∀ hs_cur (σ_cur : ℕ → Option (IdealHSt Pt ℓ)),
        hs_cur.cache = hs₁.cache →
        MainActiveInv Δcka tL t es σ_cur →
        (∀ idx, idx ≠ sIdx → σ_cur idx = σ idx) →
        (∀ v_up, Function.update σ_cur sIdx v_up = Function.update σ sIdx v_up) →
        ∀ k_ij,
        (∀ idx0 mo0 hs_k,
          k_ij (some (.accepted idx0 mo0), hs_k) =
            (StateT.run (do
              let s1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) ← get
              let bk1 : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) := (s1.book sIdx).getD {}
              if false && (none : Option (ℕ × Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).isNone &&
                  (!bk1.sCorr) && bk1.fsCount < idx0 then
                modify fun (s : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) => { s with lfWin := true }
                return none
              else
                let drop : ℕ := ((none : Option (ℕ × Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).map (fun (x : ℕ × Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) => x.1)).getD idx0
                modify fun (s : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                    { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo0, rec with
                | some m, _ => return some (some (Sum.inr sIdx, idx0, m))
                | none, some r => return some (some (Sum.inr sIdx, idx0, r.msg))
                | none, none => return none) hs_k)) →
        (∀ hs_k, k_ij (none, hs_k) = pure (none, hs_k)) →
        (∀ hs_k, k_ij (some .rejected, hs_k) = pure (some none, hs_k)) →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((liftFSMulti sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs_cur >>= k_ij) rc σ_cur) →
        (w.1.1.1 = none ∨
          (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧
            ∀ hs', hs'.cache = es.h.cache → MainActiveInv Δcka tL t { es with h := hs' } w.2) ∨
          (∃ i' m' s₀, ∃ (st₀ st' : IdealHSt Pt ℓ),
            w.1.1.1 = some (some (.inr s₀, i', m')) ∧
            w.1.1.2.cache = hs₁.cache ∧
            sIdx = s₀ ∧
            SessPinOpt t es (some s₀) ∧
            t ≤ es.g.epoch (Party.senderOf t) ∧
            (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
            (∀ Q idx, (es.g.st Q).vS = some (.inr idx) →
              Q = Party.senderOf t ∧ idx = s₀ ∧
              ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
                es.g.epoch (Party.senderOf t) = t ∧
                st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
            (∀ idx st, idx ≠ s₀ → σ idx = some st →
              st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
              st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
            (st₀.1.ended = false ∧
              (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
              (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
              (healedBy es.g.tL (2 + Δcka) t = true →
                st₀.1.senderCorruptedAt = none ∧
                (∀ r_fs ∈ st₀.1.inTransit,
                  ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
              (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
                st₀.1.isCompromised r.pos.idx = false ∧
                (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
            w.2 = Function.update σ s₀ (some st') ∧
            st'.1.ended = false ∧
            st'.1.lastSentIdx = st₀.1.lastSentIdx ∧
            st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
            (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
            ((∃ r_fs ∈ st₀.1.inTransit, r_fs.idx = i' ∧ r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
                st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx)) ∨
              (healedBy es.g.tL (2 + Δcka) t = false ∧
                ∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx = i' → r.pos ∈ es.g.comp)))) := by
      intro hs_cur σ_cur hc_cur hact_cur hσ_ne hσ_up k_ij hk_acc hk_none hk_rej hw_ij
      rcases runPubIdeal_liftFSMulti_inject_support C ℓ encT idOf N sIdx hdr e hs_cur k_ij rc σ_cur w hw_ij with
        ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
      · cases hrc : rc sIdx <;>
          simp only [hrc, Bool.false_eq_true, ↓reduceIte, hk_none, hk_rej, runPubIdeal, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hw_none <;>
          subst hw_none
        · exact Or.inr (Or.inl ⟨rfl, hc_cur, hunchanged σ_cur hact_cur⟩)
        · exact Or.inl rfl
      · have hij_body : ∀ (st₀ : IdealHSt Pt ℓ)
            (v0 : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (Plain ℓ)) × IdealHSt Pt ℓ),
            u = (v0.1, some v0.2) →
            (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
            v0 ∈ support ((injectH (m := ProbComp) (lAeadR C protoSignalCodec ℓ encT idOf)
              (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
              none ((hdr, p), e)).run st₀) →
            (w.1.1.1 = none ∨
              (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧
                ∀ hs', hs'.cache = es.h.cache → MainActiveInv Δcka tL t { es with h := hs' } w.2) ∨
              (∃ i' m' s₀, ∃ (st₀ st' : IdealHSt Pt ℓ),
                w.1.1.1 = some (some (.inr s₀, i', m')) ∧
                w.1.1.2.cache = hs₁.cache ∧
                sIdx = s₀ ∧
                SessPinOpt t es (some s₀) ∧
                t ≤ es.g.epoch (Party.senderOf t) ∧
                (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
                (∀ Q idx, (es.g.st Q).vS = some (.inr idx) →
                  Q = Party.senderOf t ∧ idx = s₀ ∧
                  ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
                    es.g.epoch (Party.senderOf t) = t ∧
                    st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
                (∀ idx st, idx ≠ s₀ → σ idx = some st →
                  st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
                  st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
                (st₀.1.ended = false ∧
                  (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
                  (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
                  (healedBy es.g.tL (2 + Δcka) t = true →
                    st₀.1.senderCorruptedAt = none ∧
                    (∀ r_fs ∈ st₀.1.inTransit,
                      ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
                  (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
                    st₀.1.isCompromised r.pos.idx = false ∧
                    (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
                w.2 = Function.update σ s₀ (some st') ∧
                st'.1.ended = false ∧
                st'.1.lastSentIdx = st₀.1.lastSentIdx ∧
                st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
                (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
                ((∃ r_fs ∈ st₀.1.inTransit, r_fs.idx = i' ∧ r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
                    st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx)) ∨
                  (healedBy es.g.tL (2 + Δcka) t = false ∧
                    ∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx = i' → r.pos ∈ es.g.comp)))) := by
          intro st₀ v0 hu_eq hst₀ hu_ij
          rw [hu_eq] at hwu
          have hspec := injectH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e)
            st₀ v0.2 v0.1 hu_ij
          cases hu1 : v0.1 with
          | none =>
            simp only [hu1, Option.map_none, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hwu
            subst hwu; exact Or.inl rfl
          | some rr =>
            cases rr with
            | rejected =>
              have hit := hspec.2.2.2.2.2 (by intro _ _ h; rw [hu1] at h; simp at h)
              simp only [hu1, Option.map_some, withPub, hk_rej, runPubIdeal,
                simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwu
              subst hwu
              exact Or.inr (Or.inl ⟨rfl, hc_cur, hrej_pres σ_cur hact_cur st₀ v0.2 hst₀ hspec.1 hspec.2.1 hspec.2.2.1 hit⟩)
            | accepted idx0 mo0 =>
              have hcomp := (hspec.2.2.2.2.1 idx0 mo0 hu1).2
              rcases hmust_s₀ σ_cur hact_cur hσ_ne st₀ hst₀ (Or.inr ⟨idx0, hcomp⟩) with
                ⟨s₀, rfl, hpin₀, hle, heqvS, hvS, hne, h5₀⟩
              have hnot_heal : healedBy es.g.tL (2 + Δcka) t = true → False := by
                intro hheal
                have hsc := (h5₀.2.2.2.1 hheal).1
                rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc idx0] at hcomp; cases hcomp
              simp only [hu1, Option.map_some, withPub, hk_acc, StateT.run_bind, StateT.run_get,
                pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_modify] at hwu
              cases mo0 with
              | none =>
                cases rec with
                | none =>
                  simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hwu
                  subst hwu; exact Or.inl rfl
                | some r_rec =>
                  simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hwu
                  subst hwu
                  exact Or.inr (Or.inr ⟨idx0, r_rec.msg, sIdx, st₀, v0.2, rfl, hc_cur, rfl, hpin₀, hle, heqvS, hvS, hne,
                    h5₀, hσ_up _, hspec.2.2.1.trans h5₀.1, hspec.2.1, hspec.1, hspec.2.2.2.1,
                    Or.inr ⟨Bool.eq_false_iff.mpr hnot_heal, fun r hr hep hidx =>
                      Classical.byContradiction fun hnc =>
                        Bool.noConfusion ((h5₀.2.2.2.2 r hr hep hnc).1.symm.trans (hidx ▸ hcomp))⟩⟩)
              | some m_raw =>
                simp only [Option.map_some, StateT.run_pure, runPubIdeal, simulateQ_pure,
                  support_pure, Set.mem_singleton_iff] at hwu
                subst hwu
                exact Or.inr (Or.inr ⟨idx0, (p, m_raw), sIdx, st₀, v0.2, rfl, hc_cur, rfl, hpin₀, hle, heqvS, hvS, hne,
                  h5₀, hσ_up _, hspec.2.2.1.trans h5₀.1, hspec.2.1, hspec.1, hspec.2.2.2.1,
                  Or.inr ⟨Bool.eq_false_iff.mpr hnot_heal, fun r hr hep hidx =>
                    Classical.byContradiction fun hnc =>
                      Bool.noConfusion ((h5₀.2.2.2.2 r hr hep hnc).1.symm.trans (hidx ▸ hcomp))⟩⟩)
        cases hσ0 : σ_cur sIdx with
        | none =>
          rw [hσ0] at hu
          simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
          rcases hu with ⟨b, _, v0, hv0, hvu⟩
          exact hij_body (hInit b .unknown) v0 hvu (Or.inr ⟨hσ0, b, rfl⟩) hv0
        | some st₀ =>
          rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
          rcases hu with ⟨v0, hv0, hvu⟩
          simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
          exact hij_body st₀ v0 hvu (Or.inl hσ0) hv0
    by_cases hguard_cs : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = true
    · have hnot_heal : healedBy es.g.tL (2 + Δcka) t = false := by
        rcases Bool.and_eq_true_iff.mp hguard_cs with ⟨h1, _⟩
        exact Bool.not_eq_true' _ |>.mp h1
      simp only [Option.isNone_none, Bool.true_and, hguard_cs, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind] at hw
      rcases corruptSender_fsRecv_step_mainActiveInv C ℓ encT idOf N Δcka tL t sIdx
          es rc σ hact hnot_heal hsafe_or_pin hs₁ _ w hw with ⟨ss_out, st₁, hact₁, hw_cs⟩
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hw_cs
      refine hij_tail
        { hs₁ with book := Function.update hs₁.book sIdx (some { ((hs₁.book sIdx).getD {}) with sCorr := true }) }
        (Function.update σ sIdx (some st₁)) rfl hact₁
        (fun idx hne => Function.update_of_ne hne _ _)
        (fun _ => Function.update_idem _ _ _)
        _ ?_ ?_ ?_ hw_cs
      · intro idx0 mo0 hs_k
        simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure, pure_bind,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none]
        cases mo0 <;> cases rec <;> rfl
      · intro _; simp only [StateT.run_pure]
      · intro _; simp only [StateT.run_pure]
    · have hgf : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = false :=
        Bool.not_eq_true _ |>.mp hguard_cs
      simp only [Option.isNone_none, Bool.true_and, hgf, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_true, Option.isSome_none] at hw
      refine hij_tail hs₁ σ rfl hact (fun _ _ => rfl) (fun _ => rfl)
        _ ?_ ?_ ?_ hw
      · intro idx0 mo0 hs_k
        simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure, pure_bind,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none]
        cases mo0 <;> cases rec <;> rfl
      · intro _; simp only [StateT.run_pure]
      · intro _; simp only [StateT.run_pure]

private theorem lookupMultiF_coinOnly
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : Pt)
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :
    CoinOnly (fun p => p.2.cache = hs.cache) C ℓ encT idOf N
      ((lookupMultiF (T := Pt) (Sig := BitVec 256) (K := BitVec 256)
        (SS := CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (RS := CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) Ik).run hs) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hs.table.lookup Ik with
  | some k => (simp only [StateT.run_pure]; apply CoinOnly.pure; exact rfl)
  | none =>
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun k _ => ?_
    simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
    apply CoinOnly.pure; exact rfl

private theorem regSessMulti_coinOnly
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : Pt)
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :
    CoinOnly (fun p => p.2.cache = hs.cache) C ℓ encT idOf N
      ((regSessMulti (T := Pt) (Sig := BitVec 256) (K := BitVec 256)
        (SS := CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (RS := CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) Ik).run hs) := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · (simp only [StateT.run_pure]; apply CoinOnly.pure; exact rfl)
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
    apply CoinOnly.pure; exact rfl

private theorem startSend_coinOnly_spec
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t t_next : ℕ) (P : Party)
    (ctx : _) (γ : _) (σr : BitVec 256) (r : Option (BitVec 256))
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :
    CoinOnly (fun p =>
      ∃ γ' T' σr' ssv,
        p.1 = some (γ', T', σr', ssv) ∧
        (t_next = t → ∃ s₀ σc k, ssv = .inr s₀ ∧
          p.2.cache t = some (T', σc, k, some s₀) ∧
          (∀ Tc σc' k' optIdx, p.2.cache t = some (Tc, σc', k', optIdx) → optIdx = some s₀) ∧
          (∀ t', t' ≠ t → p.2.cache t' = hs.cache t')) ∧
        (t_next ≠ t → (∃ ss, ssv = .inl ss) ∧ p.2.cache t = hs.cache t ∧
          ∀ t' Tc σc k optIdx, t' ≠ t →
            (∀ Tc' σc' k' optIdx', hs.cache t' = some (Tc', σc', k', optIdx') → optIdx' = none) →
            p.2.cache t' = some (Tc, σc, k, optIdx) → optIdx = none))
      C ℓ encT idOf N
      (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).startSend
        ctx P t_next γ σr r).run hs) := by
  dsimp only [hooksFSMulti]
  suffices hbody : ∀ (coins : BitVec 256),
      CoinOnly (fun p : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt × Pt × BitVec 256 × (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)) × FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) =>
        ∃ γ' T' σr' ssv,
          p.1 = some (γ', T', σr', ssv) ∧
          (t_next = t → ∃ s₀ σc k, ssv = .inr s₀ ∧
            p.2.cache t = some (T', σc, k, some s₀) ∧
            (∀ Tc σc' k' optIdx, p.2.cache t = some (Tc, σc', k', optIdx) → optIdx = some s₀) ∧
            (∀ t', t' ≠ t → p.2.cache t' = hs.cache t')) ∧
          (t_next ≠ t → (∃ ss, ssv = .inl ss) ∧ p.2.cache t = hs.cache t ∧
            ∀ t' Tc σc k optIdx, t' ≠ t →
              (∀ Tc' σc' k' optIdx', hs.cache t' = some (Tc', σc', k', optIdx') → optIdx' = none) →
              p.2.cache t' = some (Tc, σc, k, optIdx) → optIdx = none))
        C ℓ encT idOf N
        ((do
          let c := (dhScheme Dh).send γ coins
          let (σ', k, sid) ← rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) ⟨true, tL, t⟩ t_next c.2.2 σr
          let optIdx ← regSessOptMulti sid
          modify fun (s : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) => { s with cache := Function.update s.cache t_next (some (c.2.1, σ', k, optIdx)) }
          let ssv : CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ := match optIdx with
            | none => .inl ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k)
            | some sIdx => .inr sIdx
          return some (c.1, c.2.1, σ', ssv)).run hs) by
    cases r with
    | some c =>
      rw [StateT.run_bind, StateT.run_pure, pure_bind]
      exact hbody c
    | none =>
      simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
      exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun coins _ => hbody coins
  intro coins
  set c := (dhScheme Dh).send γ coins
  have hrt : CoinOnly
      (fun p : (BitVec 256 × BitVec 256 × Option Pt) × _ =>
        p.2.cache = hs.cache ∧
        ((t_next = t ∧ p.1.2.2.isSome = true) ∨ (t_next ≠ t ∧ p.1.2.2 = none)))
      C ℓ encT idOf N
      ((rootFSMulti (CryptoGames.Ratchet.rootPRNG C.F encPt) ⟨true, tL, t⟩ t_next c.2.2 σr).run hs) := by
    unfold rootFSMulti
    by_cases heq : t_next = t
    · subst heq
      simp only [Mode.tStar, lt_self_iff_false, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
          CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
            by (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, Or.inl ⟨trivial, rfl⟩⟩)
      · simp only [StateT.run_bind]
        exact CoinOnly.bind (lookupMultiF_coinOnly C ℓ encT idOf N c.2.2 hs) fun ⟨_, hs₁⟩ hc₁ =>
          by (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨hc₁, Or.inl ⟨trivial, rfl⟩⟩)
    · by_cases hgt : t < t_next
      · simp only [Mode.tStar, hgt, ↓reduceIte, StateT.run_pure]
        apply CoinOnly.pure; exact ⟨rfl, Or.inr ⟨heq, rfl⟩⟩
      · simp only [Mode.tStar, hgt, heq, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
          exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
            by (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, Or.inr ⟨heq, rfl⟩⟩)
        · (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, Or.inr ⟨heq, rfl⟩⟩)
  rw [StateT.run_bind]
  refine CoinOnly.bind hrt fun ⟨⟨σ', k, sid⟩, hs₁⟩ ⟨hc₁, hsid⟩ => ?_
  rcases hsid with ⟨rfl, hsome⟩ | ⟨hne, rfl⟩
  · rcases Option.isSome_iff_exists.mp hsome with ⟨Ik, rfl⟩
    simp only [regSessOptMulti, StateT.run_map, map_eq_bind_pure_comp, StateT.run_bind, bind_assoc]
    refine CoinOnly.bind (regSessMulti_coinOnly C ℓ encT idOf N Ik hs₁) fun ⟨s₀, hs₂⟩ hc₂ => ?_
    dsimp only at hc₂
    simp only [Prod.map, Function.comp_apply, StateT.run_bind, pure_bind, StateT.run_modify, StateT.run_pure]
    apply CoinOnly.pure; refine ⟨c.1, c.2.1, σ', .inr s₀, rfl,
      fun _ => ⟨s₀, σ', k, rfl, by simp, ?_, ?_⟩, fun h => (h rfl).elim⟩
    · intro Tc σc k' optIdx hup
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hup
      exact hup.2.2.2.symm
    · intro t' ht'
      dsimp only at hc₁ ⊢
      rw [Function.update_of_ne ht', hc₂, hc₁]
  · dsimp only at hc₁
    simp only [regSessOptMulti, StateT.run_bind, StateT.run_pure, pure_bind, StateT.run_modify]
    apply CoinOnly.pure; refine ⟨c.1, c.2.1, σ', .inl _, rfl, fun h => (hne h).elim,
      fun _ => ⟨⟨_, rfl⟩, by dsimp only; rw [Function.update_of_ne hne.symm, hc₁], ?_⟩⟩
    intro t' Tc σc k' optIdx _ hprev hup
    by_cases ht' : t' = t_next
    · subst ht'
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hup
      exact hup.2.2.2.symm
    · dsimp only at hup
      rw [Function.update_of_ne ht', hc₁] at hup
      exact hprev Tc σc k' optIdx hup

private theorem startRecv_coinOnly_spec
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t t_recv : ℕ) (P : Party)
    (ctx : _) (γ : _) (σr : BitVec 256) (Tn : Pt)
    (hs : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hcache_t : ∀ Tc σc k optIdx, hs.cache t = some (Tc, σc, k, optIdx) → ∃ sIdx, optIdx = some sIdx)
    (hcache_ne : ∀ t' Tc σc k optIdx, t' ≠ t → hs.cache t' = some (Tc, σc, k, optIdx) → optIdx = none) :
    CoinOnly (fun p =>
      p.2.cache = hs.cache ∧
      (p.1 = none ∨ p.1 = some none ∨
        ∃ γ' σr' rsv, p.1 = some (some (γ', σr', rsv)) ∧
          (t_recv = t → ∃ sIdx, rsv = .inr sIdx ∧
            (∀ σc k s₀, hs.cache t = some (Tn, σc, k, some s₀) → sIdx = s₀)) ∧
          (t_recv ≠ t → ∃ rs, rsv = .inl rs)))
      C ℓ encT idOf N
      (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).startRecv
        ctx P t_recv γ σr Tn).run hs) := by
  dsimp only [hooksFSMulti]
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  cases hct : hs.cache t_recv with
  | some quad =>
    rcases quad with ⟨Tc, σc, k, optIdx⟩
    by_cases hT : Tc = Tn
    · simp only [hT, ↓reduceIte, StateT.run_pure]
      apply CoinOnly.pure; refine ⟨rfl, Or.inr (Or.inr ⟨_, σc, _, rfl, fun heq => ?_, fun hne => ?_⟩)⟩
      · subst heq; subst hT
        rcases hcache_t Tc σc k optIdx hct with ⟨sIdx, rfl⟩
        refine ⟨sIdx, rfl, fun σc' k' s₀ hct' => ?_⟩
        rw [hct] at hct'
        injection hct' with hq
        exact Option.some.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hq).2).2).2
      · rw [hcache_ne t_recv Tc σc k optIdx hne hct]; exact ⟨_, rfl⟩
    · simp only [hT, ↓reduceIte]
      by_cases heq : t_recv = t
      · subst heq
        simp only [Mode.tStar, decide_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, Or.inl rfl⟩)
        · simp only [StateT.run_bind]
          set kk := (dhScheme Dh).receive γ Tn
          refine CoinOnly.bind (lookupMultiF_coinOnly C ℓ encT idOf N kk.2 hs) fun ⟨_, hs₁⟩ hc₁ => ?_
          refine CoinOnly.bind (regSessMulti_coinOnly C ℓ encT idOf N kk.2 hs₁) fun ⟨sIdx, hs₂⟩ hc₂ => ?_
          apply CoinOnly.pure; refine ⟨hc₂.trans hc₁, Or.inr (Or.inr ⟨kk.1, _, .inr sIdx, rfl,
            fun _ => ⟨sIdx, rfl, fun σc' k' s₀ hct' => ?_⟩, fun h => (h rfl).elim⟩)⟩
          rw [hct] at hct'
          injection hct' with hq
          exact (hT (Prod.mk.inj hq).1).elim
      · simp only [Mode.tStar, heq, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        apply CoinOnly.pure; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  | none =>
    by_cases heq : t_recv = t
    · subst heq
      simp only [Mode.tStar, decide_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · (simp only [StateT.run_pure]; apply CoinOnly.pure; exact ⟨rfl, Or.inl rfl⟩)
      · simp only [StateT.run_bind]
        set kk := (dhScheme Dh).receive γ Tn
        refine CoinOnly.bind (lookupMultiF_coinOnly C ℓ encT idOf N kk.2 hs) fun ⟨_, hs₁⟩ hc₁ => ?_
        refine CoinOnly.bind (regSessMulti_coinOnly C ℓ encT idOf N kk.2 hs₁) fun ⟨sIdx, hs₂⟩ hc₂ => ?_
        apply CoinOnly.pure; refine ⟨hc₂.trans hc₁, Or.inr (Or.inr ⟨kk.1, _, .inr sIdx, rfl,
          fun _ => ⟨sIdx, rfl, fun _ _ _ hct' => by rw [hct] at hct'; cases hct'⟩,
          fun h => (h rfl).elim⟩)⟩
    · simp only [Mode.tStar, heq, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
      apply CoinOnly.pure; exact ⟨rfl, Or.inr (Or.inl rfl)⟩

/-- Step postcondition for `hooksFSMulti.fsSend` (`la = false`, `pair = none`) on `.inr s₀` at epoch `t`. -/
private theorem fsSend_inr_step_post
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t s₀ : ℕ)
    (s₁ : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hs₁ : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hep_s₁ : s₁.epoch (Party.senderOf t) = t)
    (hs₀_pre :
      (σ s₀ = none ∧ s₁.idx (Party.senderOf t) = 0 ∧ (∀ r ∈ s₁.trans, r.pos.epoch ≠ t)) ∨
      (∃ st₀, σ s₀ = some st₀ ∧
        st₀.1.ended = false ∧
        st₀.1.lastSentIdx = s₁.idx (Party.senderOf t) ∧
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
        (healedBy s₁.tL (2 + Δcka) t = true →
          st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) ∧
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))))
    (w : ((Option ((CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ) ×
        (ℕ × LibsignalCiphertextWithSalt32)) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).fsSend
        s₁ (Party.senderOf t) t (.inr s₀) hdr pm none).run hs₁) rc σ)) :
    w.1.1.1 = none ∨
    ∃ rawCt st₂,
      let e := (s₁.idx (Party.senderOf t) + 1, rawCt)
      w.1.1.1 = some (.inr s₀, e) ∧
      w.1.1.2.cache = hs₁.cache ∧
      w.2 = Function.update σ s₀ (some st₂) ∧
      st₂.1.ended = false ∧
      st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
      (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
      (∀ st',
        let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
          ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false
        (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
        (healedBy g'.tL (2 + Δcka) t = true →
          st₂.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₂.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
        (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp →
          st₂.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) := by
  dsimp only [hooksFSMulti] at hw
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hw
  dsimp only at hw
  -- Helper running the `transmitQuery` tail from any intermediate state `(hs_mid, rc_mid, σ_mid)` and `st₁`:
  have htr_tail : ∀ hs_mid rc_mid σ_mid,
      hs_mid.cache = hs₁.cache →
      (∀ j, j ≠ s₀ → σ_mid j = σ j) →
      ((σ_mid s₀ = none ∧ s₁.idx (Party.senderOf t) = 0 ∧ (∀ r ∈ s₁.trans, r.pos.epoch ≠ t)) ∨
        ∃ st₁, σ_mid s₀ = some st₁ ∧
          st₁.1.ended = false ∧
          st₁.1.lastSentIdx = s₁.idx (Party.senderOf t) ∧
          (∀ r_fs ∈ st₁.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₁.1.lastSentIdx) ∧
          (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₁.1.lastSentIdx) ∧
          (healedBy s₁.tL (2 + Δcka) t = true →
            st₁.1.senderCorruptedAt = none ∧
            (∀ r_fs ∈ st₁.1.inTransit,
              ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) ∧
          (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp →
            st₁.1.isCompromised r.pos.idx = false ∧
            (∀ r_fs ∈ st₁.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) →
      ∀ k_tr,
      (∀ e hs_k, k_tr (some e, hs_k) =
        pure (some (Sum.inr s₀, e),
          { cache := hs_k.cache, table := hs_k.table, sessions := hs_k.sessions,
            book := Function.update hs_k.book s₀ (some
              { sCorr := ((hs_k.book s₀).getD {}).sCorr,
                fsCount := ((hs_k.book s₀).getD {}).fsCount + 1,
                fsTrans := (((hs_k.book s₀).getD {}).fsCount + 1, hdr, e) :: ((hs_k.book s₀).getD {}).fsTrans }),
            lfWin := hs_k.lfWin })) →
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        ((liftFSMulti s₀ (CryptoGames.FSAEAD.transmitQuery hdr pm)).run hs_mid >>= k_tr) rc_mid σ_mid) →
        (w.1.1.1 = none ∨
          ∃ rawCt st₂,
            let e := (s₁.idx (Party.senderOf t) + 1, rawCt)
            w.1.1.1 = some (.inr s₀, e) ∧
            w.1.1.2.cache = hs₁.cache ∧
            w.2 = Function.update σ s₀ (some st₂) ∧
            st₂.1.ended = false ∧
            st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
            (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
            (∀ st',
              let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
                ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
              (healedBy g'.tL (2 + Δcka) t = true →
                st₂.1.senderCorruptedAt = none ∧
                (∀ r_fs ∈ st₂.1.inTransit,
                  ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp →
                st₂.1.isCompromised r.pos.idx = false ∧
                (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)))) := by
    intro hs_mid rc_mid σ_mid hcache_mid hσ_ne hst₁_pre k_tr hk_some hw_tr
    rcases runPubIdeal_liftFSMulti_transmit_support C ℓ encT idOf N s₀ hdr pm hs_mid k_tr
        rc_mid σ_mid w hw_tr with ⟨u, hu, hwu⟩
    have htr_from : ∀ (st₁ : IdealHSt Pt ℓ)
        (v0 : Option (ℕ × LibsignalCiphertextWithSalt32) × IdealHSt Pt ℓ),
        u = (v0.1, some v0.2) →
        st₁.1.ended = false →
        st₁.1.lastSentIdx = s₁.idx (Party.senderOf t) →
        (∀ r_fs ∈ st₁.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₁.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₁.1.lastSentIdx) →
        (healedBy s₁.tL (2 + Δcka) t = true →
          st₁.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₁.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp →
          st₁.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₁.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)) →
        v0 ∈ support ((transmitHWith (m := ProbComp) (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hpIdeal N false)
          (DG (lChainPRG C.F)) none ((hdr, pm.1), pm.2)).run st₁) →
        (w.1.1.1 = none ∨
          ∃ rawCt st₂,
            let e := (s₁.idx (Party.senderOf t) + 1, rawCt)
            w.1.1.1 = some (.inr s₀, e) ∧
            w.1.1.2.cache = hs₁.cache ∧
            w.2 = Function.update σ s₀ (some st₂) ∧
            st₂.1.ended = false ∧
            st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
            (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
            (∀ st',
              let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
                ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
              (healedBy g'.tL (2 + Δcka) t = true →
                st₂.1.senderCorruptedAt = none ∧
                (∀ r_fs ∈ st₂.1.inTransit,
                  ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp →
                st₂.1.isCompromised r.pos.idx = false ∧
                (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)))) := by
      intro st₁ v0 hu_eq hend₁ hls₁ hit₁ hidx₁ hheal₁ huncomp₁ hu_spec
      rw [hu_eq] at hwu
      rcases transmitHWith_hpIdeal_false_step_spec _ _ _ N ((hdr, pm.1), pm.2) st₁ v0.2 v0.1
          hend₁ hu_spec with ⟨rawCt, hu1, hend₂, hsc₂, hls₂, hit₂⟩
      simp only [hu1, hls₁, hk_some,
        runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hwu
      subst hwu
      have hupd_eq : Function.update σ_mid s₀ (some v0.2) = Function.update σ s₀ (some v0.2) := by
        ext j; by_cases hj : j = s₀
        · subst hj; simp
        · simp [Function.update_of_ne hj, hσ_ne j hj]
      refine Or.inr ⟨rawCt, v0.2, rfl, hcache_mid, hupd_eq, hend₂, hls₂.trans (congrArg (· + 1) hls₁), ?_, ?_⟩
      · intro r_fs hr_fs
        rw [hit₂, List.mem_cons] at hr_fs
        rcases hr_fs with rfl | hr_old
        · exact ⟨rfl, by rw [hls₂]⟩
        · rcases hit₁ r_fs hr_old with ⟨h1, h2⟩
          exact ⟨h1, by rw [hls₂]; omega⟩
      · intro st'
        refine ⟨?_, ?_, ?_⟩
        · intro r hr hep
          simp only [GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · rw [hls₂, hls₁]
          · have := hidx₁ r hr_old hep; rw [hls₂]; omega
        · intro hheal_g'
          have hheal_s₁ : healedBy s₁.tL (2 + Δcka) t = true := hheal_g'
          rcases hheal₁ hheal_s₁ with ⟨hsc₁, htr₁⟩
          refine ⟨hsc₂.trans hsc₁, fun r_fs hr_fs => ?_⟩
          rw [hit₂, List.mem_cons] at hr_fs
          rcases hr_fs with rfl | hr_old
          · exact ⟨pm, by simp [GameState.record, hls₁]⟩
          · rcases htr₁ r_fs hr_old with ⟨m0, hm0⟩
            exact ⟨m0, by simp [GameState.record, hm0]⟩
        · intro r hr hep hnc
          simp only [GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · have hsafe : s₁.safeCh (2 + Δcka) (Party.senderOf t) = true := by
              by_contra hns
              simp only [Bool.not_eq_true] at hns
              simp [GameState.record, hns] at hnc
            have hheal_s₁ : healedBy s₁.tL (2 + Δcka) t = true := by
              simpa [GameState.safeCh, hep_s₁] using hsafe
            have hsc₁ := (hheal₁ hheal_s₁).1
            refine ⟨isCompromised_of_senderCorruptedAt_none v0.2.1 (hsc₂.trans hsc₁) _, ?_⟩
            intro r_fs hr_fs hidx_eq
            rw [hit₂, List.mem_cons] at hr_fs
            rcases hr_fs with rfl | hr_old
            · simp [hls₁]
            · have := (hit₁ r_fs hr_old).2
              simp only [hls₁] at this hidx_eq; omega
          · have hnc_s₁ : r.pos ∉ s₁.comp := by
              intro hc; apply hnc
              simp only [GameState.record]; split_ifs <;> simp [hc]
            rcases huncomp₁ r hr_old hep hnc_s₁ with ⟨hc_false, hct_match⟩
            refine ⟨by simpa [HState.isCompromised, hsc₂] using hc_false, ?_⟩
            intro r_fs hr_fs hidx_eq
            rw [hit₂, List.mem_cons] at hr_fs
            rcases hr_fs with rfl | hr_fs_old
            · have := hidx₁ r hr_old hep
              simp only at hidx_eq; omega
            · exact hct_match r_fs hr_fs_old hidx_eq
    rcases hst₁_pre with ⟨hnone, hidx0, hno_t⟩ | ⟨st₁, hsome, h1, h2, h3, h4, h5, h6⟩
    · rw [hnone] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, hvu⟩
      exact htr_from (hInit b .unknown) v0 hvu rfl hidx0.symm (by simp [hInit])
        (fun r hr hep => (hno_t r hr hep).elim)
        (fun _ => ⟨rfl, by simp [hInit]⟩)
        (fun r hr hep _ => (hno_t r hr hep).elim) hv0
    · rw [hsome, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      exact htr_from st₁ v0 hvu h1 h2 h3 h4 h5 h6 hv0
  by_cases hcond : (!(s₁.safeCh (2 + Δcka) (Party.senderOf t)) && !((hs₁.book s₀).getD {}).sCorr) = true
  · have hnot_heal : healedBy s₁.tL (2 + Δcka) t = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      simpa [GameState.safeCh, hep_s₁] using hcond.1
    simp only [hcond, ↓reduceIte, Bool.false_eq_true, StateT.run_bind] at hw
    rcases runPubIdeal_liftFSMulti_corruptSender_support C ℓ encT idOf N s₀ hs₁ _ rc σ w hw with
      ⟨u, hu, hwu⟩
    have hcs_from : ∀ (st₀ : IdealHSt Pt ℓ)
        (v0 : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) × IdealHSt Pt ℓ),
        u = (v0.1, some v0.2) →
        st₀.1.ended = false →
        st₀.1.lastSentIdx = s₁.idx (Party.senderOf t) →
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)) →
        v0 ∈ support ((corruptSenderH (m := ProbComp) (lChainPRG C.F) (hpIdeal N false) ()).run st₀) →
        (w.1.1.1 = none ∨
          ∃ rawCt st₂,
            let e := (s₁.idx (Party.senderOf t) + 1, rawCt)
            w.1.1.1 = some (.inr s₀, e) ∧
            w.1.1.2.cache = hs₁.cache ∧
            w.2 = Function.update σ s₀ (some st₂) ∧
            st₂.1.ended = false ∧
            st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
            (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
            (∀ st',
              let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
                ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
              (healedBy g'.tL (2 + Δcka) t = true →
                st₂.1.senderCorruptedAt = none ∧
                (∀ r_fs ∈ st₂.1.inTransit,
                  ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
              (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp →
                st₂.1.isCompromised r.pos.idx = false ∧
                (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)))) := by
      intro st₀ v0 hu_eq hend₀ hls₀ hit₀ hidx₀ huncomp₀ hu_cs
      rw [hu_eq] at hwu
      rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ v0.2 v0.1 hend₀ hu_cs with
        ⟨hsome_res, hend₁, hsc₁, hls₁, hit₁⟩
      rcases Option.isSome_iff_exists.mp hsome_res with ⟨ss_out, hu1⟩
      simp only [hu1, StateT.run_bind, StateT.run_modify, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwu
      refine htr_tail
        { cache := hs₁.cache, table := hs₁.table, sessions := hs₁.sessions,
          book := Function.update hs₁.book s₀ (some
            { sCorr := true, fsCount := ((hs₁.book s₀).getD {}).fsCount,
              fsTrans := ((hs₁.book s₀).getD {}).fsTrans }),
          lfWin := hs₁.lfWin }
        rc (Function.update σ s₀ (some v0.2)) rfl
        (fun j hj => Function.update_of_ne hj _ _) ?_ _
        (fun e hs_k => by simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure])
        hwu
      refine Or.inr ⟨v0.2, Function.update_self _ _ _, hend₁, hls₁.trans hls₀, ?_, ?_, ?_, ?_⟩
      · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
      · intro r hr hep; rw [hls₁]; exact hidx₀ r hr hep
      · intro hheal; rw [hnot_heal] at hheal; exact Bool.noConfusion hheal
      · intro r hr hep hnc
        rcases huncomp₀ r hr hep hnc with ⟨hc_false, hct_m⟩
        have hle_ls : r.pos.idx ≤ st₀.1.lastSentIdx := hidx₀ r hr hep
        refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (hit₁ ▸ hr_fs)⟩
        cases hsc0 : st₀.1.senderCorruptedAt with
        | none =>
          simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
        | some j0 =>
          simpa [HState.isCompromised, hsc₁, hsc0] using hc_false
    rcases hs₀_pre with ⟨hnone, hidx0, hno_t⟩ | ⟨st₀, hsome, h1, h2, h3, h4, _, h6⟩
    · rw [hnone] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, hvu⟩
      exact hcs_from (hInit b .unknown) v0 hvu rfl hidx0.symm (by simp [hInit])
        (fun r hr hep => (hno_t r hr hep).elim)
        (fun r hr hep _ => (hno_t r hr hep).elim) hv0
    · rw [hsome, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      exact hcs_from st₀ v0 hvu h1 h2 h3 h4 h6 hv0
  · have hcf : (!(s₁.safeCh (2 + Δcka) (Party.senderOf t)) && !((hs₁.book s₀).getD {}).sCorr) = false :=
      Bool.eq_false_iff.mpr hcond
    simp only [hcf, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true] at hw
    rw [StateT.run_bind] at hw
    exact htr_tail hs₁ rc σ rfl (fun _ _ => rfl) hs₀_pre _
      (fun e hs_k => by simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure])
      hw

/-- Unified `vRecv` + `accept` step lemma for `deliverE`, `injectE`, and `deliverForgeE` (`la = false`). -/
private theorem vRecv_step_spec
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka : ℕ) (tL : Option ℕ) (t : ℕ) (P : Party)
    (es : _) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : MainActiveInv Δcka tL t es σ)
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (hcall : es.g.safeInj (2 + Δcka) = true ∨ ∃ r_hdr ∈ es.g.trans, r_hdr.ct.1 = c.1)
    (w : ((Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((vRecv (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false)
        es.g P (es.g.st P) c rec).run es.h) rc σ)) :
    w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧ MainActiveInv Δcka tL t { es with h := w.1.1.2 } w.2) ∨
    ∃ st' i' m',
      w.1.1.1 = some (some (st', c.1.1, i', m')) ∧
      (rec = none → c.1.1 = t → (es.g.inTransit P.other c).isSome = false →
        es.g.trivial (2 + Δcka) ⟨P.other, t, i'⟩ = true) ∧
      (rec = none → (es.g.inTransit P.other c).isSome = false →
        MainActiveInv Δcka tL t { es with h := w.1.1.2 } w.2) ∧
      (∀ pos : Pos,
        pos.epoch = c.1.1 →
        (c.1.1 = t →
          (rec = none ∧ (es.g.inTransit P.other c).isSome = false) ∨
          (∃ r ∈ es.g.trans, rec = some r ∧ r.pos = pos ∧ r.ct = c)) →
        MainActiveInv Δcka tL t { es with g := es.g.accept P st' pos, h := w.1.1.2 } w.2) := by
  unfold vRecv at hw
  simp only [StateT.run_bind] at hw
  have hidP : (es.g.st P).id = P := hact.hid P
  have htcurP : (es.g.st P).tcur = es.g.epoch P := hact.htcur P
  by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
  · simp only [hidP, htcurP, hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hw
    subst hw; exact Or.inr (Or.inl ⟨rfl, hact⟩)
  · simp only [hidP, htcurP] at hw
    have hguard' : ((P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = false) :=
      Bool.eq_false_iff.mpr hguard
    rcases Bool.or_eq_false_iff.mp hguard' with ⟨hnot_sends, hnot_gt⟩
    have hle_ep1 : c.1.1 ≤ es.g.epoch P + 1 := Nat.le_of_not_lt (of_decide_eq_false hnot_gt)
    have hP_recv : P = Party.receiverOf c.1.1 ∧ P.other = Party.senderOf c.1.1 := by
      rcases Nat.mod_two_eq_zero_or_one c.1.1 with hmod | hmod <;>
        cases P <;>
        simp [Party.sendsIn, Party.receiverOf, Party.senderOf, Party.other, hmod] at hnot_sends ⊢
    simp only [hnot_sends, Bool.false_or, hnot_gt, Bool.false_eq_true, ↓reduceIte] at hw
    -- Common continuation from `s₁` (`s₁? = some (some s₁)`) after `startRecv`:
    have hcont : ∀ (s₁ : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) ⊕ ℕ)
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (hs₁ : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)),
        hs₁.cache = es.h.cache →
        s₁.id = P →
        s₁.tcur = max (es.g.epoch P) c.1.1 →
        s₁.vS = (es.g.st P).vS →
        (c.1.1 ≤ es.g.epoch P → s₁.curCkaMsg = (es.g.st P).curCkaMsg) →
        (∀ v, s₁.vR t = some v → ∃ sIdx, v = .inr sIdx ∧
          (healedBy es.g.tL (2 + Δcka) t = true ∨
            (∃ Q, (es.g.st Q).vR t = some (.inr sIdx)) ∨
            (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
              ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))) →
        (∀ t' v, t' ≠ t → s₁.vR t' = some v → ∃ rs, v = .inl rs) →
        (c.1.1 ≠ t → s₁.vR t = (es.g.st P).vR t) →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((match s₁.vR c.1.1 with
            | none => pure (some none)
            | some v => do
              match ← (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
                  (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).fsRecv
                es.g P c.1.1 v c.1 c.2 rec with
              | none => pure none
              | some none => pure (some none)
              | some (some (v', i, m)) =>
                pure (some (some ({ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, c.1.1, i, m)))).run hs₁)
          rc σ) →
        (w.1.1.1 = none ∨
          (w.1.1.1 = some none ∧ MainActiveInv Δcka tL t { es with h := w.1.1.2 } w.2) ∨
          ∃ st' i' m',
            w.1.1.1 = some (some (st', c.1.1, i', m')) ∧
            (rec = none → c.1.1 = t → (es.g.inTransit P.other c).isSome = false →
              es.g.trivial (2 + Δcka) ⟨P.other, t, i'⟩ = true) ∧
            (rec = none → (es.g.inTransit P.other c).isSome = false →
              MainActiveInv Δcka tL t { es with h := w.1.1.2 } w.2) ∧
            (∀ pos : Pos,
              pos.epoch = c.1.1 →
              (c.1.1 = t →
                (rec = none ∧ (es.g.inTransit P.other c).isSome = false) ∨
                (∃ r ∈ es.g.trans, rec = some r ∧ r.pos = pos ∧ r.ct = c)) →
              MainActiveInv Δcka tL t { es with g := es.g.accept P st' pos, h := w.1.1.2 } w.2)) := by
      intro s₁ hs₁ hcache₁ hid₁ htcur₁ hvS₁ hcur₁ hvR₁_t hvR₁_ne hvR₁_unch hw_fs
      have hunch_hs₁ : MainActiveInv Δcka tL t { es with h := hs₁ } σ := {
        habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
        hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hcache₁ ▸ hc),
        hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hcache₁ ▸ hc),
        hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
        hsess := by rcases hact.hsess with ⟨sSend, hs, hpin⟩; exact ⟨sSend, hs, hpin.congr_cache hcache₁⟩
      }
      cases hvRc : s₁.vR c.1.1 with
      | none =>
        simp only [hvRc, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw_fs
        subst hw_fs; exact Or.inr (Or.inl ⟨rfl, hunch_hs₁⟩)
      | some v =>
        by_cases hct_eq : c.1.1 = t
        · rcases hvR₁_t v (hct_eq ▸ hvRc) with ⟨sIdx, rfl, hsafe_or_pin⟩
          simp only [hvRc, StateT.run_bind, runPubIdeal, simulateQ_bind, MonadAttach.mem_support_bind] at hw_fs
          rcases hw_fs with ⟨w_r, hw_r, hfin⟩
          rcases fsRecv_inr_step_post C ℓ Dh encPt encT idOf N Δcka tL t sIdx P es rc σ hact hsafe_or_pin
              c.1 c.2 rec hs₁ w_r (hct_eq ▸ hw_r) with hr_none | ⟨hr_rej, hc_r, hr_inv⟩ |
              ⟨i', m', s₀, st₀, st'_fs, hr_acc, hc_r, rfl, hpin₀, hle_s₀, heqvS_s₀, hvS_s₀, hne_s₀, h5₀, hσ_upd,
               hend', hls', hsc', hsub', hacc_wit⟩
          · simp only [hr_none, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hfin
            subst hfin; exact Or.inl rfl
          · simp only [hr_rej, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hfin
            subst hfin
            exact Or.inr (Or.inl ⟨rfl, hr_inv w_r.1.1.2 (hc_r.trans hcache₁)⟩)
          · simp only [hr_acc, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hfin
            subst hfin
            have hP_t : P = Party.receiverOf t ∧ P.other = Party.senderOf t := hct_eq ▸ hP_recv
            have hP_ne_send : P ≠ Party.senderOf t := by
              intro hEq
              have hsIn : P.sendsIn t = true := by
                rw [hEq]
                rcases Nat.mod_two_eq_zero_or_one t with hmod | hmod <;>
                  simp [Party.senderOf, Party.sendsIn, hmod]
              rw [hct_eq, hsIn] at hnot_sends; cases hnot_sends
            refine Or.inr (Or.inr ⟨_, i', m', rfl, ?_, ?_, ?_⟩)
            · intro _ _ hnot_tr
              rw [hP_t.2]
              unfold GameState.trivial
              by_cases hcomp_pos : (⟨Party.senderOf t, t, i'⟩ : Pos) ∈ es.g.comp
              · simp [hcomp_pos]
              · rcases hacc_wit with ⟨r_fs₀, hr_fs₀, hidx₀, had₀, hct₀, _⟩ | ⟨hnheal, hall_comp⟩
                · have hnheal : healedBy es.g.tL (2 + Δcka) t = false := by
                    cases hh : healedBy es.g.tL (2 + Δcka) t
                    · rfl
                    · rcases (h5₀.2.2.2.1 hh).2 r_fs₀ hr_fs₀ with ⟨m_c, hm_c⟩
                      rw [had₀, hct₀] at hm_c
                      have hit_some : (es.g.inTransit P.other c).isSome = true := by
                        rw [hP_t.2]; unfold GameState.inTransit
                        rw [Option.isSome_iff_ne_none]; intro hfn
                        have := List.find?_eq_none.mp hfn _ hm_c; simp at this
                      rw [hnot_tr] at hit_some; cases hit_some
                  have hany : es.g.trans.any (fun r => r.pos == ⟨Party.senderOf t, t, i'⟩) = false :=
                    Bool.eq_false_iff.mpr fun hany_t => by
                      rcases List.any_eq_true.mp hany_t with ⟨r, hr, hpos_beq⟩
                      have hpos_eq : r.pos = ⟨Party.senderOf t, t, i'⟩ := beq_iff_eq.mp hpos_beq
                      have hep_r : r.pos.epoch = t := by rw [hpos_eq]
                      have hnc_r : r.pos ∉ es.g.comp := by rw [hpos_eq]; exact hcomp_pos
                      have hct_eq_r : (r_fs₀.ad.1, r_fs₀.ct) = r.ct :=
                        (h5₀.2.2.2.2 r hr hep_r hnc_r).2 r_fs₀ hr_fs₀ (by rw [hpos_eq]; exact hidx₀)
                      have hrc : c = r.ct := Prod.ext had₀.symm hct₀.symm |>.trans hct_eq_r
                      have hit_some : (es.g.inTransit P.other c).isSome = true := by
                        rw [hP_t.2]; unfold GameState.inTransit
                        rw [Option.isSome_iff_ne_none]; intro hfn
                        have := List.find?_eq_none.mp hfn r hr
                        simp [hpos_eq, hrc] at this
                      rw [hnot_tr] at hit_some; cases hit_some
                  simp [hany, hnheal]
                · have hany : es.g.trans.any (fun r => r.pos == ⟨Party.senderOf t, t, i'⟩) = false :=
                    Bool.eq_false_iff.mpr fun hany_t => by
                      rcases List.any_eq_true.mp hany_t with ⟨r, hr, hpos_beq⟩
                      have hpos_eq : r.pos = ⟨Party.senderOf t, t, i'⟩ := beq_iff_eq.mp hpos_beq
                      exact hcomp_pos (hpos_eq ▸ hall_comp r hr (by rw [hpos_eq]) (by rw [hpos_eq]))
                  simp [hany, hnheal]
            · intro _ hnot_tr
              have hc_final : w_r.1.1.2.cache = es.h.cache := hc_r.trans hcache₁
              refine {
                habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
                hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hc_final ▸ hc),
                hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hc_final ▸ hc),
                hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
                hsess := ?_
              }
              rw [hσ_upd]
              refine ⟨some sIdx, ⟨hle_s₀, heqvS_s₀, ?_, ?_, by intro hnone; simp at hnone, ?_⟩,
                hpin₀.congr_cache hc_final⟩
              · intro Q idx hvS
                rcases hvS_s₀ Q idx hvS with ⟨rfl, rfl, hsend⟩
                refine ⟨rfl, rfl, fun hsIn => ?_⟩
                rcases hsend hsIn with ⟨hep_t, hls_s⟩
                exact ⟨hep_t, Or.inr ⟨st'_fs, by simp, hls'.trans hls_s⟩⟩
              · intro idx st hne_idx hst_j
                rw [Function.update_of_ne hne_idx] at hst_j
                exact hne_s₀ idx st hne_idx hst_j
              · intro st hst
                simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                refine ⟨hend', ?_, fun r hr hep => hls' ▸ h5₀.2.2.1 r hr hep, ?_, ?_⟩
                · intro r_fs hr_fs
                  rcases h5₀.2.1 r_fs (hsub' r_fs hr_fs) with ⟨h1, h2⟩
                  exact ⟨h1, hls' ▸ h2⟩
                · intro hheal
                  rcases hacc_wit with ⟨r_fs₀, hr_fs₀, _, had₀, hct₀, _⟩ | ⟨hnheal, _⟩
                  · rcases (h5₀.2.2.2.1 hheal).2 r_fs₀ hr_fs₀ with ⟨m_c, hm_c⟩
                    rw [had₀, hct₀] at hm_c
                    have hit_some : (es.g.inTransit P.other c).isSome = true := by
                      rw [hP_t.2]; unfold GameState.inTransit
                      rw [Option.isSome_iff_ne_none]; intro hfn
                      have := List.find?_eq_none.mp hfn _ hm_c; simp at this
                    rw [hnot_tr] at hit_some; cases hit_some
                  · rw [hheal] at hnheal; cases hnheal
                · intro r hr hep hnc
                  rcases h5₀.2.2.2.2 r hr hep hnc with ⟨hc_f, hct_m⟩
                  exact ⟨by simpa [HState.isCompromised, hsc'] using hc_f,
                    fun r_fs hr_fs => hct_m r_fs (hsub' r_fs hr_fs)⟩
            · intro pos hpos_ep hcase_t
              have hc_final : w_r.1.1.2.cache = es.h.cache := hc_r.trans hcache₁
              refine {
                habort := hact.habort
                hwin := hact.hwin
                hid := fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.accept, GameState.delete, hid₁]
                  · simp [GameState.accept, GameState.delete, Function.update_of_ne hQ, hact.hid Q]
                htcur := fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.accept, GameState.delete, htcur₁, hpos_ep]
                  · simp [GameState.accept, GameState.delete, Function.update_of_ne hQ, hact.htcur Q]
                hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hc_final ▸ hc)
                hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hc_final ▸ hc)
                hvR_t := fun Q v0 hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self] at hv0
                    rw [hct_eq, Function.update_self, Option.some.injEq] at hv0
                    exact ⟨sIdx, hv0.symm⟩
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                    exact hact.hvR_t Q v0 hv0
                hvR_ne := fun Q t' v0 hne hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self] at hv0
                    rw [hct_eq, Function.update_of_ne hne] at hv0
                    exact hvR₁_ne t' v0 hne hv0
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                    exact hact.hvR_ne Q t' v0 hne hv0
                htrans_wf := fun r hr => by
                  simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                  rcases hact.htrans_wf r hr.1 with ⟨h1, h2, h3, h4, h5⟩
                  refine ⟨h1, h2, ?_, ?_, h5⟩
                  · by_cases hS : r.pos.sender = P
                    · simp only [GameState.accept, GameState.delete, hS, Function.update_self]
                      rw [hS] at h3; omega
                    · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h3
                  · by_cases hS : r.pos.sender = P
                    · intro hmax
                      simp only [GameState.accept, GameState.delete, hS, Function.update_self] at hmax ⊢
                      have hr_sends : P.sendsIn r.pos.epoch = true := by
                        rw [← hS, h2]
                        rcases Nat.mod_two_eq_zero_or_one r.pos.epoch with hmod | hmod <;>
                          simp [Party.senderOf, Party.sendsIn, hmod]
                      have hne_rc : r.pos.epoch ≠ c.1.1 := by intro he; rw [he, hnot_sends] at hr_sends; cases hr_sends
                      rw [hS] at h3 h4
                      exact h4 (by omega)
                    · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h4
                hsess := ?_
              }
              rw [hσ_upd]
              refine ⟨some sIdx, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · simpa [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm] using hle_s₀
              · intro hep_acc
                simp only [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm] at hep_acc ⊢
                exact heqvS_s₀ hep_acc
              · intro Q idx hvS
                have hvS_old : (es.g.st Q).vS = some (.inr idx) := by
                  by_cases hQ : Q = P
                  · subst Q; simpa [GameState.accept, GameState.delete, hvS₁] using hvS
                  · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hvS
                rcases hvS_s₀ Q idx hvS_old with ⟨rfl, rfl, hsend⟩
                refine ⟨rfl, rfl, fun hsIn => ?_⟩
                simp only [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm] at hsIn ⊢
                rcases hsend hsIn with ⟨hep_t, hls_s⟩
                exact ⟨hep_t, Or.inr ⟨st'_fs, by simp, hls'.trans hls_s⟩⟩
              · intro idx st hne_idx hst_j
                rw [Function.update_of_ne hne_idx] at hst_j
                exact hne_s₀ idx st hne_idx hst_j
              · intro hnone; simp at hnone
              · intro st hst
                simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                refine ⟨hend', ?_, ?_, ?_, ?_⟩
                · intro r_fs hr_fs
                  rcases h5₀.2.1 r_fs (hsub' r_fs hr_fs) with ⟨h1, h2⟩
                  exact ⟨h1, hls' ▸ h2⟩
                · intro r hr hep
                  simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                  exact hls' ▸ h5₀.2.2.1 r hr.1 hep
                · intro hheal
                  have hheal0 : healedBy es.g.tL (2 + Δcka) t = true := hheal
                  rcases h5₀.2.2.2.1 hheal0 with ⟨hsc0, htr0⟩
                  rcases hacc_wit with ⟨r_fs₀, hr_fs₀, _, had₀, hct₀, hit_filt⟩ | ⟨hnheal, _⟩; swap
                  · rw [hheal0] at hnheal; cases hnheal
                  refine ⟨hsc'.trans hsc0, fun r_fs hr_fs => ?_⟩
                  rw [hit_filt, List.mem_filter, bne_iff_ne] at hr_fs
                  rcases htr0 r_fs hr_fs.1 with ⟨m0, hm0⟩
                  rcases hcase_t hct_eq with ⟨_, hnot_tr⟩ | ⟨r_rec, hr_rec_mem, _, rfl, hct_rec⟩
                  · rcases htr0 r_fs₀ hr_fs₀ with ⟨m_c, hm_c⟩
                    rw [had₀, hct₀] at hm_c
                    have hit_some : (es.g.inTransit P.other c).isSome = true := by
                      rw [hP_t.2]; unfold GameState.inTransit
                      rw [Option.isSome_iff_ne_none]; intro hfn
                      have := List.find?_eq_none.mp hfn _ hm_c; simp at this
                    rw [hnot_tr] at hit_some; cases hit_some
                  · have hidx_rec : r_fs₀.idx = r_rec.pos.idx := by
                      have hc1 := (h5₀.2.1 r_fs₀ hr_fs₀).1
                      have hc2 := (hact.htrans_wf r_rec hr_rec_mem).2.2.2.2 (hpos_ep.trans hct_eq)
                      calc r_fs₀.idx = r_fs₀.ct.1 := hc1.symm
                        _ = c.2.1 := congrArg Prod.fst hct₀
                        _ = r_rec.ct.2.1 := (congrArg (fun x => x.2.1) hct_rec).symm
                        _ = r_rec.pos.idx := hc2
                    have hpos_ne : (⟨Party.senderOf t, t, r_fs.idx⟩ : Pos) ≠ r_rec.pos := by
                      intro hp_eq
                      have := congrArg Pos.idx hp_eq
                      exact hr_fs.2 (this.trans hidx_rec.symm)
                    exact ⟨m0, by simp [GameState.accept, GameState.delete, hm0, hpos_ne]⟩
                · intro r hr hep hnc
                  simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
                  have hnc0 : r.pos ∉ es.g.comp := by
                    intro hc0; apply hnc
                    simp [GameState.accept, GameState.delete, hc0, hr.2]
                  rcases h5₀.2.2.2.2 r hr.1 hep hnc0 with ⟨hc_f, hct_m⟩
                  exact ⟨by simpa [HState.isCompromised, hsc'] using hc_f,
                    fun r_fs hr_fs => hct_m r_fs (hsub' r_fs hr_fs)⟩
              · refine ⟨fun Q v0 hv0 => ?_, fun ht_pos => ?_⟩
                · by_cases hQ : Q = P
                  · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self] at hv0
                    rw [hct_eq, Function.update_self, Option.some.injEq] at hv0
                    exact hv0.symm
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                    exact hpin₀.1 Q v0 hv0
                · rcases hpin₀.2 ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                  refine ⟨Tc, σc, k, hc_final ▸ hc_Tc, ?_, ?_⟩
                  · intro hep_acc
                    simp only [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm] at hep_acc ⊢
                    exact hcur_Tc hep_acc
                  · intro r hr hep_r
                    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                    exact htr_Tc r hr.1 hep_r
        · -- Off-target epoch `c.1.1 ≠ t`: `v` is `.inl rs` (`CoinOnly`), leaving `σ` and epoch-`t` records untouched!
          rcases hvR₁_ne c.1.1 v hct_eq hvRc with ⟨rs, rfl⟩
          simp only [hvRc] at hw_fs
          dsimp only [hooksFSMulti] at hw_fs
          cases hdec : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs c.1 c.2 with
          | none =>
            simp only [hdec, Option.map_none, StateT.run_pure, pure_bind, runPubIdeal,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fs
            subst hw_fs; exact Or.inr (Or.inl ⟨rfl, hunch_hs₁⟩)
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [hdec, Option.map_some, StateT.run_pure, pure_bind, runPubIdeal,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fs
            subst hw_fs
            refine Or.inr (Or.inr ⟨_, i', m', rfl, fun _ h => (hct_eq h).elim,
              fun _ _ => hunch_hs₁, ?_⟩)
            intro pos hpos_ep _
            have hpos_ne_t : ∀ r : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt), r.pos.epoch = t → r.pos ≠ pos := by
              intro r hr_ep hp; apply hct_eq; rw [← hpos_ep, ← hp, hr_ep]
            refine {
              habort := hact.habort
              hwin := hact.hwin
              hid := fun Q => by
                by_cases hQ : Q = P
                · subst Q; simp [GameState.accept, GameState.delete, hid₁]
                · simp [GameState.accept, GameState.delete, Function.update_of_ne hQ, hact.hid Q]
              htcur := fun Q => by
                by_cases hQ : Q = P
                · subst Q; simp [GameState.accept, GameState.delete, htcur₁, hpos_ep]
                · simp [GameState.accept, GameState.delete, Function.update_of_ne hQ, hact.htcur Q]
              hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hcache₁ ▸ hc)
              hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hcache₁ ▸ hc)
              hvR_t := fun Q v0 hv0 => by
                by_cases hQ : Q = P
                · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self] at hv0
                  rw [Function.update_of_ne (Ne.symm hct_eq), hvR₁_unch hct_eq] at hv0
                  exact hact.hvR_t P v0 hv0
                · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                  exact hact.hvR_t Q v0 hv0
              hvR_ne := fun Q t' v0 hne hv0 => by
                by_cases hQ : Q = P
                · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self] at hv0
                  by_cases ht' : t' = c.1.1
                  · subst ht'; rw [Function.update_self, Option.some.injEq] at hv0
                    exact ⟨rs', hv0.symm⟩
                  · rw [Function.update_of_ne ht'] at hv0
                    exact hvR₁_ne t' v0 hne hv0
                · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                  exact hact.hvR_ne Q t' v0 hne hv0
              htrans_wf := fun r hr => by
                simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                rcases hact.htrans_wf r hr.1 with ⟨h1, h2, h3, h4, h5⟩
                refine ⟨h1, h2, ?_, ?_, h5⟩
                · by_cases hS : r.pos.sender = P
                  · simp only [GameState.accept, GameState.delete, hS, Function.update_self]
                    rw [hS] at h3; omega
                  · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h3
                · by_cases hS : r.pos.sender = P
                  · intro hmax
                    simp only [GameState.accept, GameState.delete, hS, Function.update_self] at hmax ⊢
                    have hr_sends : P.sendsIn r.pos.epoch = true := by
                      rw [← hS, h2]
                      rcases Nat.mod_two_eq_zero_or_one r.pos.epoch with hmod | hmod <;>
                        simp [Party.senderOf, Party.sendsIn, hmod]
                    have hne_rc : r.pos.epoch ≠ c.1.1 := by intro he; rw [he, hnot_sends] at hr_sends; cases hr_sends
                    rw [hS] at h3 h4
                    exact h4 (by omega)
                  · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h4
              hsess := ?_
            }
            rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
            · refine ⟨none, ⟨?_, ?_, hs.2.2⟩, ?_⟩
              · by_cases hS : Party.senderOf t = P
                · simp only [GameState.accept, GameState.delete, hS, Function.update_self]
                  have := hs.1; rw [hS] at this; omega
                · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hs.1
              · intro Q idx hvS
                by_cases hQ : Q = P
                · subst Q; simp only [GameState.accept, GameState.delete, Function.update_self, hvS₁] at hvS
                  exact hs.2.1 P idx hvS
                · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hvS
                  exact hs.2.1 Q idx hvS
              · intro Q
                by_cases hQ : Q = P
                · subst Q
                  simp [GameState.accept, GameState.delete, Function.update_of_ne (Ne.symm hct_eq),
                    hvR₁_unch hct_eq, hpin P]
                · simp [GameState.accept, GameState.delete, Function.update_of_ne hQ, hpin Q]
            · refine ⟨some s₀, ⟨?_, ?_, ?_, hs.2.2.2.1, ?_, ?_⟩, ?_⟩
              · by_cases hS : Party.senderOf t = P
                · simp only [GameState.accept, GameState.delete, hS, Function.update_self]
                  have := hs.1; rw [hS] at this; omega
                · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hs.1
              · intro hep_acc
                by_cases hS : Party.senderOf t = P
                · simp only [GameState.accept, GameState.delete, hS, Function.update_self, hvS₁] at hep_acc ⊢
                  have := hs.1; rw [hS] at this
                  have hep_eq : es.g.epoch P = t := by omega
                  exact hS ▸ hs.2.1 (hS.symm ▸ hep_eq)
                · simp only [GameState.accept, GameState.delete, Function.update_of_ne hS] at hep_acc ⊢
                  exact hs.2.1 hep_acc
              · intro Q idx hvS
                have hvS_old : (es.g.st Q).vS = some (.inr idx) := by
                  by_cases hQ : Q = P
                  · subst Q; simpa [GameState.accept, GameState.delete, hvS₁] using hvS
                  · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hvS
                rcases hs.2.2.1 Q idx hvS_old with ⟨rfl, rfl, hsend⟩
                refine ⟨rfl, rfl, fun hsIn => ?_⟩
                by_cases hS : Party.senderOf t = P
                · simp only [GameState.accept, GameState.delete, hS, hpos_ep, Function.update_self] at hsIn ⊢
                  have hle_ep : c.1.1 ≤ es.g.epoch P := by
                    by_contra hgt; have hmax : max (es.g.epoch P) c.1.1 = c.1.1 := by omega
                    rw [hmax, hnot_sends] at hsIn; cases hsIn
                  have hmax : max (es.g.epoch P) c.1.1 = es.g.epoch P := Nat.max_eq_left hle_ep
                  rw [hmax] at hsIn ⊢
                  simpa [hS] using hsend (by simpa [hS] using hsIn)
                · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hsend
                    (by simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hsIn)
              · intro hnone r hr hep
                simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                exact hs.2.2.2.2.1 hnone r hr.1 hep
              · intro st hst
                have h5 := hs.2.2.2.2.2 st hst
                refine ⟨h5.1, h5.2.1, ?_, ?_, ?_⟩
                · intro r hr hep
                  simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                  exact h5.2.2.1 r hr.1 hep
                · intro hheal
                  rcases h5.2.2.2.1 hheal with ⟨hsc0, htr0⟩
                  refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
                  rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
                  have hne_p : (⟨Party.senderOf t, t, r_fs.idx⟩ : Pos) ≠ pos :=
                    hpos_ne_t ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m0, (r_fs.ad.1, r_fs.ct)⟩ rfl
                  exact ⟨m0, by simp [GameState.accept, GameState.delete, hm0, hne_p]⟩
                · intro r hr hep hnc
                  simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
                  have hnc0 : r.pos ∉ es.g.comp := by
                    intro hc0; apply hnc
                    simp [GameState.accept, GameState.delete, hc0, hr.2]
                  exact h5.2.2.2.2 r hr.1 hep hnc0
              · refine ⟨fun Q v0 hv0 => ?_, fun ht_pos => ?_⟩
                · by_cases hQ : Q = P
                  · subst Q
                    simp only [GameState.accept, GameState.delete, Function.update_self,
                      Function.update_of_ne (Ne.symm hct_eq), hvR₁_unch hct_eq] at hv0
                    exact hpin.1 P v0 hv0
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                    exact hpin.1 Q v0 hv0
                · rcases hpin.2 ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                  refine ⟨Tc, σc, k, hcache₁ ▸ hc_Tc, ?_, ?_⟩
                  · intro hep_acc
                    by_cases hS : Party.senderOf t = P
                    · simp only [GameState.accept, GameState.delete, hS, Function.update_self,
                        hpos_ep] at hep_acc ⊢
                      have hle_ep : c.1.1 ≤ es.g.epoch P := by omega
                      have hep_eq : es.g.epoch P = t := by omega
                      rw [hcur₁ hle_ep]
                      exact hS ▸ hcur_Tc (hS.symm ▸ hep_eq)
                    · simp only [GameState.accept, GameState.delete, Function.update_of_ne hS] at hep_acc ⊢
                      exact hcur_Tc hep_acc
                  · intro r hr hep_r
                    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                    exact htr_Tc r hr.1 hep_r
    -- Dispatch `if c.1.1 = es.g.epoch P + 1` in `vRecv`:
    by_cases hnext : c.1.1 = es.g.epoch P + 1
    · simp only [hnext, ↓reduceIte] at hw
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr (Or.inl ⟨rfl, hact⟩)
      | some Tn =>
        simp only [hc2, StateT.run_bind, runPubIdeal, simulateQ_bind,
          MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨w_sr, hw_sr, hw_tail⟩
        rcases startRecv_coinOnly_spec C ℓ Dh encPt encT idOf N Δcka tL t (es.g.epoch P + 1) P
            es.g (es.g.st P).γ (es.g.st P).root Tn es.h hact.hcache_t hact.hcache_ne rc σ w_sr hw_sr with
          ⟨⟨hc_sr, hres_sr⟩, rfl, rfl⟩
        rcases hres_sr with hr_none | hr_snone | ⟨γ', σr', rsv, hr_ok, hr_t, hr_ne⟩
        · simp only [hr_none, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_tail
          subst hw_tail; exact Or.inl rfl
        · simp only [hr_snone, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_tail
          subst hw_tail
          exact Or.inr (Or.inl ⟨rfl, {
            habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
            hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hc_sr ▸ hc),
            hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hc_sr ▸ hc),
            hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
            hsess := by rcases hact.hsess with ⟨sSend, hs, hpin⟩; exact ⟨sSend, hs, hpin.congr_cache hc_sr⟩
          }⟩)
        · simp only [hr_ok, pure_bind] at hw_tail
          refine hcont
            { id := P, root := σr', vS := (es.g.st P).vS,
              vR := Function.update (es.g.st P).vR (es.g.epoch P + 1) (some rsv),
              γ := γ', curCkaMsg := (es.g.st P).curCkaMsg, tcur := es.g.epoch P + 1 }
            w_sr.1.1.2 hc_sr rfl (by dsimp only; rw [hnext]; omega) rfl
            (fun hle => absurd hle (by omega)) ?_ ?_ ?_
            (by
              dsimp only [runPubIdeal] at hw_tail ⊢
              rw [hnext]
              simp only [Function.update_self, Function.update_idem] at hw_tail ⊢
              convert hw_tail using 7
              congr 1; funext x; rcases x with _ | (_ | ⟨_, _, _⟩) <;> rfl)
          · intro v0 hv0
            dsimp only at hv0
            by_cases heq_t : t = es.g.epoch P + 1
            · subst t; simp only [Function.update_self, Option.some.injEq] at hv0
              subst v0
              rcases hr_t rfl with ⟨sIdx, rfl, hpin_cache⟩
              refine ⟨sIdx, rfl, ?_⟩
              rcases hcall with hsafe | ⟨r_hdr, hr_mem, hr_ct1⟩
              · left
                cases htL : es.g.tL with
                | none => rfl
                | some l0 =>
                  unfold GameState.safeInj healedBy at hsafe
                  unfold healedBy
                  rw [htL] at hsafe
                  simp only [decide_eq_true_eq] at hsafe ⊢
                  cases P <;> simp at hsafe <;> omega
              · have hr_ep : r_hdr.pos.epoch = es.g.epoch P + 1 :=
                  (hact.htrans_wf r_hdr hr_mem).1.trans ((congrArg Prod.fst hr_ct1).trans hnext)
                rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
                · exfalso
                  have hwf := hact.htrans_wf r_hdr hr_mem
                  have hle := hwf.2.2.1
                  rw [hwf.2.1, hr_ep] at hle
                  have hlt := hs.1
                  omega
                · rcases hpin.2 (by omega) with ⟨Tc, σc, k, hc_Tc, _, htr_Tc⟩
                  have hTc_eq : Tn = Tc := by
                    have h1 : r_hdr.ct.1.2 = some Tc := htr_Tc r_hdr hr_mem hr_ep
                    have h2 : r_hdr.ct.1.2 = some Tn := (congrArg Prod.snd hr_ct1).trans hc2
                    exact Option.some.inj (h2.symm.trans h1)
                  subst Tn
                  have hsIdx_eq : sIdx = s₀ := hpin_cache σc k s₀ hc_Tc
                  subst sIdx
                  exact Or.inr (Or.inr ⟨by omega, ⟨r_hdr, hr_mem, hr_ep⟩, Tc, σc, k, hc_Tc⟩)
            · rw [Function.update_of_ne heq_t] at hv0
              rcases hact.hvR_t P v0 hv0 with ⟨sIdx, rfl⟩
              exact ⟨sIdx, rfl, Or.inr (Or.inl ⟨P, hv0⟩)⟩
          · intro t' v0 hne_t hv0
            dsimp only at hv0
            by_cases heq_t' : t' = es.g.epoch P + 1
            · subst t'; simp only [Function.update_self, Option.some.injEq] at hv0
              subst v0; exact hr_ne hne_t
            · rw [Function.update_of_ne heq_t'] at hv0; exact hact.hvR_ne P t' v0 hne_t hv0
          · intro hne_ct
            have hne_t : t ≠ es.g.epoch P + 1 := fun h => hne_ct (hnext.trans h.symm)
            simp [Function.update_of_ne hne_t]
    · have hle_cur : c.1.1 ≤ es.g.epoch P := by omega
      simp only [hnext, ↓reduceIte, pure_bind] at hw
      exact hcont (es.g.st P) es.h rfl hidP (htcurP.trans (Nat.max_eq_left hle_cur).symm)
        rfl (fun _ => rfl)
        (fun v0 hv0 => let ⟨sIdx, heq⟩ := hact.hvR_t P v0 hv0; ⟨sIdx, heq, Or.inr (Or.inl ⟨P, heq ▸ hv0⟩)⟩)
        (hact.hvR_ne P) (fun _ => rfl)
        (by
          suffices hM_eq :
              (match (es.g.st P).vR c.1.1 with
                | none => pure (some none)
                | some v => do
                  match ← (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
                      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false).fsRecv
                    es.g P c.1.1 v c.1 c.2 rec with
                  | none => pure none
                  | some none => pure (some none)
                  | some (some (v', i, m)) =>
                    pure (some (some ({ (es.g.st P) with vR := Function.update (es.g.st P).vR c.1.1 (some v') }, c.1.1, i, m)))) = _ by
            exact hM_eq ▸ hw
          cases (es.g.st P).vR c.1.1 with
          | none => rfl
          | some _ => exact congrArg (Bind.bind _) (funext fun x => by rcases x with _ | (_ | ⟨_, _, _⟩) <;> rfl))

/-- Single-query preservation of `MainInv Δcka tL t` across `implEDFPaper` (`la = false`, `gMain = false`). -/
private theorem implEDFPaper_step_mainInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (es : _) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hinv : MainInv Δcka tL t es σ)
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaper
          (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false)
          (2 + Δcka) qep maxForwardJumps (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy q).run es)
      rc σ)) :
    MainInv Δcka tL t w.1.1.2 w.2 := by
  -- Monotonicity of `healedBy` under `leak`:
  have hheal_leak : ∀ {S₀ : Type} (g : GameState S₀ (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (l : ℕ),
      healedBy (g.leak l).tL (2 + Δcka) t = true → healedBy g.tL (2 + Δcka) t = true := by
    intro S₀ g l hh
    cases htL : g.tL with
    | none => rfl
    | some l0 =>
      simp only [GameState.leak, CryptoGames.SM.maxOpt, htL, healedBy, decide_eq_true_eq] at hh ⊢
      omega
  rcases hinv with habort | hact
  · -- Frozen when `es.abort = true`:
    rcases q with n | ⟨⟨⟨⟨⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩ | ⟨P, c, c'⟩
    · simp only [implEDFPaper, QueryImpl.add_apply, coinsE, stateT_lift_run, query_eq_liftM,
        runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind,
        simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hw
      rcases hw with ⟨_, _, rfl⟩
      exact Or.inl habort
    all_goals
      simp only [implEDFPaper, QueryImpl.add_apply, transmitE, challE, deliverE,
        injectE, corrEPaper, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, habort, Bool.true_or, ↓reduceIte,
        StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw; exact Or.inl habort
  · -- Active state (`MainActiveInv Δcka tL t es σ`):
    rcases q with n | ⟨⟨⟨⟨⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩ | ⟨P, c, c'⟩
    · -- 1. `coinsE`
      simp only [implEDFPaper, QueryImpl.add_apply, coinsE, stateT_lift_run, query_eq_liftM,
        runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind,
        simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hw
      rcases hw with ⟨_, _, rfl⟩
      exact Or.inr hact
    · -- 2. `transmitE`
      simp only [implEDFPaper, QueryImpl.add_apply, transmitE,
        StateT.run_bind, StateT.run_get, pure_bind, hact.habort, hact.hwin, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte] at hw
      cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none =>
        simp only [hep, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr hact
      | some s₁ =>
        simp only [hep] at hw
        split_ifs at hw with hdoom
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact Or.inl rfl
        · -- Helper preserving `htrans_wf` across `s₁.record ... false` when `s₁.epoch P ≠ t` (or with `e.1 = idx'`):
          unfold GameState.epMgmt at hep
          by_cases hsIn1 : P.sendsIn (es.g.epoch P + 1) = true
          · simp only [hsIn1, ↓reduceIte] at hep
            by_cases hqep : qep < es.g.epoch P + 1
            · simp [hqep] at hep
            simp only [hqep, ↓reduceIte] at hep
            injection hep with hs₁_def; symm at hs₁_def
            have hs₁_st : s₁.st = es.g.st := by subst hs₁_def; split_ifs <;> rfl
            have hs₁_tr : s₁.trans = es.g.trans := by subst hs₁_def; split_ifs <;> rfl
            have hs₁_cp : s₁.comp = es.g.comp := by subst hs₁_def; split_ifs <;> rfl
            have hs₁_win : s₁.win = false := by subst hs₁_def; split_ifs <;> exact hact.hwin
            have hs₁_epP : s₁.epoch P = es.g.epoch P + 1 := by
              subst hs₁_def; split_ifs <;> simp [GameState.leak]
            have hs₁_epQ : ∀ Q, Q ≠ P → s₁.epoch Q = es.g.epoch Q := by
              intro Q hQ; subst hs₁_def; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
            have hs₁_idxP : s₁.idx P = 0 := by subst hs₁_def; split_ifs <;> simp [GameState.leak]
            have hs₁_idxQ : ∀ Q, Q ≠ P → s₁.idx Q = es.g.idx Q := by
              intro Q hQ; subst hs₁_def; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
            have hs₁_heal : healedBy s₁.tL (2 + Δcka) t = true → healedBy es.g.tL (2 + Δcka) t = true := by
              subst hs₁_def; split_ifs
              · exact hheal_leak es.g (es.g.epoch P + 1)
              · exact id
            rw [StateT.run_bind, liftH_run_eq, runPubIdeal_bind_eq, MonadAttach.mem_support_bind] at hw
            rcases hw with ⟨w_lift, hw_lift, hw_fin⟩
            rw [runPubIdeal_bind_eq, MonadAttach.mem_support_bind] at hw_lift
            rcases hw_lift with ⟨w_v, hw_v, hw_lp⟩
            simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_lp
            subst hw_lp
            dsimp only [vSend] at hw_v
            simp only [hs₁_st, hact.hid P, hact.htcur P, hsIn1, ↓reduceIte] at hw_v
            rw [StateT.run_bind, runPubIdeal_bind_eq, MonadAttach.mem_support_bind] at hw_v
            rcases hw_v with ⟨w_ss, hw_ss, hw_fs⟩
            rcases startSend_coinOnly_spec C ℓ Dh encPt encT idOf N Δcka tL t (es.g.epoch P + 1)
                P s₁ (es.g.st P).γ (es.g.st P).root r es.h rc σ w_ss hw_ss with
              ⟨⟨γ', T', σr', ssv, hss_ok, hss_t, hss_ne⟩, hss_rc, hss_σ⟩
            rw [hss_rc, hss_σ] at hw_fs
            simp only [hss_ok, pure_bind] at hw_fs
            dsimp only [runPubIdeal] at hw_fs hw_fin
            by_cases heq_t : es.g.epoch P + 1 = t
            · -- Entering target epoch `t`: `P = Party.senderOf t` and `sSend` was `none`!
              have hP_send : P = Party.senderOf t := by
                cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn1 heq_t ⊢ <;>
                  (rw [← heq_t]; exact hsIn1)
              rcases hss_t heq_t with ⟨s₀, σc_t, k_t, rfl, hc_t_eq, hc_t, hc_ne⟩
              have hold_none : (∀ idx st, σ idx = some st →
                  st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
                  st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
                  (∀ Q, (es.g.st Q).vR t = none) := by
                rcases hact.hsess with ⟨none | s₀', hs, hpin⟩
                · exact ⟨hs.2.2, hpin⟩
                · exfalso; have := hs.1; rw [← hP_send] at this; omega
              rcases hold_none with ⟨hnone_old, hvR_none_old⟩
              have hno_t_tr : ∀ r0 ∈ s₁.trans, r0.pos.epoch ≠ t := by
                intro r0 hr0 hep0
                rw [hs₁_tr] at hr0
                have hwf := hact.htrans_wf r0 hr0
                have hle := hwf.2.2.1
                rw [hwf.2.1, hep0, ← hP_send] at hle; omega
              have hs₀_pre :
                  (σ s₀ = none ∧ s₁.idx (Party.senderOf t) = 0 ∧ (∀ r0 ∈ s₁.trans, r0.pos.epoch ≠ t)) ∨
                  (∃ st₀, σ s₀ = some st₀ ∧ st₀.1.ended = false ∧
                    st₀.1.lastSentIdx = s₁.idx (Party.senderOf t) ∧
                    (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
                    (∀ r0 ∈ s₁.trans, r0.pos.epoch = t → r0.pos.idx ≤ st₀.1.lastSentIdx) ∧
                    (healedBy s₁.tL (2 + Δcka) t = true →
                      st₀.1.senderCorruptedAt = none ∧
                      (∀ r_fs ∈ st₀.1.inTransit,
                        ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) ∧
                    (∀ r0 ∈ s₁.trans, r0.pos.epoch = t → r0.pos ∉ s₁.comp →
                      st₀.1.isCompromised r0.pos.idx = false ∧
                      (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r0.pos.idx → (r_fs.ad.1, r_fs.ct) = r0.ct))) := by
                cases hσ0 : σ s₀ with
                | none => exact Or.inl ⟨rfl, hP_send ▸ hs₁_idxP, hno_t_tr⟩
                | some st₀ =>
                  rcases hnone_old s₀ st₀ hσ0 with ⟨he, hsc, hit, hls⟩
                  exact Or.inr ⟨st₀, rfl, he, hls.trans (hP_send ▸ hs₁_idxP).symm,
                    by simp [hit], fun r0 hr0 hep0 => (hno_t_tr r0 hr0 hep0).elim,
                    fun _ => ⟨hsc, by simp [hit]⟩,
                    fun r0 hr0 hep0 _ => (hno_t_tr r0 hr0 hep0).elim⟩
              simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hw_fs
              rcases hw_fs with ⟨w_sd, hw_sd, hw_ret⟩
              rcases fsSend_inr_step_post C ℓ Dh encPt encT idOf N Δcka tL t s₀ s₁
                  (es.g.epoch P + 1, some T') pm w_ss.1.1.2 rc σ
                  (hP_send ▸ hs₁_epP.trans heq_t) hs₀_pre w_sd
                  (by rw [← hP_send, ← heq_t]; exact hw_sd) with hsd_none |
                  ⟨rawCt, st₂, hsd_ok, hc_sd, hσ_upd, hend₂, hls₂, hit₂, hrec₂⟩
              · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw_ret
                subst hw_ret
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin; exact Or.inl rfl
              · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw_ret
                subst hw_ret
                simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin
                subst hP_send
                rcases hrec₂ _ with ⟨hrec_idx, hrec_heal, hrec_unc⟩
                refine Or.inr {
                  habort := hact.habort
                  hwin := hs₁_win
                  hid := fun Q => by
                    by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp [GameState.record, hact.hid]
                    · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hact.hid Q]
                  htcur := fun Q => by
                    by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp [GameState.record, hact.htcur, hs₁_epP]
                    · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ, hact.htcur Q]
                  hcache_t := fun Tc σc k optIdx hc => ⟨s₀, hc_t Tc σc k optIdx (hc_sd ▸ hc)⟩
                  hcache_ne := fun t' Tc σc k optIdx hne hc =>
                    hact.hcache_ne t' Tc σc k optIdx hne ((hc_ne t' hne).symm ▸ hc_sd ▸ hc)
                  hvR_t := fun Q v0 hv0 => by
                    by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp only [GameState.record, Function.update_self] at hv0
                      exact hact.hvR_t _ v0 hv0
                    · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                      exact hact.hvR_t Q v0 hv0
                  hvR_ne := fun Q t' v0 hne hv0 => by
                    by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp only [GameState.record, Function.update_self] at hv0
                      exact hact.hvR_ne _ t' v0 hne hv0
                    · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                      exact hact.hvR_ne Q t' v0 hne hv0
                  htrans_wf := fun r0 hr0 => by
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · refine ⟨hs₁_epP, by rw [hs₁_epP, heq_t], by simp [GameState.record], fun _ => by simp [GameState.record], fun _ => rfl⟩
                    · rw [hs₁_tr] at hr_old
                      rcases hact.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4, h5⟩
                      refine ⟨h1, h2, ?_, ?_, h5⟩
                      · by_cases hS : r0.pos.sender = Party.senderOf t
                        · rw [hS, GameState.record, hs₁_epP]; rw [hS] at h3; omega
                        · simpa [GameState.record, hs₁_epQ _ hS] using h3
                      · by_cases hS : r0.pos.sender = Party.senderOf t
                        · intro hEq; exfalso; simp only [GameState.record, hS, hs₁_epP] at hEq
                          rw [hS] at h3; omega
                        · simpa [GameState.record, Function.update_of_ne hS, hs₁_epQ _ hS, hs₁_idxQ _ hS] using h4
                  hsess := ?_
                }
                rw [hσ_upd]
                refine ⟨some s₀, ⟨by simp [GameState.record, hs₁_epP, heq_t],
                  fun _ => by simp [GameState.record], ?_, ?_, by intro h; simp at h, ?_⟩, ?_⟩
                · intro Q idx hvS
                  by_cases hQ : Q = Party.senderOf t
                  · subst Q; simp only [GameState.record, Function.update_self, Option.some.injEq,
                      Sum.inr.injEq] at hvS
                    subst hvS
                    refine ⟨rfl, rfl, fun _ => ⟨hs₁_epP.trans heq_t, Or.inr ⟨st₂, by simp, ?_⟩⟩⟩
                    simp [GameState.record, hls₂]
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                    rcases hact.hsess with ⟨none | s₀', hs, _⟩
                    · exact (hs.2.1 Q idx hvS).elim
                    · exfalso; have := hs.1; omega
                · intro idx st hne_idx hst_j
                  rw [Function.update_of_ne hne_idx] at hst_j
                  exact hnone_old idx st hst_j
                · intro st hst
                  simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                  dsimp only
                  simp only [hs₁_epP, heq_t] at hrec_idx hrec_heal hrec_unc ⊢
                  exact ⟨hend₂, hit₂, hrec_idx, hrec_heal, hrec_unc⟩
                · refine ⟨fun Q v0 hv0 => ?_, fun _ => ?_⟩
                  · by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp only [GameState.record, Function.update_self] at hv0
                      rw [hvR_none_old] at hv0; cases hv0
                    · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                      rw [hvR_none_old Q] at hv0; cases hv0
                  · refine ⟨T', σc_t, k_t, hc_sd ▸ hc_t_eq,
                      fun _ => by simp [GameState.record], ?_⟩
                    intro r0 hr0 hep0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · rfl
                    · exact (hno_t_tr r0 hr_old hep0).elim
            · -- Entering off-target epoch `es.g.epoch P + 1 ≠ t`: `ssv = .inl ss` (`CoinOnly`)!
              rcases hss_ne heq_t with ⟨⟨ss, rfl⟩, hc_t, hc_ne⟩
              dsimp only [hooksFSMulti] at hw_fs
              simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_fs
              subst hw_fs
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              have hep_ne_t : s₁.epoch P ≠ t := hs₁_epP ▸ heq_t
              refine Or.inr {
                habort := hact.habort
                hwin := hs₁_win
                hid := fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, hact.hid]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hact.hid Q]
                htcur := fun Q => by
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, hact.htcur, hs₁_epP]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ, hact.htcur Q]
                hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hc_t ▸ hc)
                hcache_ne := fun t' Tc σc k optIdx hne hc =>
                  hc_ne t' Tc σc k optIdx hne (hact.hcache_ne t' · · · · hne) hc
                hvR_t := fun Q v0 hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self] at hv0
                    exact hact.hvR_t P v0 hv0
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                    exact hact.hvR_t Q v0 hv0
                hvR_ne := fun Q t' v0 hne hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self] at hv0
                    exact hact.hvR_ne P t' v0 hne hv0
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                    exact hact.hvR_ne Q t' v0 hne hv0
                htrans_wf := fun r0 hr0 => by
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · refine ⟨hs₁_epP, ?_, by simp [GameState.record], fun _ => by simp [GameState.record], fun h => (hep_ne_t h).elim⟩
                    rw [hs₁_epP]; cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn1 ⊢ <;> exact hsIn1
                  · rw [hs₁_tr] at hr_old
                    rcases hact.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4, h5⟩
                    refine ⟨h1, h2, ?_, ?_, h5⟩
                    · by_cases hS : r0.pos.sender = P
                      · rw [hS, GameState.record, hs₁_epP]; rw [hS] at h3; omega
                      · simpa [GameState.record, hs₁_epQ _ hS] using h3
                    · by_cases hS : r0.pos.sender = P
                      · intro hEq; exfalso
                        simp only [GameState.record, hS, hs₁_epP] at hEq
                        rw [hS] at h3; omega
                      · simpa [GameState.record, Function.update_of_ne hS, hs₁_epQ _ hS, hs₁_idxQ _ hS] using h4
                hsess := ?_
              }
              rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
              · refine ⟨none, ⟨?_, ?_, hs.2.2⟩, ?_⟩
                · by_cases hS : Party.senderOf t = P
                  · simp only [GameState.record, hS, hs₁_epP]
                    have := hs.1; rw [hS] at this; omega
                  · simpa [GameState.record, hs₁_epQ _ hS] using hs.1
                · intro Q idx hvS
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record] at hvS
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                    exact hs.2.1 Q idx hvS
                · intro Q
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, hpin P]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hpin Q]
              · refine ⟨some s₀, ⟨?_, ?_, ?_, hs.2.2.2.1, ?_, ?_⟩, ?_⟩
                · by_cases hS : Party.senderOf t = P
                  · simp only [GameState.record, hS, hs₁_epP]
                    have := hs.1; rw [hS] at this; omega
                  · simpa [GameState.record, hs₁_epQ _ hS] using hs.1
                · intro hep_rec
                  by_cases hS : Party.senderOf t = P
                  · exfalso; simp only [GameState.record, hS] at hep_rec; exact hep_ne_t hep_rec
                  · simp only [GameState.record, Function.update_of_ne hS, hs₁_st, hs₁_epQ _ hS] at hep_rec ⊢
                    exact hs.2.1 hep_rec
                · intro Q idx hvS
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record] at hvS
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                    rcases hs.2.2.1 Q idx hvS with ⟨rfl, rfl, hsend⟩
                    refine ⟨rfl, rfl, fun hsIn => ?_⟩
                    simp only [GameState.record, hs₁_epQ _ hQ, Function.update_of_ne hQ, hs₁_idxQ _ hQ] at hsIn ⊢
                    exact hsend hsIn
                · intro hnone r0 hr0 hep0
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · exact hep_ne_t hep0
                  · exact hs.2.2.2.2.1 hnone r0 (hs₁_tr ▸ hr_old) hep0
                · intro st hst
                  have h5 := hs.2.2.2.2.2 st hst
                  refine ⟨h5.1, h5.2.1, ?_, ?_, ?_⟩
                  · intro r0 hr0 hep0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · exact (hep_ne_t hep0).elim
                    · exact h5.2.2.1 r0 (hs₁_tr ▸ hr_old) hep0
                  · intro hheal_g'
                    rcases h5.2.2.2.1 (hs₁_heal hheal_g') with ⟨hsc0, htr0⟩
                    refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
                    rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
                    exact ⟨m0, by simp [GameState.record, hs₁_tr, hm0]⟩
                  · intro r0 hr0 hep0 hnc0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · exact (hep_ne_t hep0).elim
                    · have hnc_old : r0.pos ∉ es.g.comp := by
                        intro hc; apply hnc0
                        simp only [GameState.record, hs₁_cp]; split_ifs <;> simp [hc]
                      exact h5.2.2.2.2 r0 (hs₁_tr ▸ hr_old) hep0 hnc_old
                · refine ⟨fun Q v0 hv0 => ?_, fun ht_pos => ?_⟩
                  · by_cases hQ : Q = P
                    · subst Q; simp only [GameState.record, Function.update_self] at hv0
                      exact hpin.1 P v0 hv0
                    · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                      exact hpin.1 Q v0 hv0
                  · rcases hpin.2 ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                    refine ⟨Tc, σc, k, hc_t ▸ hc_Tc, ?_, ?_⟩
                    · intro hep_rec
                      by_cases hS : Party.senderOf t = P
                      · exfalso; simp only [GameState.record, hS] at hep_rec; exact hep_ne_t hep_rec
                      · simp only [GameState.record, Function.update_of_ne hS, hs₁_st, hs₁_epQ _ hS] at hep_rec ⊢
                        exact hcur_Tc hep_rec
                    · intro r0 hr0 hep0
                      simp only [GameState.record, List.mem_cons] at hr0
                      rcases hr0 with rfl | hr_old
                      · exact (hep_ne_t hep0).elim
                      · exact htr_Tc r0 (hs₁_tr ▸ hr_old) hep0
          · -- Staying in current sending epoch (`P.sendsIn (es.g.epoch P + 1) = false`, so `s₁ = es.g`):
            have hsIn0 : P.sendsIn (es.g.epoch P) = true := by
              cases P <;> simp [Party.sendsIn] at hsIn1 ⊢ <;> omega
            simp only [hsIn1, Bool.false_eq_true, ↓reduceIte] at hep
            by_cases hqep : qep < es.g.epoch P
            · simp [hqep] at hep
            simp only [hqep, ↓reduceIte] at hep
            injection hep with hs₁_eq; subst hs₁_eq
            rw [StateT.run_bind, liftH_run_eq, runPubIdeal_bind_eq, MonadAttach.mem_support_bind] at hw
            rcases hw with ⟨w_lift, hw_lift, hw_fin⟩
            rw [runPubIdeal_bind_eq, MonadAttach.mem_support_bind] at hw_lift
            rcases hw_lift with ⟨w_sd, hw_sd, hw_lp⟩
            simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_lp
            subst hw_lp
            dsimp only [vSend] at hw_sd
            simp only [hact.hid P, hact.htcur P, hsIn1, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_pure, pure_bind] at hw_sd
            dsimp only [runPubIdeal] at hw_sd hw_fin
            by_cases heq_t : es.g.epoch P = t
            · -- Current sending epoch IS `t`: `P = Party.senderOf t` and `(es.g.st P).vS = some (.inr s₀)`!
              have hP_send : P = Party.senderOf t := by
                cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn0 heq_t ⊢ <;>
                  (rw [← heq_t]; exact hsIn0)
              subst hP_send
              rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
              · exfalso; have := hs.1; omega
              · have hvS_eq : (es.g.st (Party.senderOf t)).vS = some (.inr s₀) := hs.2.1 heq_t
                rcases (hs.2.2.1 _ s₀ hvS_eq).2.2 hsIn0 with ⟨_, hpre_idx⟩
                simp only [hvS_eq, hact.htcur (Party.senderOf t), StateT.run_bind, simulateQ_bind,
                  MonadAttach.mem_support_bind] at hw_sd
                rcases hw_sd with ⟨w_fs, hw_fs, hw_ret⟩
                rcases fsSend_inr_step_post C ℓ Dh encPt encT idOf N Δcka tL t s₀ es.g
                    (es.g.epoch (Party.senderOf t), (es.g.st (Party.senderOf t)).curCkaMsg) pm es.h rc σ
                    heq_t
                    (by
                      rcases hpre_idx with ⟨hnone, hidx0⟩ | ⟨st₀, hsome, hls0⟩
                      · exact Or.inl ⟨hnone, hidx0, hs.2.2.2.2.1 hnone⟩
                      · have h5 := hs.2.2.2.2.2 st₀ hsome
                        exact Or.inr ⟨st₀, hsome, h5.1, hls0, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2⟩)
                    w_fs (heq_t ▸ hw_fs) with hsd_none |
                    ⟨rawCt, st₂, hsd_ok, hc_sd, hσ_upd, hend₂, hls₂, hit₂, hrec₂⟩
                · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hw_ret
                  subst hw_ret
                  simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                  subst hw_fin; exact Or.inl rfl
                · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hw_ret
                  subst hw_ret
                  simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                  subst hw_fin
                  rcases hrec₂ _ with ⟨hrec_idx, hrec_heal, hrec_unc⟩
                  refine Or.inr {
                    habort := hact.habort
                    hwin := hact.hwin
                    hid := fun Q => by
                      by_cases hQ : Q = Party.senderOf t
                      · subst Q; simp [GameState.record, hact.hid]
                      · simp [GameState.record, Function.update_of_ne hQ, hact.hid Q]
                    htcur := fun Q => by
                      by_cases hQ : Q = Party.senderOf t
                      · subst Q; simp [GameState.record, hact.htcur]
                      · simp [GameState.record, Function.update_of_ne hQ, hact.htcur Q]
                    hcache_t := fun Tc σc k optIdx hc => hact.hcache_t Tc σc k optIdx (hc_sd ▸ hc)
                    hcache_ne := fun t' Tc σc k optIdx hne hc => hact.hcache_ne t' Tc σc k optIdx hne (hc_sd ▸ hc)
                    hvR_t := fun Q v0 hv0 => by
                      by_cases hQ : Q = Party.senderOf t
                      · subst Q; simp only [GameState.record, Function.update_self] at hv0
                        exact hact.hvR_t _ v0 hv0
                      · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                        exact hact.hvR_t Q v0 hv0
                    hvR_ne := fun Q t' v0 hne hv0 => by
                      by_cases hQ : Q = Party.senderOf t
                      · subst Q; simp only [GameState.record, Function.update_self] at hv0
                        exact hact.hvR_ne _ t' v0 hne hv0
                      · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                        exact hact.hvR_ne Q t' v0 hne hv0
                    htrans_wf := fun r0 hr0 => by
                      simp only [GameState.record, List.mem_cons] at hr0
                      rcases hr0 with rfl | hr_old
                      · refine ⟨rfl, by rw [heq_t], le_rfl, fun _ => by simp [GameState.record], fun _ => rfl⟩
                      · rcases hact.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4, h5⟩
                        refine ⟨h1, h2, h3, ?_, h5⟩
                        by_cases hS : r0.pos.sender = Party.senderOf t
                        · intro hEq
                          dsimp only [GameState.record] at hEq
                          have := h4 hEq
                          rw [hS] at this
                          simp [GameState.record, hS]
                          omega
                        · simpa [GameState.record, Function.update_of_ne hS] using h4
                    hsess := ?_
                  }
                  rw [hσ_upd]
                  refine ⟨some s₀, ⟨hs.1, fun _ => by simp [GameState.record], ?_, ?_, by intro h; simp at h, ?_⟩, ?_⟩
                  · intro Q idx hvS
                    by_cases hQ : Q = Party.senderOf t
                    · subst Q; simp only [GameState.record, Function.update_self, Option.some.injEq,
                        Sum.inr.injEq] at hvS
                      subst hvS
                      refine ⟨rfl, rfl, fun _ => ⟨heq_t, Or.inr ⟨st₂, by simp, ?_⟩⟩⟩
                      simp [GameState.record, hls₂]
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                      exact ((hs.2.2.1 Q idx hvS).1 |> hQ).elim
                  · intro idx st hne_idx hst_j
                    rw [Function.update_of_ne hne_idx] at hst_j
                    exact hs.2.2.2.1 idx st hne_idx hst_j
                  · intro st hst
                    simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                    simpa only [heq_t] using And.intro hend₂ (And.intro hit₂ (And.intro hrec_idx (And.intro hrec_heal hrec_unc)))
                  · refine ⟨fun Q v0 hv0 => ?_, fun ht_pos => ?_⟩
                    · by_cases hQ : Q = Party.senderOf t
                      · subst Q; simp only [GameState.record, Function.update_self] at hv0
                        exact hpin.1 _ v0 hv0
                      · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                        exact hpin.1 Q v0 hv0
                    · rcases hpin.2 ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                      refine ⟨Tc, σc, k, hc_sd ▸ hc_Tc,
                        fun _ => by simpa [GameState.record] using hcur_Tc heq_t, ?_⟩
                      intro r0 hr0 hep0
                      simp only [GameState.record, List.mem_cons] at hr0
                      rcases hr0 with rfl | hr_old
                      · exact hcur_Tc heq_t
                      · exact htr_Tc r0 hr_old hep0
            · -- Off-target sending epoch `es.g.epoch P ≠ t`: `(es.g.st P).vS` cannot be `some (.inr _)`!
              have hvS_not_inr : ∀ idx, (es.g.st P).vS ≠ some (.inr idx) := by
                intro idx hvS
                rcases hact.hsess with ⟨none | s₀, hs, _⟩
                · exact hs.2.1 P idx hvS
                · rcases hs.2.2.1 P idx hvS with ⟨rfl, rfl, hsend⟩
                  exact heq_t (hsend hsIn0).1
              have hpure_off : ∃ st' e_out,
                  w_sd.1.1.1 = some (st', (es.g.epoch P, (es.g.st P).curCkaMsg), e_out) ∧
                  w_sd.1.1.2 = es.h ∧ w_sd.2 = σ ∧
                  st'.id = P ∧ st'.tcur = es.g.epoch P ∧ st'.vR = (es.g.st P).vR ∧
                  (∀ idx, st'.vS ≠ some (.inr idx)) := by
                cases hvS0 : (es.g.st P).vS with
                | none =>
                  simp only [hvS0, hact.htcur P, StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hw_sd
                  subst hw_sd
                  exact ⟨es.g.st P, default, rfl, rfl, rfl, hact.hid P, hact.htcur P, rfl, hvS_not_inr⟩
                | some v0 =>
                  cases v0 with
                  | inr idx => exact (hvS_not_inr idx hvS0).elim
                  | inl ss =>
                    dsimp only [hooksFSMulti] at hw_sd
                    simp only [hvS0, hact.htcur P, StateT.run_bind, StateT.run_pure, pure_bind,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_sd
                    subst hw_sd
                    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by intro _ h; simp at h⟩
              rcases hpure_off with ⟨st', e_out, hsd_ok, hwsd_h, hwsd_σ, hid', htcur', hvR', hvS'⟩
              rw [hwsd_h, hwsd_σ] at hw_fin
              simp only [hsd_ok, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              refine Or.inr {
                habort := hact.habort, hwin := hact.hwin,
                hid := fun Q => by by_cases hQ : Q = P <;> [subst Q; skip] <;>
                  simp [GameState.record, Function.update_of_ne, hid', hact.hid, *],
                htcur := fun Q => by by_cases hQ : Q = P <;> [subst Q; skip] <;>
                  simp [GameState.record, Function.update_of_ne, htcur', hact.htcur, *],
                hcache_t := hact.hcache_t, hcache_ne := hact.hcache_ne,
                hvR_t := fun Q v0 hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self, hvR'] at hv0
                    exact hact.hvR_t P v0 hv0
                  · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                    exact hact.hvR_t Q v0 hv0,
                hvR_ne := fun Q t' v0 hne hv0 => by
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self, hvR'] at hv0
                    exact hact.hvR_ne P t' v0 hne hv0
                  · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                    exact hact.hvR_ne Q t' v0 hne hv0,
                htrans_wf := fun r0 hr0 => by
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · refine ⟨rfl, ?_, by simp [GameState.record], fun _ => by simp [GameState.record], fun h => (heq_t h).elim⟩
                    cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn0 ⊢ <;> exact hsIn0
                  · rcases hact.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4, h5⟩
                    refine ⟨h1, h2, h3, ?_, h5⟩
                    by_cases hS : r0.pos.sender = P
                    · intro hEq
                      simp only [GameState.record, hS, Function.update_self] at hEq ⊢
                      have := h4 (by simpa [hS] using hEq)
                      rw [hS] at this; omega
                    · simpa [GameState.record, Function.update_of_ne hS] using h4,
                hsess := ?_
              }
              rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
              · refine ⟨none, ⟨hs.1, fun Q idx hvS => ?_, hs.2.2⟩, ?_⟩
                · by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self] at hvS; exact hvS' idx hvS
                  · simp only [GameState.record, Function.update_of_ne hQ] at hvS; exact hs.2.1 Q idx hvS
                · intro Q
                  by_cases hQ : Q = P
                  · subst Q; simp [GameState.record, hvR', hpin P]
                  · simp [GameState.record, Function.update_of_ne hQ, hpin Q]
              · refine ⟨some s₀, ⟨hs.1, ?_, ?_, hs.2.2.2.1, ?_, ?_⟩, ?_⟩
                · intro hep_rec
                  by_cases hS : Party.senderOf t = P
                  · exact (heq_t (hS ▸ hep_rec)).elim
                  · simp only [GameState.record, Function.update_of_ne hS] at hep_rec ⊢; exact hs.2.1 hep_rec
                · intro Q idx hvS
                  by_cases hQ : Q = P
                  · subst Q; simp only [GameState.record, Function.update_self] at hvS; exact (hvS' idx hvS).elim
                  · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                    rcases hs.2.2.1 Q idx hvS with ⟨rfl, rfl, hsend⟩
                    exact ⟨rfl, rfl, fun hsIn => by simpa [GameState.record, Function.update_of_ne hQ] using hsend hsIn⟩
                · intro hnone r0 hr0 hep0
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · exact heq_t hep0
                  · exact hs.2.2.2.2.1 hnone r0 hr_old hep0
                · intro st hst
                  have h5 := hs.2.2.2.2.2 st hst
                  refine ⟨h5.1, h5.2.1, ?_, ?_, ?_⟩
                  · intro r0 hr0 hep0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old; · exact (heq_t hep0).elim
                    exact h5.2.2.1 r0 hr_old hep0
                  · intro hheal_g'
                    rcases h5.2.2.2.1 hheal_g' with ⟨hsc0, htr0⟩
                    refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
                    rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
                    exact ⟨m0, by simp [GameState.record, hm0]⟩
                  · intro r0 hr0 hep0 hnc0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old; · exact (heq_t hep0).elim
                    have hnc_old : r0.pos ∉ es.g.comp := by
                      intro hc; apply hnc0; simp only [GameState.record]; split_ifs <;> simp [hc]
                    exact h5.2.2.2.2 r0 hr_old hep0 hnc_old
                · refine ⟨fun Q v0 hv0 => ?_, fun ht_pos => ?_⟩
                  · by_cases hQ : Q = P
                    · subst Q; simp only [GameState.record, Function.update_self, hvR'] at hv0
                      exact hpin.1 P v0 hv0
                    · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                      exact hpin.1 Q v0 hv0
                  · rcases hpin.2 ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                    refine ⟨Tc, σc, k, hc_Tc, ?_, ?_⟩
                    · intro hep_rec
                      by_cases hS : Party.senderOf t = P
                      · exact (heq_t (hS ▸ hep_rec)).elim
                      · simp only [GameState.record, Function.update_of_ne hS] at hep_rec ⊢
                        exact hcur_Tc hep_rec
                    · intro r0 hr0 hep0
                      simp only [GameState.record, List.mem_cons] at hr0
                      rcases hr0 with rfl | hr_old
                      · exact (heq_t hep0).elim
                      · exact htr_Tc r0 hr_old hep0
    · -- 3. `challE`: `(Config.auth t).challAllowedIn _ = false`!
      simp only [implEDFPaper, QueryImpl.add_apply, challE,
        StateT.run_bind, StateT.run_get, pure_bind, hact.habort, hact.hwin, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte] at hw
      cases h_ep : es.g.epMgmt (2 + Δcka) qep P r.isSome <;>
        simp only [h_ep, Mode.cfg, Config.auth, Bool.not_false, Bool.or_true, ↓reduceIte,
          StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw <;>
        subst hw <;> exact Or.inr hact
    · -- 4. `deliverE`
      simp only [implEDFPaper, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, hact.habort, hact.hwin, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte] at hw
      cases hit_find : es.g.inTransit P.other c with
      | none =>
        simp only [hit_find, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr hact
      | some r_del =>
        have hr_mem : r_del ∈ es.g.trans := List.mem_of_find?_eq_some hit_find
        have hr_pred := List.find?_some hit_find
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
        have hr_ep : r_del.pos.epoch = c.1.1 :=
          (hact.htrans_wf r_del hr_mem).1.trans (congrArg (fun x => x.1.1) hr_pred.2)
        simp only [hit_find, Mode.cfg, Config.auth, Bool.false_and, StateT.run_bind,
          liftH_run_eq, runPubIdeal, simulateQ_bind, MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨w_v, hw_v, hw_fin⟩
        rcases hw_v with ⟨w_vr, hw_vr, hw_lp⟩
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_lp
        subst hw_lp
        rcases vRecv_step_spec C ℓ Dh encPt encT idOf N Δcka tL t P es rc σ hact c (some r_del)
            (Or.inr ⟨r_del, hr_mem, congrArg Prod.fst hr_pred.2⟩)
            w_vr hw_vr with hvr_none | ⟨hvr_rej, hinv_rej⟩ | ⟨st', i', m', hvr_acc, _, _, hacc_inv⟩
        · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inl rfl
        · simp only [hvr_rej, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inr hinv_rej
        · dsimp only [commitE, hooksFSMulti] at hw_fin
          simp only [hvr_acc, StateT.run_bind, liftH_run_eq, StateT.run_pure,
            pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_modify,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin
          have hidem : { es.g.accept P st' r_del.pos with st := Function.update (es.g.accept P st' r_del.pos).st P st' } =
              es.g.accept P st' r_del.pos := by
            cases es.g; simp [GameState.accept, Function.update_idem]
          rw [hidem]
          exact Or.inr (hacc_inv r_del.pos hr_ep fun _ => Or.inr ⟨r_del, hr_mem, rfl, rfl, hr_pred.2⟩)
    · -- 5. `injectE`
      simp only [implEDFPaper, QueryImpl.add_apply, injectE, StateT.run_bind, StateT.run_get, pure_bind] at hw
      by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr hact
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hw
        have hsafe_inj : es.g.safeInj (2 + Δcka) = true := by
          cases hsi : es.g.safeInj (2 + Δcka)
          · exfalso; apply hguard; simp [hsi]
          · rfl
        have hnot_tr : (es.g.inTransit P.other c).isSome = false := by
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
          exact hguard.1.2
        simp only [StateT.run_bind, liftH_run_eq, runPubIdeal, simulateQ_bind,
          MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨w_v, ⟨w_vr, hw_vr, hw_lp⟩, hw_fin⟩
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_lp
        subst hw_lp
        rcases vRecv_step_spec C ℓ Dh encPt encT idOf N Δcka tL t P es rc σ hact c none
            (Or.inl hsafe_inj)
            w_vr hw_vr with hvr_none | ⟨hvr_rej, hinv_rej⟩ | ⟨st', i', m', hvr_acc, htriv_t, hnoacc_inv, hacc_inv⟩
        · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inl rfl
        · simp only [hvr_rej, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inr hinv_rej
        · simp only [hvr_acc] at hw_fin
          by_cases hcap : qep + 1 < c.1.1
          · simp only [hcap, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inr (hnoacc_inv rfl hnot_tr)
          · simp only [hcap, ↓reduceIte] at hw_fin
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte] at hw_fin
              dsimp only [commitE, hooksFSMulti] at hw_fin
              simp only [StateT.run_bind, liftH_run_eq, StateT.run_pure,
                pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              have hidem : { es.g.accept P st' ⟨P.other, c.1.1, i'⟩ with
                  st := Function.update (es.g.accept P st' ⟨P.other, c.1.1, i'⟩).st P st' } =
                  es.g.accept P st' ⟨P.other, c.1.1, i'⟩ := by
                cases es.g; simp [GameState.accept, Function.update_idem]
              rw [hidem]
              exact Or.inr (hacc_inv ⟨P.other, c.1.1, i'⟩ rfl fun _ => Or.inl ⟨rfl, hnot_tr⟩)
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hw_fin
              have hne_t : c.1.1 ≠ t := by
                intro heq_t
                exact htriv (heq_t.symm ▸ htriv_t rfl heq_t hnot_tr)
              simp only [Mode.cfg, Config.auth, beq_iff_eq, hne_t, ↓reduceIte, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inr (hnoacc_inv rfl hnot_tr)
    · -- 6. `corrEPaper`
      simp only [implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind, StateT.run_get, pure_bind] at hw
      by_cases hguard : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr hact
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hw
        by_cases hdoom : (({ auth := true, tL := tL, tStar := t } : Mode).policy.leakDoom es.g (es.g.afterCorr P) ||
            ({ auth := true, tL := tL, tStar := t } : Mode).policy.corrDoom es.g P) = true
        · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact Or.inl rfl
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hw
          dsimp only [hooksFSMulti] at hw
          simp only [StateT.run_bind, liftH_run_eq, runPubIdeal, simulateQ_bind,
            MonadAttach.mem_support_bind] at hw
          rcases hw with ⟨w_rv, ⟨w_h, hw_h, hw_lp⟩, hw_fin⟩
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_lp
          subst hw_lp
          -- Split `(es.g.st P).vS` in `hooksFSMulti.reveal`:
          have hafter_heal : healedBy (es.g.afterCorr P).tL (2 + Δcka) t = true →
              healedBy es.g.tL (2 + Δcka) t = true := by
            intro hh
            dsimp only [GameState.afterCorr] at hh
            exact hheal_leak _ (max (es.g.epoch .A) (es.g.epoch .B)) hh
          cases hvSP : (es.g.st P).vS with
          | none =>
            simp only [hvSP, StateT.run_pure, pure_bind] at hw_h
            split at hw_h <;> simp [runPubIdeal] at hw_h <;> subst hw_h
            · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inl rfl
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              refine Or.inr {
                habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
                hcache_t := hact.hcache_t, hcache_ne := hact.hcache_ne,
                hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
                hsess := ?_
              }
              rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
              · exact ⟨none, hs, by simpa [SessPinOpt, GameState.afterCorr, GameState.leak] using hpin⟩
              · refine ⟨some s₀, ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, fun st hst => ?_⟩,
                  by simpa [SessPinOpt, GameState.afterCorr, GameState.leak] using hpin⟩
                have h5 := hs.2.2.2.2.2 st hst
                refine ⟨h5.1, h5.2.1, h5.2.2.1, fun hh => h5.2.2.2.1 (hafter_heal hh),
                  fun r0 hr0 hep0 hnc0 => h5.2.2.2.2 r0 hr0 hep0 ?_⟩
                intro hc; apply hnc0; simp [GameState.afterCorr, GameState.leak, hc]
          | some vS0 =>
            cases vS0 with
            | inl ss =>
              simp only [hvSP, StateT.run_pure, pure_bind] at hw_h
              split at hw_h <;> simp [runPubIdeal] at hw_h <;> subst hw_h
              · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin; exact Or.inl rfl
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin
                refine Or.inr {
                  habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
                  hcache_t := hact.hcache_t, hcache_ne := hact.hcache_ne,
                  hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
                  hsess := ?_
                }
                rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
                · exact ⟨none, hs, by simpa [SessPinOpt, GameState.afterCorr, GameState.leak] using hpin⟩
                · refine ⟨some s₀, ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, fun st hst => ?_⟩,
                    by simpa [SessPinOpt, GameState.afterCorr, GameState.leak] using hpin⟩
                  have h5 := hs.2.2.2.2.2 st hst
                  refine ⟨h5.1, h5.2.1, h5.2.2.1, fun hh => h5.2.2.2.1 (hafter_heal hh),
                    fun r0 hr0 hep0 hnc0 => h5.2.2.2.2 r0 hr0 hep0 ?_⟩
                  intro hc; apply hnc0; simp [GameState.afterCorr, GameState.leak, hc]
            | inr sIdx =>
              rcases hact.hsess with ⟨none | s₀, hs, hpin⟩
              · exact (hs.2.1 P sIdx hvSP).elim
              · rcases hs.2.2.1 P sIdx hvSP with ⟨rfl, rfl, hsend⟩
                have hnot_heal_after : healedBy (es.g.afterCorr (Party.senderOf t)).tL (2 + Δcka) t = false := by
                  have hle : t ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
                    have := hs.1
                    cases hP : Party.senderOf t <;> (rw [hP] at this; omega)
                  cases htL : es.g.tL <;>
                    simp [GameState.afterCorr, GameState.leak, _root_.CryptoGames.SM.maxOpt, htL, healedBy] <;> omega
                simp only [hvSP, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hw_h
                rcases runPubIdeal_liftFSMulti_corruptSender_support C ℓ encT idOf N sIdx es.h _
                    rc σ w_h hw_h with ⟨u, hu, hwu⟩
                have hcs_rev : ∀ (st₀ : IdealHSt Pt ℓ)
                    (v0 : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) × IdealHSt Pt ℓ),
                    u = (v0.1, some v0.2) →
                    st₀.1.ended = false →
                    (σ sIdx = none → st₀.1.lastSentIdx = 0 ∧ ∀ r0 ∈ es.g.trans, r0.pos.epoch ≠ t) →
                    (∀ st_ex, σ sIdx = some st_ex → st₀ = st_ex) →
                    (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
                    (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos.idx ≤ st₀.1.lastSentIdx) →
                    (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos ∉ es.g.comp →
                      st₀.1.isCompromised r0.pos.idx = false ∧
                      (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r0.pos.idx → (r_fs.ad.1, r_fs.ct) = r0.ct)) →
                    v0 ∈ support ((corruptSenderH (m := ProbComp) (lChainPRG C.F) (hpIdeal N false) ()).run st₀) →
                    MainInv Δcka tL t w.1.1.2 w.2 := by
                  intro st₀ v0 hu_eq hend₀ hif_none hif_some hit₀ hidx₀ hunc₀ hu_cs
                  rw [hu_eq] at hwu
                  rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ v0.2 v0.1 hend₀ hu_cs with
                    ⟨hsome_res, hend₁, hsc₁, hls₁, hit₁⟩
                  rcases Option.isSome_iff_exists.mp hsome_res with ⟨ss_out, hu1⟩
                  simp only [hu1, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] at hwu
                  split at hwu <;> simp only [↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
                    support_pure, Set.mem_singleton_iff] at hwu <;> subst hwu
                  · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                    subst hw_fin; exact Or.inl rfl
                  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                    subst hw_fin
                    refine Or.inr {
                      habort := hact.habort, hwin := hact.hwin, hid := hact.hid, htcur := hact.htcur,
                      hcache_t := hact.hcache_t, hcache_ne := hact.hcache_ne,
                      hvR_t := hact.hvR_t, hvR_ne := hact.hvR_ne, htrans_wf := hact.htrans_wf,
                      hsess := ?_
                    }
                    refine ⟨some sIdx, ⟨hs.1, hs.2.1, ?_, ?_, by intro h; simp at h, ?_⟩,
                      by simpa [SessPinOpt, GameState.afterCorr, GameState.leak] using hpin⟩
                    · intro Q idx hvSQ
                      rcases hs.2.2.1 Q idx hvSQ with ⟨rfl, rfl, hsendQ⟩
                      refine ⟨rfl, rfl, fun hsIn => ?_⟩
                      rcases hsendQ hsIn with ⟨hep_t, ⟨hnone, hidx0⟩ | ⟨st_ex, hsome, hls_ex⟩⟩
                      · exact ⟨hep_t, Or.inr ⟨v0.2, by simp, hls₁.trans ((hif_none hnone).1.trans hidx0.symm)⟩⟩
                      · have hst_eq := hif_some st_ex hsome; subst hst_eq
                        exact ⟨hep_t, Or.inr ⟨v0.2, by simp, hls₁.trans hls_ex⟩⟩
                    · intro idx st hne_idx hst_j
                      simp only at hst_j
                      rw [Function.update_of_ne hne_idx] at hst_j
                      exact hs.2.2.2.1 idx st hne_idx hst_j
                    · intro st hst
                      simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                      refine ⟨hend₁, ?_, fun r0 hr0 hep0 => hls₁ ▸ hidx₀ r0 hr0 hep0, ?_, ?_⟩
                      · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
                      · intro hh
                        change healedBy (es.g.afterCorr (Party.senderOf t)).tL (2 + Δcka) t = true at hh
                        rw [hnot_heal_after] at hh; cases hh
                      · intro r0 hr0 hep0 hnc0
                        have hnc_old : r0.pos ∉ es.g.comp := by
                          intro hc; apply hnc0; simp [GameState.afterCorr, GameState.leak, hc]
                        rcases hunc₀ r0 hr0 hep0 hnc_old with ⟨hc_f, hct_m⟩
                        have hle_ls := hidx₀ r0 hr0 hep0
                        refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (hit₁ ▸ hr_fs)⟩
                        cases hsc0 : st₀.1.senderCorruptedAt with
                        | none => simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
                        | some j0 => simpa [HState.isCompromised, hsc₁, hsc0] using hc_f
                cases hσ0 : σ sIdx with
                | none =>
                  rw [hσ0] at hu
                  simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
                    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
                  rcases hu with ⟨b, _, v0, hv0, hvu⟩
                  exact hcs_rev (hInit b .unknown) v0 hvu rfl (fun _ => ⟨rfl, hs.2.2.2.2.1 hσ0⟩)
                    (fun _ h => by rw [hσ0] at h; cases h) (by simp [hInit])
                    (fun r0 hr0 hep0 => (hs.2.2.2.2.1 hσ0 r0 hr0 hep0).elim)
                    (fun r0 hr0 hep0 _ => (hs.2.2.2.2.1 hσ0 r0 hr0 hep0).elim) hv0
                | some st₀ =>
                  rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
                  rcases hu with ⟨v0, hv0, hvu⟩
                  simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
                  have h5 := hs.2.2.2.2.2 st₀ hσ0
                  exact hcs_rev st₀ v0 hvu h5.1 (fun h => by rw [hσ0] at h; cases h)
                    (fun _ h => Option.some.inj (hσ0.symm.trans h)) h5.2.1 h5.2.2.1 h5.2.2.2.2 hv0
    · -- 7. `deliverForgeE`
      simp only [implEDFPaper, QueryImpl.add_apply, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, hact.habort, hact.hwin, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte] at hw
      cases hit_c : es.g.inTransit P.other c with
      | none =>
        simp only [hit_c, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact Or.inr hact
      | some r_ref =>
        simp only [hit_c] at hw
        by_cases hguard : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r_ref.pos || c.1 != c'.1) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw
          subst hw; exact Or.inr hact
        · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hw
          have hr_ref_mem : r_ref ∈ es.g.trans := List.mem_of_find?_eq_some hit_c
          have hr_ref_pred := List.find?_some hit_c
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_ref_pred
          have hc_hdr_eq : c.1 = c'.1 := by
            by_contra hne; apply hguard; simp [hne]
          have hnot_tr' : (es.g.inTransit P.other c').isSome = false := by
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
            exact hguard.1.1
          simp only [StateT.run_bind, liftH_run_eq, runPubIdeal, simulateQ_bind,
            MonadAttach.mem_support_bind] at hw
          rcases hw with ⟨w_v, ⟨w_vr, hw_vr, hw_lp⟩, hw_fin⟩
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_lp
          subst hw_lp
          rcases vRecv_step_spec C ℓ Dh encPt encT idOf N Δcka tL t P es rc σ hact c' none
              (Or.inr ⟨r_ref, hr_ref_mem, (congrArg Prod.fst hr_ref_pred.2).trans hc_hdr_eq⟩)
              w_vr hw_vr with hvr_none | ⟨hvr_rej, hinv_rej⟩ | ⟨st', i', m', hvr_acc, htriv_t, hnoacc_inv, hacc_inv⟩
          · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inl rfl
          · simp only [hvr_rej, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inr hinv_rej
          · simp only [hvr_acc] at hw_fin
            by_cases hcap : (decide (qep + 1 < c'.1.1) || c'.1.1 != r_ref.pos.epoch) = true
            · simp only [hcap, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inr (hnoacc_inv rfl hnot_tr')
            · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at hw_fin
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
              · simp only [htriv, ↓reduceIte] at hw_fin
                dsimp only [commitE, hooksFSMulti] at hw_fin
                simp only [StateT.run_bind, liftH_run_eq, StateT.run_pure,
                  pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw_fin
                subst hw_fin
                have hidem : { es.g.accept P st' ⟨P.other, c'.1.1, i'⟩ with
                    st := Function.update (es.g.accept P st' ⟨P.other, c'.1.1, i'⟩).st P st' } =
                    es.g.accept P st' ⟨P.other, c'.1.1, i'⟩ := by
                  cases es.g; simp [GameState.accept, Function.update_idem]
                rw [hidem]
                exact Or.inr (hacc_inv ⟨P.other, c'.1.1, i'⟩ rfl fun _ => Or.inl ⟨rfl, hnot_tr'⟩)
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hw_fin
                have hne_t : c'.1.1 ≠ t := by
                  intro heq_t
                  exact htriv (heq_t.symm ▸ htriv_t rfl heq_t hnot_tr')
                simp only [Mode.cfg, Config.auth, beq_iff_eq, hne_t, ↓reduceIte, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin; exact Or.inr (hnoacc_inv rfl hnot_tr')

private theorem runPubIdeal_bind_support_false {α β : Type}
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {N : ℕ}
    (x : OracleComp (PubMultiSpec Pt ℓ) α)
    (f : α → OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false (x >>= f) rc σ)) :
    ∃ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (f z.1.1) z.1.2 z.2) := by
  simpa only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] using hw

private theorem redFSAuthDFPaperMulti_la_false_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (N Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N false
      (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep false tL t A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hsim : ∀ (m : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      es rc σ, MainInv Δcka tL t es σ →
      ∀ u ∈ support (runPubIdeal C ℓ encT idOf N false
        ((simulateQ (implEDFPaper
            (hooksFSMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, t⟩ false false)
            (2 + Δcka) qep maxForwardJumps (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy) m).run es)
        rc σ),
        MainInv Δcka tL t u.1.1.2 u.2 := by
    intro m
    induction m using OracleComp.inductionOn with
    | pure a =>
      intro es rc σ hinv u hu
      simp only [simulateQ_pure, StateT.run_pure, runPubIdeal, support_pure,
        Set.mem_singleton_iff] at hu
      subst hu
      exact hinv
    | query_bind q k ih =>
      intro es rc σ hinv u hu
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind] at hu
      rcases runPubIdeal_bind_support_false _ _ rc σ hu with ⟨z, hz, hu'⟩
      exact ih z.1.1.1 z.1.1.2 z.1.2 z.2
        (implEDFPaper_step_mainInv C ℓ Dh encPt encT idOf N Δcka qep tL t q es rc σ hinv z hz)
        u hu'
  intro w hw
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper at hw
  have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms, bind_assoc] at hw
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw with ⟨z₀, hz₀, hw₁⟩
  have ⟨hinv₀, hrc₀, hσ₀⟩ := initFSMultiRaw_mainInv C ℓ Dh encPt encT idOf lam N Δcka tL t
    (fun _ => false) (fun _ => none) z₀ hz₀
  rw [hrc₀, hσ₀] at hw₁
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw₁ with ⟨z₁, hz₁, hw₂⟩
  have hinv₁ := hsim A z₀.1.1 (fun _ => false) (fun _ => none) hinv₀ z₁ hz₁
  simp only [Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hw₂
  subst hw₂
  exact authOut_eq_false_of_mainInv hinv₁

end PaperMultiEndZero

section MultiSessEndZero

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)

/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFPaperMulti`. -/
theorem multiSessEndWinProb_redFSAuthDFPaperMulti_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la' tL t A))
      la = 0 := by
  refine multiSessEndWinProb_eq_zero_of_hpIdeal C ℓ encT idOf q qR
    (fun la' =>
      redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la' tL t A)
    la (fun la' s => ?_) hqR ?_
  · convert redFSAuthDFPaperMulti_sess_isQueryBoundP
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep tL t la' A hq s using 2
    rename_i x; rcases x with _ | ⟨_, _⟩ <;> rfl
  · refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT idOf
      (authHopCutoff maxForwardJumps qR la) la _ ?_
    cases la with
    | false =>
      exact redFSAuthDFPaperMulti_la_false_zero C ℓ Dh encPt encT idOf lam
        (authHopCutoff maxForwardJumps qR false) Δcka qep tL t A
    | true =>
      exact redFSAuthDFPaperMulti_la_true_zero C ℓ Dh encPt encT idOf lam
        (authHopCutoff maxForwardJumps qR true) Δcka qep tL t A

end MultiSessEndZero

end

end Computational.Proofs.E2E.SessionAuthMultiEnd
