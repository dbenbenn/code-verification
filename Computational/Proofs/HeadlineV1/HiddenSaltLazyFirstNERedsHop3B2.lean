/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs

import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
import Computational.Specifications.Session.StatementIdsModel
import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
import Computational.Proofs.CryptoGames.SM.Engine
import Computational.Proofs.CryptoGames.SM.Reductions
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForge
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS2
import Computational.Proofs.E2E.SessionAuthBridge
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import Computational.Proofs.SessionCostedFig8.BundlesCompilers
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B2

public section

open scoped ENNReal
open OracleComp OracleSpec
open _root_.ReductionDsl (CostedReduction)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.PRFPRNG (prngOps prngSMCodecDF)
open _root_.CryptoGames.FSAEAD (EncMsgsOk MakesAtMostQueries RatchetReceiverState
  RatchetSenderState challengeQuery corruptSenderQuery deliverQuery encBadMsg injectQuery
  transmitQuery)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.E2E (idsOf)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (GuardedSMDFShort SendMsgsOkDF badSendMsgDF)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32
  LibsignalMsgPublicPart dummyKey lAead lChainPRG lFS lPubOf)
open _root_.CryptoGames.SM (Config GameState specDF)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiSpec FSMultiState Header Mode PartyState
  fsClamp fsaeadMultiHeaderAdIface hooksFSMulti initFSMultiRaw liftFSMulti lookupMultiF mkParties
  regSessMulti regSessOptMulti rootFSMulti sampleT)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF
  afterCorrShifted corrEShiftedPaper deliverForgeE deliverForgeEB1 implEDFShiftedPaperGen injectEB1
  localAuthDFShiftedPaper trivB1)
open _root_.CryptoGames.SM.Engine (EState Hooks HooksVRInv Policy RSReach SMEngineInv SMVRInv TComp
  VP abortE challE coinsE commitE deliverE implE implEDFShiftedPaper_inv implEDFShiftedPaper_vrInv
  run_liftH_bind transmitE vRecv vRecvStep1 vRecv_eq_bind vSend vSendStep1 vSend_eq_bind)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (fsAuthCompBoundWith fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (AllPartiesInv DdhRoleOk
  HooksLocalCKAAgree commitE_localCKA_eq ddhRoleOk_initA ddhRoleOk_initB
  dhSchemeFb_receive_of_roleOk dhSchemeFb_send_of_roleOk implE_localCKA_eq vRecv_localCKA_eq)
open Computational.Proofs.E2E.SessionAuthBridge (RouterAdvCompat multiSessPubToAD)
open Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK
  (redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2
  (redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedPaperMultiProg
   redFSAuthDFShiftedPaperMultiGen redFSAuthDFShiftedPaperMultiGen_fsClamp_fromAEADPRG
   redFSAuthDFShiftedPaperMultiGenProg_eval_clamp runFSMultiDFShiftedPaper)
open Computational.Proofs.ReductionDsl.Fig8Atomic (RSReachB atomicShortPubB
  atomicShortPubB_imp_shortB dhSchemeFb fsAtomicB fsAtomicB_receive_eq fsAtomicB_send_eq)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic
  compileFsMultiDFAtomic_encMsgsOk compileFsMultiDFAtomic_isQueryBoundP
  compileFsMultiDFAtomic_routerAdvCompat)
open Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
  (redFSAuthDFCasePaperMultiAtomicProg redFSAuthDFShiftedPaperMultiAtomicProg)

private theorem fsAuthCompBoundWith_eq_fsAeadAuthSlotSumBound
    {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) {encT : Pt → PublicKey} {idOf : Party → IdentityKey} (qR : ℕ)
    (R : CryptoVerification.LibsignalSession.FsCostedReds C protoSignalCodec ℓ encT idOf)
    (A : Bool → Bool → CryptoVerification.LibsignalSession.FsAdv Pt ℓ) : fsAuthCompBoundWith C protoSignalCodec ℓ qR R A =
      CryptoVerification.E2E.fsAeadAuthSlotSumBound C qR R A := by
  unfold fsAuthCompBoundWith CryptoVerification.E2E.fsAeadAuthSlotSumBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun _ _ => ?_)
  dsimp only; rw [add_assoc]
private theorem hooksFSMulti_localCKAAgree
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq E] [SampleableType Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) (hooksFSMulti (dhSchemeFb Dh) prng fs Δcka mo gMain la)
      (hooksFSMulti (dhScheme Dh) prng fs Δcka mo gMain la) where
  startSend_eq _ P t γ σ r h ht hSend hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [hooksFSMulti]
    have hCoins : ∀ coins : BitVec 256,
        let body := fun c : CryptoGames.CKA.DDH.State (BitVec 256) Pt × Pt × Pt => (do
          let (σ', k, sid) ← rootFSMulti (SS := SS) (RS := RS) (M := M) (E := E) prng mo t c.2.2 σ
          let optIdx ← regSessOptMulti (SS := SS) (RS := RS) (M := M) (E := E) sid
          modify fun (s : FSMultiState Pt RSt K Pt E) => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender k) | some sIdx => .inr sIdx
          pure (some (c.1, c.2.1, σ', ssv)))
        (body ((dhSchemeFb Dh).send γ coins)).run h = (body ((dhScheme Dh).send γ coins)).run h ∧
        ∀ q ∈ support ((body ((dhScheme Dh).send γ coins)).run h), ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
      intro coins; dsimp only
      have hsnd := dhSchemeFb_send_of_roleOk Dh hRole hSend' coins
      have hRole' : DdhRoleOk P t ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
      simp only [hsnd.1]; refine ⟨trivial, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨⟨⟨σ₁, k₁, sid⟩, h₂⟩, _, hq⟩ := hq
      rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨⟨optIdx, h₃⟩, _, hq⟩ := hq
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [mem_support_bind_iff] at hq; obtain ⟨coins, _, hq⟩ := hq; exact (hCoins coins).2 q hq γ' T' σ' ss hEq
    · simp only [pure_bind]; exact hCoins c
  startRecv_eq _ P t γ σ Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksFSMulti]; simp only [hrcv.1]; refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hq
    cases hcache : h.cache t with
    | none =>
      simp only [hcache] at hq
      split_ifs at hq
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
      · rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
        rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq; exact hRole'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
    | some val =>
      rcases val with ⟨Tc, σc, k, optIdx⟩; simp only [hcache] at hq
      by_cases hT : Tc = Tn
      · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq; exact hRole'
      · simp only [hT, ↓reduceIte] at hq; split_ifs at hq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
        · rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
          rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq; exact hRole'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl
private theorem implEDFShiftedPaper_localCKA_step
    {Pt ι HS RSt SS RS M E σV ssV rsV : Type} {TSpec : OracleSpec.{0, 0} ι} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E
      (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (b1 : Bool) (l Δ qep maxSkip tStar : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (t : (CryptoGames.SM.specDF (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)).Domain)
    (hEs : AllPartiesInv es) : (implEDFShiftedPaperGen b1 l hk₁ Δ qep maxSkip tStar cfg π (.inr t)).run es =
      (implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π (.inr t)).run es ∧
    ∀ res ∈ support ((implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π (.inr t)).run es), AllPartiesInv res.2 := by
  rcases t with ((t3 | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inl t3)) hEs
  · cases b1
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inr (P, c))) hEs
    · change (injectEB1 hk₁ qep tStar cfg (P, c)).run es =
          (injectEB1 hk₂ qep tStar cfg (P, c)).run es ∧
        ∀ res ∈ support ((injectEB1 hk₂ qep tStar cfg (P, c)).run es), AllPartiesInv res.2
      unfold injectEB1 abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2)) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c none es.h (hEs P)
        simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
        refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_, fun res hmem => ?_⟩
        · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · rfl
          · rfl
          · by_cases hqep : qep + 1 < t'
            · simp [hqep]
            · simp only [hqep, ↓reduceIte]
              by_cases htriv : trivB1 tStar es.g ⟨P.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte, StateT.run_bind]; rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                  { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
              · simp [htriv]
        · rw [mem_support_bind_iff] at hmem; obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
          · by_cases hqep : qep + 1 < t'
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
            · simp only [hqep, ↓reduceIte] at hmem
              by_cases htriv : trivB1 tStar es.g ⟨P.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
                obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
                have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                  { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
                rcases cmRes with _ | s₁
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact hcm.2 s₁ rfl
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                split_ifs at hmem <;>
                  (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs)
  · change (corrEShiftedPaper l hk₁ π P).run es = (corrEShiftedPaper l hk₂ π P).run es ∧
        ∀ res ∈ support ((corrEShiftedPaper l hk₂ π P).run es), AllPartiesInv res.2
    refine ⟨by unfold corrEShiftedPaper; rw [hAg.reveal_eq], fun res hmem => ?_⟩
    unfold corrEShiftedPaper abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
    · rw [run_liftH_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem
      rcases revRes with _ | _ <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro Q;
          simpa [AllPartiesInv, afterCorrShifted, GameState.leak] using hEs Q)
  · cases b1 <;>
      [ (change (deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es = (deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es ∧
           ∀ res ∈ support ((deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es), AllPartiesInv res.2;
         unfold deliverForgeE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind];
         generalize es.g.trivial Δ = trivF);
        (change (deliverForgeEB1 hk₁ qep tStar cfg (P, c, c')).run es = (deliverForgeEB1 hk₂ qep tStar cfg (P, c, c')).run es ∧
           ∀ res ∈ support ((deliverForgeEB1 hk₂ qep tStar cfg (P, c, c')).run es), AllPartiesInv res.2;
         unfold deliverForgeEB1 abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind];
         generalize trivB1 tStar es.g = trivF) ]
    all_goals
      by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases htr : es.g.inTransit P.other c with _ | r
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
          · simp only [hchk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
          · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c' none es.h (hEs P)
            simp only [hchk, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
            refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_, fun res hmem => ?_⟩
            · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
              · rfl
              · rfl
              · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
                · simp [hqep]
                · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
                  by_cases htriv : trivF ⟨P.other, t', i'⟩ = true
                  · simp only [htriv, ↓reduceIte, StateT.run_bind]
                    rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                      { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
                  · simp [htriv]
            · rw [mem_support_bind_iff] at hmem; obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
              rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
              · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
                · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
                · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
                  by_cases htriv : trivF ⟨P.other, t', i'⟩ = true
                  · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
                    obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
                    have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                      { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
                    rcases cmRes with _ | s₁
                    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                      subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
                    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem
                      subst hmem; exact hcm.2 s₁ rfl
                  · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                    split_ifs at hmem <;>
                      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs)
private theorem redFSAuthDFShiftedPaperMultiGen_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka qep l tStar : ℕ) (authH la : Bool)
    (A : AdversaryDF (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256) (Header Pt × E)) :
    redFSAuthDFShiftedPaperMultiGen (dhSchemeFb Dh) prng fs lam Δcka qep l tStar authH la A =
      redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) prng fs lam Δcka qep l tStar authH la A := by
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  have hInitEq : initFSMultiRaw (dhSchemeFb Dh) prng fs lam ⟨authH, some (l - 1), tStar⟩ false =
      initFSMultiRaw (dhScheme Dh) prng fs lam ⟨authH, some (l - 1), tStar⟩ false := rfl
  simp only [bind_assoc, hInitEq]; refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have hEs₀ : AllPartiesInv es₀ := by
    unfold initFSMultiRaw at hes₀; rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀; rw [mem_support_bind_iff] at hes₀; obtain ⟨_, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨_, _, hes₀⟩ := hes₀; simp only [support_pure, Set.mem_singleton_iff] at hes₀; subst hes₀
    intro P; cases P
    · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
    · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
  have hAg := hooksFSMulti_localCKAAgree Dh prng fs Δcka ⟨authH, some (l - 1), tStar⟩ false la
  generalize hhk₁ : hooksFSMulti (dhSchemeFb Dh) prng fs Δcka ⟨authH, some (l - 1), tStar⟩ false la = hk₁
  generalize hhk₂ : hooksFSMulti (dhScheme Dh) prng fs Δcka ⟨authH, some (l - 1), tStar⟩ false la = hk₂
  generalize hcfg : (⟨true, some (l - 1), tStar⟩ : Mode).cfg = cfg; generalize hπ : (⟨true, some (l - 1), tStar⟩ : Mode).policy = π
  rw [hhk₁, hhk₂] at hAg
  suffices hSim : ∀ es, AllPartiesInv es →
      (simulateQ (implEDFShiftedPaperGen (!authH) l hk₁ (2 + Δcka) qep fs.maxSkip tStar cfg π) A).run es =
      (simulateQ (implEDFShiftedPaperGen (!authH) l hk₂ (2 + Δcka) qep fs.maxSkip tStar cfg π) A).run es by
    exact congrArg (· >>= _) (hSim es₀ hEs₀)
  intro es hEs
  induction A using OracleComp.inductionOn generalizing es with
  | pure _ => simp
  | query_bind qy mx ih =>
    rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind]
    rcases qy with n | t_sm
    · change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]; exact bind_congr fun u => ih u es hEs
    · obtain ⟨hEq, hInv⟩ := implEDFShiftedPaper_localCKA_step hAg (!authH) l (2 + Δcka) qep
        fs.maxSkip tStar cfg π es t_sm hEs
      rw [hEq]; exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ih u es' (hInv _ hmem)
private def FSVROkMultiReachB (maxSkip k : ℕ)
    (rsv : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) : Prop :=
  match rsv with
  | .inl rs => RSReachB maxSkip k rs
  | .inr _ => True
private theorem rsReachB_skippedKeys_le {CK MK : Type} {maxSkip k B0 : ℕ}
    {rs : RatchetReceiverState CK MK} (h : RSReachB maxSkip k rs) (hkB : (k + 1) * (maxSkip + 1) ≤ B0) : rs.skippedKeys.length ≤ B0 := by
  have h1 : rs.skippedKeys.length ≤ rs.lastIndex := h.2
  have h2 : rs.lastIndex ≤ k * (maxSkip + 1) := h.1.1
  have h3 : k * (maxSkip + 1) ≤ (k + 1) * (maxSkip + 1) := Nat.mul_le_mul_right _ (Nat.le_succ k)
  omega
private theorem hooksFSMulti_vrInv_fsClamp_lFS
    {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ B0 : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    HooksVRInv (FSVROkMultiReachB maxForwardJumps)
      (hooksFSMulti cka prng (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo gMain la) where
  mono {_ _ rsv} hle hv := by cases rsv with | inl rs => exact hv.mono hle | inr _ => trivial
  startRecv_step _ _ t γ σ Tn h res hmem _ _ rsv := by
    dsimp only [hooksFSMulti] at hmem; rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    cases hcache : h.cache t with
    | none =>
      simp only [hcache] at hmem; split_ifs at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
      · rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq; trivial
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
    | some val =>
      rcases val with ⟨Tc, σc, k, optIdx⟩; simp only [hcache] at hmem
      by_cases hT : Tc = Tn
      · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
        rcases optIdx with _ | _
        · exact RSReachB.init
            ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps k
        · trivial
      · simp only [hT, ↓reduceIte] at hmem; split_ifs at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
        · rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
          rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq; trivial
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
  fsRecv_step ctx _ t0 rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩; dsimp only at hEq; subst hEq
    rcases rsv with rs | sIdx
    · dsimp only [hooksFSMulti, fsClamp] at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
      obtain ⟨o, ho, hEqO⟩ := Option.map_eq_some_iff.mp hmem.1.symm; obtain ⟨o₀, ho₀, rfl⟩ := Option.map_eq_some_iff.mp ho
      rcases o₀ with ⟨rs', i₀, m₀⟩
      cases hEqO; exact (RSReachB.receive_fromAEADPRG ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps _ hVR (by simpa [lFS] using ho₀)).2
    · dsimp only [hooksFSMulti] at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      generalize List.find? _ ((h.book sIdx).getD {}).fsTrans = matched at hmem
      by_cases hCond : ((matched.isNone && !(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0)) &&
          !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hCond, ↓reduceIte] at hmem
        cases la
        · simp only [Bool.false_eq_true, ↓reduceIte] at hmem; rw [StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨csAns, h₀⟩, _, hmem⟩ := hmem
          rcases csAns with _ | _
          · simp at hmem
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
            split_ifs at hmem <;>
              (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
               obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
               rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
               simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
               split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
               simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
               rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
                 simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
                 first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
        · simp at hmem
      · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
        split_ifs at hmem <;>
          (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
           obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
           rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
           simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
           split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
           simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
           rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
             simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
             first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFSMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; cases hEq; rfl
private theorem redFSAuthDFShiftedPaperMultiGen_fsClamp_fsAtomicB_eq_lFS
    {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (C : Crypto) (ℓ B0 L B_q q Δcka qep l tStar : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (authH la : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqB : q ≤ B_q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    redFSAuthDFShiftedPaperMultiGen cka (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep l tStar authH la A =
      redFSAuthDFShiftedPaperMultiGen cka (rootPRNG C.F encPt) (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        lam Δcka qep l tStar authH la A := by
  let prng := rootPRNG C.F encPt
  let fs₁ := fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  let fs₂ := fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  let mo' : Mode := ⟨true, some (l - 1), tStar⟩
  let hk₁ := hooksFSMulti cka prng fs₁ Δcka mo false la
  let hk₂ := hooksFSMulti cka prng fs₂ Δcka mo false la
  have hVRHk : HooksVRInv (FSVROkMultiReachB maxForwardJumps) hk₂ :=
    hooksFSMulti_vrInv_fsClamp_lFS cka prng C ℓ B0 encT idOf Δcka mo false la
  have hInitEq : initFSMultiRaw cka (rootPRNG C.F encPt)
      (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam ⟨authH, some (l - 1), tStar⟩ false = initFSMultiRaw cka (rootPRNG C.F encPt)
        (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) lam ⟨authH, some (l - 1), tStar⟩ false := by
    unfold initFSMultiRaw fsClamp fsAtomicB Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomic lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  have hms1 : (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := rfl
  have hms2 : (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)).maxSkip = maxForwardJumps := rfl
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper; simp only [bind_assoc, hInitEq, hms1, hms2]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, hVR₀⟩ : SMEngineInv L B_q q es₀.g ∧ SMVRInv (FSVROkMultiReachB maxForwardJumps) B_q q es₀.g := by
    unfold initFSMultiRaw at hes₀; rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨optIdx, h₂⟩, _, hes₀⟩ := hes₀
    simp only [support_pure, Set.mem_singleton_iff] at hes₀; subst hes₀
    refine ⟨(SMEngineInv.init _ false hB1 hBB).mono hqB, fun P t₀ v hv => ?_⟩
    cases P <;> simp only [mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
        rcases optIdx with _ | _
        · exact (RSReachB.init
            ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
            (lChainPRG C.F) maxForwardJumps k).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  have hFsSendEq : ∀ ctx P t ssv hdr m pair, atomicShortPubB m.1 = true →
      hk₁.fsSend ctx P t ssv hdr m pair = hk₂.fsSend ctx P t ssv hdr m pair := by
    intro ctx P t ssv hdr m pair hm
    rcases ssv with ss | sIdx
    · dsimp only [hk₁, hk₂, hooksFSMulti, fs₁, fs₂, fsClamp]; rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
    · rfl
  have hFsRecvEq : ∀ ctx P t rsv hdr e rec_ k', (k' + 1) * (maxForwardJumps + 1) ≤ B0 → FSVROkMultiReachB maxForwardJumps k' rsv →
      hk₁.fsRecv ctx P t rsv hdr e rec_ = hk₂.fsRecv ctx P t rsv hdr e rec_ := by
    intro ctx P t rsv hdr e rec_ k' hkB hvr
    rcases rsv with rs | sIdx
    · dsimp only [hk₁, hk₂, hooksFSMulti, fs₁, fs₂, fsClamp]
      rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e (rsReachB_skippedKeys_le hvr hkB)]
    · rfl
  have hStartSend : hk₁.startSend = hk₂.startSend := by
    unfold hk₁ hk₂ hooksFSMulti fs₁ fs₂ fsClamp fsAtomicB
      Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomic lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  have hStartRecv : hk₁.startRecv = hk₂.startRecv := by
    unfold hk₁ hk₂ hooksFSMulti fs₁ fs₂ fsClamp fsAtomicB
      Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomic lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  have hCommit : hk₁.commit = hk₂.commit := by unfold hk₁ hk₂ hooksFSMulti; rfl
  have hReveal : hk₁.reveal = hk₂.reveal := by unfold hk₁ hk₂ hooksFSMulti; rfl
  have hA_game : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q :=
    hq.of_imp fun x hx => by cases x <;> [cases hx; rfl]
  change (simulateQ (implEDFShiftedPaperGen (!authH) l hk₁ (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) A).run es₀ >>= _ =
    (simulateQ (implEDFShiftedPaperGen (!authH) l hk₂ (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) A).run es₀ >>= _
  generalize hhk₁ : hk₁ = hkL; generalize hhk₂ : hk₂ = hkR
  rw [hhk₂] at hVRHk; rw [hhk₁, hhk₂] at hFsSendEq hFsRecvEq hStartSend hStartRecv hCommit hReveal
  suffices hSim : ∀ q_rem es, A.IsQueryBoundP (ReductionDsl.isGameQuery (G := _)) q_rem →
      SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A → SMEngineInv L B_q q_rem es.g →
      SMVRInv (FSVROkMultiReachB maxForwardJumps) B_q q_rem es.g →
      (simulateQ (implEDFShiftedPaperGen (!authH) l hkL (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) A).run es =
      (simulateQ (implEDFShiftedPaperGen (!authH) l hkR (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) A).run es by
    exact congrArg (· >>= _) (hSim q es₀ hA_game hsh hInv₀ hVR₀)
  clear hq hA_game hsh
  intro q_rem es hoa hSendOk hInv hVR
  induction A using OracleComp.inductionOn generalizing q_rem es with
  | pure _ => simp
  | query_bind qy mx ih =>
    unfold SendMsgsOkDF at hSendOk; rw [isQueryBoundP_query_bind_iff] at hoa hSendOk
    rcases hoa with ⟨hq0, hmx⟩
    rcases hSendOk with ⟨hBad0, hSendMx⟩; rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u q_rem es (hmx u) (by simpa [SendMsgsOkDF] using hSendMx u) hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q_rem = q' + 1 := ⟨q_rem - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hBadFalse : badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
          (fun m => atomicShortPubB m.1) (.inr t_sm) = false :=
        Bool.eq_false_iff.mpr (hBad0.resolve_right (by omega))
      have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
      have hCommitE : commitE hkL = commitE hkR := by unfold commitE; rw [hCommit]
      have hvSendEq : ∀ s P m pair r, atomicShortPubB m.1 = true → (vSend hkL s P (s.st P) m pair r).run es.h =
            (vSend hkR s P (s.st P) m pair r).run es.h := by
        intro s P m pair r hm; rw [_root_.CryptoGames.SM.Engine.vSend_eq_bind, _root_.CryptoGames.SM.Engine.vSend_eq_bind,
          StateT.run_bind, StateT.run_bind]
        have hStep1 : _root_.CryptoGames.SM.Engine.vSendStep1 hkL s P (s.st P) r =
            _root_.CryptoGames.SM.Engine.vSendStep1 hkR s P (s.st P) r := by
          unfold _root_.CryptoGames.SM.Engine.vSendStep1; rw [hStartSend]
        rw [hStep1]; refine bind_congr fun ⟨s₁?, h₁⟩ => ?_
        rcases s₁? with _ | s₁
        · rfl
        · rcases hvS : s₁.vS with _ | ssv
          · simp only [hvS]
          · simp only [hvS, StateT.run_bind, hFsSendEq s P s₁.tcur ssv (s₁.tcur, s₁.curCkaMsg) m pair hm]
      have hvRecvEq : ∀ P c rec_, (vRecv hkL es.g P (es.g.st P) c rec_).run es.h = (vRecv hkR es.g P (es.g.st P) c rec_).run es.h := by
        intro P c rec_; rw [_root_.CryptoGames.SM.Engine.vRecv_eq_bind, _root_.CryptoGames.SM.Engine.vRecv_eq_bind]
        by_cases href : ((es.g.st P).id.sendsIn c.1.1 || decide ((es.g.st P).tcur + 1 < c.1.1)) = true
        · simp [href]
        · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          have hStep1 : _root_.CryptoGames.SM.Engine.vRecvStep1 hkL es.g P (es.g.st P) c =
              _root_.CryptoGames.SM.Engine.vRecvStep1 hkR es.g P (es.g.st P) c := by
            unfold _root_.CryptoGames.SM.Engine.vRecvStep1; rw [hStartRecv]
          rw [hStep1]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
          rcases s₁? with _ | (_ | s₁)
          · rfl
          · rfl
          · have hs₁VR : ∀ t v, s₁.vR t = some v → FSVROkMultiReachB maxForwardJumps (B_q - (q' + 1)) v := by
              unfold _root_.CryptoGames.SM.Engine.vRecvStep1 at hmem
              by_cases ht : c.1.1 = (es.g.st P).tcur + 1
              · simp only [ht, ↓reduceIte] at hmem
                rcases hTn : c.1.2 with _ | Tn
                · simp [hTn] at hmem
                · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
                  rcases srRes with _ | _ | ⟨γ', σ', rsv⟩
                  · simp at hmem
                  · simp at hmem
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    intro t₀ v₀ hv₀
                    by_cases ht₀ : t₀ = (es.g.st P).tcur + 1
                    · subst ht₀; simp only [Function.update_self, Option.some.injEq] at hv₀; subst hv₀
                      exact hVRHk.mono (Nat.zero_le _) (hVRHk.startRecv_step es.g P ((es.g.st P).tcur + 1)
                          (es.g.st P).γ (es.g.st P).root Tn es.h (some (some (γ', σ', rsv)), h₁) hsr γ' σ' rsv rfl)
                    · simp only [Function.update_of_ne ht₀] at hv₀; exact hVR P t₀ v₀ hv₀
              · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
                rcases hmem with ⟨rfl, _⟩; exact hVR P
            rcases hvRc : s₁.vR c.1.1 with _ | rsv
            · simp [hvRc]
            · simp only [hvRc, StateT.run_bind, hFsRecvEq es.g P c.1.1 rsv c.1 c.2 rec_ _ hkB (hs₁VR c.1.1 rsv hvRc)]
      have hStepEq : (implEDFShiftedPaperGen (!authH) l hkL (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t_sm)).run es =
          (implEDFShiftedPaperGen (!authH) l hkR (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t_sm)).run es := by
        rcases t_sm with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
        · change (transmitE hkL (2 + Δcka) qep mo'.policy (P, m, r)).run es =
            (transmitE hkR (2 + Δcka) qep mo'.policy (P, m, r)).run es
          have hm : atomicShortPubB m.1 = true := by simpa [badSendMsgDF] using hBadFalse
          unfold transmitE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
            · rfl
            · dsimp only
              by_cases hld : mo'.policy.leakDoom es.g s₁ = true
              · simp [hld]
              · simp only [hld, Bool.false_eq_true, ↓reduceIte, _root_.CryptoGames.SM.Engine.run_liftH_bind, hvSendEq s₁ P m none r hm]
        · change (challE hkL (2 + Δcka) qep mo'.cfg mo'.policy (P, m₀, m₁, r)).run es =
            (challE hkR (2 + Δcka) qep mo'.cfg mo'.policy (P, m₀, m₁, r)).run es
          have hm : atomicShortPubB m₀.1 = true ∧ atomicShortPubB m₁.1 = true := by
            simpa [badSendMsgDF, Bool.or_eq_false_iff, Bool.not_eq_false'] using hBadFalse
          unfold challE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
            · rfl
            · dsimp only
              by_cases hsc : (!(s₁.safeCh (2 + Δcka) P) || !((mo'.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P))) = true
              · simp [hsc]
              · simp only [hsc, Bool.false_eq_true, ↓reduceIte]
                by_cases hld : mo'.policy.leakDoom es.g s₁ = true
                · simp [hld]
                · have hmb : atomicShortPubB ((mo'.cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)).1 = true := by
                    dsimp only [mo', Mode.cfg, Option.getD]; cases es.g.b <;> [exact hm.1; exact hm.2]
                  simp only [hld, Bool.false_eq_true, ↓reduceIte, _root_.CryptoGames.SM.Engine.run_liftH_bind, hvSendEq s₁ P _ (some (m₀, m₁)) r hmb]
        · change (deliverE hkL maxForwardJumps mo'.cfg (P, c)).run es =
            (deliverE hkR maxForwardJumps mo'.cfg (P, c)).run es
          unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.inTransit P.other c with _ | rec_
            · rfl
            · simp only [_root_.CryptoGames.SM.Engine.run_liftH_bind, hvRecvEq P c (some rec_), hCommitE]
        · cases authH
          · change (injectEB1 hkL qep tStar mo'.cfg (P, c)).run es =
              (injectEB1 hkR qep tStar mo'.cfg (P, c)).run es
            unfold injectEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
            by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2)) = true
            · simp [href]
            · simp only [href, Bool.false_eq_true, ↓reduceIte, _root_.CryptoGames.SM.Engine.run_liftH_bind, hvRecvEq P c none, hCommitE]
          · change (_root_.CryptoGames.SM.Engine.injectE hkL (2 + Δcka) qep mo'.cfg (P, c)).run es =
              (_root_.CryptoGames.SM.Engine.injectE hkR (2 + Δcka) qep mo'.cfg (P, c)).run es
            unfold _root_.CryptoGames.SM.Engine.injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
            by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
            · simp [href]
            · simp only [href, Bool.false_eq_true, ↓reduceIte, _root_.CryptoGames.SM.Engine.run_liftH_bind, hvRecvEq P c none, hCommitE]
        · change (corrEShiftedPaper l hkL mo'.policy P).run es = (corrEShiftedPaper l hkR mo'.policy P).run es
          unfold corrEShiftedPaper; rw [hReveal]
        · cases authH <;>
            [ (change (deliverForgeEB1 hkL qep tStar mo'.cfg (P, c, c')).run es =
                 (deliverForgeEB1 hkR qep tStar mo'.cfg (P, c, c')).run es;
               unfold deliverForgeEB1);
              (change (deliverForgeE hkL (2 + Δcka) qep mo'.cfg (P, c, c')).run es =
                 (deliverForgeE hkR (2 + Δcka) qep mo'.cfg (P, c, c')).run es;
               unfold deliverForgeE) ]
          all_goals
            simp only [StateT.run_bind, StateT.run_get, pure_bind]
            by_cases hab : (es.abort || es.g.win) = true
            · simp [hab]
            · simp only [hab, Bool.false_eq_true, ↓reduceIte]
              rcases es.g.inTransit P.other c with _ | r
              · rfl
              · dsimp only
                by_cases hbad : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
                · simp only [hbad, ↓reduceIte]
                · simp only [hbad, Bool.false_eq_true, ↓reduceIte, _root_.CryptoGames.SM.Engine.run_liftH_bind, hvRecvEq P c' none, hCommitE]
      rw [hStepEq]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      exact ih u q' es' (by simpa using hmx u) (by simpa [SendMsgsOkDF] using hSendMx u)
        (implEDFShiftedPaper_inv (!authH) hkR l mo'.cfg mo'.policy es t_sm hInv (u, es') hmem)
        (implEDFShiftedPaper_vrInv (!authH) hkR hVRHk l mo'.cfg mo'.policy es t_sm hInv hVR (u, es') hmem)
private theorem hm_run_bind {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS α β : Type}
    (x : StateT HS (TComp tspec) α) (f : α → StateT HS (TComp tspec) β) (s : HS) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := rfl
private abbrev SafeZeroAll {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (Q : spec.Domain → Prop) (oa : OracleComp spec α) : Prop :=
  GuardedSafePost (fun _ _ => True) Q (fun _ => True) oa
private theorem safeZeroAll_to_isQueryBoundP {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {Q : spec.Domain → Prop} [DecidablePred Q] {oa : OracleComp spec α} (h : SafeZeroAll Q oa) : oa.IsQueryBoundP Q 0 := by
  induction h with
  | pure _ => simp
  | query_bind hQt _ ih =>
    rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl hQt, fun u => by simpa [hQt] using ih u trivial⟩
private theorem safeZeroAll_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {Q : spec.Domain → Prop} (a : α) : SafeZeroAll Q (pure a : OracleComp spec α) :=
  GuardedSafePost.pure trivial
private theorem safeZeroAll_run_pure {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS α : Type}
    {Q : (unifSpec + tspec).Domain → Prop} (a : α) (s : HS) : SafeZeroAll Q ((pure a : StateT HS (TComp tspec) α).run s) :=
  safeZeroAll_pure (a, s)
private theorem safeZeroAll_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {Q : spec.Domain → Prop} {oa : OracleComp spec α} {f : α → OracleComp spec β}
    (hoa : SafeZeroAll Q oa) (hf : ∀ a, SafeZeroAll Q (f a)) : SafeZeroAll Q (oa >>= f) :=
  hoa.bind fun a _ => hf a
private theorem redFSAuthDFShiftedPaperMultiGen_query_zero
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (cka : CKAScheme (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep l tStar : ℕ) (authH la : Bool)
    (MsgOk : M → Bool) (Pbad : (unifSpec + FSMultiSpec SS RS Pt M E).Domain → Prop) [DecidablePred Pbad]
    (hUnif0 : ∀ n, ¬ Pbad (.inl n)) (hCorrS : ∀ sIdx, ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩))
    (hTrans : ∀ sIdx hdr m, MsgOk m = true → ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, m)))))⟩))
    (hChall : ∀ sIdx hdr m₀ m₁, MsgOk m₀ = true → MsgOk m₁ = true → ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁)))))⟩))
    (hDeliv : ∀ sIdx hdr e, ¬ Pbad (.inr ⟨sIdx, .inl (.inr (hdr, e))⟩)) (hInj : ∀ sIdx hdr e, ¬ Pbad (.inr ⟨sIdx, .inr (hdr, e)⟩))
    (A : AdversaryDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256) (Header Pt × E))
    (hsh : SendMsgsOkDF MsgOk A) : (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l tStar authH la A).IsQueryBoundP
      Pbad 0 := by
  apply safeZeroAll_to_isQueryBoundP
  have hSample0 : ∀ (X : Type) [SampleableType X], SafeZeroAll Pbad (sampleT (tspec := FSMultiSpec SS RS Pt M E) X) := fun X _ =>
    GuardedSafePost.liftComp_unif hUnif0 ($ᵗ X : ProbComp X)
  have hSample : ∀ (X : Type) [SampleableType X] (h : FSMultiState Pt RSt K Pt E), SafeZeroAll Pbad
        ((StateT.lift (sampleT (tspec := FSMultiSpec SS RS Pt M E) X) :
          StateT (FSMultiState Pt RSt K Pt E) (TComp (FSMultiSpec SS RS Pt M E)) X).run h) := by
    intro X _ h; rw [StateT.run_lift]; exact safeZeroAll_bind (hSample0 X) fun _ => safeZeroAll_pure _
  have hLiftOk : ∀ sIdx (q : (_root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E).Domain), ¬ Pbad (.inr ⟨sIdx, q⟩) →
      ∀ h, SafeZeroAll Pbad ((liftFSMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) (Sig := RSt) (K := K) (I := Pt) sIdx
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E) (.inr q)))).run h) := by
    intro sIdx q hq h
    have hEq : ((liftFSMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) (Sig := RSt) (K := K) (I := Pt) sIdx
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E) (.inr q)))).run h) =
        ((liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS Pt M E) (.inr ⟨sIdx, q⟩)) :
          TComp (FSMultiSpec SS RS Pt M E) _) >>= fun a => pure (a, h)) := by
      simp [liftFSMulti, StateT.run_lift]
    rw [hEq]; exact GuardedSafePost.query_bind hq fun _ _ => safeZeroAll_pure _
  have hLookup : ∀ Ik (h : FSMultiState Pt RSt K Pt E),
      SafeZeroAll Pbad ((lookupMultiF (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) Ik).run h) := by
    intro Ik h; unfold lookupMultiF; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases h.table.lookup Ik with _ | _
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact safeZeroAll_bind (hSample K h) fun _ => safeZeroAll_pure _
    · exact safeZeroAll_run_pure _ _
  have hReg : ∀ Ik (h : FSMultiState Pt RSt K Pt E),
      SafeZeroAll Pbad ((regSessMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) Ik).run h) := by
    intro Ik h; unfold regSessMulti; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;>
      exact safeZeroAll_pure _
  have hRegOpt : ∀ sid (h : FSMultiState Pt RSt K Pt E),
      SafeZeroAll Pbad ((regSessOptMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) sid).run h) := by
    intro sid h; rcases sid with _ | Ik
    · simp only [regSessOptMulti]; exact safeZeroAll_run_pure _ _
    · rw [regSessOptMulti, map_eq_bind_pure_comp, hm_run_bind]; exact safeZeroAll_bind (hReg Ik h) fun _ => safeZeroAll_run_pure _ _
  have hRoot : ∀ mo t' Ik σ (h : FSMultiState Pt RSt K Pt E),
      SafeZeroAll Pbad ((rootFSMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) prng mo t' Ik σ).run h) := by
    intro mo t' Ik σ h; unfold rootFSMulti; split_ifs
    · exact safeZeroAll_run_pure _ _
    · rw [hm_run_bind]; refine safeZeroAll_bind (hSample Pt h) fun ⟨_, h₁⟩ => ?_
      rw [hm_run_bind]; exact safeZeroAll_bind (hSample K h₁) fun _ => safeZeroAll_run_pure _ _
    · rw [hm_run_bind]; exact safeZeroAll_bind (hLookup Ik h) fun _ => safeZeroAll_run_pure _ _
    · rw [hm_run_bind]; exact safeZeroAll_bind (hSample Pt h) fun _ => safeZeroAll_run_pure _ _
    · exact safeZeroAll_run_pure _ _
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  generalize hhk : hooksFSMulti cka prng fs Δcka ⟨authH, some (l - 1), tStar⟩ false la = hk
  have hStartSend : ∀ ctx P t' γ σ r h, SafeZeroAll Pbad ((hk.startSend ctx P t' γ σ r).run h) := by
    intro ctx P t' γ σ r h; subst hhk; dsimp only [hooksFSMulti]
    rcases r with _ | c
    · dsimp only; rw [hm_run_bind]; refine safeZeroAll_bind (hSample (BitVec 256) h) fun ⟨_, h₀⟩ => ?_
      rw [hm_run_bind]; refine safeZeroAll_bind (hRoot _ _ _ _ h₀) fun ⟨⟨_, _, sid⟩, h₁⟩ => ?_
      rw [hm_run_bind]; refine safeZeroAll_bind (hRegOpt sid h₁) fun _ => ?_
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
    · dsimp only; simp only [pure_bind]; rw [hm_run_bind]; refine safeZeroAll_bind (hRoot _ _ _ _ h) fun ⟨⟨_, _, sid⟩, h₁⟩ => ?_
      rw [hm_run_bind]; refine safeZeroAll_bind (hRegOpt sid h₁) fun _ => ?_
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
  have hStartRecv : ∀ ctx P t' γ σ Tn h, SafeZeroAll Pbad ((hk.startRecv ctx P t' γ σ Tn).run h) := by
    intro ctx P t' γ σ Tn h; subst hhk; dsimp only [hooksFSMulti]; rw [hm_run_bind, StateT.run_get, pure_bind]
    have hForged : ∀ b : Bool, SafeZeroAll Pbad ((if b then return some none
          else if (⟨authH, some (l - 1), tStar⟩ : Mode).auth && t' = (⟨authH, some (l - 1), tStar⟩ : Mode).tStar then
            if (⟨authH, some (l - 1), tStar⟩ : Mode).tL.isSome && (⟨authH, some (l - 1), tStar⟩ : Mode).tStar = (⟨authH, some (l - 1), tStar⟩ : Mode).tH then
              return none
            else do
              let kk := cka.receive γ Tn
              let _ ← lookupMultiF (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) kk.2
              let sIdx ← regSessMulti (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) kk.2
              return some (some (kk.1, (prng.up σ kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ)))
          else return some none).run h) := by
      intro b; split_ifs
      · exact safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
      · rw [hm_run_bind]; refine safeZeroAll_bind (hLookup _ h) fun ⟨_, h₁⟩ => ?_
        rw [hm_run_bind]; exact safeZeroAll_bind (hReg _ h₁) fun _ => safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
    rcases h.cache t' with _ | ⟨Tc, _, _, _⟩
    · exact hForged false
    · dsimp only; by_cases hTc : Tc = Tn
      · simp only [hTc, ↓reduceIte]; exact safeZeroAll_run_pure _ _
      · simp only [hTc, ↓reduceIte]; exact hForged false
  have hFsSend : ∀ ctx P t' ssv hdr m pair h,
      (match pair with | none => MsgOk m = true | some (m₀, m₁) => MsgOk m₀ = true ∧ MsgOk m₁ = true) →
      SafeZeroAll Pbad ((hk.fsSend ctx P t' ssv hdr m pair).run h) := by
    intro ctx P t' ssv hdr m pair h hpair; subst hhk; dsimp only [hooksFSMulti]
    rcases ssv with _ | sIdx
    · exact safeZeroAll_run_pure _ _
    · rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hc, ↓reduceIte]; cases la
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold corruptSenderQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, _⟩ => ?_
          rcases o with _ | _
          · exact safeZeroAll_run_pure _ _
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rcases pair with _ | ⟨m₀, m₁⟩
            · rw [hm_run_bind]; unfold transmitQuery
              refine safeZeroAll_bind (hLiftOk sIdx _ (hTrans sIdx hdr m hpair) _) fun ⟨e?, _⟩ => ?_
              rcases e? with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact safeZeroAll_pure _
            · rw [hm_run_bind]; unfold challengeQuery
              refine safeZeroAll_bind (hLiftOk sIdx _ (hChall sIdx hdr m₀ m₁ hpair.1 hpair.2) _) fun ⟨e?, _⟩ => ?_
              rcases e? with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact safeZeroAll_pure _
        · simp only [↓reduceIte]; exact safeZeroAll_run_pure _ _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        rcases pair with _ | ⟨m₀, m₁⟩
        · rw [hm_run_bind]; unfold transmitQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hTrans sIdx hdr m hpair) h) fun ⟨e?, _⟩ => ?_
          rcases e? with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact safeZeroAll_pure _
        · rw [hm_run_bind]; unfold challengeQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hChall sIdx hdr m₀ m₁ hpair.1 hpair.2) h) fun ⟨e?, _⟩ => ?_
          rcases e? with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact safeZeroAll_pure _
  have hFsRecv : ∀ ctx P t0 rsv hdr e rec_ h, SafeZeroAll Pbad ((hk.fsRecv ctx P t0 rsv hdr e rec_).run h) := by
    intro ctx P t0 rsv hdr e rec_ h; subst hhk; dsimp only [hooksFSMulti]
    rcases rsv with _ | sIdx
    · exact safeZeroAll_run_pure _ _
    · rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
      set matched := ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
      by_cases hc : ((matched.isNone && !_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0) && !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hc, ↓reduceIte]; cases la
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold corruptSenderQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, _⟩ => ?_
          rcases o with _ | _
          · exact safeZeroAll_run_pure _ _
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases hm : matched.isSome = true
            · simp only [hm, ↓reduceIte]; rw [hm_run_bind]; unfold deliverQuery
              refine safeZeroAll_bind (hLiftOk sIdx _ (hDeliv sIdx hdr e) _) fun ⟨res, _⟩ => ?_
              rcases res with _ | (_ | ⟨_, mo'⟩)
              · exact safeZeroAll_run_pure _ _
              · exact safeZeroAll_run_pure _ _
              · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
                · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                  rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
            · simp only [hm, Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold injectQuery
              refine safeZeroAll_bind (hLiftOk sIdx _ (hInj sIdx hdr e) _) fun ⟨res, _⟩ => ?_
              rcases res with _ | (_ | ⟨_, mo'⟩)
              · exact safeZeroAll_run_pure _ _
              · exact safeZeroAll_run_pure _ _
              · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
                · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                  rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
        · simp only [↓reduceIte]; exact safeZeroAll_run_pure _ _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        by_cases hm : matched.isSome = true
        · simp only [hm, ↓reduceIte]; rw [hm_run_bind]; unfold deliverQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hDeliv sIdx hdr e) h) fun ⟨res, _⟩ => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact safeZeroAll_run_pure _ _
          · exact safeZeroAll_run_pure _ _
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold injectQuery
          refine safeZeroAll_bind (hLiftOk sIdx _ (hInj sIdx hdr e) h) fun ⟨res, _⟩ => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact safeZeroAll_run_pure _ _
          · exact safeZeroAll_run_pure _ _
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
  have hReveal : ∀ ctx P vp h, SafeZeroAll Pbad ((hk.reveal ctx P vp).run h) := by
    intro ctx P vp h; subst hhk; dsimp only [hooksFSMulti]
    rcases vp.vS with _ | (_ | sIdx)
    · simp only [pure_bind]; split_ifs <;> exact safeZeroAll_run_pure _ _
    · simp only [pure_bind]; split_ifs <;> exact safeZeroAll_run_pure _ _
    · cases la
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold corruptSenderQuery
        refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, _⟩ => ?_
        rcases o with _ | _
        · simp only [pure_bind]; exact safeZeroAll_run_pure _ _
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; split_ifs <;> exact safeZeroAll_run_pure _ _
      · simp only [↓reduceIte, pure_bind]; exact safeZeroAll_run_pure _ _
  have hvSend : ∀ ctx P st m pair r h, (match pair with | none => MsgOk m = true | some (m₀, m₁) => MsgOk m₀ = true ∧ MsgOk m₁ = true) →
      SafeZeroAll Pbad ((vSend hk ctx P st m pair r).run h) := by
    intro ctx P st m pair r h hpair; rw [vSend_eq_bind, hm_run_bind]
    have hS1 : SafeZeroAll Pbad ((vSendStep1 hk ctx P st r).run h) := by
      unfold vSendStep1; split_ifs
      · rw [hm_run_bind]; refine safeZeroAll_bind (hStartSend _ _ _ _ _ _ _) fun ⟨sr, _⟩ => ?_
        rcases sr with _ | ⟨_, _, _, _⟩ <;> exact safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
    refine safeZeroAll_bind hS1 fun ⟨s₁?, h₁⟩ => ?_
    rcases s₁? with _ | s₁
    · exact safeZeroAll_run_pure _ _
    · dsimp only; rcases s₁.vS with _ | ssv
      · exact safeZeroAll_run_pure _ _
      · rw [hm_run_bind]; refine safeZeroAll_bind (hFsSend _ _ _ ssv _ m pair h₁ hpair) fun ⟨fr, _⟩ => ?_
        rcases fr with _ | _ <;> exact safeZeroAll_run_pure _ _
  have hvRecv : ∀ ctx P st c rec_ h, SafeZeroAll Pbad ((vRecv hk ctx P st c rec_).run h) := by
    intro ctx P st c rec_ h; rw [vRecv_eq_bind]; split_ifs
    · exact safeZeroAll_run_pure _ _
    · rw [hm_run_bind]
      have hS1 : SafeZeroAll Pbad ((vRecvStep1 hk ctx P st c).run h) := by
        unfold vRecvStep1; split_ifs
        · rcases c.1.2 with _ | _
          · exact safeZeroAll_run_pure _ _
          · rw [hm_run_bind]; refine safeZeroAll_bind (hStartRecv _ _ _ _ _ _ _) fun ⟨sr, _⟩ => ?_
            rcases sr with _ | (_ | _) <;> exact safeZeroAll_run_pure _ _
        · exact safeZeroAll_run_pure _ _
      refine safeZeroAll_bind hS1 fun ⟨s₁?, h₁⟩ => ?_
      rcases s₁? with _ | (_ | s₁)
      · exact safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
      · dsimp only; rcases s₁.vR c.1.1 with _ | rsv
        · exact safeZeroAll_run_pure _ _
        · rw [hm_run_bind]; refine safeZeroAll_bind (hFsRecv _ _ _ rsv _ _ rec_ h₁) fun ⟨fr, _⟩ => ?_
          rcases fr with _ | (_ | _) <;> exact safeZeroAll_run_pure _ _
  have hCommit : ∀ s P old new pos es0, SafeZeroAll Pbad ((commitE hk s P old new pos).run es0) := by
    intro s P old new pos es0; subst hhk; unfold commitE; dsimp only [hooksFSMulti]
    rw [run_liftH_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
  have hInit : SafeZeroAll Pbad (initFSMultiRaw cka prng fs lam ⟨authH, some (l - 1), tStar⟩ false) := by
    unfold initFSMultiRaw; exact safeZeroAll_bind (hSample0 KR) fun kr => safeZeroAll_bind (hSample0 (BitVec 256)) fun _ =>
      safeZeroAll_bind (hRoot _ 0 lam (prng.init kr) {}) fun ⟨⟨_, _, sid⟩, h₁⟩ =>
      safeZeroAll_bind (hRegOpt sid h₁) fun _ => safeZeroAll_pure _
  rw [bind_assoc]; refine safeZeroAll_bind hInit fun es₀ => ?_
  suffices hSim : SendMsgsOkDF MsgOk A → ∀ es, SafeZeroAll Pbad
      ((simulateQ (implEDFShiftedPaperGen (!authH) l hk (2 + Δcka) qep fs.maxSkip tStar
        (⟨true, some (l - 1), tStar⟩ : Mode).cfg (⟨true, some (l - 1), tStar⟩ : Mode).policy) A).run es) by
    exact safeZeroAll_bind (hSim hsh es₀) fun _ => safeZeroAll_pure _
  clear hsh
  induction A using OracleComp.inductionOn with
  | pure _ => intro _ _; simp only [simulateQ_pure, StateT.run_pure]; exact safeZeroAll_pure _
  | query_bind qy mx ih =>
    intro hSendOk es; unfold SendMsgsOkDF at hSendOk
    rw [isQueryBoundP_query_bind_iff] at hSendOk; rcases hSendOk with ⟨hBad0, hSendMx⟩; rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    refine safeZeroAll_bind ?_ fun ⟨u, es'⟩ => ih u (by simpa [SendMsgsOkDF] using hSendMx u) es'
    rcases qy with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · change SafeZeroAll Pbad ((coinsE n).run es); unfold coinsE; rw [StateT.run_lift]
      exact GuardedSafePost.query_bind (hUnif0 n) fun _ _ => safeZeroAll_pure _
    · have hm : MsgOk m = true := by
        simpa [badSendMsgDF] using Bool.eq_false_iff.mpr (hBad0.resolve_right (Nat.not_lt_zero 0))
      change SafeZeroAll Pbad ((transmitE hk (2 + Δcka) qep _ (P, m, r)).run es)
      unfold transmitE abortE; rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · exact safeZeroAll_run_pure _ _
        · dsimp only
          by_cases hld : ((⟨true, some (l - 1), tStar⟩ : Mode).policy.leakDoom es.g s₁) = true
          · simp only [hld, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
          · simp only [hld, Bool.false_eq_true, ↓reduceIte]
            rw [run_liftH_bind]; refine safeZeroAll_bind (hvSend _ P _ m none r _ hm) fun ⟨r?, _⟩ => ?_
            rcases r? with _ | _ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _)
    · have hm01 : MsgOk m₀ = true ∧ MsgOk m₁ = true := by
        simpa [badSendMsgDF, Bool.or_eq_true] using Bool.eq_false_iff.mpr (hBad0.resolve_right (Nat.not_lt_zero 0))
      change SafeZeroAll Pbad ((challE hk (2 + Δcka) qep _ _ (P, m₀, m₁, r)).run es)
      unfold challE abortE; rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only
      by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte]; exact safeZeroAll_run_pure _ _
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · exact safeZeroAll_run_pure _ _
        · dsimp only
          by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((⟨true, some (l - 1), tStar⟩ : Mode).cfg (M := M) |>.challAllowedIn (s₁.epoch P))) = true
          · simp only [hch, ↓reduceIte]; exact safeZeroAll_run_pure _ _
          · simp only [hch, Bool.false_eq_true, ↓reduceIte]
            by_cases hld : ((⟨true, some (l - 1), tStar⟩ : Mode).policy.leakDoom es.g s₁) = true
            · simp only [hld, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · simp only [hld, Bool.false_eq_true, ↓reduceIte]
              rw [run_liftH_bind]; refine safeZeroAll_bind (hvSend _ P _ _ (some (m₀, m₁)) r _ hm01) fun ⟨r?, _⟩ => ?_
              rcases r? with _ | _ <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _)
    · change SafeZeroAll Pbad ((deliverE hk fs.maxSkip _ (P, c)).run es)
      unfold deliverE abortE; rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rcases es.g.inTransit P.other c with _ | _
        · exact safeZeroAll_run_pure _ _
        · dsimp only; rw [run_liftH_bind]; refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
          rcases r? with _ | (_ | ⟨_, _, _, _⟩)
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
          · dsimp only; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [StateT.run_bind]; refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
            rcases s₁? with _ | _
            · exact safeZeroAll_run_pure _ _
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
    · change SafeZeroAll Pbad
        ((_root_.CryptoGames.SM.Engine.injectEGen (!authH) hk (2 + Δcka) qep tStar _ (P, c)).run es)
      cases authH <;> simp only [_root_.CryptoGames.SM.Engine.injectEGen, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> ·
        (try unfold injectEB1); (try unfold _root_.CryptoGames.SM.Engine.injectE); unfold abortE
        rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
        · exact safeZeroAll_run_pure _ _
        · rw [run_liftH_bind]; refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
          rcases r? with _ | (_ | ⟨_, _, _, _⟩)
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; split_ifs
            · exact safeZeroAll_run_pure _ _
            · rw [StateT.run_bind]; refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
              rcases s₁? with _ | _
              · exact safeZeroAll_run_pure _ _
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
            · exact safeZeroAll_run_pure _ _
    · change SafeZeroAll Pbad ((corrEShiftedPaper l hk _ P).run es)
      unfold corrEShiftedPaper abortE; rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
      · rw [run_liftH_bind]; refine safeZeroAll_bind (hReveal _ _ _ _) fun ⟨r?, _⟩ => ?_
        rcases r? with _ | _ <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _)
    · change SafeZeroAll Pbad
        ((_root_.CryptoGames.SM.Engine.deliverForgeEGen (!authH) hk (2 + Δcka) qep tStar _ (P, c, c')).run es)
      cases authH <;> simp only [_root_.CryptoGames.SM.Engine.deliverForgeEGen, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> ·
        (try unfold deliverForgeEB1); (try unfold deliverForgeE); unfold abortE
        rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
        · exact safeZeroAll_run_pure _ _
        · rcases es.g.inTransit P.other c with _ | _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; split_ifs
            · exact safeZeroAll_run_pure _ _
            · rw [run_liftH_bind]; refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
              rcases r? with _ | (_ | ⟨_, _, _, _⟩)
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
              · exact safeZeroAll_run_pure _ _
              · dsimp only; split_ifs
                · exact safeZeroAll_run_pure _ _
                · rw [StateT.run_bind]; refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
                  rcases s₁? with _ | _
                  · exact safeZeroAll_run_pure _ _
                  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact safeZeroAll_pure _
                · exact safeZeroAll_run_pure _ _
private theorem sendMsgsOkDF_true {St M Coins C : Type}
    (oa : AdversaryDF St M Coins C) : SendMsgsOkDF (fun _ : M => true) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp [SendMsgsOkDF]
  | query_bind qy mx ih =>
    unfold SendMsgsOkDF at ih ⊢; rw [isQueryBoundP_query_bind_iff]
    have h0 : badSendMsgDF (St := St) (Coins := Coins) (C := C) (fun _ : M => true) qy = false := by
      rcases qy with _ | ((((((_ | _) | _) | _) | _) | _)) <;> simp [badSendMsgDF]
    exact ⟨Or.inl (by simp [h0]), fun u => by simpa [h0] using ih u⟩
private theorem redFSAuthDFShiftedPaperMultiGen_noCr
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (cka : CKAScheme (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep l tStar : ℕ) (authH la : Bool)
    (A : AdversaryDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256) (Header Pt × E)) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l tStar authH la A).IsQueryBoundP
      (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 :=
  redFSAuthDFShiftedPaperMultiGen_query_zero cka prng fs lam Δcka qep l tStar authH la
    (fun _ => true) (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) A (sendMsgsOkDF_true A)
private theorem redFSAuthDFShiftedPaperMultiGen_encBadMsg
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (ℓ Δcka qep l tStar : ℕ) (authH la : Bool) (s : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l tStar authH la A).IsQueryBoundP
      (fun x => (match x with
        | .inl _ => false
        | .inr ⟨s', qv⟩ => decide (s' = s) &&
            encBadMsg (SS := RatchetSenderState (BitVec 256)) (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (C := ℕ × LibsignalCiphertextWithSalt32)
              (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr qv)) = true) 0 :=
  redFSAuthDFShiftedPaperMultiGen_query_zero (dhScheme Dh) (rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l tStar authH la
    (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) _ (by simp) (by simp [encBadMsg])
    (fun _ _ m hm => by have h1 := atomicShortPubB_imp_shortB hm; simp_all [encBadMsg, atomicShortB]) (fun _ _ m₀ m₁ hm₀ hm₁ => by
      have h0 := atomicShortPubB_imp_shortB hm₀
      have h1 := atomicShortPubB_imp_shortB hm₁
      simp_all [encBadMsg, atomicShortB])
    (by simp [encBadMsg]) (by simp [encBadMsg]) A hsh

/-- Stage-2 Hop-3 `B2` (`localAuthDFShiftedPaper`) bound into `fsAeadAuthSlotSumBound` +
`4 * macForgeryTerm` at `qR = min (2 * q) (q + 2)` (`N11b`). -/
theorem localAuthDFShiftedPaper_le_casePaperAtomic_sum_min
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (Z : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, Z.D k (Z.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q qep t : ℕ)
    (hq32 : 2 * q + 25002 < 2 ^ 32)
    (ht : t ∈ Finset.Ico 3 ((qep + 1) + 2))
    (challAdvDF : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq_ch : MakesAtMostQueriesDF challAdvDF q)
    (hsh_ch : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) challAdvDF)
    (hg_ch : GuardedSMDFShort challAdvDF) :
    𝒟[localAuthDFShiftedPaper (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) (t - 2)
        (some ((t - 2) - 1)) t challAdvDF] {true} ≤
      (∑ j ∈ Finset.range q,
        CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2))
          (fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)))
          (fun stage la =>
            (redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT (idsOf idA idB) lam
              stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t).eval (fun _ => challAdvDF) ())) +
      4 * macForgeryTerm Z q := by
  have ht3 : 3 ≤ t := (Finset.mem_Ico.mp ht).1
  have ht_lt : t < (qep + 1) + 2 := (Finset.mem_Ico.mp ht).2
  have ht_le3 : t ≤ (qep + 1) + 3 := by omega
  have hqR_le : min (2 * q) (q + 2) ≤ 2 * q + 2 := (Nat.min_le_left _ _).trans (by omega)
  have hne2 : ¬ (2 ≤ t ∧ (some (t - 3) : Option ℕ) = some (t - 2)) := by
    rintro ⟨_, hEq⟩; simp only [Option.some.injEq] at hEq; omega
  let idOf := idsOf idA idB
  let B0 := (q + 1) * (maxForwardJumps + 1)
  obtain ⟨R_sh, hR_sh⟩ : ∃ R_sh : Bool → _root_.ReductionDsl.CostedReduction
        (Computational.Proofs.SessionCostedFig8.BundlesCompilers.fig8CkaOpsShallow ℓ Pt Z Dh encPt encT idOf lam B0)
        (_root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (_root_.CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (_root_.CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        .unit .unit .bool .bool,
      ∀ la, R_sh la = redFSAuthDFShiftedPaperMultiProg (q + 1) B0 1 (qep + 1) maxForwardJumps (t - 2) t la :=
    ⟨_, fun _ => rfl⟩
  have hActive : ∀ stage la j, (redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t) =
      compileFsMultiDFAtomic ℓ Pt Z Dh encPt encT idOf lam stage la j (qep + 1) (min (2 * q) (q + 2)) B0 (R_sh la) := by
    intro stage la j; rw [hR_sh la]
    unfold redFSAuthDFCasePaperMultiAtomicProg; rw [ite_eq_right_iff.mpr fun h => absurd h hne2]
    rw [ite_eq_left_iff.mpr fun h => absurd ⟨ht3, rfl⟩ h]; unfold redFSAuthDFShiftedPaperMultiAtomicProg
    dsimp only; rw [ite_eq_left_iff.mpr fun h => absurd ⟨ht_le3, hqR_le⟩ h]
  have hA_inr : challAdvDF.IsQueryBoundP (fun x => x.isRight = true) q := hq_ch.of_imp fun x hx => by cases x <;> [cases hx; rfl]
  have hSessQ : ∀ la s, ((R_sh la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true) (min (2 * q) (q + 2)) :=
    fun la s => (Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK.redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min
      (q + 1) B0 1 (qep + 1) maxForwardJumps (t - 2) t true la s q (R_sh la) (hR_sh la) challAdvDF
      (hA_inr.of_imp fun x hx => by cases x <;> [cases hx; rfl])).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx
  have hEval : ∀ la, (R_sh la).eval (fun _ => challAdvDF) () = redFSAuthDFShiftedPaperMulti (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 (qep + 1) (t - 2) t la challAdvDF := by
    intro la; rw [hR_sh la]
    have hB1 : q + 1 ≤ q + 1 := le_rfl
    have hBB : q * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    have hEv0 := redFSAuthDFShiftedPaperMultiGenProg_eval_clamp (KR := BitVec 256) (RSt := BitVec 256) (K := BitVec 256) (lam := lam)
      (eqT := (· == ·)) (eqI := (· == ·)) (eqM := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
      (eqE := @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq)
      (dhSchemeFb Dh) (rootPRNG Z.F encPt) (fsAtomicB Z ℓ encT idOf B0) (q + 1) B0 q 1 (qep + 1) (t - 2) t true la
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hB1 hBB challAdvDF q hq_ch le_rfl
    have hms : (fsAtomicB Z ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl; rw [hms] at hEv0
    have hStep1 := redFSAuthDFShiftedPaperMultiGen_dhSchemeFb_eq Dh (rootPRNG Z.F encPt)
      (fsClamp B0 (fsAtomicB Z ℓ encT idOf B0)) lam 1 (qep + 1) (t - 2) t true la challAdvDF
    have hStep2 := redFSAuthDFShiftedPaperMultiGen_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) Z ℓ B0 (q + 1) q q
      1 (qep + 1) (t - 2) t encPt encT idOf lam true la le_rfl hB1 hBB challAdvDF hq_ch le_rfl hsh_ch
    have hStep3 := redFSAuthDFShiftedPaperMultiGen_fsClamp_fromAEADPRG (dhScheme Dh) (rootPRNG Z.F encPt)
      ((lAead Z protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG Z.F) maxForwardJumps (q + 1) B0 q 1 (qep + 1) (t - 2) t lam true la le_rfl hB1 hBB challAdvDF q hq_ch le_rfl
    have hlFS : ∀ ms, _root_.CryptoGames.FSAEAD.fromAEADPRG
        ((lAead Z protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)) (lChainPRG Z.F) ms =
      lFS Z protoSignalCodec ℓ encT idOf ms := fun _ => rfl
    rw [hlFS] at hStep3; exact hEv0.trans (hStep1.trans (hStep2.trans hStep3))
  have hNoCr : ∀ la, ((R_sh la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
      (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 := fun la => by
    rw [hEval la]; exact (redFSAuthDFShiftedPaperMultiGen_noCr (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 (qep + 1) (t - 2) t true la challAdvDF).of_imp
      fun x hx => by rcases x with _ | ⟨_, ((_ | _) | _) | _⟩ <;> exact hx
  have hShort : ∀ la s, ((R_sh la).eval (fun _ => challAdvDF) ()).IsQueryBoundP (fun x => (match x with
        | .inl _ => false
        | .inr ⟨s', qv⟩ => decide (s' = s) &&
            encBadMsg (SS := RatchetSenderState (BitVec 256)) (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (C := ℕ × LibsignalCiphertextWithSalt32)
              (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr qv)) = true) 0 := fun la s => by
    rw [hEval la]; exact (redFSAuthDFShiftedPaperMultiGen_encBadMsg Z Dh encPt encT idOf lam ℓ 1 (qep + 1) (t - 2) t true la s
      challAdvDF hsh_ch).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx
  have hMB0 : q ≤ ((qep + 1) + 2) * B0 + B0 * B0 + 1 := by
    have hqB0 : q ≤ B0 := by dsimp only [B0]; unfold maxForwardJumps; omega
    have h1 : q ≤ ((qep + 1) + 2) * B0 := le_trans hqB0 (Nat.le_mul_of_pos_left B0 (by omega))
    omega
  have hqR_B0 : min (2 * q) (q + 2) ≤ B0 :=
    (Nat.min_le_left _ _).trans (by dsimp only [B0]; unfold maxForwardJumps; omega)
  have hqR_sim : min (2 * q) (q + 2) ≤ 2 * min (2 * q) (q + 2) + 4 := by
    have h1 : min (2 * q) (q + 2) ≤ 2 * min (2 * q) (q + 2) :=
      Nat.le_mul_of_pos_left (min (2 * q) (q + 2)) (by omega)
    exact le_trans h1 (Nat.le_add_right _ 4)
  have hCompat0 := compileFsMultiDFAtomic_routerAdvCompat ℓ Pt Z Dh encPt encT
    (pure ()) (fun _ => idOf) (fun _ => lam) hℓ hinj (qep + 1) (min (2 * q) (q + 2)) q B0 hMB0 hqR_B0 (fun la _ _ => R_sh la) (fun _ => challAdvDF)
    (fun la _ _ s => ((hSessQ la s).mono hqR_sim).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx)
    (fun la _ _ => (hNoCr la).of_imp fun x hx => by rcases x with _ | ⟨_, ((_ | _) | _) | _⟩ <;> exact hx)
    (fun la _ _ s => (hShort la s).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx)
  have hCompat : RouterAdvCompat Z protoSignalCodec ℓ encT (pure ()) (fun _ => idOf) maxForwardJumps (min (2 * q) (q + 2)) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 (qep + 1) (t - 2) t la challAdvDF))
      (fun stage la j _ => (redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t).eval (fun _ => challAdvDF) ()) := by
    simpa only [hEval, hActive] using hCompat0
  have hF_q : ∀ j < q, ∀ stage la, MakesAtMostQueries ((redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t).eval (fun _ => challAdvDF) ()) (min (2 * q) (q + 2)) := by
    intro j _ stage la; rw [hActive stage la j]
    have hQ := compileFsMultiDFAtomic_isQueryBoundP ℓ Pt Z Dh encPt encT idOf lam
      stage la j (qep + 1) (min (2 * q) (q + 2)) B0 (R_sh la) challAdvDF (fun _ => true) (min (2 * q) (q + 2))
      ((hSessQ la j).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> simp only [Bool.and_true] at hx <;> exact hx)
    exact hQ.of_imp fun x hx => by cases x <;> exact hx
  have hF_sh : ∀ j < q, ∀ stage la, EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
      ((redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t).eval (fun _ => challAdvDF) ()) := by
    intro j _ stage la; rw [hActive stage la j]; exact compileFsMultiDFAtomic_encMsgsOk ℓ Pt Z Dh encPt encT idOf lam
      stage la j (qep + 1) (min (2 * q) (q + 2)) B0 (R_sh la) challAdvDF (fun m => atomicShortB m.1)
      ((hShort la j).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx)
  have hMain := Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti.localAuthDFShiftedPaper_le_fsAuthCompBoundWith_min
      ℓ Pt Z Dh hD encPt encT hinj hdum idOf lam hℓ q 1 (qep + 1) (t - 2) t hq32 ht3 rfl challAdvDF hq_ch hsh_ch hg_ch
      (fun stage la j => (redFSAuthDFCasePaperMultiAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t).eval (fun _ => challAdvDF) ()) hCompat hF_q hF_sh
  have hms25000 : maxForwardJumps = 25000 := rfl
  simpa only [hms25000, fsAuthCompBoundWith_eq_fsAeadAuthSlotSumBound] using hMain

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B2
